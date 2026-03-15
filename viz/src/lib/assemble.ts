import type {
	FunctionTrace, TraceEvent, AsmEvent, BlockView,
	WasmGroupView, OpView, StackState
} from './types';

/** Format a trace event as a human-readable operation string. */
function formatEvent(e: TraceEvent, func: FunctionTrace): string {
	switch (e.type) {
		case 'define': {
			const v = e.value;
			if (v === 'pending') return `${e.vreg} = <pending>`;
			if ('preg' in v) return `${e.vreg} = PReg(${v.preg})`;
			return `${e.vreg} = #${v.const}`;
		}
		case 'setslot': {
			const region = func.regions.find(r => r.id === e.region);
			return `${region?.label ?? e.region}[${e.index}] <- ${e.vreg}`;
		}
		case 'clearslot': {
			const region = func.regions.find(r => r.id === e.region);
			return `${region?.label ?? e.region}[${e.index}]:pop -> ${e.vreg}`;
		}
		case 'clobber':
			return `clobber ${e.vreg}`;
		case 'resolve':
			return `resolve ${e.vreg}`;
		case 'ir': {
			const inst = e.inst;
			if (inst === 'ret') return 'ret';
			if ('alu' in inst) return `${inst.alu.dst} = ${inst.alu.op} ${inst.alu.lhs}, ${inst.alu.rhs}`;
			if ('call' in inst) return `call ${inst.call.target}`;
			if ('branch' in inst) return `br ${inst.branch.target}`;
			if ('br_if' in inst) return `br_if ${inst.br_if.cond} then ${inst.br_if.block_if} else ${inst.br_if.block_else}`;
			return '?';
		}
		default:
			return '';
	}
}

/** Extract vregs read by an event. */
function vregsRead(e: TraceEvent): string[] {
	switch (e.type) {
		case 'setslot': return [e.vreg];
		case 'clearslot': return [e.vreg];
		case 'clobber': return [e.vreg];
		case 'resolve': return [e.vreg];
		case 'ir': {
			const inst = e.inst;
			if (inst === 'ret') return [];
			if ('alu' in inst) return [inst.alu.lhs, inst.alu.rhs];
			if ('br_if' in inst) return [inst.br_if.cond];
			return [];
		}
		default: return [];
	}
}

/** Extract vregs defined by an event. */
function vregsDefined(e: TraceEvent): string[] {
	switch (e.type) {
		case 'define': return [e.vreg];
		case 'ir': {
			const inst = e.inst;
			if (inst !== 'ret' && 'alu' in inst) return [inst.alu.dst];
			return [];
		}
		default: return [];
	}
}

/** Assemble raw events into block views. */
export function assembleBlocks(func: FunctionTrace): BlockView[] {
	const blocks: BlockView[] = [];
	let currentBlock: BlockView | null = null;
	let currentGroup: WasmGroupView | null = null;
	const asmEvents = func.events.filter((e): e is AsmEvent => e.type === 'asm');
	const asmByParent = new Map<number, AsmEvent[]>();
	for (const asm of asmEvents) {
		const list = asmByParent.get(asm.parent) ?? [];
		list.push(asm);
		asmByParent.set(asm.parent, list);
	}

	for (const event of func.events) {
		if (event.type === 'block_start') {
			currentBlock = { id: event.block, successors: event.successors, groups: [] };
			blocks.push(currentBlock);
			currentGroup = null;
			continue;
		}

		if (event.type === 'wasm_op') {
			currentGroup = { pc: event.pc, label: event.label, ops: [] };
			currentBlock?.groups.push(currentGroup);
			continue;
		}

		if (event.type === 'asm') continue; // handled via parent lookup

		if (!currentBlock || !currentGroup) continue;

		const op: OpView = {
			seq: event.seq,
			text: formatEvent(event, func),
			event,
			asm: asmByParent.get(event.seq) ?? [],
		};
		currentGroup.ops.push(op);
	}

	return blocks;
}

/** Compute stack state at a given seq by replaying events. */
export function computeStateAt(func: FunctionTrace, targetSeq: number): StackState {
	const state: StackState = { locals: [], ops: [], fibre: [] };

	function getStack(region: string): string[] {
		if (region === 'locals') return state.locals;
		if (region === 'operands') return state.ops;
		if (region === 'fibre') return state.fibre;
		return [];
	}

	for (const event of func.events) {
		if (event.seq > targetSeq) break;

		switch (event.type) {
			case 'setslot': {
				const stack = getStack(event.region);
				if (event.index >= stack.length) {
					stack.push(event.vreg);
				} else {
					stack[event.index] = event.vreg;
				}
				break;
			}
			case 'clearslot': {
				const stack = getStack(event.region);
				if (event.index === stack.length - 1) {
					stack.pop();
				}
				break;
			}
		}
	}

	return state;
}

export { vregsRead, vregsDefined };
