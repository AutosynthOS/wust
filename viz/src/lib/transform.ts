/**
 * Shared transform: raw trace events → structured view.
 *
 * Used by both the frontend (import) and CLI (bun scripts/transform.ts).
 * No fs, no process — pure data transformation.
 */

// ---- Output types ----

export interface FunctionView {
	index: number;
	vreg_defs: VRegDefView[];
	vreg_refs: VRegRefView[];
	regions: RegionDefView[];
	blocks: BlockView[];
}

export interface VRegRefView {
	id: string;
	width: string;
	source: VRegRefSourceView;
}

export type VRegRefSourceView =
	| { kind: 'direct'; target: string }
	| { kind: 'phi'; sources: { block: string; vreg: string }[] };

export interface VRegDefView {
	id: string;
	width: string;
	target: string | null;
}

export interface RegionDefView {
	label: string;
	base: string;
	base_offset: number;
}

export interface BlockView {
	id: string;
	groups: GroupView[];
	successors: string[];
}

export interface GroupView {
	pc: number | null;
	label: string;
	ops: OpView[];
}

export interface OpView {
	seq: number;
	kind: 'ir' | 'reg';
	inst: unknown;
	text: string;
	asm: AsmView[];
	region_snapshot: RegionSnapshotView[] | null;
	regalloc_snapshot: RegAllocSnapshotView | null;
}

export interface AsmView {
	addr: number;
	text: string;
	origin: string;
}

export interface RegionSnapshotView {
	label: string;
	slots: string[];
}

export interface RegAllocSnapshotView {
	bindings: { preg: string; vreg: string | null }[];
	vreg_locs: VRegLocView[];
}

export interface VRegLocView {
	vreg: string;
	loc: 'reg' | 'mem' | 'const' | 'pending';
	preg?: string;
	dirty?: boolean;
}

// ---- Formatting helpers ----

/** Format a VReg, resolving Refs through the refs table. */
export function fmtVreg(v: unknown, refs: VRegRefView[]): string {
	if (typeof v === 'number') return `v${v}`;
	if (typeof v === 'object' && v !== null) {
		if ('Def' in v) return `v${(v as { Def: number }).Def}`;
		if ('Ref' in v) {
			const id = (v as { Ref: number }).Ref;
			const ref = refs[id];
			if (ref) {
				if (ref.source.kind === 'direct') return ref.source.target;
				const srcs = ref.source.sources.map(s => s.vreg).join(',');
				return `\u03C6(${srcs})`;
			}
			return `r${id}`;
		}
	}
	return String(v);
}

/** Raw vreg id string without resolving refs. */
export function fmtVregRaw(v: unknown): string {
	if (typeof v === 'number') return `v${v}`;
	if (typeof v === 'object' && v !== null) {
		if ('Def' in v) return `v${(v as { Def: number }).Def}`;
		if ('Ref' in v) return `r${(v as { Ref: number }).Ref}`;
	}
	return String(v);
}

export function fmtPreg(id: number): string {
	if (id === 31) return 'sp';
	return `x${id}`;
}

function fmtWidth(w: string): string {
	if (w === 'W32') return 'i32';
	if (w === 'W64') return 'i64';
	return w;
}

function fmtBlockId(b: unknown): string {
	if (b === 'Entry') return 'Entry';
	if (b === 'Epilogue') return 'Epilogue';
	if (typeof b === 'object' && b !== null) {
		if ('User' in b) return `User(${(b as { User: number }).User})`;
		if ('Gen' in b) return `Gen(${(b as { Gen: number }).Gen})`;
	}
	return String(b);
}

function fmtAluOp(op: unknown): string {
	if (typeof op === 'string') return op.toLowerCase();
	if (typeof op === 'object' && op !== null && 'Comp' in op) {
		return (op as { Comp: string }).Comp.toLowerCase();
	}
	return String(op);
}

export function fmtRegInst(inst: unknown, refs: VRegRefView[]): string {
	const v = (x: unknown) => fmtVreg(x, refs);
	if (typeof inst !== 'object' || inst === null) return String(inst);
	if ('Define' in inst) {
		const d = (inst as { Define: { vreg: unknown; value: unknown } }).Define;
		const val = d.value;
		if (val === 'InstDst') return `${v(d.vreg)} = <pending>`;
		if (typeof val === 'object' && val !== null) {
			if ('Const' in val) return `${v(d.vreg)} = #${(val as { Const: number }).Const}`;
			if ('PReg' in val) return `${v(d.vreg)} = ${fmtPreg((val as { PReg: number }).PReg)}`;
		}
		return `define ${v(d.vreg)}`;
	}
	if ('SetSlot' in inst) {
		const s = (inst as { SetSlot: { vreg: unknown; slot: { base: number; offset: number } } }).SetSlot;
		return `set [${fmtPreg(s.slot.base)}+${s.slot.offset}] <- ${v(s.vreg)}`;
	}
	if ('ClearSlot' in inst) {
		const s = (inst as { ClearSlot: { vreg: unknown; slot: { base: number; offset: number } } }).ClearSlot;
		return `clear [${fmtPreg(s.slot.base)}+${s.slot.offset}] ${v(s.vreg)}`;
	}
	if ('Clobber' in inst) {
		return `clobber ${v((inst as { Clobber: { vreg: unknown } }).Clobber.vreg)}`;
	}
	if ('Resolve' in inst) {
		return `resolve ${v((inst as { Resolve: { vreg: unknown } }).Resolve.vreg)}`;
	}
	return JSON.stringify(inst);
}

export function fmtIrInst(inst: unknown, refs: VRegRefView[]): string {
	const v = (x: unknown) => fmtVreg(x, refs);
	if (inst === 'Return') return 'ret';
	if (typeof inst !== 'object' || inst === null) return String(inst);
	if ('Alu' in inst) {
		const a = (inst as { Alu: { op: unknown; dst: unknown; lhs: unknown; rhs: unknown } }).Alu;
		return `${v(a.dst)} = ${fmtAluOp(a.op)} ${v(a.lhs)}, ${v(a.rhs)}`;
	}
	if ('Call' in inst) {
		const c = (inst as { Call: { func_idx: { User: number } } }).Call;
		return `call fn${c.func_idx.User}`;
	}
	if ('Branch' in inst) {
		return `br ${fmtBlockId((inst as { Branch: { target: unknown } }).Branch.target)}`;
	}
	if ('BrIf' in inst) {
		const b = (inst as { BrIf: { cond: unknown; block_if: unknown; block_else: unknown } }).BrIf;
		return `br_if ${v(b.cond)} then ${fmtBlockId(b.block_if)} else ${fmtBlockId(b.block_else)}`;
	}
	if ('Skipped' in inst) {
		return `~${fmtIrInst((inst as { Skipped: unknown }).Skipped, refs)}`;
	}
	if ('Load' in inst) {
		const l = (inst as { Load: { dst: number; base: number; offset: number } }).Load;
		return `${fmtPreg(l.dst)} = load [${fmtPreg(l.base)}+${l.offset}]`;
	}
	if ('Store' in inst) {
		const s = (inst as { Store: { src: number; base: number; offset: number } }).Store;
		return `store [${fmtPreg(s.base)}+${s.offset}], ${fmtPreg(s.src)}`;
	}
	if ('Move' in inst) {
		const m = (inst as { Move: { dst: number; src: number } }).Move;
		return `${fmtPreg(m.dst)} = mov ${fmtPreg(m.src)}`;
	}
	return JSON.stringify(inst);
}

// ---- Snapshot converters ----

function convertRegionSnapshot(regions: { label: string; slots: unknown[] }[], refs: VRegRefView[]): RegionSnapshotView[] {
	return regions.map(r => ({
		label: r.label,
		slots: r.slots.map(s => fmtVreg(s, refs)),
	}));
}

function convertRegAllocState(state: {
	bindings: (unknown | null)[];
	entries: (null | { loc: unknown; slots: { slot: { base: number; offset: number }; dirty: boolean }[] })[];
}): RegAllocSnapshotView {
	const bindings = state.bindings.map((vreg, i) => ({
		preg: fmtPreg(i),
		vreg: vreg !== null ? fmtVregRaw(vreg) : null,
	}));

	const vreg_locs: VRegLocView[] = [];
	for (let i = 0; i < state.def_entries.length; i++) {
		const entry = state.def_entries[i];
		if (!entry) continue;
		const loc = entry.loc;
		const vreg = `v${i}`;
		if (loc === 'Pending') {
			vreg_locs.push({ vreg, loc: 'pending' });
		} else if (loc === 'Mem') {
			vreg_locs.push({ vreg, loc: 'mem' });
		} else if (typeof loc === 'object' && loc !== null && 'Const' in loc) {
			vreg_locs.push({ vreg, loc: 'const' });
		} else if (typeof loc === 'object' && loc !== null && 'Reg' in loc) {
			vreg_locs.push({
				vreg,
				loc: 'reg',
				preg: fmtPreg((loc as { Reg: number }).Reg),
				dirty: entry.slots.some(s => s.dirty),
			});
		}
	}

	return { bindings, vreg_locs };
}

// ---- Pre-scan: extract vreg_refs per function ----

function parseVRegRefs(raw: unknown[]): VRegRefView[] {
	return (raw as { id: unknown; width: string; source: unknown }[]).map(r => {
		const src = r.source;
		let source: VRegRefSourceView;
		if (typeof src === 'object' && src !== null) {
			if ('Direct' in src) {
				source = { kind: 'direct', target: fmtVregRaw((src as { Direct: unknown }).Direct) };
			} else if ('Phi' in src) {
				const entries = (src as { Phi: [unknown, unknown][] }).Phi;
				source = {
					kind: 'phi',
					sources: entries.map(([block, vreg]) => ({
						block: fmtBlockId(block),
						vreg: fmtVregRaw(vreg),
					})),
				};
			} else {
				source = { kind: 'direct', target: '?' };
			}
		} else {
			source = { kind: 'direct', target: '?' };
		}
		return {
			id: fmtVregRaw(r.id),
			width: fmtWidth(r.width),
			source,
		};
	});
}

// ---- Main transform ----

// eslint-disable-next-line @typescript-eslint/no-explicit-any
export function transformTrace(raw: any[]): FunctionView[] {
	const functions: FunctionView[] = [];
	let currentFunc: FunctionView | null = null;
	let currentBlock: BlockView | null = null;
	let currentGroup: GroupView | null = null;

	// Pre-pass 1: collect vreg_refs per function index so they're
	// available before any block/inst events are processed.
	const refsByFuncIndex = new Map<number, VRegRefView[]>();
	let funcIndex = -1;
	for (const e of raw) {
		if (e.type === 'function_start') funcIndex = e.index;
		if (e.type === 'build_end' && e.vreg_refs) {
			refsByFuncIndex.set(funcIndex, parseVRegRefs(e.vreg_refs));
		}
	}

	// Pre-pass 2: collect regalloc snapshots, ASM, and converge ops, keyed by ir_index/parent
	const regAllocByIrIndex = new Map<number, RegAllocSnapshotView>();
	const asmByParent = new Map<number, AsmView[]>();
	const convergeByParent = new Map<number, { phi: string; src: string }[]>();
	let lastIrIndex = -1;

	for (const e of raw) {
		if (e.type === 'lower_inst') {
			lastIrIndex = e.ir_index;
		} else if (e.type === 'regalloc_state') {
			regAllocByIrIndex.set(lastIrIndex, convertRegAllocState(e.state));
		} else if (e.type === 'asm' && e.parent !== undefined) {
			const parent = e.parent as number;
			const list = asmByParent.get(parent) ?? [];
			list.push({ addr: e.addr, text: e.text, origin: e.origin ?? 'lower' });
			asmByParent.set(parent, list);
		} else if (e.type === 'converge' && e.parent !== undefined) {
			const parent = e.parent as number;
			const list = convergeByParent.get(parent) ?? [];
			list.push({ phi: e.phi, src: e.src });
			convergeByParent.set(parent, list);
		}
	}

	// Main pass: build structure from build-phase events.
	// refs is always available from pre-pass 1.
	let buildIrIndex = 0;
	let refs: VRegRefView[] = [];

	for (const e of raw) {
		if (e.phase !== 'build' && e.type !== 'build_end' && e.type !== 'function_start') continue;

		switch (e.type) {
			case 'function_start': {
				refs = refsByFuncIndex.get(e.index) ?? [];
				currentFunc = { index: e.index, vreg_defs: [], vreg_refs: refs, regions: [], blocks: [] };
				functions.push(currentFunc);
				currentBlock = null;
				currentGroup = null;
				buildIrIndex = 0;
				break;
			}
			case 'build_end': {
				if (!currentFunc) break;
				currentFunc.vreg_defs = e.vreg_defs.map((d: { id: unknown; width: string; target: number | null }) => ({
					id: fmtVregRaw(d.id),
					width: fmtWidth(d.width),
					target: d.target !== null ? fmtPreg(d.target) : null,
				}));
				currentFunc.regions = e.regions.map((r: { label: string; base: number; base_offset: number }) => ({
					label: r.label,
					base: fmtPreg(r.base),
					base_offset: r.base_offset,
				}));
				break;
			}
			case 'block_start': {
				if (!currentFunc) break;
				currentBlock = { id: e.block, groups: [], successors: [] };
				currentFunc.blocks.push(currentBlock);
				currentGroup = null;
				break;
			}
			case 'wasm_op':
			case 'group': {
				if (!currentBlock) break;
				currentGroup = { pc: e.pc ?? null, label: e.label ?? '', ops: [] };
				currentBlock.groups.push(currentGroup);
				break;
			}
			case 'reg': {
				if (!currentGroup && currentBlock) {
					currentGroup = { pc: null, label: '', ops: [] };
					currentBlock.groups.push(currentGroup);
				}
				if (!currentGroup) { buildIrIndex++; break; }
				const irIdx = buildIrIndex++;
				currentGroup.ops.push({
					seq: e.seq,
					kind: 'reg',
					inst: e.inst,
					text: fmtRegInst(e.inst, refs),
					asm: asmByParent.get(irIdx) ?? [],
					region_snapshot: e.regions ? convertRegionSnapshot(e.regions, refs) : null,
					regalloc_snapshot: regAllocByIrIndex.get(irIdx) ?? null,
				});
				break;
			}
			case 'ir': {
				if (!currentGroup && currentBlock) {
					currentGroup = { pc: null, label: '', ops: [] };
					currentBlock.groups.push(currentGroup);
				}
				if (!currentGroup) { buildIrIndex++; break; }
				const irIdx = buildIrIndex++;
				const allAsm = asmByParent.get(irIdx) ?? [];
				const converges = convergeByParent.get(irIdx) ?? [];

				// Split asm: first N entries are convergence materializations,
				// rest belong to the actual instruction (e.g. branch).
				const convergeAsm = allAsm.slice(0, converges.length);
				const instrAsm = allAsm.slice(converges.length);

				for (let i = 0; i < converges.length; i++) {
					currentGroup.ops.push({
						seq: e.seq,
						kind: 'ir',
						inst: null,
						text: `materialize ${converges[i].src} \u2192 ${converges[i].phi}`,
						asm: convergeAsm[i] ? [convergeAsm[i]] : [],
						region_snapshot: null,
						regalloc_snapshot: null,
					});
				}

				currentGroup.ops.push({
					seq: e.seq,
					kind: 'ir',
					inst: e.inst,
					text: fmtIrInst(e.inst, refs),
					asm: instrAsm,
					region_snapshot: null,
					regalloc_snapshot: regAllocByIrIndex.get(irIdx) ?? null,
				});

				// Extract successors from branch instructions
				if (currentBlock && typeof e.inst === 'object' && e.inst !== null) {
					const addSucc = (b: unknown) => {
						const s = fmtBlockId(b);
						if (!currentBlock!.successors.includes(s)) currentBlock!.successors.push(s);
					};
					if ('Branch' in e.inst) addSucc(e.inst.Branch.target);
					if ('BrIf' in e.inst) {
						addSucc(e.inst.BrIf.block_if);
						addSucc(e.inst.BrIf.block_else);
					}
				}
				break;
			}
		}
	}

	return functions;
}

// ---- Text renderer (LLM-friendly) ----

export function renderText(functions: FunctionView[]): string {
	const lines: string[] = [];
	const w = (s: string) => lines.push(s);

	for (const func of functions) {
		const refs = func.vreg_refs;
		const nOps = func.blocks.reduce((n, b) => n + b.groups.reduce((m, g) => m + g.ops.length, 0), 0);
		const nAsm = func.blocks.reduce((n, b) => n + b.groups.reduce((m, g) => m + g.ops.reduce((o, op) => o + op.asm.length, 0), 0), 0);
		w(`=== func ${func.index} — ${func.vreg_defs.length} vregs, ${refs.length} refs, ${func.blocks.length} blocks, ${nAsm} asm ===`);
		w('');

		const defStrs = func.vreg_defs.map(d => {
			let s = `${d.id}:${d.width}`;
			if (d.target) s += `→${d.target}`;
			return s;
		});
		w(`vregs: ${defStrs.join(' ')}`);

		if (refs.length > 0) {
			const refStrs = refs.map(r => {
				if (r.source.kind === 'direct') return `${r.id}→${r.source.target}`;
				const srcs = r.source.sources.map(s => `${s.block}:${s.vreg}`).join(',');
				return `${r.id}→\u03C6(${srcs})`;
			});
			w(`refs: ${refStrs.join(' ')}`);
		}

		w(`regions: ${func.regions.map(r => `${r.label}(${r.base}+${r.base_offset})`).join(' ')}`);
		w('');

		for (const block of func.blocks) {
			const succ = block.successors.length > 0 ? ` → ${block.successors.join(',')}` : '';
			w(`--- ${block.id}${succ} ---`);

			for (const group of block.groups) {
				const pcStr = group.pc !== null ? `[${group.pc}]` : ' --';
				w(`  ${pcStr} ${group.label}`);

				for (const op of group.ops) {
					const parts: string[] = [`    ${op.text}`];
					if (op.asm.length > 0) {
						const asmStr = op.asm.map(a => `${a.addr.toString(16).padStart(4, '0')} ${a.text}`).join(' | ');
						parts.push(`  → ${asmStr}`);
					}
					w(parts.join(''));

					if (op.region_snapshot) {
						const rgn = op.region_snapshot
							.filter(r => r.slots.length > 0)
							.map(r => `${r.label}:[${r.slots.join(',')}]`)
							.join(' ');
						if (rgn) w(`      ${rgn}`);
					}
				}
			}

			const lastSnap = findLastSnapshot(block);
			if (lastSnap) {
				const bound = lastSnap.bindings
					.filter(b => b.vreg !== null)
					.map(b => `${b.preg}→${b.vreg}`)
					.join(' ');
				const locs = lastSnap.vreg_locs
					.map(v => {
						if (v.loc === 'reg') return `${v.vreg}:${v.preg}${v.dirty ? '!' : ''}`;
						return `${v.vreg}:${v.loc}`;
					})
					.join(' ');
				if (bound) w(`  bindings: ${bound}`);
				if (locs) w(`  locs: ${locs}`);
			}
			w('');
		}
	}

	return lines.join('\n');
}

function findLastSnapshot(block: BlockView): RegAllocSnapshotView | null {
	for (const group of [...block.groups].reverse()) {
		for (const op of [...group.ops].reverse()) {
			if (op.regalloc_snapshot) return op.regalloc_snapshot;
		}
	}
	return null;
}
