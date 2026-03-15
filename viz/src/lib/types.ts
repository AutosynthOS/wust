export type EventId = string;

export interface VRegBinding {
	vreg: string;
	preg: string | null;
	loc: 'reg' | 'mem' | 'const' | 'pending';
}

export interface StackChange {
	action: 'push' | 'pop' | 'set';
	vreg: string;
	index?: number;
}

export interface StackChanges {
	locals: StackChange[];
	ops: StackChange[];
	fibre: StackChange[];
}

/** A single operation in the pipeline — the granular unit. */
export interface Op {
	id: EventId;
	/** Compact display: e.g. "v7 = le_s v0, v6:#1" */
	text: string;
	kind: 'define' | 'setslot' | 'clearslot' | 'clobber' | 'resolve' | 'ir' | 'branch' | 'call' | 'ret';
	vregsRead: string[];
	vregsDefined: string[];
	stackChanges: StackChanges;
	bindings: VRegBinding[];
}

export interface AsmEvent {
	id: EventId;
	parentOp: EventId;
	addr: number;
	asm: string;
	origin: 'lower' | 'regalloc' | 'fuse';
}

/** A wasm instruction and all the ops + asm it produces. */
export interface WasmGroup {
	wasmPc: number | null;
	label: string;
	ops: Op[];
}

export interface Block {
	id: string;
	blockIdx: number;
	label: string;
	groups: WasmGroup[];
	asmEvents: AsmEvent[];
	successors: string[];
	predecessors: string[];
}

export interface WatLine {
	line: number;
	text: string;
	wasmPcs: number[];
	indent: number;
}

export interface FunctionData {
	name: string;
	signature: string;
	watSource: WatLine[];
	blocks: Block[];
	vregDefs: { vreg: string; width: string; target: string | null }[];
	pregColors: Record<string, string>;
}
