// ---- Raw compiler output ----

/** Top-level: one module compilation produces this. */
export interface ModuleTrace {
	functions: FunctionTrace[];
	source: WasmSourceLine[];
}

/** Linear wasm instruction in the source view. */
export interface WasmSourceLine {
	pc: number;
	text: string;
	indent: number;
	func_index: number;
}

/** One function's compilation trace. */
export interface FunctionTrace {
	index: number;
	name: string | null;
	params: ParamDef[];
	results: ResultDef[];
	vregs: VRegDef[];
	regions: RegionDef[];
	events: TraceEvent[];
}

export interface ParamDef {
	index: number;
	name: string | null;
	width: string;
	/** CC register, null if stack-passed (overflow). */
	preg: string | null;
}

export interface ResultDef {
	index: number;
	width: string;
	preg: string | null;
}

export interface VRegDef {
	id: string;
	width: string;
	target: string | null;
}

export interface RegionDef {
	id: string;
	label: string;
	base_preg: string;
	base_offset: number;
}

// ---- Event stream ----

/** Discriminated union of all compilation events. */
export type TraceEvent =
	| BlockStartEvent
	| WasmOpEvent
	| DefineEvent
	| SetSlotEvent
	| ClearSlotEvent
	| ClobberEvent
	| ResolveEvent
	| IrEvent
	| AsmEvent;

interface BaseEvent {
	seq: number;
	/** Regalloc state after this event (compiler-authoritative). */
	snapshot?: RegAllocSnapshot;
}

export interface BlockStartEvent extends BaseEvent {
	type: 'block_start';
	block: string;
	successors: string[];
}

export interface WasmOpEvent extends BaseEvent {
	type: 'wasm_op';
	pc: number | null;
	label: string;
}

export interface DefineEvent extends BaseEvent {
	type: 'define';
	vreg: string;
	value: VInit;
}

export interface SetSlotEvent extends BaseEvent {
	type: 'setslot';
	vreg: string;
	region: string;
	index: number;
}

export interface ClearSlotEvent extends BaseEvent {
	type: 'clearslot';
	vreg: string;
	region: string;
	index: number;
}

export interface ClobberEvent extends BaseEvent {
	type: 'clobber';
	vreg: string;
}

export interface ResolveEvent extends BaseEvent {
	type: 'resolve';
	vreg: string;
}

export interface IrEvent extends BaseEvent {
	type: 'ir';
	inst: IrInstData;
}

export interface AsmEvent extends BaseEvent {
	type: 'asm';
	addr: number;
	text: string;
	origin: 'lower' | 'regalloc' | 'fuse';
	/** Seq of the event that caused this emission. */
	parent: number;
}

export type VInit =
	| { const: number }
	| { preg: string }
	| 'pending';

export type IrInstData =
	| { alu: { op: string; dst: string; lhs: string; rhs: string } }
	| { call: { target: string } }
	| { branch: { target: string } }
	| { br_if: { cond: string; block_if: string; block_else: string } }
	| 'ret';

// ---- Frontend-assembled views (computed from events) ----

export interface BlockView {
	id: string;
	successors: string[];
	groups: WasmGroupView[];
	/** VRegs this block expects from predecessors */
	params: string[];
	/** VRegs this block produces for successors */
	results: string[];
}

export interface WasmGroupView {
	pc: number | null;
	label: string;
	/** Events between this wasm_op and the next (or block end). */
	ops: OpView[];
}

export interface OpView {
	seq: number;
	text: string;
	event: TraceEvent;
	asm: AsmEvent[];
}

export interface StackState {
	locals: string[];
	ops: string[];
	fibre: string[];
}

/** Authoritative regalloc state snapshot, emitted by the compiler. */
export interface RegAllocSnapshot {
	/** PReg → VReg bindings (null = free) */
	bindings: { preg: string; vreg: string | null }[];
	/** Per-vreg location + dirty state */
	vreg_locs: VRegLoc[];
}

export interface VRegLoc {
	vreg: string;
	loc: 'reg' | 'mem' | 'const' | 'pending';
	/** Which preg, if loc === 'reg' */
	preg?: string;
	/** Has value been stored to its canonical slot? */
	dirty?: boolean;
}
