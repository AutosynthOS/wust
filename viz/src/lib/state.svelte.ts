import type { WasmSourceLine } from './types';

class AppState {
	highlightedVreg: string | null = $state(null);
	hoveredOp: number | null = $state(null);
	selectedOp: number | null = $state(null);
	/** Selected seq numbers (multiple when a group/label is clicked) */
	selectedOps: Set<number> = $state(new Set());
	highlightedWasmPcs: Set<number> = $state(new Set());
	selectedWasmPc: number | null = $state(null);
}

export const app = new AppState();

export function toggleVreg(v: string) {
	app.highlightedVreg = app.highlightedVreg === v ? null : v;
}

export function selectOp(seq: number) {
	if (app.selectedOp === seq) {
		app.selectedOp = null;
		app.selectedOps = new Set();
	} else {
		app.selectedOp = seq;
		app.selectedOps = new Set([seq]);
	}
}

export function selectGroup(seqs: number[]) {
	const first = seqs[0];
	if (app.selectedOp === first) {
		app.selectedOp = null;
		app.selectedOps = new Set();
	} else {
		app.selectedOp = first;
		app.selectedOps = new Set(seqs);
	}
}

export function toggleSourceLine(line: WasmSourceLine) {
	if (app.selectedWasmPc === line.pc) {
		app.selectedWasmPc = null;
		app.highlightedWasmPcs = new Set();
	} else {
		app.selectedWasmPc = line.pc;
		app.highlightedWasmPcs = new Set([line.pc]);
	}
}
