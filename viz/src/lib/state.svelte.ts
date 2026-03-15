import type { WasmSourceLine } from './types';

class AppState {
	highlightedVreg: string | null = $state(null);
	hoveredOp: number | null = $state(null);
	selectedOp: number | null = $state(null);
	highlightedWasmPcs: Set<number> = $state(new Set());
	selectedWasmPc: number | null = $state(null);
}

export const app = new AppState();

export function toggleVreg(v: string) {
	app.highlightedVreg = app.highlightedVreg === v ? null : v;
}

export function selectOp(seq: number) {
	app.selectedOp = app.selectedOp === seq ? null : seq;
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
