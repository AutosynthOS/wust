import type { WatLine } from './types';

class AppState {
	highlightedVreg: string | null = $state(null);
	hoveredOp: number | null = $state(null);       // seq number
	selectedOp: number | null = $state(null);       // seq number
	highlightedWasmPcs: Set<number> = $state(new Set());
	hoveredWatLine: number | null = $state(null);
}

export const app = new AppState();

export function toggleVreg(v: string) {
	app.highlightedVreg = app.highlightedVreg === v ? null : v;
}

export function selectOp(seq: number) {
	app.selectedOp = app.selectedOp === seq ? null : seq;
}

export function toggleWatLine(wl: WatLine) {
	if (app.hoveredWatLine === wl.line) {
		app.hoveredWatLine = null;
		app.highlightedWasmPcs = new Set();
	} else {
		app.hoveredWatLine = wl.line;
		app.highlightedWasmPcs = new Set(wl.wasmPcs);
	}
}
