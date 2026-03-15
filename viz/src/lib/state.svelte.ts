import type { FunctionData, Op, WatLine, WasmGroup } from './types';

// Svelte 5: reactive state must be in a class to be exported
class AppState {
	highlightedVreg: string | null = $state(null);
	hoveredOp: string | null = $state(null);
	selectedOp: { blockId: string; opId: string } | null = $state(null);
	highlightedWasmPcs: Set<number> = $state(new Set());
	hoveredWatLine: number | null = $state(null);
}

export const app = new AppState();

// --- Actions ---
export function toggleVreg(v: string) {
	app.highlightedVreg = app.highlightedVreg === v ? null : v;
}

export function selectOpAction(blockId: string, opId: string) {
	if (app.selectedOp?.blockId === blockId && app.selectedOp?.opId === opId) app.selectedOp = null;
	else app.selectedOp = { blockId, opId };
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

// --- Queries ---
export function opTouchesVreg(op: Op, v: string): boolean {
	return op.vregsRead.includes(v) || op.vregsDefined.includes(v);
}

export function groupHasWasmPc(g: WasmGroup, pcs: Set<number>): boolean {
	return g.wasmPc !== null && pcs.has(g.wasmPc);
}

export function vregWidth(data: FunctionData, v: string): string {
	return data.vregDefs.find(d => d.vreg === v)?.width ?? '?';
}

export function pregColor(data: FunctionData, p: string): string {
	return data.pregColors[p] ?? '#abb2bf';
}

export function kindColor(kind: string): string {
	switch (kind) {
		case 'define': return '#a6e3a1';
		case 'setslot': return '#89b4fa';
		case 'clearslot': return '#f38ba8';
		case 'clobber': return '#fab387';
		case 'resolve': return '#cba6f7';
		case 'ir': return '#cdd6f4';
		case 'branch': return '#f38ba8';
		case 'call': return '#f9e2af';
		case 'ret': return '#a6adc8';
		default: return '#6c7086';
	}
}

export function blockColor(id: string): string {
	return id.startsWith('G') ? '#f38ba8' : id === 'Ep' ? '#a6e3a1' : '#89b4fa';
}

export function originBadge(o: string): string {
	return o === 'lower' ? 'lo' : o === 'regalloc' ? 'ra' : 'fu';
}

export function formatAddr(a: number): string {
	return a.toString(16).padStart(4, '0');
}
