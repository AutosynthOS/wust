<script lang="ts">
	import '$lib/theme.css';
	import { onMount } from 'svelte';
	import { transformTrace, type FunctionView, type BlockView, type OpView } from '$lib/transform';
	import { app } from '$lib/state.svelte';
	import BlockNode from '$lib/components/BlockNode.svelte';
	import VmState from '$lib/components/VmState.svelte';
	import VReg from '$lib/components/VReg.svelte';
	import PReg from '$lib/components/PReg.svelte';
	import rawTrace from '$lib/trace.json';

	const functions = transformTrace(rawTrace);
	const func = functions[0] ?? null;
	const blocks = func?.blocks ?? [];
	const allOps = blocks.flatMap(b => b.groups.flatMap(g => g.ops));
	const blockMap = new Map(blocks.map(b => [b.id, b]));

	// Vreg initial values from define events
	const vregInits = $derived.by(() => {
		const m = new Map<string, string>();
		if (!func) return m;
		for (const block of func.blocks) {
			for (const group of block.groups) {
				for (const op of group.ops) {
					if (op.kind !== 'reg' || typeof op.inst !== 'object' || op.inst === null) continue;
					if ('Define' in op.inst) {
						const d = (op.inst as { Define: { vreg: number; value: unknown } }).Define;
						const val = d.value;
						const id = `v${d.vreg}`;
						if (val === 'InstDst') m.set(id, 'dst');
						else if (typeof val === 'object' && val !== null) {
							if ('Const' in val) m.set(id, `#${(val as { Const: number }).Const}`);
							if ('PReg' in val) m.set(id, `x${(val as { PReg: number }).PReg}`);
						}
					}
				}
			}
		}
		return m;
	});

	// --- Graph layout: assign grid col/row per block ---
	const blockPos = new Map<string, { col: number; row: number }>();

	function layout() {
		const placed = new Set<string>();
		const colNext = new Map<number, number>();
		const nr = (c: number) => colNext.get(c) ?? 0;
		const adv = (c: number, r: number) => colNext.set(c, Math.max(nr(c), r));

		function place(id: string, col: number, row: number) {
			if (placed.has(id)) return;
			placed.add(id);
			const r = Math.max(row, nr(col));
			blockPos.set(id, { col, row: r });
			adv(col, r + 1);
			const block = blockMap.get(id)!;
			if (block.successors.length === 2) {
				if (!placed.has(block.successors[0])) place(block.successors[0], col + 1, r);
				if (!placed.has(block.successors[1])) place(block.successors[1], col, r + 1);
			} else if (block.successors.length === 1) {
				if (!placed.has(block.successors[0])) place(block.successors[0], col, r + 1);
			}
		}
		if (blocks.length > 0) place(blocks[0].id, 0, 0);
		for (const b of blocks) if (!placed.has(b.id)) place(b.id, 0, nr(0));
	}
	layout();

	const maxCol = Math.max(...[...blockPos.values()].map(p => p.col), 0);
	const maxRow = Math.max(...[...blockPos.values()].map(p => p.row), 0);

	// --- Pan/zoom ---
	let zoom = $state(0.85);
	let panX = $state(20);
	let panY = $state(20);
	let isPanning = $state(false);
	let psx = 0; let psy = 0; let ppx = 0; let ppy = 0;

	function onWheel(e: WheelEvent) {
		e.preventDefault();
		const d = e.deltaY > 0 ? 0.92 : 1.08;
		const nz = Math.max(0.15, Math.min(3, zoom * d));
		const r = (e.currentTarget as HTMLElement).getBoundingClientRect();
		const cx = e.clientX - r.left, cy = e.clientY - r.top;
		panX = cx - (cx - panX) * (nz / zoom);
		panY = cy - (cy - panY) * (nz / zoom);
		zoom = nz;
	}

	function onPtrDown(e: PointerEvent) {
		if (e.button === 1 || (e.button === 0 && e.altKey)) {
			isPanning = true;
			psx = e.clientX; psy = e.clientY;
			ppx = panX; ppy = panY;
			(e.currentTarget as HTMLElement).setPointerCapture(e.pointerId);
			e.preventDefault();
		}
	}

	function onPtrMove(e: PointerEvent) {
		if (isPanning) {
			panX = ppx + (e.clientX - psx);
			panY = ppy + (e.clientY - psy);
		}
	}

	function onPtrUp() { isPanning = false; }

	// --- SVG arrows from DOM bounding boxes ---
	let graphEl: HTMLDivElement;
	const blockEls = new Map<string, HTMLDivElement>();
	let arrowPaths: { fall: boolean; path: string }[] = $state([]);

	function registerBlock(node: HTMLDivElement, id: string) {
		blockEls.set(id, node);
		requestAnimationFrame(recomputeArrows);
		return {
			destroy() { blockEls.delete(id); }
		};
	}

	function getBlockRect(el: HTMLElement) {
		// Use offsetLeft/offsetTop which are relative to offsetParent (the grid),
		// not affected by CSS transforms
		return {
			left: el.offsetLeft,
			top: el.offsetTop,
			width: el.offsetWidth,
			height: el.offsetHeight,
			right: el.offsetLeft + el.offsetWidth,
			bottom: el.offsetTop + el.offsetHeight,
		};
	}

	function recomputeArrows() {
		if (!graphEl) return;
		const res: typeof arrowPaths = [];

		for (const block of blocks) {
			const fromEl = blockEls.get(block.id);
			if (!fromEl) continue;
			const fr = getBlockRect(fromEl);
			const is2 = block.successors.length === 2;

			for (let i = 0; i < block.successors.length; i++) {
				const s = block.successors[i];
				const toEl = blockEls.get(s);
				if (!toEl) continue;
				const tr = getBlockRect(toEl);
				const fall = !is2 || i === 1;

				if (fall) {
					const fx = fr.left + fr.width * 0.4;
					const tx = tr.left + tr.width * 0.4;
					res.push({ fall: true, path: `M${fx},${fr.bottom} L${tx},${tr.top}` });
				} else {
					const fy = fr.top + fr.height * 0.7;
					const cpx = (fr.right + tr.left) / 2;
					const ty = tr.top + 12;
					res.push({ fall: false, path: `M${fr.right},${fy} C${cpx},${fy} ${cpx},${ty} ${tr.left},${ty}` });
				}
			}
		}
		arrowPaths = res;
	}

	onMount(() => {
		recomputeArrows();
	});

	// Recompute arrows whenever blocks might resize
	$effect(() => {
		// Touch reactive deps that might cause layout changes
		app.selectedOp;
		app.highlightedVreg;
		// Tick then measure
		requestAnimationFrame(recomputeArrows);
	});
</script>

{#if !func}
	<div class="loading">no functions in trace</div>
{:else}
<div class="layout">
	<aside class="panel left">
		<VmState {func} {allOps} />
	</aside>

	<main
		class="graph"
		onwheel={onWheel}
		onpointerdown={onPtrDown}
		onpointermove={onPtrMove}
		onpointerup={onPtrUp}
	>
		<div class="toolbar">
			<span class="zoom">{Math.round(zoom * 100)}%</span>
			{#if app.highlightedVreg}
				<button class="btn" onclick={() => app.highlightedVreg = null}>
					✕ {app.highlightedVreg}
				</button>
			{/if}
			<span class="hint">alt+drag pan · scroll zoom</span>
		</div>

		<div class="viewport">
			<div class="canvas" style="transform: translate({panX}px, {panY}px) scale({zoom});">
				<div class="func-container">
					<!-- Source sidebar -->
					<div class="func-sidebar">
						<div class="func-header">
							<span class="func-name">func[{func.index}]</span>
						</div>

						<div class="func-defs">
							<h3>vreg definitions</h3>
							{#each func.vreg_defs as def}
								{@const init = vregInits.get(def.id)}
								<div class="def-row" class:def-active={app.highlightedVreg === def.id}>
									<VReg id={def.id} /><span class="def-sep">:</span><span class="def-w">{def.width}</span>
									{#if init}
										<span class="def-eq">=</span>
										{#if def.target}
											<PReg id={def.target} />
										{:else}
											<span class="def-init">{init}</span>
										{/if}
									{/if}
								</div>
							{/each}
						</div>
					</div>

					<!-- Graph grid + SVG arrows -->
					<div class="func-graph">
						<!-- Blocks in CSS grid -->
						<div class="block-grid" bind:this={graphEl} style="grid-template-columns: repeat({maxCol + 1}, auto); grid-template-rows: repeat({maxRow + 1}, auto);">
							<!-- SVG arrow overlay -->
							<svg class="arrows">
								<defs>
									<marker id="af" viewBox="0 0 10 10" refX="10" refY="5"
										markerWidth="7" markerHeight="7" orient="auto-start-reverse">
										<path d="M0 0L10 5L0 10z" fill="var(--text-dim)" />
									</marker>
									<marker id="ab" viewBox="0 0 10 10" refX="10" refY="5"
										markerWidth="7" markerHeight="7" orient="auto-start-reverse">
										<path d="M0 0L10 5L0 10z" fill="var(--accent-red)" />
									</marker>
								</defs>
								{#each arrowPaths as a}
									<path
										d={a.path}
										fill="none"
										stroke={a.fall ? 'var(--text-dim)' : 'var(--accent-red)'}
										stroke-width={a.fall ? 1.5 : 2}
										stroke-dasharray={a.fall ? '' : '6,3'}
										marker-end="url(#{a.fall ? 'af' : 'ab'})"
									/>
								{/each}
							</svg>

							{#each blocks as block}
								{@const pos = blockPos.get(block.id)!}
								<div
									class="block"
									style="grid-column: {pos.col + 1}; grid-row: {pos.row + 1};"
									use:registerBlock={block.id}
								>
									<BlockNode {block} {func} />
								</div>
							{/each}
						</div>
					</div>
				</div>
			</div>
		</div>
	</main>
</div>
{/if}

<style>
	.loading {
		color: var(--text-dim);
		padding: 40px;
		text-align: center;
	}
	:global(*, *::before, *::after) {
		box-sizing: border-box;
	}

	:global(body) {
		margin: 0;
		background: var(--bg-base);
		color: var(--text);
		font-family: var(--font-mono);
		font-size: 13px;
		overflow: hidden;
	}

	.layout {
		display: flex;
		height: 100vh;
	}

	.panel {
		background: var(--bg-panel);
		padding: 12px;
		overflow-y: auto;
		display: flex;
		flex-direction: column;
		gap: 14px;
		flex-shrink: 0;
		user-select: none;
		-webkit-user-select: none;

		&.left {
			width: 240px;
			border-right: 1px solid var(--border);
		}
	}


	.graph {
		flex: 1;
		display: flex;
		flex-direction: column;
		overflow: hidden;
	}

	.toolbar {
		display: flex;
		align-items: center;
		gap: 8px;
		padding: 6px 14px;
		min-height: 34px;
		border-bottom: 1px solid var(--border);
		background: var(--bg-panel);
		flex-shrink: 0;
		user-select: none;
		-webkit-user-select: none;
	}

	.zoom { color: var(--text-dim); font-size: var(--font-size-sm); }
	.btn {
		background: var(--bg-elevated);
		border: 1px solid var(--text-faint);
		color: var(--text);
		padding: 1px 6px;
		border-radius: 3px;
		cursor: pointer;
		font-family: inherit;
		font-size: var(--font-size-sm);
		&:hover { background: var(--text-faint); }
	}
	.hint { margin-left: auto; color: var(--text-faint); font-size: var(--font-size-xs); }

	.viewport {
		flex: 1;
		overflow: hidden;
		position: relative;
	}

	.canvas {
		transform-origin: 0 0;
		padding: 20px;
		width: max-content;
	}

	/* Function container */
	.func-container {
		display: flex;
		background: rgba(24, 24, 37, 0.3);
		border: 1px solid rgba(49, 50, 68, 0.4);
		border-radius: 10px;
		overflow: visible;
		width: max-content;
	}

	.func-sidebar {
		min-width: 200px;
		border-right: 1px solid var(--border-subtle);
		display: flex;
		flex-direction: column;
	}

	.func-header {
		padding: 6px 10px;
		display: flex;
		flex-direction: column;
		gap: 2px;
		border-bottom: 1px solid var(--border-subtle);
	}

	.func-name {
		color: var(--text);
		font-weight: bold;
		font-size: var(--font-size-base);
	}

	.func-params {
		display: flex;
		gap: 4px;
		align-items: center;
		flex-wrap: wrap;
	}

	.func-param { font-size: var(--font-size-base); }
	.fp-colon { color: var(--text-faint); }
	.fp-type { color: var(--text-muted); }
	.fp-sep { color: var(--text-faint); margin-right: 2px; }
	.fp-arrow { color: var(--text-faint); margin: 0 2px; }

	.func-source {
		display: flex;
		flex-direction: column;
		padding: 4px 0;
	}

	.src-line {
		display: flex;
		gap: 4px;
		padding: 0 6px;
		background: none;
		border: none;
		border-left: 2px solid transparent;
		color: var(--text);
		cursor: pointer;
		font-family: inherit;
		font-size: var(--font-size-sm);
		text-align: left;
		line-height: 18px;
		&:hover { background: var(--hover-bg); }
		&.src-active { background: rgba(137, 180, 250, 0.1); border-left-color: var(--accent-blue); }
		&.src-match { background: rgba(137, 180, 250, 0.06); }
	}

	.src-pc {
		color: var(--text-dim);
		min-width: 16px;
		text-align: right;
		font-size: var(--font-size-sm);
	}

	.src-text { color: var(--text-secondary); white-space: pre; }
	.src-active .src-text { color: var(--text); }

	.func-defs {
		padding: 4px 6px;
		border-top: 1px solid var(--border-subtle);

		h3 {
			font-size: var(--font-size-xs);
			color: var(--text-dim);
			margin: 0 0 4px 0;
			text-transform: uppercase;
			letter-spacing: 0.5px;
		}
	}

	.def-row {
		display: flex;
		align-items: center;
		gap: 2px;
		padding: 1px 4px;
		border-radius: 3px;
		font-size: var(--font-size-sm);
		&.def-active { background: var(--highlight-bg); }
	}

	.def-sep { color: var(--text-faint); }
	.def-w { color: var(--text-muted); }
	.def-eq { color: var(--text-faint); margin: 0 2px; }
	.def-init { color: var(--accent-teal); }

	/* Graph area */
	.func-graph {
		position: relative;
		background: rgba(0, 0, 0, 0.25);
		padding: 48px;
	}

	.block-grid {
		display: grid;
		gap: 40px 80px;
		position: relative;
		width: max-content;
		align-items: start;
	}

	.arrows {
		position: absolute;
		top: 0;
		left: 0;
		width: 100%;
		height: 100%;
		pointer-events: none;
		z-index: 2;
		overflow: visible;
	}

	.block {
		border-radius: 6px;
		background: rgba(22, 22, 32, 0.7);
		overflow: hidden;
		user-select: none;
		-webkit-user-select: none;
	}
</style>
