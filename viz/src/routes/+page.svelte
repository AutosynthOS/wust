<script lang="ts">
	import '$lib/theme.css';
	import { onMount } from 'svelte';
	import { mockTrace } from '$lib/mock';
	import type { BlockView, OpView } from '$lib/types';
	import { assembleBlocks } from '$lib/assemble';
	import { app, toggleSourceLine } from '$lib/state.svelte';
	import BlockNode from '$lib/components/BlockNode.svelte';
	import VmState from '$lib/components/VmState.svelte';
	import VReg from '$lib/components/VReg.svelte';
	import PReg from '$lib/components/PReg.svelte';

	const trace = mockTrace;
	const func = trace.functions[0];
	const blocks = assembleBlocks(func);
	const allOps = blocks.flatMap(b => b.groups.flatMap(g => g.ops));
	const blockMap = new Map(blocks.map(b => [b.id, b]));

	// Vreg initial values from define events
	const vregInits = new Map<string, string>();
	for (const e of func.events) {
		if (e.type === 'define') {
			const v = e.value;
			if (v === 'pending') vregInits.set(e.vreg, 'dst');
			else if ('preg' in v) vregInits.set(e.vreg, v.preg);
			else vregInits.set(e.vreg, `#${v.const}`);
		}
	}

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

	function recomputeArrows() {
		if (!graphEl) return;
		const graphRect = graphEl.getBoundingClientRect();
		const res: typeof arrowPaths = [];

		for (const block of blocks) {
			const fromEl = blockEls.get(block.id);
			if (!fromEl) continue;
			const fr = fromEl.getBoundingClientRect();
			const is2 = block.successors.length === 2;

			for (let i = 0; i < block.successors.length; i++) {
				const s = block.successors[i];
				const toEl = blockEls.get(s);
				if (!toEl) continue;
				const tr = toEl.getBoundingClientRect();
				const fall = !is2 || i === 1;

				// Coordinates relative to graphEl
				const fLeft = fr.left - graphRect.left;
				const fRight = fr.right - graphRect.left;
				const fTop = fr.top - graphRect.top;
				const fBottom = fr.bottom - graphRect.top;
				const fCx = fLeft + fr.width * 0.4;

				const tLeft = tr.left - graphRect.left;
				const tTop = tr.top - graphRect.top;
				const tCx = tLeft + tr.width * 0.4;

				if (fall) {
					res.push({ fall: true, path: `M${fCx},${fBottom} L${tCx},${tTop}` });
				} else {
					// Branch: from right edge at bottom area, curve to target top
					const fy = fTop + fr.height * 0.7;
					const tx = tLeft;
					const ty = tTop + 12;
					const cpx = (fRight + tx) / 2;
					res.push({ fall: false, path: `M${fRight},${fy} C${cpx},${fy} ${cpx},${ty} ${tx},${ty}` });
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
							<span class="func-name">{func.name ?? `func[${func.index}]`}</span>
							<div class="func-params">
								{#each func.params as p, i}
									<span class="func-param">
										{#if p.preg}<PReg id={p.preg} />{/if}<span class="fp-colon">:</span><span class="fp-type">{p.width}</span>{#if i < func.params.length - 1}<span class="fp-sep">,</span>{/if}
									</span>
								{/each}
								<span class="fp-arrow">→</span>
								{#each func.results as r, i}
									<span class="func-param">
										{#if r.preg}<PReg id={r.preg} />{/if}<span class="fp-colon">:</span><span class="fp-type">{r.width}</span>{#if i < func.results.length - 1}<span class="fp-sep">,</span>{/if}
									</span>
								{/each}
							</div>
						</div>
						<div class="func-source">
							{#each trace.source.filter(l => l.func_index === func.index) as line}
								<button
									class="src-line"
									class:src-active={app.selectedWasmPc === line.pc}
									class:src-match={app.highlightedWasmPcs.has(line.pc)}
									onclick={() => toggleSourceLine(line)}
								>
									<span class="src-pc">{line.pc >= 0 ? line.pc : ''}</span>
									<code class="src-text" style="padding-left: {line.indent * 10}px">{line.text}</code>
								</button>
							{/each}
						</div>

						<div class="func-defs">
							<h3>vreg definitions</h3>
							{#each func.vregs as def}
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
					<div class="func-graph" bind:this={graphEl}>
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

						<!-- Blocks in CSS grid -->
						<div class="block-grid" style="grid-template-columns: repeat({maxCol + 1}, auto); grid-template-rows: repeat({maxRow + 1}, auto);">
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

<style>
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
		min-height: 28px;
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
		background: rgba(0, 0, 0, 0.15);
		padding: 16px;
	}

	.arrows {
		position: absolute;
		top: 0;
		left: 0;
		width: 100%;
		height: 100%;
		pointer-events: none;
		z-index: 0;
		overflow: visible;
	}

	.block-grid {
		display: grid;
		gap: 24px 60px;
		position: relative;
		z-index: 1;
		width: max-content;
	}

	.block {
		border-radius: 6px;
		background: rgba(22, 22, 32, 0.7);
		overflow: hidden;
		user-select: none;
		-webkit-user-select: none;
	}
</style>
