<script lang="ts">
	import '$lib/theme.css';
	import { mockTrace } from '$lib/mock';
	import type { BlockView, OpView } from '$lib/types';
	import { assembleBlocks } from '$lib/assemble';
	import { app } from '$lib/state.svelte';
	import WatPanel from '$lib/components/WatPanel.svelte';
	import BlockNode from '$lib/components/BlockNode.svelte';
	import VmState from '$lib/components/VmState.svelte';

	const trace = mockTrace;
	const func = trace.functions[0];
	const blocks = assembleBlocks(func);
	const allOps = blocks.flatMap(b => b.groups.flatMap(g => g.ops));

	// --- Pan/zoom ---
	let zoom = $state(0.85);
	let panX = $state(20);
	let panY = $state(20);
	let isPanning = $state(false);
	let psx = 0; let psy = 0; let ppx = 0; let ppy = 0;

	// --- Graph layout ---
	const blockMap = new Map(blocks.map(b => [b.id, b]));
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

	const ROW_H = 20;
	const BLOCK_W = 560;
	const GAP_X = 80;
	const GAP_Y = 36;

	function blockHeight(block: BlockView): number {
		let rows = 0;
		for (const g of block.groups) {
			for (const op of g.ops) {
				rows += Math.max(1, op.asm.length);
			}
		}
		return 24 + Math.max(rows, 1) * ROW_H + 4;
	}

	const maxRow = Math.max(...[...blockPos.values()].map(p => p.row), 0);
	const rowY = new Map<number, number>();
	let yAcc = 0;
	for (let r = 0; r <= maxRow; r++) {
		rowY.set(r, yAcc);
		let mh = 50;
		for (const [id, pos] of blockPos)
			if (pos.row === r) mh = Math.max(mh, blockHeight(blockMap.get(id)!));
		yAcc += mh + GAP_Y;
	}
	const maxCol = Math.max(...[...blockPos.values()].map(p => p.col), 0);
	const canvasW = (maxCol + 1) * (BLOCK_W + GAP_X) + 80;
	const canvasH = yAcc + 40;

	function getRect(id: string) {
		const pos = blockPos.get(id)!;
		return {
			x: 20 + pos.col * (BLOCK_W + GAP_X),
			y: rowY.get(pos.row)!,
			w: BLOCK_W,
			h: blockHeight(blockMap.get(id)!),
		};
	}

	function computeArrows() {
		const res: { fall: boolean; path: string }[] = [];
		for (const block of blocks) {
			const fr = getRect(block.id);
			const is2 = block.successors.length === 2;
			for (let i = 0; i < block.successors.length; i++) {
				const s = block.successors[i];
				if (!blockPos.has(s)) continue;
				const tr = getRect(s);
				const fall = !is2 || i === 1;
				if (fall) {
					const x = fr.x + fr.w * 0.4;
					res.push({ fall: true, path: `M${x},${fr.y + fr.h} L${x},${tr.y}` });
				} else {
					const fx = fr.x + fr.w;
					const fy = fr.y + fr.h * 0.45;
					const tx = tr.x;
					const ty = tr.y + 12;
					res.push({ fall: false, path: `M${fx},${fy} C${(fx + tx) / 2},${fy} ${(fx + tx) / 2},${ty} ${tx},${ty}` });
				}
			}
		}
		return res;
	}
	const arrows = computeArrows();

	// --- Handlers ---
	function onWheel(e: WheelEvent) {
		e.preventDefault();
		const d = e.deltaY > 0 ? 0.92 : 1.08;
		const nz = Math.max(0.15, Math.min(3, zoom * d));
		const r = (e.currentTarget as HTMLElement).getBoundingClientRect();
		const cx = e.clientX - r.left;
		const cy = e.clientY - r.top;
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

	function onPtrUp() {
		isPanning = false;
	}
</script>

<div class="layout">
	<aside class="panel left">
		<WatPanel {trace} {func} />
	</aside>

	<main
		class="graph"
		onwheel={onWheel}
		onpointerdown={onPtrDown}
		onpointermove={onPtrMove}
		onpointerup={onPtrUp}
	>
		<div class="toolbar">
			<h1>{func.name ?? `func[${func.index}]`}</h1>
			<span class="zoom">{Math.round(zoom * 100)}%</span>
			<button class="btn" onclick={() => { zoom = 0.85; panX = 20; panY = 20; }}>reset</button>
			{#if app.highlightedVreg}
				<button class="btn" onclick={() => app.highlightedVreg = null}>
					✕ {app.highlightedVreg}
				</button>
			{/if}
			<span class="hint">alt+drag pan · scroll zoom</span>
		</div>

		<div class="viewport">
			<div
				class="canvas"
				style="
					transform: translate({panX}px, {panY}px) scale({zoom});
					width: {canvasW}px;
					height: {canvasH}px;
				"
			>
				<!-- Function container -->
				<div class="func-container" style="width: {canvasW - 10}px; height: {canvasH - 10}px;">
					<div class="func-header">
						{func.name ?? `func[${func.index}]`}({func.params.map(p => `${p.name ?? `$${p.index}`}: ${p.width}`).join(', ')}) → {func.results.map(r => r.width).join(', ')}
					</div>
				</div>

				<!-- SVG arrows -->
				<svg class="arrows" width={canvasW} height={canvasH}>
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
					{#each arrows as a}
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

				<!-- Blocks -->
				{#each blocks as block}
					{@const rect = getRect(block.id)}
					<div
						class="block"
						style="
							left: {rect.x}px;
							top: {rect.y}px;
							width: {rect.w}px;
						"
					>
						<BlockNode {block} {func} />
					</div>
				{/each}
			</div>
		</div>
	</main>

	<aside class="panel right">
		<VmState {func} {allOps} />
	</aside>
</div>

<style>
	:global(body) {
		margin: 0;
		background: var(--bg-base);
		color: var(--text);
		font-family: var(--font-mono);
		font-size: 12px;
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

		&.right {
			width: 200px;
			border-left: 1px solid var(--border);
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
		border-bottom: 1px solid var(--border);
		background: var(--bg-panel);
		flex-shrink: 0;
		user-select: none;
		-webkit-user-select: none;

		h1 {
			font-size: 15px;
			margin: 0;
			color: var(--accent-purple);
		}
	}

	.zoom {
		color: var(--text-dim);
		font-size: var(--font-size-sm);
	}

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

	.hint {
		margin-left: auto;
		color: var(--text-faint);
		font-size: var(--font-size-xs);
	}

	.viewport {
		flex: 1;
		overflow: hidden;
		position: relative;
	}

	.canvas {
		position: absolute;
		top: 0;
		left: 0;
		transform-origin: 0 0;
	}

	.func-container {
		position: absolute;
		top: 5px;
		left: 5px;
		border: 1px dashed var(--border);
		border-radius: 10px;
		pointer-events: none;
	}

	.func-header {
		position: absolute;
		top: -10px;
		left: 16px;
		background: var(--bg-base);
		padding: 0 8px;
		color: var(--text-muted);
		font-size: var(--font-size-xs);
	}

	.arrows {
		position: absolute;
		top: 0;
		left: 0;
		pointer-events: none;
		z-index: 0;
	}

	.block {
		position: absolute;
		border: 1px solid var(--border);
		border-radius: 6px;
		background: var(--bg-block);
		z-index: 1;
		overflow: hidden;
		box-shadow: 0 2px 12px rgba(0, 0, 0, 0.4);
		user-select: none;
		-webkit-user-select: none;
	}
</style>
