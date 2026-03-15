<script lang="ts">
	import { fibData } from '$lib/mock';
	import type { Block } from '$lib/types';
	import { app, blockColor } from '$lib/state.svelte';
	import WatPanel from '$lib/components/WatPanel.svelte';
	import BlockNode from '$lib/components/BlockNode.svelte';
	import VmState from '$lib/components/VmState.svelte';

	const data = fibData;
	const blockMap = new Map(data.blocks.map(b => [b.id, b]));

	// Pan/zoom
	let zoom = $state(0.85);
	let panX = $state(20);
	let panY = $state(20);
	let isPanning = $state(false);
	let psx = 0; let psy = 0; let ppx = 0; let ppy = 0;

	// --- Stack state computation ---
	interface StackState { locals: string[]; ops: string[]; fibre: string[]; }
	const blockOpStates = new Map<string, Map<string, StackState>>();

	for (const block of data.blocks) {
		let s: StackState = { locals: [], ops: [], fibre: [] };
		const pred = block.predecessors[0];
		if (pred) {
			const predStates = blockOpStates.get(pred);
			if (predStates) {
				const predBlock = blockMap.get(pred)!;
				const lastOp = predBlock.groups.at(-1)?.ops.at(-1);
				if (lastOp && predStates.has(lastOp.id)) {
					const ps = predStates.get(lastOp.id)!;
					s = { locals: [...ps.locals], ops: [...ps.ops], fibre: [...ps.fibre] };
				}
			}
		}
		const states = new Map<string, StackState>();
		for (const g of block.groups) {
			for (const op of g.ops) {
				for (const c of op.stackChanges.locals) {
					if (c.action === 'push') s.locals = [...s.locals, c.vreg];
					else if (c.action === 'pop') s.locals = s.locals.slice(0, -1);
					else if (c.action === 'set' && c.index !== undefined) { s.locals = [...s.locals]; s.locals[c.index] = c.vreg; }
				}
				for (const c of op.stackChanges.ops) {
					if (c.action === 'push') s.ops = [...s.ops, c.vreg];
					else if (c.action === 'pop') s.ops = s.ops.slice(0, -1);
				}
				for (const c of op.stackChanges.fibre) {
					if (c.action === 'push') s.fibre = [...s.fibre, c.vreg];
					else if (c.action === 'pop') s.fibre = s.fibre.slice(0, -1);
				}
				states.set(op.id, { locals: [...s.locals], ops: [...s.ops], fibre: [...s.fibre] });
			}
		}
		blockOpStates.set(block.id, states);
	}

	// --- Graph layout ---
	interface BlockPos { col: number; row: number; }
	const blockPos = new Map<string, BlockPos>();

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
		if (data.blocks.length > 0) place(data.blocks[0].id, 0, 0);
		for (const b of data.blocks) if (!placed.has(b.id)) place(b.id, 0, nr(0));
	}
	layout();

	const ROW_H = 20;
	const BLOCK_W = 560;
	const GAP_X = 80;
	const GAP_Y = 36;

	function blockHeight(block: Block): number {
		let rows = 0;
		for (const g of block.groups) {
			for (const op of g.ops) {
				rows += Math.max(1, block.asmEvents.filter(a => a.parentOp === op.id).length);
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
		for (const [id, pos] of blockPos) if (pos.row === r) mh = Math.max(mh, blockHeight(blockMap.get(id)!));
		yAcc += mh + GAP_Y;
	}
	const maxCol = Math.max(...[...blockPos.values()].map(p => p.col), 0);
	const canvasW = (maxCol + 1) * (BLOCK_W + GAP_X) + 80;
	const canvasH = yAcc + 40;

	function getRect(id: string) {
		const pos = blockPos.get(id)!;
		return { x: 20 + pos.col * (BLOCK_W + GAP_X), y: rowY.get(pos.row)!, w: BLOCK_W, h: blockHeight(blockMap.get(id)!) };
	}

	function computeArrows() {
		const res: { f: string; t: string; fall: boolean; path: string }[] = [];
		for (const block of data.blocks) {
			const fr = getRect(block.id);
			const is2 = block.successors.length === 2;
			for (let i = 0; i < block.successors.length; i++) {
				const s = block.successors[i];
				if (!blockPos.has(s)) continue;
				const tr = getRect(s);
				const fall = !is2 || i === 1;
				if (fall) {
					res.push({ f: block.id, t: s, fall: true, path: `M${fr.x + fr.w * 0.4},${fr.y + fr.h} L${fr.x + fr.w * 0.4},${tr.y}` });
				} else {
					const fx = fr.x + fr.w, fy = fr.y + fr.h * 0.45, tx = tr.x, ty = tr.y + 12;
					res.push({ f: block.id, t: s, fall: false, path: `M${fx},${fy} C${(fx + tx) / 2},${fy} ${(fx + tx) / 2},${ty} ${tx},${ty}` });
				}
			}
		}
		return res;
	}
	const arrows = computeArrows();

	// Pan/zoom handlers
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
			isPanning = true; psx = e.clientX; psy = e.clientY; ppx = panX; ppy = panY;
			(e.currentTarget as HTMLElement).setPointerCapture(e.pointerId); e.preventDefault();
		}
	}
	function onPtrMove(e: PointerEvent) { if (isPanning) { panX = ppx + (e.clientX - psx); panY = ppy + (e.clientY - psy); } }
	function onPtrUp() { isPanning = false; }
</script>

<div class="layout">
	<aside class="panel left">
		<WatPanel {data} />
	</aside>

	<main class="graph" onwheel={onWheel} onpointerdown={onPtrDown} onpointermove={onPtrMove} onpointerup={onPtrUp}>
		<div class="tbar">
			<h1>{data.name}</h1><code class="sig">{data.signature}</code>
			<span class="zi">{Math.round(zoom * 100)}%</span>
			<button class="tb" onclick={() => { zoom = 0.85; panX = 20; panY = 20; }}>reset</button>
			{#if app.highlightedVreg}<button class="tb" onclick={() => app.highlightedVreg = null}>✕ {app.highlightedVreg}</button>{/if}
			<span class="hint">alt+drag pan · scroll zoom · click op for state</span>
		</div>
		<div class="vp">
			<div class="cv" style="transform:translate({panX}px,{panY}px) scale({zoom}); width:{canvasW}px; height:{canvasH}px;">
				<svg class="arr" width={canvasW} height={canvasH}>
					<defs>
						<marker id="af" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="#585b70"/></marker>
						<marker id="ab" viewBox="0 0 10 10" refX="10" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0 0L10 5L0 10z" fill="#f38ba8"/></marker>
					</defs>
					{#each arrows as a}
						<path d={a.path} fill="none" stroke={a.fall ? '#585b70' : '#f38ba8'} stroke-width={a.fall ? 1.5 : 2} stroke-dasharray={a.fall ? '' : '6,3'} marker-end="url(#{a.fall ? 'af' : 'ab'})"/>
					{/each}
				</svg>

				{#each data.blocks as block}
					{@const rect = getRect(block.id)}
					<div class="blk" style="left:{rect.x}px;top:{rect.y}px;width:{rect.w}px;border-left-color:{blockColor(block.id)}">
						<BlockNode {block} {data} />
					</div>
				{/each}
			</div>
		</div>
	</main>

	<aside class="panel right">
		<VmState {data} {blockOpStates} />
	</aside>
</div>

<style>
	:global(body) { margin:0; background:#11111b; color:#cdd6f4; font-family:'SF Mono','Fira Code',monospace; font-size:12px; overflow:hidden; }
	.layout { display:flex; height:100vh; }
	.panel { background:#141420; padding:12px; overflow-y:auto; display:flex; flex-direction:column; gap:12px; flex-shrink:0; }
	.panel.left { width:240px; border-right:1px solid #313244; }
	.panel.right { width:200px; border-left:1px solid #313244; }

	.graph { flex:1; display:flex; flex-direction:column; overflow:hidden; }
	.tbar { display:flex; align-items:center; gap:8px; padding:6px 14px; border-bottom:1px solid #313244; background:#141420; flex-shrink:0; }
	h1 { font-size:15px; margin:0; color:#cba6f7; }
	.sig { color:#6c7086; font-size:11px; } .zi { color:#585b70; font-size:10px; }
	.tb { background:#313244; border:1px solid #45475a; color:#cdd6f4; padding:1px 6px; border-radius:3px; cursor:pointer; font-family:inherit; font-size:10px; }
	.tb:hover { background:#45475a; }
	.hint { margin-left:auto; color:#45475a; font-size:9px; }

	.vp { flex:1; overflow:hidden; position:relative; }
	.cv { position:absolute; top:0; left:0; transform-origin:0 0; }
	.arr { position:absolute; top:0; left:0; pointer-events:none; z-index:0; }

	.blk { position:absolute; border:1px solid #313244; border-left:3px solid; border-radius:6px; background:#181825; z-index:1; overflow:hidden; box-shadow:0 2px 12px rgba(0,0,0,0.4); }
</style>
