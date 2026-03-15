<script lang="ts">
	import { fibData } from '$lib/mock';
	import type { Block, Op, WatLine, WasmGroup } from '$lib/types';

	let highlightedVreg: string | null = $state(null);
	let hoveredOp: string | null = $state(null);
	let selectedOp: { blockId: string; opId: string } | null = $state(null);
	let highlightedWasmPcs: Set<number> = $state(new Set());
	let hoveredWatLine: number | null = $state(null);
	let zoom = $state(0.85);
	let panX = $state(20);
	let panY = $state(20);
	let isPanning = $state(false);
	let psx = 0; let psy = 0; let ppx = 0; let ppy = 0;

	const data = fibData;
	const blockMap = new Map(data.blocks.map(b => [b.id, b]));

	// --- Stack state at each op ---
	interface StackState { locals: string[]; ops: string[]; fibre: string[]; }

	// Flatten all ops per block with running stack state
	const blockOpStates = new Map<string, Map<string, StackState>>();
	for (const block of data.blocks) {
		let s: StackState = { locals: [], ops: [], fibre: [] };
		// Inherit from first predecessor
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

	function getSelectedVM() {
		if (!selectedOp) return null;
		const states = blockOpStates.get(selectedOp.blockId);
		if (!states) return null;
		const state = states.get(selectedOp.opId);
		if (!state) return null;
		// Find the op object
		const block = blockMap.get(selectedOp.blockId)!;
		let op: Op | null = null;
		for (const g of block.groups) { op = g.ops.find(o => o.id === selectedOp!.opId) ?? op; }
		return op ? { state, op } : null;
	}

	function selectOp(blockId: string, opId: string, e: MouseEvent) {
		e.stopPropagation();
		if (selectedOp?.blockId === blockId && selectedOp?.opId === opId) selectedOp = null;
		else selectedOp = { blockId, opId };
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
				const asmCount = block.asmEvents.filter(a => a.parentOp === op.id).length;
				rows += Math.max(1, asmCount);
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

	// Handlers
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

	function pregColor(p: string) { return data.pregColors[p] ?? '#abb2bf'; }
	function originBadge(o: string) { return o === 'lower' ? 'lo' : o === 'regalloc' ? 'ra' : 'fu'; }
	function formatAddr(a: number) { return a.toString(16).padStart(4, '0'); }
	function toggleVreg(v: string, e: MouseEvent) { e.stopPropagation(); highlightedVreg = highlightedVreg === v ? null : v; }
	function vregWidth(v: string) { return data.vregDefs.find(d => d.vreg === v)?.width ?? '?'; }
	function opTouchesVreg(op: Op, v: string) { return op.vregsRead.includes(v) || op.vregsDefined.includes(v); }
	function groupHasWasmPc(g: WasmGroup, pcs: Set<number>) { return g.wasmPc !== null && pcs.has(g.wasmPc); }
	function toggleWatLine(wl: WatLine) {
		if (hoveredWatLine === wl.line) { hoveredWatLine = null; highlightedWasmPcs = new Set(); }
		else { hoveredWatLine = wl.line; highlightedWasmPcs = new Set(wl.wasmPcs); }
	}
	function watMatchesHover(wl: WatLine) {
		if (!hoveredOp) return false;
		for (const b of data.blocks) for (const g of b.groups) {
			if (g.ops.some(o => o.id === hoveredOp) && g.wasmPc !== null) return wl.wasmPcs.includes(g.wasmPc);
		}
		return false;
	}
	function blockColor(id: string) { return id.startsWith('G') ? '#f38ba8' : id === 'Ep' ? '#a6e3a1' : '#89b4fa'; }

	function kindColor(kind: string) {
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
</script>

<div class="layout">
	<aside class="panel left">
		<h2>source</h2>
		<div class="wat-lines">
			{#each data.watSource as wl}
				<button class="wl" class:wl-on={hoveredWatLine === wl.line} class:wl-hov={watMatchesHover(wl)} onclick={() => toggleWatLine(wl)}>
					<span class="wpc">{wl.wasmPcs[0] ?? ''}</span>
					<code class="wt" style="padding-left:{wl.indent * 12}px">{wl.text}</code>
				</button>
			{/each}
		</div>
		<h2>vregs</h2>
		<div class="vlist">
			{#each data.vregDefs as def}
				<button class="vdef" class:vdef-on={highlightedVreg === def.vreg} onclick={(e) => toggleVreg(def.vreg, e)}>
					<span class="vn">{def.vreg}</span><span class="vw">{def.width}</span>
					{#if def.target}<span class="vt" style="color:{pregColor(def.target)}">→{def.target}</span>{/if}
				</button>
			{/each}
		</div>
		<h2>legend</h2>
		<div class="leg">
			<span><span class="bdg" style="background:#a6e3a1">def</span> define</span>
			<span><span class="bdg" style="background:#89b4fa">set</span> setslot</span>
			<span><span class="bdg" style="background:#f38ba8">clr</span> clear/pop</span>
			<span><span class="bdg" style="background:#fab387">clo</span> clobber</span>
			<span><span class="bdg" style="background:#cba6f7">res</span> resolve</span>
		</div>
	</aside>

	<main class="graph" onwheel={onWheel} onpointerdown={onPtrDown} onpointermove={onPtrMove} onpointerup={onPtrUp}>
		<div class="tbar">
			<h1>{data.name}</h1><code class="sig">{data.signature}</code>
			<span class="zi">{Math.round(zoom * 100)}%</span>
			<button class="tb" onclick={() => { zoom = 0.85; panX = 20; panY = 20; }}>reset</button>
			{#if highlightedVreg}<button class="tb" onclick={() => highlightedVreg = null}>✕ {highlightedVreg}</button>{/if}
			<span class="hint">alt+drag · scroll zoom</span>
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
						<div class="bh"><span class="bi" style="color:{blockColor(block.id)}">{block.id}</span><span class="bl">{block.label}</span>
							{#if block.successors.length}<span class="bs">→ {block.successors.join(', ')}</span>{/if}
						</div>
						<div class="bb">
							<!-- Col 1: WAT/IR label -->
							<div class="c-wat">
								{#each block.groups as g}
									{@const opCount = g.ops.reduce((sum, op) => sum + Math.max(1, block.asmEvents.filter(a => a.parentOp === op.id).length), 0)}
									<div class="wat-cell" class:wat-match={highlightedWasmPcs.size > 0 && groupHasWasmPc(g, highlightedWasmPcs)} style="height:{opCount * ROW_H}px">
										{#if g.wasmPc !== null}<span class="wpc2">{g.wasmPc}</span>{/if}
										<span class="wat-lbl">{g.label}</span>
									</div>
								{/each}
							</div>
							<!-- Col 2: Operations -->
							<div class="c-ops">
								{#each block.groups as g}
									{#each g.ops as op}
										{@const asmList = block.asmEvents.filter(a => a.parentOp === op.id)}
										{@const h = Math.max(1, asmList.length) * ROW_H}
										<div class="op-row" style="height:{h}px; border-left-color:{kindColor(op.kind)}"
											class:op-hov={hoveredOp === op.id}
											class:op-sel={selectedOp?.opId === op.id}
											class:op-hl={highlightedVreg !== null && opTouchesVreg(op, highlightedVreg)}
											class:op-dim={highlightedVreg !== null && !opTouchesVreg(op, highlightedVreg)}
											onmouseenter={() => hoveredOp = op.id}
											onmouseleave={() => hoveredOp = null}
											onclick={(e) => selectOp(block.id, op.id, e)}>
											<span class="op-text">
												{#each op.text.split(/(v\d+)/) as part}
													{#if part.match(/^v\d+$/)}
														<button class="vr" class:vr-hl={highlightedVreg === part}
															onclick={(e) => toggleVreg(part, e)} title="{part}: {vregWidth(part)}">{part}</button>
													{:else}{part}{/if}
												{/each}
											</span>
										</div>
									{/each}
								{/each}
							</div>
							<!-- Col 3: ASM -->
							<div class="c-asm">
								{#each block.groups as g}
									{#each g.ops as op}
										{@const asmList = block.asmEvents.filter(a => a.parentOp === op.id)}
										{@const h = Math.max(1, asmList.length) * ROW_H}
										<div class="asm-grp" style="height:{h}px"
											class:op-hov={hoveredOp === op.id}
											onmouseenter={() => hoveredOp = op.id}
											onmouseleave={() => hoveredOp = null}>
											{#each asmList as asm}
												<div class="aln">
													<span class="aa">{formatAddr(asm.addr)}</span>
													<span class="ab {asm.origin}">{originBadge(asm.origin)}</span>
													<code class="at">{asm.asm}</code>
												</div>
											{/each}
										</div>
									{/each}
								{/each}
							</div>
						</div>
					</div>
				{/each}
			</div>
		</div>
	</main>

	<aside class="panel right">
		{#if getSelectedVM()}
			{@const vm = getSelectedVM()!}
			<h2>state @ {selectedOp?.opId}</h2>
			<div class="vm-op" style="border-left-color:{kindColor(vm.op.kind)}">{vm.op.text}</div>

			<h3>locals <span class="rb">x29+0</span></h3>
			<div class="stk">
				{#each vm.state.locals as v, i}
					{@const ch = vm.op.stackChanges.locals.find(c => (c.action === 'set' && c.index === i) || (c.action === 'push' && i === vm.state.locals.length - 1))}
					<div class="sl" class:sl-push={ch?.action === 'push'} class:sl-set={ch?.action === 'set'} class:sl-hl={highlightedVreg === v}>
						<span class="si">{i}</span>
						<button class="sv2" onclick={(e) => toggleVreg(v, e)}>{v}</button>
						<span class="sw">{vregWidth(v)}</span>
					</div>
				{/each}
				{#if vm.state.locals.length === 0}<div class="empty">—</div>{/if}
			</div>

			<h3>operands <span class="rb">x29+24</span></h3>
			<div class="stk">
				{#each vm.state.ops as v, i}
					{@const ch = vm.op.stackChanges.ops.find(c => c.action === 'push' && c.vreg === v)}
					<div class="sl" class:sl-push={!!ch} class:sl-hl={highlightedVreg === v}>
						<span class="si">{i}</span>
						<button class="sv2" onclick={(e) => toggleVreg(v, e)}>{v}</button>
						<span class="sw">{vregWidth(v)}</span>
					</div>
				{/each}
				{#if vm.state.ops.length === 0}<div class="empty">—</div>{/if}
			</div>

			<h3>fibre <span class="rb">sp+0</span></h3>
			<div class="stk">
				{#each vm.state.fibre as v, i}
					{@const ch = vm.op.stackChanges.fibre.find(c => c.action === 'push' && c.vreg === v)}
					<div class="sl" class:sl-push={!!ch} class:sl-hl={highlightedVreg === v}>
						<span class="si">{i}</span>
						<button class="sv2" onclick={(e) => toggleVreg(v, e)}>{v}</button>
						<span class="sw">{vregWidth(v)}</span>
					</div>
				{/each}
				{#if vm.state.fibre.length === 0}<div class="empty">—</div>{/if}
			</div>

			{#if vm.op.bindings.length > 0}
				<h3>bindings</h3>
				<div class="stk">
					{#each vm.op.bindings as b}
						<div class="sl">
							<button class="sv2" class:sl-hl={highlightedVreg === b.vreg} onclick={(e) => toggleVreg(b.vreg, e)}>{b.vreg}</button>
							{#if b.preg}
								<span class="ba">→</span><span class="bp" style="color:{pregColor(b.preg)}">{b.preg}</span>
							{:else}
								<span class="bloc">{b.loc}</span>
							{/if}
						</div>
					{/each}
				</div>
			{/if}
		{:else}
			<div class="vm-empty">click an op to inspect VM state</div>
		{/if}
	</aside>
</div>

<style>
	:global(body) { margin:0; background:#1e1e2e; color:#cdd6f4; font-family:'SF Mono','Fira Code',monospace; font-size:12px; overflow:hidden; }
	.layout { display:flex; height:100vh; }

	.panel { background:#181825; padding:12px; overflow-y:auto; display:flex; flex-direction:column; gap:12px; flex-shrink:0; }
	.panel.left { width:240px; border-right:1px solid #313244; }
	.panel.right { width:200px; border-left:1px solid #313244; }
	.panel h2 { font-size:10px; text-transform:uppercase; letter-spacing:1px; color:#6c7086; margin:0; }

	.wat-lines { display:flex; flex-direction:column; }
	.wl { display:flex; gap:4px; padding:1px 4px; background:none; border:none; border-left:2px solid transparent; color:#cdd6f4; cursor:pointer; font-family:inherit; font-size:11px; text-align:left; }
	.wl:hover { background:rgba(255,255,255,0.03); }
	.wl-on { background:rgba(137,180,250,0.1)!important; border-left-color:#89b4fa; }
	.wl-hov { background:rgba(203,166,247,0.08)!important; border-left-color:#cba6f7; }
	.wpc { color:#585b70; min-width:16px; text-align:right; font-size:9px; background:#313244; padding:0 3px; border-radius:2px; }
	.wl-on .wpc { color:#89b4fa; }
	.wt { color:#a6adc8; white-space:pre; } .wl-on .wt { color:#cdd6f4; }

	.vlist { display:flex; flex-direction:column; gap:1px; }
	.vdef { display:flex; gap:6px; background:none; border:1px solid transparent; color:#cdd6f4; padding:1px 6px; border-radius:3px; cursor:pointer; font-family:inherit; font-size:11px; text-align:left; }
	.vdef:hover { background:#313244; } .vdef-on { border-color:#fab387; background:rgba(250,179,135,0.1); }
	.vn { color:#fab387; min-width:24px; } .vw { color:#585b70; font-size:10px; } .vt { font-size:10px; }
	.leg { display:flex; flex-direction:column; gap:2px; font-size:10px; color:#6c7086; }
	.bdg { display:inline-block; padding:0 4px; border-radius:3px; color:#1e1e2e; font-size:8px; font-weight:bold; }

	.graph { flex:1; display:flex; flex-direction:column; overflow:hidden; }
	.tbar { display:flex; align-items:center; gap:8px; padding:6px 14px; border-bottom:1px solid #313244; background:#181825; flex-shrink:0; }
	h1 { font-size:15px; margin:0; color:#cba6f7; }
	.sig { color:#6c7086; font-size:11px; } .zi { color:#585b70; font-size:10px; }
	.tb { background:#313244; border:1px solid #45475a; color:#cdd6f4; padding:1px 6px; border-radius:3px; cursor:pointer; font-family:inherit; font-size:10px; }
	.tb:hover { background:#45475a; }
	.hint { margin-left:auto; color:#45475a; font-size:9px; }

	.vp { flex:1; overflow:hidden; cursor:grab; position:relative; }
	.vp:active { cursor:grabbing; }
	.cv { position:absolute; top:0; left:0; transform-origin:0 0; }
	.arr { position:absolute; top:0; left:0; pointer-events:none; z-index:0; }

	.blk { position:absolute; border:1px solid #313244; border-left:3px solid; border-radius:6px; background:#1e1e2e; z-index:1; overflow:hidden; box-shadow:0 2px 8px rgba(0,0,0,0.3); }
	.bh { display:flex; gap:6px; padding:3px 8px; background:#181825; border-bottom:1px solid #313244; align-items:center; }
	.bi { font-weight:bold; font-size:11px; } .bl { color:#6c7086; font-size:10px; } .bs { margin-left:auto; color:#45475a; font-size:9px; }
	.bb { display:flex; }

	/* Col 1: WAT label */
	.c-wat { min-width:100px; max-width:120px; display:flex; flex-direction:column; border-right:1px solid #313244; }
	.wat-cell { display:flex; align-items:center; gap:3px; padding:0 6px; border-bottom:1px solid rgba(49,50,68,0.3); box-sizing:border-box; overflow:hidden; }
	.wat-cell:last-child { border-bottom:none; }
	.wat-match { background:rgba(137,180,250,0.1); }
	.wpc2 { color:#585b70; font-size:8px; background:#313244; padding:0 2px; border-radius:2px; min-width:10px; text-align:center; }
	.wat-lbl { color:#bac2de; font-size:10px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }

	/* Col 2: Ops */
	.c-ops { flex:1; display:flex; flex-direction:column; border-right:1px solid #313244; min-width:0; }
	.op-row { display:flex; align-items:center; padding:0 6px; border-bottom:1px solid rgba(49,50,68,0.3); border-left:2px solid transparent; box-sizing:border-box; overflow:hidden; }
	.op-row:last-child { border-bottom:none; }
	.op-row:hover { background:rgba(255,255,255,0.02); }
	.op-hov { background:rgba(137,180,250,0.06)!important; }
	.op-sel { background:rgba(203,166,247,0.1)!important; border-left-color:#cba6f7 !important; }
	.op-hl { background:rgba(250,179,135,0.06)!important; }
	.op-dim { opacity:0.2; }
	.op-text { color:#a6adc8; font-size:10px; white-space:nowrap; }
	.vr { background:none; border:none; color:#fab387; padding:0; cursor:pointer; font-family:inherit; font-size:inherit; }
	.vr:hover { text-decoration:underline; } .vr-hl { color:#fab387; background:rgba(250,179,135,0.15); border-radius:2px; padding:0 2px; }

	/* Col 3: ASM */
	.c-asm { min-width:170px; display:flex; flex-direction:column; }
	.asm-grp { display:flex; flex-direction:column; justify-content:center; padding:0 6px; border-bottom:1px solid rgba(49,50,68,0.3); box-sizing:border-box; }
	.asm-grp:last-child { border-bottom:none; }
	.asm-grp.op-hov { background:rgba(137,180,250,0.06)!important; }
	.aln { display:flex; align-items:center; gap:4px; height:18px; }
	.aa { color:#45475a; font-size:9px; min-width:28px; }
	.ab { font-size:7px; padding:0 3px; border-radius:2px; color:#1e1e2e; font-weight:bold; }
	.ab.lower { background:#61afef; } .ab.regalloc { background:#e5c07b; } .ab.fuse { background:#c678dd; }
	.at { color:#a6e3a1; font-size:10px; }

	/* Right panel: VM state */
	.panel.right h2 { font-size:10px; text-transform:uppercase; letter-spacing:1px; color:#6c7086; margin:0; }
	.panel.right h3 { font-size:9px; color:#585b70; margin:8px 0 3px 0; display:flex; align-items:center; gap:4px; }
	.rb { font-size:8px; color:#45475a; font-weight:normal; }
	.vm-op { font-size:10px; color:#bac2de; background:#313244; padding:3px 6px; border-radius:4px; border-left:2px solid transparent; word-break:break-all; }
	.vm-empty { color:#45475a; font-size:10px; padding:30px 0; text-align:center; }
	.stk { display:flex; flex-direction:column; gap:1px; }
	.sl { display:flex; align-items:center; gap:3px; padding:2px 5px; background:#313244; border-radius:3px; border-left:2px solid transparent; font-size:10px; }
	.sl-push { border-left-color:#a6e3a1; background:rgba(166,227,161,0.06); }
	.sl-set { border-left-color:#fab387; background:rgba(250,179,135,0.06); }
	.sl-hl { border-left-color:#fab387; background:rgba(250,179,135,0.12); }
	.si { color:#45475a; font-size:8px; min-width:8px; }
	.sv2 { background:none; border:none; color:#fab387; cursor:pointer; font-family:inherit; font-size:10px; padding:0; }
	.sv2:hover { text-decoration:underline; }
	.sw { color:#45475a; font-size:8px; margin-left:auto; }
	.empty { color:#45475a; font-size:9px; padding:2px 5px; }
	.ba { color:#585b70; } .bp { font-weight:bold; font-size:10px; }
	.bloc { color:#585b70; font-size:8px; background:#1e1e2e; padding:0 3px; border-radius:2px; }
</style>
