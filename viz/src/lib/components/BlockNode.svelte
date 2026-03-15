<script lang="ts">
	import type { Block, FunctionData } from '$lib/types';
	import { app, groupHasWasmPc, blockColor } from '$lib/state.svelte';
	import OpRow from './OpRow.svelte';

	let { block, data }: { block: Block; data: FunctionData } = $props();
	const ROW_H = 20;
</script>

<div class="bh">
	<span class="bi" style="color:{blockColor(block.id)}">{block.id}</span>
	<span class="bl">{block.label}</span>
	{#if block.successors.length}<span class="bs">→ {block.successors.join(', ')}</span>{/if}
</div>
<div class="bb">
	<div class="c-wat">
		{#each block.groups as g}
			{@const opCount = g.ops.reduce((sum, op) => sum + Math.max(1, block.asmEvents.filter(a => a.parentOp === op.id).length), 0)}
			<div class="wat-cell" class:wat-match={app.highlightedWasmPcs.size > 0 && groupHasWasmPc(g, app.highlightedWasmPcs)} style="height:{opCount * ROW_H}px">
				{#if g.wasmPc !== null}<span class="wpc2">{g.wasmPc}</span>{/if}
				<span class="wat-lbl">{g.label}</span>
			</div>
		{/each}
	</div>
	<div class="c-main">
		{#each block.groups as g}
			{#each g.ops as op}
				<OpRow {op} asmList={block.asmEvents.filter(a => a.parentOp === op.id)} blockId={block.id} {data} />
			{/each}
		{/each}
	</div>
</div>

<style>
	.bh { display:flex; gap:6px; padding:3px 8px; background:#141420; border-bottom:1px solid #313244; align-items:center; }
	.bi { font-weight:bold; font-size:11px; } .bl { color:#6c7086; font-size:10px; } .bs { margin-left:auto; color:#45475a; font-size:9px; }
	.bb { display:flex; }
	.c-wat { min-width:100px; max-width:130px; display:flex; flex-direction:column; border-right:1px solid #313244; }
	.wat-cell { display:flex; align-items:center; gap:3px; padding:0 6px; border-bottom:1px solid rgba(49,50,68,0.3); box-sizing:border-box; overflow:hidden; }
	.wat-cell:last-child { border-bottom:none; }
	.wat-match { background:rgba(137,180,250,0.1); }
	.wpc2 { color:#585b70; font-size:8px; background:#313244; padding:0 2px; border-radius:2px; min-width:10px; text-align:center; }
	.wat-lbl { color:#cdd6f4; font-size:10px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
	.c-main { flex:1; display:flex; flex-direction:column; }
</style>
