<script lang="ts">
	import type { Op, AsmEvent } from '$lib/types';
	import { app, toggleVreg, opTouchesVreg, selectOpAction, kindColor } from '$lib/state.svelte';
	import AsmLine from './AsmLine.svelte';

	let { op, asmList, blockId, data }: { op: Op; asmList: AsmEvent[]; blockId: string; data: any } = $props();
	const ROW_H = 20;
	const h = Math.max(1, asmList.length) * ROW_H;
	function vw(v: string): string { return data.vregDefs.find((d: any) => d.vreg === v)?.width ?? '?'; }
</script>

<div class="row" style="height:{h}px; border-left-color:{kindColor(op.kind)}"
	class:r-hov={app.hoveredOp === op.id}
	class:r-sel={app.selectedOp?.opId === op.id}
	class:r-hl={app.highlightedVreg !== null && opTouchesVreg(op, app.highlightedVreg)}
	class:r-dim={app.highlightedVreg !== null && !opTouchesVreg(op, app.highlightedVreg)}
	onmouseenter={() => app.hoveredOp = op.id}
	onmouseleave={() => app.hoveredOp = null}
	onclick={(e) => { e.stopPropagation(); selectOpAction(blockId, op.id); }}>
	<div class="op-cell">
		<span class="op-text">
			{#each op.text.split(/(v\d+)/) as part}
				{#if part.match(/^v\d+$/)}
					<button class="vr" class:vr-hl={app.highlightedVreg === part}
						onclick={(e) => { e.stopPropagation(); toggleVreg(part); }}
						title="{part}: {vw(part)}">{part}</button>
				{:else}{part}{/if}
			{/each}
		</span>
	</div>
	<div class="asm-cell">
		{#each asmList as asm}
			<AsmLine asm={asm.asm} addr={asm.addr} origin={asm.origin} />
		{/each}
	</div>
</div>

<style>
	.row { display:flex; border-bottom:1px solid rgba(49,50,68,0.3); border-left:2px solid transparent; box-sizing:border-box; cursor:pointer; }
	.row:last-child { border-bottom:none; }
	.row:hover { background:rgba(255,255,255,0.04); }
	.r-hov { background:rgba(137,180,250,0.06)!important; }
	.r-sel { background:rgba(203,166,247,0.1)!important; border-left-color:#cba6f7 !important; }
	.r-hl { background:rgba(250,179,135,0.06)!important; }
	.r-dim { opacity:0.2; }
	.op-cell { flex:1; display:flex; align-items:center; padding:0 6px; border-right:1px solid #313244; min-width:0; overflow:hidden; }
	.op-text { color:#bac2de; font-size:11px; white-space:nowrap; }
	.vr { background:none; border:none; color:#fab387; padding:0; cursor:pointer; font-family:inherit; font-size:inherit; }
	.vr:hover { text-decoration:underline; }
	.vr-hl { color:#fab387; background:rgba(250,179,135,0.15); border-radius:2px; padding:0 2px; }
	.asm-cell { min-width:180px; display:flex; flex-direction:column; justify-content:center; padding:0 6px; }
</style>
