<script lang="ts">
	import type { FunctionData } from '$lib/types';
	import { app, toggleWatLine, toggleVreg, pregColor } from '$lib/state.svelte';

	let { data }: { data: FunctionData } = $props();

	function watMatchesHover(wl: { wasmPcs: number[] }) {
		if (!app.hoveredOp) return false;
		for (const b of data.blocks) for (const g of b.groups) {
			if (g.ops.some(o => o.id === app.hoveredOp) && g.wasmPc !== null) return wl.wasmPcs.includes(g.wasmPc);
		}
		return false;
	}
</script>

<h2>source</h2>
<div class="wat-lines">
	{#each data.watSource as wl}
		<button class="wl" class:wl-on={app.hoveredWatLine === wl.line} class:wl-hov={watMatchesHover(wl)} onclick={() => toggleWatLine(wl)}>
			<span class="wpc">{wl.wasmPcs[0] ?? ''}</span>
			<code class="wt" style="padding-left:{wl.indent * 12}px">{wl.text}</code>
		</button>
	{/each}
</div>
<h2>vregs</h2>
<div class="vlist">
	{#each data.vregDefs as def}
		<button class="vdef" class:vdef-on={app.highlightedVreg === def.vreg} onclick={() => toggleVreg(def.vreg)}>
			<span class="vn">{def.vreg}</span><span class="vw">{def.width}</span>
			{#if def.target}<span class="vt" style="color:{pregColor(data, def.target)}">→{def.target}</span>{/if}
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

<style>
	h2 { font-size:10px; text-transform:uppercase; letter-spacing:1px; color:#6c7086; margin:0; }
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
</style>
