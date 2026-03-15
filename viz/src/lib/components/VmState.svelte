<script lang="ts">
	import type { FunctionData, Op } from '$lib/types';
	import { app, toggleVreg, kindColor, pregColor, vregWidth } from '$lib/state.svelte';

	let { data, blockOpStates }: {
		data: FunctionData;
		blockOpStates: Map<string, Map<string, { locals: string[]; ops: string[]; fibre: string[] }>>;
	} = $props();

	const blockMap = new Map(data.blocks.map(b => [b.id, b]));

	function getVM() {
		if (!app.selectedOp) return null;
		const states = blockOpStates.get(app.selectedOp.blockId);
		if (!states) return null;
		const state = states.get(app.selectedOp.opId);
		if (!state) return null;
		const block = blockMap.get(app.selectedOp.blockId)!;
		let op: Op | null = null;
		for (const g of block.groups) { op = g.ops.find(o => o.id === app.selectedOp!.opId) ?? op; }
		return op ? { state, op } : null;
	}
</script>

{#if getVM()}
	{@const vm = getVM()!}
	<h2>state @ {app.selectedOp?.opId}</h2>
	<div class="vm-op" style="border-left-color:{kindColor(vm.op.kind)}">{vm.op.text}</div>

	<h3>locals <span class="rb">x29+0</span></h3>
	<div class="stk">
		{#each vm.state.locals as v, i}
			{@const ch = vm.op.stackChanges.locals.find(c => (c.action === 'set' && c.index === i) || (c.action === 'push' && i === vm.state.locals.length - 1))}
			<div class="sl" class:sl-push={ch?.action === 'push'} class:sl-set={ch?.action === 'set'} class:sl-hl={app.highlightedVreg === v}>
				<span class="si">{i}</span>
				<button class="sv" onclick={() => toggleVreg(v)}>{v}</button>
				<span class="sw">{vregWidth(data, v)}</span>
			</div>
		{/each}
		{#if vm.state.locals.length === 0}<div class="empty">—</div>{/if}
	</div>

	<h3>operands <span class="rb">x29+24</span></h3>
	<div class="stk">
		{#each vm.state.ops as v, i}
			{@const ch = vm.op.stackChanges.ops.find(c => c.action === 'push' && c.vreg === v)}
			<div class="sl" class:sl-push={!!ch} class:sl-hl={app.highlightedVreg === v}>
				<span class="si">{i}</span>
				<button class="sv" onclick={() => toggleVreg(v)}>{v}</button>
				<span class="sw">{vregWidth(data, v)}</span>
			</div>
		{/each}
		{#if vm.state.ops.length === 0}<div class="empty">—</div>{/if}
	</div>

	<h3>fibre <span class="rb">sp+0</span></h3>
	<div class="stk">
		{#each vm.state.fibre as v, i}
			{@const ch = vm.op.stackChanges.fibre.find(c => c.action === 'push' && c.vreg === v)}
			<div class="sl" class:sl-push={!!ch} class:sl-hl={app.highlightedVreg === v}>
				<span class="si">{i}</span>
				<button class="sv" onclick={() => toggleVreg(v)}>{v}</button>
				<span class="sw">{vregWidth(data, v)}</span>
			</div>
		{/each}
		{#if vm.state.fibre.length === 0}<div class="empty">—</div>{/if}
	</div>

	{#if vm.op.bindings.length > 0}
		<h3>bindings</h3>
		<div class="stk">
			{#each vm.op.bindings as b}
				<div class="sl">
					<button class="sv" class:sl-hl={app.highlightedVreg === b.vreg} onclick={() => toggleVreg(b.vreg)}>{b.vreg}</button>
					{#if b.preg}
						<span class="ba">→</span><span class="bp" style="color:{pregColor(data, b.preg)}">{b.preg}</span>
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

<style>
	h2 { font-size:10px; text-transform:uppercase; letter-spacing:1px; color:#6c7086; margin:0; }
	h3 { font-size:9px; color:#585b70; margin:8px 0 3px 0; display:flex; align-items:center; gap:4px; }
	.rb { font-size:8px; color:#45475a; font-weight:normal; }
	.vm-op { font-size:11px; color:#cdd6f4; background:#1e1e2e; padding:4px 8px; border-radius:4px; border-left:2px solid transparent; word-break:break-all; }
	.vm-empty { color:#585b70; font-size:11px; padding:30px 0; text-align:center; }
	.stk { display:flex; flex-direction:column; gap:1px; }
	.sl { display:flex; align-items:center; gap:3px; padding:3px 6px; background:#1e1e2e; border-radius:3px; border-left:2px solid transparent; font-size:11px; }
	.sl-push { border-left-color:#a6e3a1; background:rgba(166,227,161,0.06); }
	.sl-set { border-left-color:#fab387; background:rgba(250,179,135,0.06); }
	.sl-hl { border-left-color:#fab387; background:rgba(250,179,135,0.12); }
	.si { color:#45475a; font-size:8px; min-width:8px; }
	.sv { background:none; border:none; color:#fab387; cursor:pointer; font-family:inherit; font-size:11px; padding:0; }
	.sv:hover { text-decoration:underline; }
	.sw { color:#45475a; font-size:8px; margin-left:auto; }
	.empty { color:#45475a; font-size:9px; padding:2px 5px; }
	.ba { color:#585b70; } .bp { font-weight:bold; font-size:11px; }
	.bloc { color:#585b70; font-size:8px; background:#141420; padding:0 3px; border-radius:2px; }
</style>
