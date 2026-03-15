<script lang="ts">
	import type { FunctionTrace, OpView, StackState } from '$lib/types';
	import { app, toggleVreg } from '$lib/state.svelte';
	import { computeStateAt } from '$lib/assemble';
	import VReg from './VReg.svelte';
	import PReg from './PReg.svelte';

	let { func, allOps }: {
		func: FunctionTrace;
		allOps: OpView[];
	} = $props();

	const selectedSeq = $derived(app.selectedOp);
	const selectedEvent = $derived(
		selectedSeq !== null ? allOps.find(o => o.seq === selectedSeq) : null
	);
	const state = $derived(
		selectedSeq !== null ? computeStateAt(func, selectedSeq) : null
	);
</script>

{#if selectedEvent && state}
	<h2>state @ seq {selectedSeq}</h2>
	<div class="op-preview">{selectedEvent.text}</div>

	{#each func.regions as region}
		{@const stack = region.id === 'locals' ? state.locals : region.id === 'operands' ? state.ops : state.fibre}
		<h3>{region.label} <span class="base">{region.base_preg}+{region.base_offset}</span></h3>
		<div class="stack">
			{#each stack as v, i}
				<div class="slot" class:slot-hl={app.highlightedVreg === v}>
					<span class="idx">{i}</span>
					<VReg id={v} />
				</div>
			{/each}
			{#if stack.length === 0}
				<div class="empty">—</div>
			{/if}
		</div>
	{/each}
{:else}
	<div class="placeholder">
		click an op to inspect
	</div>
{/if}

<style>
	h2 {
		font-size: var(--font-size-sm);
		text-transform: uppercase;
		letter-spacing: 1px;
		color: var(--text-muted);
		margin: 0;
	}

	h3 {
		font-size: var(--font-size-xs);
		color: var(--text-dim);
		margin: 10px 0 3px 0;
		display: flex;
		align-items: center;
		gap: 4px;
	}

	.base {
		font-size: var(--font-size-xxs);
		color: var(--text-faint);
		font-weight: normal;
	}

	.op-preview {
		font-size: var(--font-size-base);
		color: var(--text);
		background: var(--bg-surface);
		padding: 4px 8px;
		border-radius: 4px;
		word-break: break-all;
	}

	.stack {
		display: flex;
		flex-direction: column;
		gap: 1px;
	}

	.slot {
		display: flex;
		align-items: center;
		gap: 4px;
		padding: 3px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		border-left: 2px solid transparent;
		font-size: var(--font-size-base);

		&.slot-hl {
			border-left-color: var(--accent-vreg);
			background: var(--highlight-bg);
		}
	}

	.idx {
		color: var(--text-faint);
		font-size: var(--font-size-xxs);
		min-width: 8px;
	}

	.empty {
		color: var(--text-faint);
		font-size: var(--font-size-xs);
		padding: 2px 6px;
	}

	.placeholder {
		color: var(--text-dim);
		font-size: var(--font-size-base);
		padding: 30px 0;
		text-align: center;
	}
</style>
