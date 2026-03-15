<script lang="ts">
	import type { FunctionTrace, OpView } from '$lib/types';
	import { app } from '$lib/state.svelte';
	import { computeStateDiff, type SlotDiff } from '$lib/assemble';
	import VReg from './VReg.svelte';

	let { func, allOps }: {
		func: FunctionTrace;
		allOps: OpView[];
	} = $props();

	const selectedEvent = $derived(
		app.selectedOp !== null ? allOps.find(o => o.seq === app.selectedOp) : null
	);
	const diff = $derived(
		app.selectedOp !== null ? computeStateDiff(func, app.selectedOp) : null
	);

	function renderStack(slots: SlotDiff[]): SlotDiff[] {
		return slots;
	}
</script>

{#if selectedEvent && diff}
	<h2>state @ seq {app.selectedOp}</h2>
	<div class="op-preview">{selectedEvent.text}</div>

	{#each func.regions as region}
		{@const slots = region.id === 'locals' ? diff.locals : region.id === 'operands' ? diff.ops : diff.fibre}
		<h3>{region.label}</h3>
		<div class="stack">
			{#each slots as slot, i}
				<div class="slot" class:pushed={slot.action === 'pushed'} class:popped={slot.action === 'popped'} class:replaced={slot.action === 'set'}>
					<span class="diff-mark">
						{#if slot.action === 'pushed'}+{:else if slot.action === 'popped'}−{:else if slot.action === 'set'}~{:else}&nbsp;{/if}
					</span>
					<span class="slot-idx">{i}</span>
					<VReg id={slot.vreg} />
				</div>
			{/each}
			{#if slots.length === 0}
				<div class="empty">—</div>
			{/if}
		</div>
	{/each}
{:else}
	<div class="placeholder">click an op to inspect</div>
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
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);

		&.pushed {
			background: rgba(166, 227, 161, 0.1);
		}

		&.popped {
			background: rgba(243, 139, 168, 0.1);
			text-decoration: line-through;
			opacity: 0.6;
		}

		&.replaced {
			background: rgba(250, 179, 135, 0.1);
		}
	}

	.diff-mark {
		min-width: 10px;
		font-weight: bold;
		font-size: var(--font-size-base);
	}

	.pushed .diff-mark { color: var(--accent-green); }
	.popped .diff-mark { color: var(--accent-red); }
	.replaced .diff-mark { color: var(--accent-vreg); }

	.slot-idx {
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
		padding: 20px 0;
		text-align: center;
	}
</style>
