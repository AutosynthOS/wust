<script lang="ts">
	import type { FunctionTrace, OpView, RegAllocSnapshot, VRegLoc } from '$lib/types';
	import { app } from '$lib/state.svelte';
	import { computeStateDiff, computeStateAt, type SlotDiff } from '$lib/assemble';
	import VReg from './VReg.svelte';
	import PReg from './PReg.svelte';
	import DirtyBadge from './DirtyBadge.svelte';

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

	const state = $derived(
		app.selectedOp !== null ? computeStateAt(func, app.selectedOp) : null
	);

	// Find most recent snapshot at or before selected event
	const snapshot = $derived.by((): RegAllocSnapshot | null => {
		if (app.selectedOp === null) return null;
		let best: RegAllocSnapshot | null = null;
		for (const op of allOps) {
			if (op.seq > app.selectedOp) break;
			if (op.event.snapshot) best = op.event.snapshot;
		}
		return best;
	});

	// Look up a vreg's location from the snapshot
	function vregLoc(vreg: string): VRegLoc | null {
		return snapshot?.vreg_locs.find(vl => vl.vreg === vreg) ?? null;
	}

	// Find vreg width from func defs
	function vregWidth(vreg: string): string {
		return func.vregs.find(d => d.id === vreg)?.width ?? '?';
	}

	function slotOffset(regionId: string, index: number): number {
		const region = func.regions.find(r => r.id === regionId);
		return (region?.base_offset ?? 0) + index * 4; // approximate
	}
</script>

{#if selectedEvent && diff && state}
	<h2>state @ seq {app.selectedOp}</h2>
	<div class="op-preview">{selectedEvent.text}</div>

	<!-- Bindings: ordered by preg — constant height -->
	{#if snapshot}
		<h3>bindings</h3>
		<div class="stack">
			{#each snapshot.bindings as b}
				<div class="slot" class:free={!b.vreg}>
					<PReg id={b.preg} />
					<span class="spacer"></span>
					{#if b.vreg}
						<VReg id={b.vreg} />
					{:else}
						<span class="free-label">free</span>
					{/if}
				</div>
			{/each}
		</div>
	{/if}

	<!-- Regions: unified vreg view per slot -->
	{#each func.regions as region}
		{@const slots = region.id === 'locals' ? diff.locals : region.id === 'operands' ? diff.ops : diff.fibre}
		<h3>{region.label}</h3>
		<div class="stack">
			{#each slots as slot, i}
				{@const vl = vregLoc(slot.vreg)}
				<div class="slot {slot.action}">
					<span class="diff-mark">
						{#if slot.action === 'pushed'}+{:else if slot.action === 'popped'}−{:else if slot.action === 'set'}~{:else}&nbsp;{/if}
					</span>
					<span class="slot-offset">+{slotOffset(region.id, i)}</span>
					<VReg id={slot.vreg} />
					<span class="slot-type">:{vregWidth(slot.vreg)}</span>
					<span class="spacer"></span>
					{#if vl?.preg}
						<PReg id={vl.preg} />
					{/if}
					{#if vl}
						<DirtyBadge dirty={vl.dirty !== false} />
					{/if}
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
		gap: 3px;
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);

		&.pushed { background: rgba(166, 227, 161, 0.1); }
		&.popped { background: rgba(243, 139, 168, 0.1); opacity: 0.6; }
		&.set { background: rgba(250, 179, 135, 0.1); }
	}

	.diff-mark {
		min-width: 10px;
		font-weight: bold;
	}

	.pushed .diff-mark { color: var(--accent-green); }
	.popped .diff-mark { color: var(--accent-red); }
	.set .diff-mark { color: var(--accent-vreg); }

	.slot-offset {
		color: var(--text-faint);
		font-size: var(--font-size-xxs);
		min-width: 20px;
	}

	.slot-type {
		color: var(--text-faint);
		font-size: var(--font-size-xs);
	}

	.spacer { flex: 1; }

	.const-badge {
		font-size: var(--font-size-xxs);
		color: var(--accent-teal);
	}

	.free { opacity: 0.35; }
	.free-label {
		color: var(--text-faint);
		font-size: var(--font-size-xs);
		font-style: italic;
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
