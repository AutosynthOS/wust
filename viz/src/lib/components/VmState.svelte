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

	const snapshot = $derived.by((): RegAllocSnapshot | null => {
		if (app.selectedOp === null) return null;
		let best: RegAllocSnapshot | null = null;
		for (const op of allOps) {
			if (op.seq > app.selectedOp) break;
			if (op.event.snapshot) best = op.event.snapshot;
		}
		return best;
	});

	function vregLoc(vreg: string): VRegLoc | null {
		return snapshot?.vreg_locs.find(vl => vl.vreg === vreg) ?? null;
	}

	function vregWidth(vreg: string): string {
		return func.vregs.find(d => d.id === vreg)?.width ?? '?';
	}

	function slotOffset(regionId: string, index: number): number {
		const region = func.regions.find(r => r.id === regionId);
		return (region?.base_offset ?? 0) + index * 4;
	}
</script>

{#if selectedEvent && diff && state}
	<h2>state @ seq {app.selectedOp}</h2>
	<div class="op-preview">{selectedEvent.text}</div>

	<!-- Bindings -->
	{#if snapshot}
		<h3>bindings</h3>
		<div class="bindings-grid">
			{#each snapshot.bindings as b}
				<div class="bind-preg" class:free={!b.vreg}>
					<PReg id={b.preg} />
				</div>
				<div class="bind-vreg" class:free={!b.vreg}>
					{#if b.vreg}
						{@const vl = vregLoc(b.vreg)}
						<VReg id={b.vreg} /><span class="type">:{vregWidth(b.vreg)}</span>
						{#if vl}
							<span class="spacer"></span>
							<DirtyBadge dirty={vl.dirty !== false} />
						{/if}
					{:else}
						<span class="free-label">free</span>
					{/if}
				</div>
			{/each}
		</div>
	{/if}

	<!-- Regions -->
	{#each func.regions as region}
		{@const slots = region.id === 'locals' ? diff.locals : region.id === 'operands' ? diff.ops : diff.fibre}
		<h3>{region.label}</h3>
		<div class="slots-grid">
			{#each slots as slot, i}
				{@const vl = vregLoc(slot.vreg)}
				<div class="slot-mark {slot.action}">
					{#if slot.action === 'pushed'}+{:else if slot.action === 'popped'}−{:else}{i}{/if}
				</div>
				<div class="slot-data {slot.action}">
					<span class="offset">+{slotOffset(region.id, i)}</span>
					<VReg id={slot.vreg} /><span class="type">:{vregWidth(slot.vreg)}</span>
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
				<div class="empty-mark"></div>
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

	/* Bindings grid */
	.bindings-grid {
		display: grid;
		grid-template-columns: auto 1fr;
		gap: 1px;
	}

	.bind-preg {
		display: flex;
		align-items: center;
		padding: 2px 6px;
		font-size: var(--font-size-base);
		&.free { opacity: 0.35; }
	}

	.bind-vreg {
		display: flex;
		align-items: center;
		gap: 3px;
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);
		&.free { opacity: 0.35; }
	}

	.free-label {
		color: var(--text-faint);
		font-size: var(--font-size-xs);
		font-style: italic;
	}

	/* Slots grid */
	.slots-grid {
		display: grid;
		grid-template-columns: 18px 1fr;
		gap: 1px;
	}

	.slot-mark {
		display: flex;
		align-items: center;
		justify-content: center;
		font-size: var(--font-size-sm);
		font-weight: bold;
		color: var(--text-faint);

		&.pushed { color: var(--accent-green); }
		&.popped { color: var(--accent-red); }
	}

	.slot-data {
		display: flex;
		align-items: center;
		gap: 3px;
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);

		&.pushed { background: rgba(166, 227, 161, 0.1); }
		&.popped { background: rgba(243, 139, 168, 0.1); }
		&.set { background: rgba(250, 179, 135, 0.1); }
	}

	.offset {
		color: var(--text-dim);
		font-size: var(--font-size-sm);
		min-width: 22px;
	}

	.type {
		color: var(--text-dim);
		font-size: var(--font-size-xs);
	}

	.spacer { flex: 1; }

	.empty-mark { }
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
