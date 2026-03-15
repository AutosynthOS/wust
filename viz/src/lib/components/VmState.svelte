<script lang="ts">
	import type { FunctionView, OpView, RegAllocSnapshotView, RegionSnapshotView } from '$lib/transform';
	import { app } from '$lib/state.svelte';
	import VReg from './VReg.svelte';
	import PReg from './PReg.svelte';
	import DirtyBadge from './DirtyBadge.svelte';

	let { func, allOps }: {
		func: FunctionView;
		allOps: OpView[];
	} = $props();

	const selectedOp = $derived(
		app.selectedOp !== null ? allOps.find(o => o.seq === app.selectedOp) : null
	);

	// Find nearest regalloc snapshot at or before selected op
	const snapshot = $derived.by((): RegAllocSnapshotView | null => {
		if (app.selectedOp === null) return null;
		let best: RegAllocSnapshotView | null = null;
		for (const op of allOps) {
			if (op.seq > app.selectedOp) break;
			if (op.regalloc_snapshot) best = op.regalloc_snapshot;
		}
		return best;
	});

	// Find nearest region snapshot at or before selected op
	const regionSnapshot = $derived.by((): RegionSnapshotView[] | null => {
		if (app.selectedOp === null) return null;
		let best: RegionSnapshotView[] | null = null;
		for (const op of allOps) {
			if (op.seq > app.selectedOp) break;
			if (op.region_snapshot) best = op.region_snapshot;
		}
		return best;
	});

	function vregWidth(vreg: string): string {
		return func.vreg_defs.find(d => d.id === vreg)?.width ?? '?';
	}
</script>

{#if selectedOp && snapshot}
	<h2>state @ seq {app.selectedOp}</h2>
	<div class="op-preview">{selectedOp.text}</div>

	<!-- Bindings -->
	<h3>bindings</h3>
	<div class="bindings-grid">
		{#each snapshot.bindings as b}
			<div class="bind-preg" class:free={!b.vreg}>
				<PReg id={b.preg} />
			</div>
			<div class="bind-vreg" class:free={!b.vreg}>
				{#if b.vreg}
					{@const vl = snapshot.vreg_locs.find(v => v.vreg === b.vreg)}
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

	<!-- Regions -->
	{#if regionSnapshot}
		{#each regionSnapshot as region}
			<h3>{region.label}</h3>
			<div class="slots-grid">
				{#each region.slots as vreg, i}
					{@const vl = snapshot.vreg_locs.find(v => v.vreg === vreg)}
					<div class="slot-mark">{i}</div>
					<div class="slot-data">
						<VReg id={vreg} /><span class="type">:{vregWidth(vreg)}</span>
						<span class="spacer"></span>
						{#if vl?.preg}
							<PReg id={vl.preg} />
						{/if}
						{#if vl}
							<DirtyBadge dirty={vl.dirty !== false} />
						{/if}
					</div>
				{/each}
				{#if region.slots.length === 0}
					<div class="empty-mark"></div>
					<div class="empty">—</div>
				{/if}
			</div>
		{/each}
	{/if}
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
	}

	.slot-data {
		display: flex;
		align-items: center;
		gap: 3px;
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);
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
