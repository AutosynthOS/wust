<script lang="ts">
	import type { FunctionTrace, OpView, RegAllocSnapshot } from '$lib/types';
	import { app } from '$lib/state.svelte';
	import { computeStateDiff, type SlotDiff } from '$lib/assemble';
	import VReg from './VReg.svelte';
	import PReg from './PReg.svelte';

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

	// Find the most recent snapshot at or before the selected event
	const snapshot = $derived.by((): RegAllocSnapshot | null => {
		if (app.selectedOp === null) return null;
		// Walk backwards through allOps to find nearest snapshot
		let best: RegAllocSnapshot | null = null;
		for (const op of allOps) {
			if (op.seq > app.selectedOp) break;
			if (op.event.snapshot) best = op.event.snapshot;
		}
		return best;
	});

	function locLabel(loc: string): string {
		switch (loc) {
			case 'reg': return 'reg';
			case 'mem': return 'mem';
			case 'const': return 'const';
			case 'pending': return 'pending';
			default: return loc;
		}
	}

	function locColor(loc: string): string {
		switch (loc) {
			case 'reg': return 'var(--accent-green)';
			case 'mem': return 'var(--accent-yellow)';
			case 'const': return 'var(--accent-teal)';
			case 'pending': return 'var(--text-dim)';
			default: return 'var(--text-muted)';
		}
	}
</script>

{#if selectedEvent && diff}
	<h2>state @ seq {app.selectedOp}</h2>
	<div class="op-preview">{selectedEvent.text}</div>

	<!-- Stack diffs -->
	{#each func.regions as region}
		{@const slots = region.id === 'locals' ? diff.locals : region.id === 'operands' ? diff.ops : diff.fibre}
		<h3>{region.label}</h3>
		<div class="stack">
			{#each slots as slot, i}
				<div class="slot {slot.action}">
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

	<!-- RegAlloc snapshot -->
	{#if snapshot}
		<h3>bindings</h3>
		<div class="bindings">
			{#each snapshot.bindings as b}
				<div class="binding" class:free={!b.vreg}>
					<PReg id={b.preg} />
					{#if b.vreg}
						<span class="bind-arrow">←</span>
						<VReg id={b.vreg} />
					{:else}
						<span class="bind-free">free</span>
					{/if}
				</div>
			{/each}
		</div>

		<h3>vreg locations</h3>
		<div class="locs">
			{#each snapshot.vreg_locs as vl}
				<div class="loc-row">
					<VReg id={vl.vreg} />
					<span class="loc-badge" style="color: {locColor(vl.loc)}">{locLabel(vl.loc)}</span>
					{#if vl.preg}
						<PReg id={vl.preg} />
					{/if}
					<span class="spacer"></span>
					<span class="dirty-badge" class:is-dirty={vl.dirty !== false}>
						{vl.dirty === false ? 'clean' : 'dirty'}
					</span>
				</div>
			{/each}
		</div>
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

		&.pushed { background: rgba(166, 227, 161, 0.1); }
		&.popped { background: rgba(243, 139, 168, 0.1); opacity: 0.6; }
		&.replaced { background: rgba(250, 179, 135, 0.1); }
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

	/* Bindings */
	.bindings {
		display: flex;
		flex-direction: column;
		gap: 1px;
	}

	.binding {
		display: flex;
		align-items: center;
		gap: 4px;
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);

		&.free { opacity: 0.4; }
	}

	.bind-arrow {
		color: var(--text-faint);
	}

	.bind-free {
		color: var(--text-faint);
		font-size: var(--font-size-xs);
		font-style: italic;
	}

	/* VReg locations */
	.locs {
		display: flex;
		flex-direction: column;
		gap: 1px;
	}

	.loc-row {
		display: flex;
		align-items: center;
		gap: 4px;
		padding: 2px 6px;
		background: var(--bg-surface);
		border-radius: 3px;
		font-size: var(--font-size-base);
	}

	.loc-badge {
		font-size: var(--font-size-xs);
		font-weight: bold;
	}

	.spacer {
		flex: 1;
	}

	.dirty-badge {
		font-size: var(--font-size-xxs);
		padding: 0 3px;
		border-radius: 2px;
		background: rgba(166, 227, 161, 0.15);
		color: var(--accent-green);

		&.is-dirty {
			background: rgba(250, 179, 135, 0.15);
			color: var(--accent-vreg);
		}
	}

	.placeholder {
		color: var(--text-dim);
		font-size: var(--font-size-base);
		padding: 20px 0;
		text-align: center;
	}
</style>
