<script lang="ts">
	import type { BlockView, FunctionTrace } from '$lib/types';
	import { app } from '$lib/state.svelte';
	import OpRow from './OpRow.svelte';

	let { block, func }: { block: BlockView; func: FunctionTrace } = $props();

	const ROW_H = 20;

	function groupHeight(group: typeof block.groups[0]): number {
		let rows = 0;
		for (const op of group.ops) {
			rows += Math.max(1, op.asm.length);
		}
		return Math.max(1, rows) * ROW_H;
	}
</script>

<div class="header">
	<span class="block-id">{block.id}</span>
	{#if block.successors.length}
		<span class="successors">→ {block.successors.join(', ')}</span>
	{/if}
</div>

<div class="body">
	<!-- WAT/label column -->
	<div class="col-label">
		{#each block.groups as group}
			<div class="label-cell" style="height: {groupHeight(group)}px"
				class:wat-match={app.highlightedWasmPcs.size > 0 && group.pc !== null && app.highlightedWasmPcs.has(group.pc)}>
				{#if group.pc !== null}
					<span class="pc">{group.pc}</span>
				{/if}
				<span class="label-text">{group.label}</span>
			</div>
		{/each}
	</div>

	<!-- Ops + ASM columns -->
	<div class="col-main">
		{#each block.groups as group}
			{#each group.ops as op}
				<OpRow {op} />
			{/each}
		{/each}
	</div>
</div>

<style>
	.header {
		display: flex;
		align-items: center;
		gap: 8px;
		padding: 3px 8px;
		background: var(--bg-block-header);
		border-bottom: 1px solid var(--border);
	}

	.block-id {
		font-weight: bold;
		font-size: var(--font-size-base);
		color: var(--text);
	}

	.successors {
		margin-left: auto;
		color: var(--text-faint);
		font-size: var(--font-size-xs);
	}

	.body {
		display: flex;
	}

	.col-label {
		min-width: 110px;
		max-width: 140px;
		display: flex;
		flex-direction: column;
		border-right: 1px solid var(--border);
	}

	.label-cell {
		display: flex;
		align-items: center;
		gap: 4px;
		padding: 0 6px;
		border-bottom: 1px solid var(--border-subtle);
		box-sizing: border-box;
		overflow: hidden;

		&:last-child { border-bottom: none; }
		&.wat-match { background: rgba(137, 180, 250, 0.08); }
	}

	.pc {
		color: var(--text-dim);
		font-size: var(--font-size-xxs);
		background: var(--bg-elevated);
		padding: 0 3px;
		border-radius: 2px;
		min-width: 12px;
		text-align: center;
	}

	.label-text {
		color: var(--text);
		font-size: var(--font-size-sm);
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}

	.col-main {
		flex: 1;
		display: flex;
		flex-direction: column;
	}
</style>
