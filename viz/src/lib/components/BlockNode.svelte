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
	<!-- PC column -->
	<div class="col-pc">
		{#each block.groups as group}
			<div class="pc-cell" style="height: {groupHeight(group)}px"
				class:wat-match={app.highlightedWasmPcs.size > 0 && group.pc !== null && app.highlightedWasmPcs.has(group.pc)}>
				{#if group.pc !== null}
					<span class="pc">{group.pc}</span>
				{/if}
			</div>
		{/each}
	</div>

	<!-- Label column -->
	<div class="col-label">
		{#each block.groups as group}
			<div class="label-cell" style="height: {groupHeight(group)}px">
				<span class="label-text">{group.label}</span>
			</div>
		{/each}
	</div>

	<!-- Ops + ASM -->
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
		padding: 4px 8px;
		background: var(--bg-block-header);
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

	.col-pc {
		min-width: 28px;
		display: flex;
		flex-direction: column;
		border-right: 1px solid var(--border-subtle);
	}

	.pc-cell {
		display: flex;
		align-items: center;
		justify-content: center;
		padding: 0 4px;
		box-sizing: border-box;

		&.wat-match { background: rgba(137, 180, 250, 0.08); }
	}

	.pc {
		color: var(--text-dim);
		font-size: var(--font-size-xxs);
	}

	.col-label {
		min-width: 100px;
		max-width: 130px;
		display: flex;
		flex-direction: column;
		border-right: 1px solid var(--border-subtle);
	}

	.label-cell {
		display: flex;
		align-items: center;
		padding: 0 6px;
		box-sizing: border-box;
		overflow: hidden;
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
