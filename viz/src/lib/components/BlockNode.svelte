<script lang="ts">
	import type { BlockView, FunctionTrace, OpView } from '$lib/types';
	import { app } from '$lib/state.svelte';
	import OpRow from './OpRow.svelte';

	let { block, func }: { block: BlockView; func: FunctionTrace } = $props();

	const ROW_H = 20;

	function opHeight(op: OpView): number {
		return Math.max(1, op.asm.length) * ROW_H;
	}

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
	{#each block.groups as group, gi}
		<div class="group" class:group-border={gi > 0}>
			<!-- PC -->
			<div class="col-pc" style="height: {groupHeight(group)}px"
				class:wat-match={app.highlightedWasmPcs.size > 0 && group.pc !== null && app.highlightedWasmPcs.has(group.pc)}>
				{#if group.pc !== null}
					<span class="pc">{group.pc}</span>
				{/if}
			</div>

			<!-- Label -->
			<div class="col-label" style="height: {groupHeight(group)}px">
				<span class="label-text">{group.label}</span>
			</div>

			<!-- Ops + ASM rows -->
			<div class="col-main">
				{#each group.ops as op}
					<OpRow {op} />
				{/each}
			</div>
		</div>
	{/each}
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
		flex-direction: column;
	}

	.group {
		display: flex;

		&.group-border {
			border-top: 1px solid var(--border-subtle);
		}
	}

	.col-pc {
		min-width: 28px;
		display: flex;
		align-items: center;
		justify-content: center;
		padding: 0 4px;
		border-right: 1px solid var(--border-subtle);

		&.wat-match {
			background: rgba(137, 180, 250, 0.08);
		}
	}

	.pc {
		color: var(--text-muted);
		font-size: var(--font-size-base);
	}

	.col-label {
		min-width: 100px;
		max-width: 130px;
		display: flex;
		align-items: center;
		padding: 0 6px;
		border-right: 1px solid var(--border-subtle);
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
