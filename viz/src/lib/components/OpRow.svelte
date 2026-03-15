<script lang="ts">
	import type { OpView } from '$lib/types';
	import { app, toggleVreg, selectOp } from '$lib/state.svelte';
	import { vregsRead, vregsDefined } from '$lib/assemble';
	import AsmLine from './AsmLine.svelte';
	import VReg from './VReg.svelte';

	let { op }: { op: OpView } = $props();

	const ROW_H = 20;
	const h = Math.max(1, op.asm.length) * ROW_H;
	const reads = vregsRead(op.event);
	const defs = vregsDefined(op.event);
	const touchesHighlighted = $derived(
		app.highlightedVreg !== null &&
		(reads.includes(app.highlightedVreg) || defs.includes(app.highlightedVreg))
	);
</script>

<div
	class="row"
	style="height: {h}px"
	class:hovered={app.hoveredOp === op.seq}
	class:selected={app.selectedOp === op.seq}
	class:highlighted={touchesHighlighted}
	class:dimmed={app.highlightedVreg !== null && !touchesHighlighted}
	onmouseenter={() => app.hoveredOp = op.seq}
	onmouseleave={() => app.hoveredOp = null}
	onclick={(e) => { e.stopPropagation(); selectOp(op.seq); }}
>
	<div class="op-cell">
		{#each op.text.split(/(v\d+)/) as part}
			{#if part.match(/^v\d+$/)}
				<VReg id={part} />
			{:else}
				<span class="op-text">{part}</span>
			{/if}
		{/each}
	</div>

	<div class="asm-cell">
		{#each op.asm as asm}
			<AsmLine {asm} />
		{/each}
	</div>
</div>

<style>
	.row {
		display: flex;
		box-sizing: border-box;
		cursor: pointer;

		&:hover { background: var(--hover-bg); }
		&.hovered { background: rgba(137, 180, 250, 0.06); }
		&.selected { background: var(--selected-bg); }
		&.highlighted { background: var(--highlight-bg); }
		&.dimmed { opacity: var(--dim-opacity); }
	}

	.op-cell {
		flex: 1;
		display: flex;
		align-items: center;
		padding: 0 6px;
		border-right: 1px solid var(--border-subtle);
		min-width: 0;
		overflow: hidden;
	}

	.op-text {
		color: var(--text-secondary);
		font-size: var(--font-size-base);
		white-space: pre;
	}

	.vreg {
		background: none;
		border: none;
		color: var(--accent-vreg);
		padding: 0;
		cursor: pointer;
		font-family: inherit;
		font-size: inherit;

		&:hover { text-decoration: underline; }
		&.vreg-active {
			background: var(--highlight-bg);
			border-radius: 2px;
			padding: 0 2px;
		}
	}

	.asm-cell {
		min-width: 200px;
		display: flex;
		flex-direction: column;
		justify-content: center;
		padding: 0 6px;
	}
</style>
