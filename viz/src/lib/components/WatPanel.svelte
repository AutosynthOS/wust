<script lang="ts">
	import type { ModuleTrace, FunctionTrace } from '$lib/types';
	import { app, toggleSourceLine, toggleVreg } from '$lib/state.svelte';
	import VReg from './VReg.svelte';

	let { trace, func }: { trace: ModuleTrace; func: FunctionTrace } = $props();

	const source = $derived(
		trace.source.filter(l => l.func_index === func.index)
	);
</script>

<section>
	<h2>source</h2>
	<div class="lines">
		{#each source as line}
			<button
				class="line"
				class:active={app.selectedWasmPc === line.pc}
				onclick={() => toggleSourceLine(line)}
			>
				<span class="pc">{line.pc}</span>
				<code class="text" style="padding-left: {line.indent * 12}px">{line.text}</code>
			</button>
		{/each}
	</div>
</section>

<section>
	<h2>vregs</h2>
	<div class="vreg-list">
		{#each func.vregs as def}
			<div class="vreg-row" class:vreg-active={app.highlightedVreg === def.id}>
				<VReg id={def.id} width={def.width} target={def.target} />
				<span class="vreg-width">{def.width}</span>
				{#if def.target}
					<span class="vreg-target">→{def.target}</span>
				{/if}
			</div>
		{/each}
	</div>
</section>

<style>
	section {
		display: flex;
		flex-direction: column;
		gap: 4px;
	}

	h2 {
		font-size: var(--font-size-sm);
		text-transform: uppercase;
		letter-spacing: 1px;
		color: var(--text-muted);
		margin: 0;
	}

	.lines {
		display: flex;
		flex-direction: column;
	}

	.line {
		display: flex;
		gap: 4px;
		padding: 1px 4px;
		background: none;
		border: none;
		border-left: 2px solid transparent;
		color: var(--text);
		cursor: pointer;
		font-family: inherit;
		font-size: var(--font-size-base);
		text-align: left;

		&:hover { background: var(--hover-bg); }
		&.active {
			background: rgba(137, 180, 250, 0.1);
			border-left-color: var(--accent-blue);
		}
	}

	.pc {
		color: var(--text-dim);
		min-width: 16px;
		text-align: right;
		font-size: var(--font-size-base);
	}

	.text {
		color: var(--text-secondary);
		white-space: pre;
	}

	.active .text { color: var(--text); }

	.vreg-list {
		display: flex;
		flex-direction: column;
		gap: 1px;
	}

	.vreg-row {
		display: flex;
		align-items: center;
		gap: 6px;
		padding: 1px 6px;
		border-radius: 3px;
		font-size: var(--font-size-base);

		&.vreg-active {
			background: var(--highlight-bg);
		}
	}

	.vreg-width { color: var(--text-dim); font-size: var(--font-size-sm); }
	.vreg-target { color: var(--text-dim); font-size: var(--font-size-sm); }
</style>
