<script lang="ts">
	import { app, toggleVreg } from '$lib/state.svelte';

	let { id, boundVreg }: { id: string; boundVreg?: string | null } = $props();

	function handleClick(e: MouseEvent) {
		e.stopPropagation();
		if (boundVreg) {
			toggleVreg(boundVreg);
		}
	}

	const isHighlighted = $derived(boundVreg !== undefined && boundVreg !== null && app.highlightedVreg === boundVreg);
</script>

{#if boundVreg}
	<button class="preg clickable" class:highlighted={isHighlighted} onclick={handleClick} title="{id} → {boundVreg}">{id}</button>
{:else}
	<span class="preg">{id}</span>
{/if}

<style>
	.preg {
		color: var(--accent-blue);
	}

	.clickable {
		background: none;
		border: none;
		color: var(--accent-blue);
		padding: 0 1px;
		cursor: pointer;
		font-family: inherit;
		font-size: inherit;
		border-radius: 2px;

		&:hover {
			text-decoration: underline;
		}

		&.highlighted {
			background: var(--highlight-bg);
		}
	}
</style>
