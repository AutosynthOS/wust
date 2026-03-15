<script lang="ts">
	import { app, toggleVreg } from '$lib/state.svelte';

	let { id, width, target }: {
		id: string;
		width?: string;
		target?: string | null;
	} = $props();

	const active = $derived(app.highlightedVreg === id);
	const title = $derived(
		[id, width, target ? `→${target}` : null].filter(Boolean).join(' ')
	);
</script>

<button
	class="vreg"
	class:active
	{title}
	onclick={(e) => { e.stopPropagation(); toggleVreg(id); }}
>{id}</button>

<style>
	.vreg {
		background: none;
		border: none;
		color: var(--accent-vreg);
		padding: 0 2px;
		cursor: pointer;
		font-family: inherit;
		font-size: inherit;
		border-radius: 2px;

		&:hover {
			text-decoration: underline;
		}

		&.active {
			background: var(--highlight-bg);
		}
	}
</style>
