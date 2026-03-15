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
		padding: 0;
		cursor: pointer;
		font-family: inherit;
		font-size: inherit;

		&:hover {
			text-decoration: underline;
		}

		&.active {
			background: var(--highlight-bg);
			border-radius: 2px;
			padding: 0 2px;
		}
	}
</style>
