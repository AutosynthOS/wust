<script lang="ts">
	let { id }: { id: string } = $props();
</script>

<span class="preg">{id}</span>

<style>
	.preg {
		color: var(--accent-blue);
	}
</style>
