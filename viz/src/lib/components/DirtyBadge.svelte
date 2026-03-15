<script lang="ts">
	let { dirty }: { dirty: boolean } = $props();
</script>

<span class="badge" class:dirty>{dirty ? 'dirty' : 'clean'}</span>

<style>
	.badge {
		font-size: var(--font-size-xxs);
		padding: 0 3px;
		border-radius: 2px;
		background: rgba(166, 227, 161, 0.15);
		color: var(--accent-green);

		&.dirty {
			background: rgba(243, 139, 168, 0.15);
			color: var(--accent-red);
		}
	}
</style>
