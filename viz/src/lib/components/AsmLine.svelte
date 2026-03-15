<script lang="ts">
	import { toggleVreg, formatAddr, originBadge } from '$lib/state.svelte';

	interface AsmToken { text: string; kind: 'mnemonic' | 'reg' | 'imm' | 'mem' | 'label' | 'punct'; preg?: string; }

	let { asm, addr, origin }: { asm: string; addr: number; origin: string } = $props();

	function parseAsm(text: string): AsmToken[] {
		const tokens: AsmToken[] = [];
		const parts = text.split(/(\s+|,\s*|\[|\]|#)/);
		let first = true;
		for (const part of parts) {
			if (!part || part.match(/^[\s,]+$/)) { tokens.push({ text: part, kind: 'punct' }); continue; }
			if (part === '[' || part === ']') { tokens.push({ text: part, kind: 'mem' }); continue; }
			if (part === '#') { tokens.push({ text: part, kind: 'imm' }); continue; }
			if (first && part.match(/^[a-z]/)) { tokens.push({ text: part, kind: 'mnemonic' }); first = false; continue; }
			first = false;
			if (part.match(/^[xw]\d+$/) || part === 'sp') {
				tokens.push({ text: part, kind: 'reg', preg: part });
			} else if (part.match(/^-?\d+$/)) {
				tokens.push({ text: part, kind: 'imm' });
			} else if (part.match(/^[A-Z]|^fib$/)) {
				tokens.push({ text: part, kind: 'label' });
			} else {
				tokens.push({ text: part, kind: 'punct' });
			}
		}
		return tokens;
	}

	const tokens = parseAsm(asm);
</script>

<div class="aln">
	<span class="aa">{formatAddr(addr)}</span>
	<span class="ab {origin}">{originBadge(origin)}</span>
	<code class="at">
		{#each tokens as tok}
			{#if tok.kind === 'reg'}
				<span class="asm-reg">{tok.text}</span>
			{:else if tok.kind === 'imm'}
				<span class="asm-imm">{tok.text}</span>
			{:else if tok.kind === 'mnemonic'}
				<span class="asm-mn">{tok.text}</span>
			{:else if tok.kind === 'mem'}
				<span class="asm-mem">{tok.text}</span>
			{:else if tok.kind === 'label'}
				<span class="asm-lbl">{tok.text}</span>
			{:else}{tok.text}{/if}
		{/each}
	</code>
</div>

<style>
	.aln { display:flex; align-items:center; gap:4px; height:18px; }
	.aa { color:#585b70; font-size:9px; min-width:28px; }
	.ab { font-size:7px; padding:0 3px; border-radius:2px; color:#1e1e2e; font-weight:bold; }
	.ab.lower { background:#61afef; } .ab.regalloc { background:#e5c07b; } .ab.fuse { background:#c678dd; }
	.at { font-size:11px; color:#cdd6f4; }
	.asm-mn { color:#7f849c; }
	.asm-reg { color:#89b4fa; }
	.asm-imm { color:#f9e2af; }
	.asm-mem { color:#94e2d5; }
	.asm-lbl { color:#f38ba8; font-style:italic; }
</style>
