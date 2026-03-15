<script lang="ts">
	import type { AsmEvent } from '$lib/types';

	let { asm }: { asm: AsmEvent } = $props();

	interface Token {
		text: string;
		kind: 'mnemonic' | 'reg' | 'imm' | 'mem' | 'label' | 'punct';
	}

	function parse(text: string): Token[] {
		const tokens: Token[] = [];
		const parts = text.split(/(\s+|,\s*|\[|\]|#)/);
		let first = true;

		for (const part of parts) {
			if (!part || part.match(/^[\s,]+$/)) {
				tokens.push({ text: part, kind: 'punct' });
				continue;
			}
			if (part === '[' || part === ']') {
				tokens.push({ text: part, kind: 'mem' });
				continue;
			}
			if (part === '#') {
				tokens.push({ text: part, kind: 'imm' });
				continue;
			}
			if (first && part.match(/^[a-z]/)) {
				tokens.push({ text: part, kind: 'mnemonic' });
				first = false;
				continue;
			}
			first = false;

			if (part.match(/^[xw]\d+$/) || part === 'sp') {
				tokens.push({ text: part, kind: 'reg' });
			} else if (part.match(/^-?\d+$/)) {
				tokens.push({ text: part, kind: 'imm' });
			} else if (part.match(/^[A-Z]/) || part === 'fib') {
				tokens.push({ text: part, kind: 'label' });
			} else {
				tokens.push({ text: part, kind: 'punct' });
			}
		}
		return tokens;
	}

	function formatAddr(a: number): string {
		return a.toString(16).padStart(4, '0');
	}

	function originLabel(o: string): string {
		return o === 'lower' ? 'lo' : o === 'regalloc' ? 'ra' : 'fu';
	}

	const tokens = parse(asm.text);
</script>

<div class="line">
	<span class="addr">{formatAddr(asm.addr)}</span>
	<span class="origin {asm.origin}">{originLabel(asm.origin)}</span>
	<code class="inst">
		{#each tokens as tok}
			<span class={tok.kind}>{tok.text}</span>
		{/each}
	</code>
</div>

<style>
	.line {
		display: flex;
		align-items: center;
		gap: 4px;
		height: var(--row-h);
	}

	.addr {
		color: var(--text-faint);
		font-size: var(--font-size-xs);
		min-width: 28px;
	}

	.origin {
		font-size: 7px;
		padding: 0 3px;
		border-radius: 2px;
		color: var(--bg-base);
		font-weight: bold;

		&.lower { background: var(--accent-blue); }
		&.regalloc { background: var(--accent-yellow); }
		&.fuse { background: var(--accent-purple); }
	}

	.inst {
		font-size: var(--font-size-base);
	}

	.mnemonic { color: var(--text-muted); }
	.reg { color: var(--accent-blue); }
	.imm { color: var(--accent-yellow); }
	.mem { color: var(--accent-teal); }
	.label { color: var(--accent-red); font-style: italic; }
	.punct { color: var(--text-dim); }
</style>
