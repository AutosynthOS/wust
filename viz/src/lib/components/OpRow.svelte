<script lang="ts">
	import type { OpView } from '$lib/types';
	import { app, toggleVreg, selectOp } from '$lib/state.svelte';
	import { vregsRead, vregsDefined } from '$lib/assemble';
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

	function originLabel(o: string): string {
		return o === 'lower' ? 'lo' : o === 'regalloc' ? 'ra' : 'fu';
	}

	function formatAddr(a: number): string {
		return a.toString(16).padStart(4, '0');
	}

	interface AsmToken {
		text: string;
		kind: 'mnemonic' | 'reg' | 'imm' | 'mem' | 'label' | 'punct';
	}

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
			if (part.match(/^[xw]\d+$/) || part === 'sp') tokens.push({ text: part, kind: 'reg' });
			else if (part.match(/^-?\d+$/)) tokens.push({ text: part, kind: 'imm' });
			else if (part.match(/^[A-Z]/) || part === 'fib') tokens.push({ text: part, kind: 'label' });
			else tokens.push({ text: part, kind: 'punct' });
		}
		return tokens;
	}
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
	<!-- Op text -->
	<div class="col-op">
		{#each op.text.split(/(v\d+)/) as part}
			{#if part.match(/^v\d+$/)}
				<VReg id={part} />
			{:else}
				<span class="op-text">{part}</span>
			{/if}
		{/each}
	</div>

	<!-- ASM: addr | origin + instruction -->
	<div class="col-asm">
		{#each op.asm as asm}
			<div class="asm-line">
				<span class="asm-addr">{formatAddr(asm.addr)}</span>
				<span class="asm-origin {asm.origin}">{originLabel(asm.origin)}</span>
				<code class="asm-inst">
					{#each parseAsm(asm.text) as tok}
						<span class="asm-{tok.kind}">{tok.text}</span>
					{/each}
				</code>
			</div>
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

	.col-op {
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

	.col-asm {
		min-width: 220px;
		display: flex;
		flex-direction: column;
		justify-content: center;
		padding: 0 4px;
	}

	.asm-line {
		display: flex;
		align-items: center;
		gap: 4px;
		height: var(--row-h);
	}

	.asm-addr {
		color: var(--text-muted);
		font-size: var(--font-size-base);
		min-width: 30px;
		text-align: right;
	}

	.asm-origin {
		font-size: 7px;
		padding: 0 3px;
		border-radius: 2px;
		color: var(--bg-base);
		font-weight: bold;

		&.lower { background: var(--accent-blue); }
		&.regalloc { background: var(--accent-yellow); }
		&.fuse { background: var(--accent-purple); }
	}

	.asm-inst {
		font-size: var(--font-size-base);
	}

	.asm-mnemonic { color: var(--text-muted); }
	.asm-reg { color: var(--accent-blue); }
	.asm-imm { color: var(--accent-yellow); }
	.asm-mem { color: var(--accent-teal); }
	.asm-label { color: var(--accent-red); font-style: italic; }
	.asm-punct { color: var(--text-dim); }
</style>
