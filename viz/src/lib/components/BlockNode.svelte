<script lang="ts">
	import type { BlockView, FunctionTrace, OpView, AsmEvent } from '$lib/types';
	import { app, selectOp, toggleVreg } from '$lib/state.svelte';
	import { vregsRead, vregsDefined } from '$lib/assemble';
	import VReg from './VReg.svelte';

	let { block, func }: { block: BlockView; func: FunctionTrace } = $props();

	const ROW_H = 20;

	// Flatten into grid rows: each row = one op (or one asm sub-line)
	interface GridRow {
		op: OpView;
		asm: AsmEvent | null;
		/** Is this the first row for this op? */
		opStart: boolean;
		/** Total rows this op spans (only set on opStart) */
		opSpan: number;
		/** Group info — set on first row of group */
		groupStart: boolean;
		groupSpan: number;
		groupPc: number | null;
		groupLabel: string;
		/** Is this the first group? (no top border) */
		firstGroup: boolean;
	}

	function buildRows(): GridRow[] {
		const rows: GridRow[] = [];
		let isFirst = true;

		for (const group of block.groups) {
			let groupRowCount = 0;
			const groupStartIdx = rows.length;

			for (const op of group.ops) {
				const asmList = op.asm;
				const opRowCount = Math.max(1, asmList.length);
				groupRowCount += opRowCount;

				for (let i = 0; i < opRowCount; i++) {
					rows.push({
						op,
						asm: asmList[i] ?? null,
						opStart: i === 0,
						opSpan: opRowCount,
						groupStart: false,
						groupSpan: 0,
						groupPc: group.pc,
						groupLabel: group.label,
						firstGroup: isFirst,
					});
				}
			}

			// Patch group start
			if (groupStartIdx < rows.length) {
				rows[groupStartIdx].groupStart = true;
				rows[groupStartIdx].groupSpan = groupRowCount;
			}
			isFirst = false;
		}
		return rows;
	}

	const gridRows = buildRows();

	function opTouches(op: OpView, vreg: string): boolean {
		const r = vregsRead(op.event);
		const d = vregsDefined(op.event);
		return r.includes(vreg) || d.includes(vreg);
	}

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

<div class="header">
	<span class="block-id">{block.id}</span>
	{#if block.successors.length}
		<span class="successors">→ {block.successors.join(', ')}</span>
	{/if}
</div>

<div class="grid" style="grid-template-rows: repeat({gridRows.length}, {ROW_H}px);">
	{#each gridRows as row, ri}
		<!-- PC cell (spans group) -->
		{#if row.groupStart}
			<div
				class="cell cell-pc"
				class:group-border={!row.firstGroup}
				class:wat-match={app.highlightedWasmPcs.size > 0 && row.groupPc !== null && app.highlightedWasmPcs.has(row.groupPc)}
				style="grid-row: {ri + 1} / span {row.groupSpan}; grid-column: 1;"
			>
				{#if row.groupPc !== null}
					<span class="pc-text">{row.groupPc}</span>
				{/if}
			</div>
		{/if}

		<!-- Label cell (spans group) -->
		{#if row.groupStart}
			<div
				class="cell cell-label"
				class:group-border={!row.firstGroup}
				style="grid-row: {ri + 1} / span {row.groupSpan}; grid-column: 2;"
			>
				<span class="label-text">{row.groupLabel}</span>
			</div>
		{/if}

		<!-- Op cell (spans op) -->
		{#if row.opStart}
			<div
				class="cell cell-op"
				class:group-border={!row.firstGroup && row.groupStart}
				class:row-hov={app.hoveredOp === row.op.seq}
				class:row-sel={app.selectedOp === row.op.seq}
				class:row-hl={app.highlightedVreg !== null && opTouches(row.op, app.highlightedVreg)}
				class:row-dim={app.highlightedVreg !== null && !opTouches(row.op, app.highlightedVreg)}
				style="grid-row: {ri + 1} / span {row.opSpan}; grid-column: 3;"
				onmouseenter={() => app.hoveredOp = row.op.seq}
				onmouseleave={() => app.hoveredOp = null}
				onclick={(e) => { e.stopPropagation(); selectOp(row.op.seq); }}
			>
				{#each row.op.text.split(/(v\d+)/) as part}
					{#if part.match(/^v\d+$/)}
						<VReg id={part} />
					{:else}
						<span class="op-text">{part}</span>
					{/if}
				{/each}
			</div>
		{/if}

		<!-- Addr cell -->
		<div
			class="cell cell-addr"
			class:group-border={!row.firstGroup && row.groupStart}
			class:row-hov={app.hoveredOp === row.op.seq}
			style="grid-row: {ri + 1}; grid-column: 4;"
		>
			{#if row.asm}
				<span class="addr-text">{formatAddr(row.asm.addr)}</span>
			{/if}
		</div>

		<!-- Origin badge -->
		<div
			class="cell cell-origin"
			class:group-border={!row.firstGroup && row.groupStart}
			class:row-hov={app.hoveredOp === row.op.seq}
			style="grid-row: {ri + 1}; grid-column: 5;"
		>
			{#if row.asm}
				<span class="origin {row.asm.origin}">{originLabel(row.asm.origin)}</span>
			{/if}
		</div>

		<!-- ASM instruction -->
		<div
			class="cell cell-asm"
			class:group-border={!row.firstGroup && row.groupStart}
			class:row-hov={app.hoveredOp === row.op.seq}
			style="grid-row: {ri + 1}; grid-column: 6;"
		>
			{#if row.asm}
				<code>
					{#each parseAsm(row.asm.text) as tok}
						<span class="t-{tok.kind}">{tok.text}</span>
					{/each}
				</code>
			{/if}
		</div>
	{/each}
</div>

<style>
	.header {
		display: flex;
		align-items: center;
		gap: 8px;
		padding: 4px 8px;
		background: rgba(49, 50, 68, 0.3);
	}

	.block-id {
		font-weight: bold;
		font-size: var(--font-size-base);
		color: var(--text);
	}

	.successors {
		margin-left: auto;
		color: var(--text-faint);
		font-size: var(--font-size-xs);
	}

	.grid {
		display: grid;
		grid-template-columns:
			[pc] 30px
			[label] minmax(90px, 130px)
			[op] 1fr
			[addr] 36px
			[origin] 22px
			[asm] minmax(140px, 1fr);
	}

	.cell {
		display: flex;
		align-items: flex-start;
		padding: 2px 6px;
		min-height: var(--row-h);
		box-sizing: border-box;
		font-size: var(--font-size-base);

		&.group-border {
			border-top: 1px solid var(--border-subtle);
		}
	}

	/* Column-specific */
	.cell-pc {
		justify-content: center;
		border-right: 1px solid var(--border-subtle);

		&.wat-match {
			background: rgba(137, 180, 250, 0.08);
		}
	}

	.pc-text {
		color: var(--text-muted);
	}

	.cell-label {
		border-right: 1px solid var(--border-subtle);
		overflow: hidden;
	}

	.label-text {
		color: var(--text);
		font-size: var(--font-size-sm);
		white-space: nowrap;
		overflow: hidden;
		text-overflow: ellipsis;
	}

	.cell-op {
		cursor: pointer;
		border-right: 1px solid var(--border-subtle);
		overflow: hidden;

		&:hover { background: var(--hover-bg); }
		&.row-hov { background: rgba(137, 180, 250, 0.06); }
		&.row-sel { background: var(--selected-bg); }
		&.row-hl { background: var(--highlight-bg); }
		&.row-dim { opacity: var(--dim-opacity); }
	}

	.op-text {
		color: var(--text-secondary);
		white-space: pre;
	}

	.cell-addr {
		justify-content: flex-end;
		color: var(--text-muted);
	}

	.addr-text {
		font-variant-numeric: tabular-nums;
	}

	.cell-origin {
		justify-content: center;
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

	.cell-asm {
		overflow: hidden;

		code {
			white-space: nowrap;
		}
	}

	.t-mnemonic { color: var(--text-muted); }
	.t-reg { color: var(--accent-blue); }
	.t-imm { color: var(--accent-yellow); }
	.t-mem { color: var(--accent-teal); }
	.t-label { color: var(--accent-red); font-style: italic; }
	.t-punct { color: var(--text-dim); }

	/* Hover linking: when op is hovered, highlight addr/origin/asm too */
	.row-hov {
		background: rgba(137, 180, 250, 0.04);
	}
</style>
