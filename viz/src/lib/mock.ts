import type { FunctionData } from './types';

export const fibData: FunctionData = {
	name: 'fib',
	signature: 'fn fib(n: i32) -> i32',
	pregColors: {
		'x0': '#e06c75', 'w0': '#e06c75', 'x1': '#e5c07b', 'w1': '#e5c07b',
		'x2': '#61afef', 'w2': '#61afef', 'x28': '#c678dd', 'x29': '#56b6c2', 'x30': '#98c379', 'sp': '#d19a66',
	},
	vregDefs: [
		{ vreg: 'v0', width: 'i32', target: 'x0' }, { vreg: 'v1', width: 'i32', target: null },
		{ vreg: 'v2', width: 'i32', target: null }, { vreg: 'v3', width: 'i64', target: 'sp' },
		{ vreg: 'v5', width: 'i64', target: 'x30' }, { vreg: 'v6', width: 'i32', target: null },
		{ vreg: 'v7', width: 'i32', target: null }, { vreg: 'v9', width: 'i32', target: null },
		{ vreg: 'v14', width: 'i32', target: null }, { vreg: 'v16', width: 'i32', target: null },
		{ vreg: 'v26', width: 'i32', target: null }, { vreg: 'v30', width: 'i32', target: null },
	],
	watSource: [
		{ line: 0, text: 'local.get $n', wasmPcs: [0], indent: 0 },
		{ line: 1, text: 'i32.const 1', wasmPcs: [1], indent: 0 },
		{ line: 2, text: 'i32.le_s', wasmPcs: [2], indent: 0 },
		{ line: 3, text: 'if', wasmPcs: [3], indent: 0 },
		{ line: 4, text: 'local.get $n', wasmPcs: [4], indent: 1 },
		{ line: 5, text: 'return', wasmPcs: [5], indent: 1 },
		{ line: 6, text: 'end', wasmPcs: [6], indent: 0 },
		{ line: 7, text: 'local.get $n', wasmPcs: [7], indent: 0 },
		{ line: 8, text: 'i32.const 1', wasmPcs: [8], indent: 0 },
		{ line: 9, text: 'i32.sub', wasmPcs: [9], indent: 0 },
		{ line: 10, text: 'call $fib', wasmPcs: [10], indent: 0 },
		{ line: 11, text: 'local.set $a', wasmPcs: [11], indent: 0 },
		{ line: 12, text: 'local.get $n', wasmPcs: [12], indent: 0 },
		{ line: 13, text: 'i32.const 2', wasmPcs: [13], indent: 0 },
		{ line: 14, text: 'i32.sub', wasmPcs: [14], indent: 0 },
		{ line: 15, text: 'call $fib', wasmPcs: [15], indent: 0 },
		{ line: 16, text: 'local.set $b', wasmPcs: [16], indent: 0 },
		{ line: 17, text: 'local.get $a', wasmPcs: [17], indent: 0 },
		{ line: 18, text: 'local.get $b', wasmPcs: [18], indent: 0 },
		{ line: 19, text: 'i32.add', wasmPcs: [19], indent: 0 },
		{ line: 20, text: 'end', wasmPcs: [20], indent: 0 },
	],
	blocks: [
		{
			id: 'E0', blockIdx: 0, label: 'entry', successors: ['U0'], predecessors: [],
			groups: [
				{ wasmPc: null, label: 'param 0', ops: [
					{ id: '0.0', text: 'v0 = PReg(x0)', kind: 'define', vregsRead: [], vregsDefined: ['v0'], stackChanges: { locals: [{ action: 'push', vreg: 'v0' }], ops: [], fibre: [] }, bindings: [{ vreg: 'v0', preg: 'x0', loc: 'reg' }] },
				]},
				{ wasmPc: null, label: 'local 1', ops: [
					{ id: '0.1', text: 'v1 = #0', kind: 'define', vregsRead: [], vregsDefined: ['v1'], stackChanges: { locals: [{ action: 'push', vreg: 'v1' }], ops: [], fibre: [] }, bindings: [{ vreg: 'v1', preg: null, loc: 'const' }] },
				]},
				{ wasmPc: null, label: 'local 2', ops: [
					{ id: '0.2', text: 'v2 = #0', kind: 'define', vregsRead: [], vregsDefined: ['v2'], stackChanges: { locals: [{ action: 'push', vreg: 'v2' }], ops: [], fibre: [] }, bindings: [{ vreg: 'v2', preg: null, loc: 'const' }] },
				]},
				{ wasmPc: null, label: 'prologue', ops: [
					{ id: '0.3', text: 'v3 = sub sp, #16', kind: 'ir', vregsRead: ['v3'], vregsDefined: ['v3'], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '0.4', text: 'v5 = PReg(x30)', kind: 'define', vregsRead: [], vregsDefined: ['v5'], stackChanges: { locals: [], ops: [], fibre: [{ action: 'push', vreg: 'v5' }] }, bindings: [{ vreg: 'v5', preg: 'x30', loc: 'reg' }] },
				]},
			],
			asmEvents: [
				{ id: '0.3.0', parentOp: '0.3', addr: 0x0000, asm: 'sub sp, sp, #16', origin: 'lower' },
			],
		},
		{
			id: 'U0', blockIdx: 1, label: 'compare n ≤ 1', successors: ['U4', 'U6'], predecessors: ['E0'],
			groups: [
				{ wasmPc: 0, label: 'local.get 0', ops: [
					{ id: '1.0', text: 'push v0', kind: 'setslot', vregsRead: ['v0'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v0' }], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 1, label: 'i32.const 1', ops: [
					{ id: '1.1', text: 'v6 = #1', kind: 'define', vregsRead: [], vregsDefined: ['v6'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v6' }], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 2, label: 'i32.le_s', ops: [
					{ id: '1.2a', text: 'pop v6', kind: 'clearslot', vregsRead: ['v6'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v6' }], fibre: [] }, bindings: [] },
					{ id: '1.2b', text: 'pop v0', kind: 'clearslot', vregsRead: ['v0'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v0' }], fibre: [] }, bindings: [] },
					{ id: '1.2c', text: 'v7 = le_s v0, v6:#1', kind: 'ir', vregsRead: ['v0', 'v6'], vregsDefined: ['v7'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v7' }], fibre: [] }, bindings: [{ vreg: 'v7', preg: 'w1', loc: 'reg' }] },
				]},
				{ wasmPc: 3, label: 'if', ops: [
					{ id: '1.3a', text: 'pop v7', kind: 'clearslot', vregsRead: ['v7'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v7' }], fibre: [] }, bindings: [] },
					{ id: '1.3b', text: 'br_if v7 → U4 / U6', kind: 'branch', vregsRead: ['v7'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '1.2c.0', parentOp: '1.2c', addr: 0x0004, asm: 'subs w1, w0, #1', origin: 'fuse' },
				{ id: '1.3b.0', parentOp: '1.3b', addr: 0x0008, asm: 'b.gt U6', origin: 'fuse' },
			],
		},
		{
			id: 'U4', blockIdx: 2, label: 'return n', successors: [], predecessors: ['U0'],
			groups: [
				{ wasmPc: 4, label: 'local.get 0', ops: [
					{ id: '2.0', text: 'push v0', kind: 'setslot', vregsRead: ['v0'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v0' }], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 5, label: 'return', ops: [
					{ id: '2.1a', text: 'pop v0 → x0', kind: 'resolve', vregsRead: ['v0'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v0' }], fibre: [] }, bindings: [] },
					{ id: '2.1b', text: 'pop lr → x30', kind: 'resolve', vregsRead: ['v5'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [{ action: 'pop', vreg: 'v5' }] }, bindings: [] },
					{ id: '2.1c', text: 'add sp, sp, #16', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '2.1d', text: 'ret', kind: 'ret', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '2.1c.0', parentOp: '2.1c', addr: 0x000c, asm: 'add sp, sp, #16', origin: 'lower' },
				{ id: '2.1d.0', parentOp: '2.1d', addr: 0x0010, asm: 'ret', origin: 'lower' },
			],
		},
		{
			id: 'U6', blockIdx: 3, label: 'fib(n-1)', successors: ['G0', 'U10'], predecessors: ['U0'],
			groups: [
				{ wasmPc: 7, label: 'local.get 0', ops: [
					{ id: '3.0', text: 'push v0', kind: 'setslot', vregsRead: ['v0'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v0' }], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 9, label: 'i32.sub', ops: [
					{ id: '3.1a', text: 'pop v0', kind: 'clearslot', vregsRead: ['v0'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v0' }], fibre: [] }, bindings: [] },
					{ id: '3.1b', text: 'v9 = sub v0, #1', kind: 'ir', vregsRead: ['v0'], vregsDefined: ['v9'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v9' }], fibre: [] }, bindings: [{ vreg: 'v0', preg: null, loc: 'mem' }] },
				]},
				{ wasmPc: 10, label: 'call $fib', ops: [
					{ id: '3.2a', text: 'pop v9 → x0', kind: 'resolve', vregsRead: ['v9'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v9' }], fibre: [] }, bindings: [] },
					{ id: '3.2b', text: 'clobber locals', kind: 'clobber', vregsRead: ['v0', 'v1', 'v2'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '3.2c', text: 'clobber fibre', kind: 'clobber', vregsRead: ['v5'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '3.2d', text: 'advance g.lb +24', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '3.2e', text: 'call fib', kind: 'call', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '3.2f', text: 'restore g.lb -24', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '3.2g', text: 'v14 = result x0', kind: 'define', vregsRead: [], vregsDefined: ['v14'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v14' }], fibre: [] }, bindings: [{ vreg: 'v14', preg: 'x0', loc: 'reg' }] },
					{ id: '3.2h', text: 'fuel: subs x28, #13', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '3.2i', text: 'b.gt G0', kind: 'branch', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '3.1b.0', parentOp: '3.1b', addr: 0x0014, asm: 'str w0, [x29]', origin: 'regalloc' },
				{ id: '3.1b.1', parentOp: '3.1b', addr: 0x0018, asm: 'sub w0, w0, #1', origin: 'lower' },
				{ id: '3.2c.0', parentOp: '3.2c', addr: 0x001c, asm: 'str x30, [sp]', origin: 'regalloc' },
				{ id: '3.2d.0', parentOp: '3.2d', addr: 0x0020, asm: 'add x29, x29, #24', origin: 'lower' },
				{ id: '3.2e.0', parentOp: '3.2e', addr: 0x0024, asm: 'bl fib', origin: 'lower' },
				{ id: '3.2f.0', parentOp: '3.2f', addr: 0x0028, asm: 'sub x29, x29, #24', origin: 'lower' },
				{ id: '3.2h.0', parentOp: '3.2h', addr: 0x002c, asm: 'subs x28, x28, #13', origin: 'fuse' },
				{ id: '3.2i.0', parentOp: '3.2i', addr: 0x0030, asm: 'b.gt G0', origin: 'fuse' },
			],
		},
		{
			id: 'G0', blockIdx: 4, label: 'suspend', successors: [], predecessors: ['U6'],
			groups: [
				{ wasmPc: null, label: 'suspend', ops: [
					{ id: '4.0', text: 'ret (no epilogue)', kind: 'ret', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '4.0.0', parentOp: '4.0', addr: 0x0034, asm: 'ret', origin: 'lower' },
			],
		},
		{
			id: 'U10', blockIdx: 5, label: 'fib(n-2)', successors: ['G1', 'U15'], predecessors: ['U6'],
			groups: [
				{ wasmPc: 11, label: 'local.set $a', ops: [
					{ id: '5.0a', text: 'pop v14', kind: 'clearslot', vregsRead: ['v14'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v14' }], fibre: [] }, bindings: [] },
					{ id: '5.0b', text: 'locals[1] = v16', kind: 'setslot', vregsRead: ['v16'], vregsDefined: [], stackChanges: { locals: [{ action: 'set', vreg: 'v16', index: 1 }], ops: [], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 14, label: 'i32.sub', ops: [
					{ id: '5.1', text: 'v21 = sub v0, #2', kind: 'ir', vregsRead: ['v0'], vregsDefined: ['v21'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v21' }], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 15, label: 'call $fib', ops: [
					{ id: '5.2a', text: 'pop v21 → x0', kind: 'resolve', vregsRead: ['v21'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v21' }], fibre: [] }, bindings: [] },
					{ id: '5.2b', text: 'clobber all', kind: 'clobber', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '5.2c', text: 'advance g.lb +24', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '5.2d', text: 'call fib', kind: 'call', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '5.2e', text: 'restore g.lb -24', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '5.2f', text: 'v26 = result x0', kind: 'define', vregsRead: [], vregsDefined: ['v26'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v26' }], fibre: [] }, bindings: [{ vreg: 'v26', preg: 'x0', loc: 'reg' }] },
					{ id: '5.2g', text: 'fuel: subs x28, #8', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '5.2h', text: 'b.gt G1', kind: 'branch', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '5.1.0', parentOp: '5.1', addr: 0x0038, asm: 'str w0, [x29, #4]', origin: 'regalloc' },
				{ id: '5.1.1', parentOp: '5.1', addr: 0x003c, asm: 'ldr w0, [x29]', origin: 'regalloc' },
				{ id: '5.1.2', parentOp: '5.1', addr: 0x0040, asm: 'sub w0, w0, #2', origin: 'lower' },
				{ id: '5.2c.0', parentOp: '5.2c', addr: 0x0044, asm: 'add x29, x29, #24', origin: 'lower' },
				{ id: '5.2d.0', parentOp: '5.2d', addr: 0x0048, asm: 'bl fib', origin: 'lower' },
				{ id: '5.2e.0', parentOp: '5.2e', addr: 0x004c, asm: 'sub x29, x29, #24', origin: 'lower' },
				{ id: '5.2g.0', parentOp: '5.2g', addr: 0x0050, asm: 'subs x28, x28, #8', origin: 'fuse' },
				{ id: '5.2h.0', parentOp: '5.2h', addr: 0x0054, asm: 'b.gt G1', origin: 'fuse' },
			],
		},
		{
			id: 'G1', blockIdx: 6, label: 'suspend', successors: [], predecessors: ['U10'],
			groups: [
				{ wasmPc: null, label: 'suspend', ops: [
					{ id: '6.0', text: 'ret (no epilogue)', kind: 'ret', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '6.0.0', parentOp: '6.0', addr: 0x0058, asm: 'ret', origin: 'lower' },
			],
		},
		{
			id: 'U15', blockIdx: 7, label: 'a + b, return', successors: [], predecessors: ['U10'],
			groups: [
				{ wasmPc: 16, label: 'local.set $b', ops: [
					{ id: '7.0a', text: 'pop v26', kind: 'clearslot', vregsRead: ['v26'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v26' }], fibre: [] }, bindings: [] },
					{ id: '7.0b', text: 'locals[2] = v26', kind: 'setslot', vregsRead: ['v26'], vregsDefined: [], stackChanges: { locals: [{ action: 'set', vreg: 'v26', index: 2 }], ops: [], fibre: [] }, bindings: [] },
				]},
				{ wasmPc: 19, label: 'i32.add', ops: [
					{ id: '7.1a', text: 'pop v26', kind: 'clearslot', vregsRead: ['v26'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '7.1b', text: 'pop v16', kind: 'clearslot', vregsRead: ['v16'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '7.1c', text: 'v30 = add v16, v26', kind: 'ir', vregsRead: ['v16', 'v26'], vregsDefined: ['v30'], stackChanges: { locals: [], ops: [{ action: 'push', vreg: 'v30' }], fibre: [] }, bindings: [{ vreg: 'v30', preg: 'x0', loc: 'reg' }] },
				]},
				{ wasmPc: 20, label: 'end (return)', ops: [
					{ id: '7.2a', text: 'pop v30 → x0', kind: 'resolve', vregsRead: ['v30'], vregsDefined: [], stackChanges: { locals: [], ops: [{ action: 'pop', vreg: 'v30' }], fibre: [] }, bindings: [] },
					{ id: '7.2b', text: 'pop lr → x30', kind: 'resolve', vregsRead: ['v5'], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [{ action: 'pop', vreg: 'v5' }] }, bindings: [] },
					{ id: '7.2c', text: 'add sp, sp, #16', kind: 'ir', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
					{ id: '7.2d', text: 'ret', kind: 'ret', vregsRead: [], vregsDefined: [], stackChanges: { locals: [], ops: [], fibre: [] }, bindings: [] },
				]},
			],
			asmEvents: [
				{ id: '7.1c.0', parentOp: '7.1c', addr: 0x005c, asm: 'ldr w2, [x29, #4]', origin: 'regalloc' },
				{ id: '7.1c.1', parentOp: '7.1c', addr: 0x0060, asm: 'add w0, w2, w0', origin: 'lower' },
				{ id: '7.2b.0', parentOp: '7.2b', addr: 0x0064, asm: 'ldr x30, [sp]', origin: 'regalloc' },
				{ id: '7.2c.0', parentOp: '7.2c', addr: 0x0068, asm: 'add sp, sp, #16', origin: 'lower' },
				{ id: '7.2d.0', parentOp: '7.2d', addr: 0x006c, asm: 'ret', origin: 'lower' },
			],
		},
	],
};
