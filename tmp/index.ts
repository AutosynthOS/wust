import type { Operation, TimeNode } from "./types";
import { w, x, oref, vref } from "./types";
import { C, fmtOp, printTimeline } from "./format";
import { buildTimeline, assignOrder, findHead, propagateSlots, checkScope, checkContracts } from "./timeline";
import { foldImmediates, markReachable, sweep } from "./transforms";
import { applyPaths } from "./pathfinder";

// --- Operation registry ---

const ops = new Map<string, Operation>();
function op(o: Operation) { ops.set(o.id, o); }

// --- Build fib graph ---

// Params
op({ id: "o0",  op: "param", operands: [], defines: [{ vreg: "v0", preg: w(0) }] });
op({ id: "o1",  op: "param", operands: [], defines: [{ vreg: "v1", preg: x(30) }] });

// Constants
op({ id: "o2",  op: "const", operands: [], defines: [{ vreg: "c#1", const: 1 }] });
op({ id: "o3",  op: "const", operands: [], defines: [{ vreg: "c#2", const: 2 }] });

// set_slot: v0 → local[0]
op({ id: "o4",  op: { kind: "set_slot", base: x(29), offset: 0 },
  operands: [oref("o0"), vref("v0")], defines: [] });

// set_slot: LR → fibre[0]
op({ id: "o5",  op: { kind: "set_slot", base: x(31), offset: 0 },
  operands: [oref("o1"), vref("v1")], defines: [] });

// set_slot: v0 → operand (for cmp)
op({ id: "o6",  op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o4"), vref("v0")], defines: [] });

// clear_slot: pop v0
op({ id: "o7",  op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o6"), vref("v0")], defines: [] });

// set_slot: c#1 → operand
op({ id: "o8",  op: { kind: "set_slot", base: x(29), offset: 28 },
  operands: [oref("o2"), vref("c#1")], defines: [] });

// clear_slot: pop c#1
op({ id: "o9",  op: { kind: "clear_slot", base: x(29), offset: 28 },
  operands: [oref("o8"), vref("c#1")], defines: [] });

// cmp_les(v0, c#1) → v4
op({ id: "o10", op: { alu: "cmp_les" }, operands: [oref("o7"), oref("o9")],
  defines: [{ vreg: "v4" }] });

// set_slot: v4 → operand
op({ id: "o11", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o10"), vref("v4")], defines: [] });

// clear_slot: pop v4
op({ id: "o12", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o11"), vref("v4")], defines: [] });

// brif(v4)
op({ id: "o13", op: "brif", operands: [oref("o12")], defines: [] });

// --- Case(0): return v0 ---
op({ id: "o14", op: "return", operands: [oref("o7")], defines: [], effect: "o13" });

// --- Case(1) ---

// sub(v0, c#1) → v5
op({ id: "o15", op: { alu: "sub" }, operands: [oref("o7"), oref("o9")],
  defines: [{ vreg: "v5" }] });

// set_slot: v5 → operand
op({ id: "o16", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o15"), vref("v5")], defines: [] });

// clear_slot: pop v5
op({ id: "o17", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o16"), vref("v5")], defines: [] });

// call fib(v5) → v6
op({ id: "o18", op: "call", operands: [oref("o17")],
  defines: [{ vreg: "v6", preg: w(0) }], effect: "o13" });

// push call result to operand stack
op({ id: "o19", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o18"), vref("v6")], defines: [] });

// pop from operand stack (local.set $a consumes it)
op({ id: "o20", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o19"), vref("v6")], defines: [] });

// local.set $a → store to local[1] at [x29+4]
op({ id: "o20a", op: { kind: "set_slot", base: x(29), offset: 4 },
  operands: [oref("o20"), vref("v6")], defines: [] });

// local.get $a → push from local[1] to operand stack [x29+24]
op({ id: "o21", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o20a"), vref("v6")], defines: [] });

// pop from operand stack (for add)
op({ id: "o22", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o21"), vref("v6")], defines: [] });

// set_slot: c#2 → operand
op({ id: "o23", op: { kind: "set_slot", base: x(29), offset: 28 },
  operands: [oref("o3"), vref("c#2")], defines: [] });

// clear_slot: pop c#2
op({ id: "o24", op: { kind: "clear_slot", base: x(29), offset: 28 },
  operands: [oref("o23"), vref("c#2")], defines: [] });

// sub(v0, c#2) → v7
op({ id: "o25", op: { alu: "sub" }, operands: [oref("o7"), oref("o24")],
  defines: [{ vreg: "v7" }] });

// set_slot: v7 → operand
op({ id: "o26", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o25"), vref("v7")], defines: [] });

// clear_slot: pop v7
op({ id: "o27", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o26"), vref("v7")], defines: [] });

// call fib(v7) → v8
op({ id: "o28", op: "call", operands: [oref("o27")],
  defines: [{ vreg: "v8", preg: w(0) }], effect: "o18" });

// push call result to operand stack
op({ id: "o29", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o28"), vref("v8")], defines: [] });

// pop from operand stack (local.set $b consumes it)
op({ id: "o30", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o29"), vref("v8")], defines: [] });

// local.set $b → store to local[2] at [x29+8]
op({ id: "o30a", op: { kind: "set_slot", base: x(29), offset: 8 },
  operands: [oref("o30"), vref("v8")], defines: [] });

// local.get $b → push from local[2] to operand stack [x29+28]
op({ id: "o31", op: { kind: "set_slot", base: x(29), offset: 28 },
  operands: [oref("o30a"), vref("v8")], defines: [] });

// pop from operand stack (for add)
op({ id: "o32", op: { kind: "clear_slot", base: x(29), offset: 28 },
  operands: [oref("o31"), vref("v8")], defines: [] });

// add(v6, v8) → v9
op({ id: "o33", op: { alu: "add" }, operands: [oref("o22"), oref("o32")],
  defines: [{ vreg: "v9" }] });

// set_slot: v9 → operand
op({ id: "o34", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o33"), vref("v9")], defines: [] });

// clear_slot: pop v9 from operand stack (for return)
op({ id: "o34a", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o34"), vref("v9")], defines: [] });

// return v9
op({ id: "o35", op: "return", operands: [oref("o34a")], defines: [], effect: "o28" });

// --- Roots ---
const roots = ["o14", "o35"];

// --- Shuffle ---
const entries = [...ops.entries()];
for (let i = entries.length - 1; i > 0; i--) {
  const j = Math.floor(Math.random() * (i + 1));
  [entries[i], entries[j]] = [entries[j], entries[i]];
}
ops.clear();
for (const [k, v] of entries) ops.set(k, v);

// --- Build timeline ---
const timeVisited = new Map<string, TimeNode>();
let tail: TimeNode | undefined;
for (const rootId of roots) {
  tail = buildTimeline(rootId, ops, timeVisited, tail);
}
const head = findHead(tail!);
assignOrder(head);
propagateSlots(head, ops);

printTimeline("Timeline", head, ops);

// --- Fold + sweep ---
foldImmediates(head, ops);
const live = markReachable(roots, ops);
const cleanHead = sweep(head, live);
assignOrder(cleanHead);
propagateSlots(cleanHead, ops);

printTimeline("After fold + sweep", cleanHead, ops);

// --- Noop fuser (disabled — pathfinder handles it) ---
// const fusedHead = fuseNoopPairs(cleanHead);
const fusedHead = cleanHead;
assignOrder(fusedHead);
propagateSlots(fusedHead, ops);

printTimeline("After fuse no-ops", fusedHead, ops);

// --- Scope + contract check ---
checkScope(fusedHead, ops);
checkContracts(fusedHead);

// --- Pathfinder ---
let pass = 0;
let head2 = fusedHead;
while (true) {
  pass++;
  console.log(`\n${C.bold}=== Pathfinder (pass ${pass}) ===${C.reset}`);
  const applied = applyPaths(head2, ops);
  console.log(`  ${applied} change(s) applied`);
  if (applied === 0) break;

  head2 = findHead(head2);
  assignOrder(head2);
  propagateSlots(head2, ops);
}

printTimeline(`After pathfinder (${pass} passes)`, head2, ops);
checkScope(head2, ops);
checkContracts(head2);

// --- Post-pathfinder sweep ---
const live2 = markReachable(roots, ops);
let deadCount = 0;
{
  let c: TimeNode | undefined = head2;
  while (c) {
    if (!live2.has(c.op.id)) {
      console.log(`  ${C.dim}DEAD${C.reset} [${c.order}] ${C.dim}${c.op.id}${C.reset}: ${fmtOp(c.op, ops)}`);
      deadCount++;
    }
    c = c.next;
  }
}
console.log(`\n${C.bold}=== Post-pathfinder sweep ===${C.reset}`);
console.log(`  ${deadCount} dead node(s)`);
if (deadCount > 0) {
  head2 = sweep(head2, live2);
  assignOrder(head2);
  propagateSlots(head2, ops);
  printTimeline("After sweep", head2, ops);
  checkScope(head2, ops);
  checkContracts(head2);
}
