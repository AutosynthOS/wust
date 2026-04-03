import type { Operation, TimeNode } from "./types";
import { w, x, oref, vref } from "./types";
import { C, fmtOp, printTimeline } from "./format";
import { buildNodes, topoSortAndLink, assignOrder, computeAllStates, checkScope, checkContracts } from "./timeline";
import { foldImmediates, markReachable, sweep } from "./transforms";
import { applyPaths } from "./pathfinder";

// --- Operation registry ---

const ops = new Map<string, Operation>();
function op(o: Operation) { ops.set(o.id, o); }

// --- Build fib graph ---

op({ id: "o0",  op: "param", operands: [], defines: [{ vreg: "v0", preg: w(0) }] });
op({ id: "o1",  op: "param", operands: [], defines: [{ vreg: "v1", preg: x(30) }] });
op({ id: "o2",  op: "const", operands: [], defines: [{ vreg: "c#1", const: 1 }] });
op({ id: "o3",  op: "const", operands: [], defines: [{ vreg: "c#2", const: 2 }] });

op({ id: "o4",  op: { kind: "set_slot", base: x(29), offset: 0 },
  operands: [oref("o0"), vref("v0")], defines: [] });
op({ id: "o5",  op: { kind: "set_slot", base: x(31), offset: 0 },
  operands: [oref("o1"), vref("v1")], defines: [] });
op({ id: "o6",  op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o4"), vref("v0")], defines: [] });
op({ id: "o7",  op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o6"), vref("v0")], defines: [] });
op({ id: "o8",  op: { kind: "set_slot", base: x(29), offset: 28 },
  operands: [oref("o2"), vref("c#1")], defines: [] });
op({ id: "o9",  op: { kind: "clear_slot", base: x(29), offset: 28 },
  operands: [oref("o8"), vref("c#1")], defines: [] });

op({ id: "o10", op: { alu: "cmp_les" }, operands: [oref("o7"), oref("o9")],
  defines: [{ vreg: "v4" }] });
op({ id: "o11", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o10"), vref("v4")], defines: [] });
op({ id: "o12", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o11"), vref("v4")], defines: [] });
op({ id: "o13", op: "brif", operands: [oref("o12")], defines: [] });

// Case(0): return v0
op({ id: "o14", op: "return", operands: [oref("o7")], defines: [], effect: "o13" });

// Case(1): recursive
op({ id: "o15", op: { alu: "sub" }, operands: [oref("o7"), oref("o9")],
  defines: [{ vreg: "v5" }] });
op({ id: "o16", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o15"), vref("v5")], defines: [] });
op({ id: "o17", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o16"), vref("v5")], defines: [] });
op({ id: "o18", op: "call", operands: [oref("o17")],
  defines: [{ vreg: "v6", preg: w(0) }], effect: "o13" });

op({ id: "o19", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o18"), vref("v6")], defines: [] });
op({ id: "o20", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o19"), vref("v6")], defines: [] });
op({ id: "o20a", op: { kind: "set_slot", base: x(29), offset: 4 },
  operands: [oref("o20"), vref("v6")], defines: [] });
op({ id: "o21", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o20a"), vref("v6")], defines: [] });
op({ id: "o22", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o21"), vref("v6")], defines: [] });

op({ id: "o23", op: { kind: "set_slot", base: x(29), offset: 28 },
  operands: [oref("o3"), vref("c#2")], defines: [] });
op({ id: "o24", op: { kind: "clear_slot", base: x(29), offset: 28 },
  operands: [oref("o23"), vref("c#2")], defines: [] });

op({ id: "o25", op: { alu: "sub" }, operands: [oref("o7"), oref("o24")],
  defines: [{ vreg: "v7" }] });
op({ id: "o26", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o25"), vref("v7")], defines: [] });
op({ id: "o27", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o26"), vref("v7")], defines: [] });
op({ id: "o28", op: "call", operands: [oref("o27")],
  defines: [{ vreg: "v8", preg: w(0) }], effect: "o18" });

op({ id: "o29", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o28"), vref("v8")], defines: [] });
op({ id: "o30", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o29"), vref("v8")], defines: [] });
op({ id: "o30a", op: { kind: "set_slot", base: x(29), offset: 8 },
  operands: [oref("o30"), vref("v8")], defines: [] });
op({ id: "o31", op: { kind: "set_slot", base: x(29), offset: 28 },
  operands: [oref("o30a"), vref("v8")], defines: [] });
op({ id: "o32", op: { kind: "clear_slot", base: x(29), offset: 28 },
  operands: [oref("o31"), vref("v8")], defines: [] });

op({ id: "o33", op: { alu: "add" }, operands: [oref("o22"), oref("o32")],
  defines: [{ vreg: "v9" }] });
op({ id: "o34", op: { kind: "set_slot", base: x(29), offset: 24 },
  operands: [oref("o33"), vref("v9")], defines: [] });
op({ id: "o34a", op: { kind: "clear_slot", base: x(29), offset: 24 },
  operands: [oref("o34"), vref("v9")], defines: [] });
op({ id: "o35", op: "return", operands: [oref("o34a")], defines: [], effect: "o28" });

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
const visited = buildNodes(roots, ops);
const terminals = roots.map(r => visited.get(r)!);
let nodes = topoSortAndLink(visited, ops);
assignOrder(nodes);
computeAllStates(nodes, ops);
printTimeline("Timeline", nodes, terminals, ops);

// --- Fold + sweep ---
foldImmediates(nodes, ops);
const live = markReachable(roots, ops);
nodes = sweep(nodes, live, ops);
assignOrder(nodes);
computeAllStates(nodes, ops);
printTimeline("After fold + sweep", nodes, terminals, ops);
checkScope(nodes, ops);
checkContracts(nodes);

// --- Pathfinder ---
let pass = 0;
while (true) {
  pass++;
  console.log(`\n${C.bold}=== Pathfinder (pass ${pass}) ===${C.reset}`);
  computeAllStates(nodes, ops);
  const applied = applyPaths(nodes, ops, visited);
  console.log(`  ${applied} change(s) applied`);
  if (applied === 0) break;
  // Re-collect nodes (new loads were inserted) but DON'T re-sort.
  // The loads were inserted with correct prev pointers.
  const allNodes = [...visited.values()];
  // Sort by walking prev to get correct order
  const seen = new Set<TimeNode>();
  nodes = [];
  function visit(n: TimeNode) { if (seen.has(n)) return; seen.add(n); if (n.prev) visit(n.prev); nodes.push(n); }
  for (const n of allNodes) visit(n);
  assignOrder(nodes);
}

computeAllStates(nodes, ops);
printTimeline(`After pathfinder (${pass} passes)`, nodes, terminals, ops);
checkScope(nodes, ops);
checkContracts(nodes);

// --- Post-pathfinder sweep ---
const live2 = markReachable(roots, ops);
let deadCount = 0;
for (const n of nodes) {
  if (!live2.has(n.op.id)) {
    console.log(`  ${C.dim}DEAD${C.reset} [${n.order}] ${C.dim}${n.op.id}${C.reset}: ${fmtOp(n.op, ops)}`);
    deadCount++;
  }
}
console.log(`\n${C.bold}=== Post-pathfinder sweep ===${C.reset}`);
console.log(`  ${deadCount} dead node(s)`);
if (deadCount > 0) {
  nodes = sweep(nodes, live2, ops);
  assignOrder(nodes);
  computeAllStates(nodes, ops);
  printTimeline("Final", nodes, terminals, ops);
  checkScope(nodes, ops);
  checkContracts(nodes);
}
