import type { PReg, TimeNode, SlotMap, VRegId, Slot, MemSlot, Operation } from "./types";
import { w, oref, vref, fmtPreg, PREG_COUNT } from "./types";
import { slotVreg, resolveOperandVreg } from "./slots";
import { getSlotsBefore } from "./timeline";
import { C } from "./format";

export interface PathResult {
  vreg: VRegId;
  targetSlot: string;
  foundAt: TimeNode;
  foundIn: string;
  foundSlot: Slot;
  cost: number;
}

export const costs = {
  free: 0,
  mov: 10,
  load: 100,
  store: 150,
  materialize: 10,
};

export let nextOpId = 100;

// Walk backwards to find the set_slot that wrote `vreg` to `slotKey`.
function findStore(from: TimeNode, slotKey: string, vreg: VRegId): TimeNode | undefined {
  let cur: TimeNode | undefined = from;
  while (cur) {
    const s = cur.op.op;
    if (typeof s === "object" && "kind" in s && s.kind === "set_slot") {
      const vrefOp = cur.op.operands[1];
      if (vrefOp?.kind === "vreg" && vrefOp.id === vreg
          && `m[${fmtPreg(s.base)}+${s.offset}]` === slotKey) {
        return cur;
      }
    }
    cur = cur.prev;
  }
  return undefined;
}

// Find where a vreg lives by looking at prev's results (computed on demand).
export function findPath(from: TimeNode, targetSlotKey: string | null, targetVreg: VRegId): PathResult | null {
  const prev = from.prev;
  if (!prev) return null;

  let best: PathResult | null = null;
  let bestStoreOrder = Infinity;
  for (const [k, slot] of prev.results) {
    const vid = slotVreg(slot);
    if (vid !== targetVreg) continue;
    if (slot.kind === "preg" && slot.state === false) continue;

    const isExactPreg = slot.kind === "preg" && targetSlotKey !== null && k === targetSlotKey;
    const cost =
      slot.kind === "vreg"  ? costs.free :
      isExactPreg           ? costs.free :
      slot.kind === "preg"  ? costs.mov :
      slot.kind === "mem"   ? costs.load :
      slot.kind === "const" ? costs.materialize :
      null;
    if (cost === null) continue;

    const storeOrder = slot.kind === "mem" ? (findStore(prev, k, targetVreg)?.order ?? Infinity) : Infinity;
    if (!best || cost < best.cost || (cost === best.cost && storeOrder < bestStoreOrder)) {
      best = { vreg: targetVreg, targetSlot: targetSlotKey, foundAt: prev, foundIn: k, foundSlot: slot, cost };
      bestStoreOrder = storeOrder;
    }
  }

  return best;
}

function findFreePreg(slots: SlotMap): PReg | null {
  for (let i = 0; i < PREG_COUNT; i++) {
    const slot = slots.get(`w${i}`);
    if (!slot || (slot.kind === "preg" && slot.state === true)) {
      return w(i);
    }
  }
  return null;
}

// Insert a new node before target by updating prev pointers.
// All nodes that had target as prev now need updating — but since
// we only insert right before `target`, just set newNode.prev = target.prev
// and target.prev = newNode.
function insertBefore(target: TimeNode, newNode: TimeNode) {
  newNode.prev = target.prev;
  target.prev = newNode;
}

function findDefiningOp(from: TimeNode, vreg: VRegId): TimeNode | undefined {
  let cur: TimeNode | undefined = from;
  while (cur) {
    if (cur.op.defines.some(d => d.vreg === vreg)) return cur;
    cur = cur.prev;
  }
  return undefined;
}

function findSourceOp(node: TimeNode, vreg: VRegId): string | undefined {
  const path = findPath(node, null, vreg);
  if (!path) return undefined;

  if (path.foundSlot.kind === "mem") {
    return findStore(path.foundAt, path.foundIn, vreg)?.op.id;
  }
  return findDefiningOp(path.foundAt, vreg)?.op.id;
}

// Check if a contract entry is already satisfied by prev's results.
function isSatisfied(prevResults: SlotMap, k: string, reqVreg: VRegId): boolean {
  if (k.startsWith("need:")) {
    for (const [, slot] of prevResults) {
      if (slot.kind === "preg" && typeof slot.state === "string" && slot.state === reqVreg) return true;
    }
    return false;
  }
  const prevSlot = prevResults.get(k);
  return prevSlot ? slotVreg(prevSlot) === reqVreg : false;
}

// Assign a preg to an unallocated vreg's defining op.
function assignPreg(path: PathResult, reqVreg: VRegId, required: Slot): boolean {
  const defNode = findDefiningOp(path.foundAt, reqVreg);
  const def = defNode?.op.defines.find(d => d.vreg === reqVreg);
  if (!def || !defNode) return false;

  if (required.kind === "preg") {
    def.preg = { num: required.num, width: required.width };
    console.log(`  ${C.green}ASSIGN${C.reset} ${C.dim}${defNode.op.id}${C.reset}: ${C.cyan}${reqVreg}${C.reset} → dst=${C.magenta}w${required.num}${C.reset}`);
  } else {
    const free = findFreePreg(getSlotsBefore(defNode));
    if (!free) return false;
    def.preg = free;
    console.log(`  ${C.green}ASSIGN${C.reset} ${C.dim}${defNode.op.id}${C.reset}: ${C.cyan}${reqVreg}${C.reset} → dst=${C.magenta}${fmtPreg(free)}${C.reset}`);
  }
  return true;
}

// Insert a load from memory before a consumer node.
function emitLoad(cur: TimeNode, path: PathResult, reqVreg: VRegId, ops: Map<string, Operation>, visited?: Map<string, TimeNode>): boolean {
  const memSlot = path.foundSlot as MemSlot;
  const free = findFreePreg(getSlotsBefore(cur));
  if (!free) return false;

  const store = findStore(cur.prev!, path.foundIn, reqVreg);
  const loadId = `gen${nextOpId++}`;
  const loadOp: Operation = {
    id: loadId,
    op: { kind: "load", base: memSlot.base, offset: memSlot.offset },
    operands: store ? [oref(store.op.id)] : [vref(reqVreg)],
    defines: [{ vreg: reqVreg, preg: free }],
  };
  ops.set(loadId, loadOp);
  const loadNode: TimeNode = { op: loadOp, order: 0, prev: cur.prev, inputs: new Map(), results: new Map() };
  insertBefore(cur, loadNode);
  if (visited) visited.set(loadId, loadNode);

  console.log(`  ${C.green}LOAD${C.reset} ${C.dim}${loadId}${C.reset}: ${C.cyan}${reqVreg}${C.reset} from ${C.blue}${path.foundIn}${C.reset} → ${C.magenta}${fmtPreg(free)}${C.reset} (before ${C.dim}${cur.op.id}${C.reset})`);
  return true;
}

// Rewrite operands to point at their valid source via pathfinder.
function rewriteOperands(cur: TimeNode, ops: Map<string, Operation>) {
  for (let i = 0; i < cur.op.operands.length; i++) {
    const operand = cur.op.operands[i];
    if (operand.kind !== "op") continue;
    const vid = resolveOperandVreg(operand, ops);
    if (!vid) continue;
    const sourceId = findSourceOp(cur, vid);
    if (sourceId && sourceId !== operand.op) {
      cur.op.operands[i] = oref(sourceId);
    }
  }
}

// Run pathfinder: resolve contracts, insert loads, rewrite operands.
export function applyPaths(nodes: TimeNode[], ops: Map<string, Operation>, visited?: Map<string, TimeNode>) {
  let applied = 0;
  const assigned = new Set<VRegId>();

  for (const cur of nodes) {
    if (!cur.prev) continue;

    for (const [k, required] of cur.inputs) {
      const reqVreg = slotVreg(required);
      if (!reqVreg || isSatisfied(cur.prev.results, k, reqVreg)) continue;

      const path = findPath(cur, k.startsWith("need:") ? null : k, reqVreg);
      if (!path) continue;

      const isNeedAny = k.startsWith("need:");
      if (path.foundSlot.kind === "vreg" && path.cost === costs.free && !(isNeedAny && assigned.has(reqVreg))) {
        if (assignPreg(path, reqVreg, required)) { assigned.add(reqVreg); applied++; }
      } else if (path.foundSlot.kind === "mem") {
        if (emitLoad(cur, path, reqVreg, ops, visited)) applied++;
      }
    }

    rewriteOperands(cur, ops);
  }
  return applied;
}
