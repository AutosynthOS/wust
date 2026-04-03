import type { PReg, TimeNode, SlotMap, VRegId, Slot, MemSlot, Operation, Define } from "./types";
import { w, oref, vref, fmtPreg } from "./types";
import { slotVreg, resolveOperandVreg } from "./slots";
import { C } from "./format";

export interface PathResult {
  vreg: VRegId;
  targetSlot: string;
  foundAt: TimeNode;
  foundIn: string;
  foundSlot: Slot;
  cost: number;
}

export const COST_FREE = 0;
export const COST_MOV = 10;
export const COST_LOAD = 100;
export const COST_STORE = 150;

export let nextOpId = 100;

function findStoreOrder(from: TimeNode, slotKey: string, vreg: VRegId): number {
  let cur: TimeNode | undefined = from;
  while (cur) {
    const s = cur.op.op as { kind: string; base?: PReg; offset?: number };
    if (s.kind === "set_slot") {
      const vrefOp = cur.op.operands[1];
      if (vrefOp?.kind === "vreg" && vrefOp.id === vreg
          && `m[${fmtPreg(s.base!)}+${s.offset}]` === slotKey) {
        return cur.order;
      }
    }
    cur = cur.prev;
  }
  return Infinity;
}

export function findPath(from: TimeNode, targetSlotKey: string, targetVreg: VRegId): PathResult | null {
  const prev = from.prev;
  if (!prev) return null;

  let best: PathResult | null = null;
  let bestStoreOrder = Infinity;
  for (const [k, slot] of prev.after) {
    const vid = slotVreg(slot);
    if (vid !== targetVreg) continue;
    if (slot.kind === "preg" && slot.state === false) continue;

    let cost: number;
    if (slot.kind === "vreg") {
      cost = COST_FREE;
    } else if (slot.kind === "preg" && k === targetSlotKey) {
      cost = COST_FREE;
    } else if (slot.kind === "preg") {
      cost = COST_MOV;
    } else if (slot.kind === "mem") {
      cost = COST_LOAD;
    } else if (slot.kind === "const") {
      cost = COST_MOV;
    } else {
      continue;
    }

    const storeOrder = slot.kind === "mem" ? findStoreOrder(prev, k, targetVreg) : Infinity;
    if (!best || cost < best.cost || (cost === best.cost && storeOrder < bestStoreOrder)) {
      best = { vreg: targetVreg, targetSlot: targetSlotKey, foundAt: prev, foundIn: k, foundSlot: slot, cost };
      bestStoreOrder = storeOrder;
    }
  }

  return best;
}

function findFreePreg(slots: SlotMap): PReg | null {
  for (let i = 0; i <= 30; i++) {
    const slot = slots.get(`w${i}`);
    if (!slot || (slot.kind === "preg" && slot.state === true)) {
      return w(i);
    }
  }
  return null;
}

function insertBefore(target: TimeNode, newNode: TimeNode) {
  newNode.next = target;
  newNode.prev = target.prev;
  if (target.prev) target.prev.next = newNode;
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
  const path = findPath(node, "", vreg);
  if (!path) return undefined;

  if (path.foundSlot.kind === "preg" || path.foundSlot.kind === "vreg") {
    const defNode = findDefiningOp(path.foundAt, vreg);
    return defNode?.op.id;
  } else if (path.foundSlot.kind === "mem") {
    const slotKey = path.foundIn;
    let walk: TimeNode | undefined = path.foundAt;
    while (walk) {
      const s = walk.op.op as { kind: string; base?: PReg; offset?: number };
      const opVref = walk.op.operands[1];
      if (s.kind === "set_slot" && `m[${fmtPreg(s.base!)}+${s.offset}]` === slotKey
          && opVref?.kind === "vreg" && opVref.id === vreg) {
        return walk.op.id;
      }
      walk = walk.prev;
    }
  } else if (path.foundSlot.kind === "const") {
    const defNode = findDefiningOp(path.foundAt, vreg);
    return defNode?.op.id;
  }
  return undefined;
}

export function applyPaths(head: TimeNode, ops: Map<string, Operation>) {
  let applied = 0;
  let cur: TimeNode | undefined = head;
  while (cur) {
    if (!cur.prev) { cur = cur.next; continue; }

    // Phase 1: Resolve contract violations
    if (cur.contract.size > 0) {
      for (const [k, required] of cur.contract) {
        const reqVreg = slotVreg(required);
        if (!reqVreg) continue;

        const isNeedAny = k.startsWith("need:");
        let satisfied = false;
        if (isNeedAny) {
          for (const [, slot] of cur.prev!.after) {
            if (slot.kind === "preg" && typeof slot.state === "string" && slot.state === reqVreg) {
              satisfied = true; break;
            }
          }
        } else {
          const prevSlot = cur.prev!.after.get(k);
          const prevVreg = prevSlot ? slotVreg(prevSlot) : null;
          satisfied = prevVreg === reqVreg;
        }

        if (satisfied) continue;

        const targetSlotKey = isNeedAny ? "" : k;
        const path = findPath(cur, targetSlotKey, reqVreg);
        if (!path) continue;

        if (path.foundSlot.kind === "vreg" && path.cost === COST_FREE) {
          const defNode = findDefiningOp(path.foundAt, reqVreg);
          const def = defNode?.op.defines.find(d => d.vreg === reqVreg);
          if (def && defNode) {
            if (required.kind === "preg") {
              def.preg = { num: required.num, width: required.width };
              console.log(`  ${C.green}ASSIGN${C.reset} ${C.dim}${defNode.op.id}${C.reset}: ${C.cyan}${reqVreg}${C.reset} → dst=${C.magenta}${k}${C.reset}`);
            } else {
              const free = findFreePreg(defNode.after);
              if (free) {
                def.preg = free;
                console.log(`  ${C.green}ASSIGN${C.reset} ${C.dim}${defNode.op.id}${C.reset}: ${C.cyan}${reqVreg}${C.reset} → dst=${C.magenta}${fmtPreg(free)}${C.reset}`);
              }
            }
            applied++;
          }
        } else if (path.foundSlot.kind === "mem") {
          const memSlot = path.foundSlot as MemSlot;
          const free = findFreePreg(cur.prev!.after);
          if (free) {
            const slotKey = path.foundIn;
            let storeId: string | undefined;
            let walk: TimeNode | undefined = cur.prev ?? undefined;
            while (walk) {
              const op = walk.op;
              const s = op.op as { kind: string; base?: PReg; offset?: number };
              const opVref = op.operands[1];
              if (s.kind === "set_slot" && `m[${fmtPreg(s.base!)}+${s.offset}]` === slotKey
                  && opVref?.kind === "vreg" && opVref.id === reqVreg) {
                storeId = op.id;
                break;
              }
              walk = walk.prev;
            }

            const loadId = `gen${nextOpId++}`;
            const loadOp: Operation = {
              id: loadId,
              op: { kind: "load", base: memSlot.base, offset: memSlot.offset },
              operands: storeId ? [oref(storeId)] : [vref(reqVreg)],
              defines: [{ vreg: reqVreg, preg: free }],
            };
            ops.set(loadId, loadOp);
            const loadNode: TimeNode = {
              op: loadOp, order: 0,
              contract: new Map(), before: new Map(), after: new Map(),
            };
            insertBefore(cur, loadNode);

            console.log(`  ${C.green}LOAD${C.reset} ${C.dim}${loadId}${C.reset}: ${C.cyan}${reqVreg}${C.reset} from ${C.blue}${path.foundIn}${C.reset} → ${C.magenta}${fmtPreg(free)}${C.reset} (before ${C.dim}${cur.op.id}${C.reset})`);
            applied++;
          }
        }
      }
    }

    // Phase 2: Rewrite ALL operands to their valid source via pathfinder
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

    cur = cur.next;
  }
  return applied;
}
