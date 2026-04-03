import type { Operation, TimeNode, SlotMap, Operand } from "./types";
import { opKind, slotVreg, resolveOperandVreg } from "./slots";

export function resolveConst(operand: Operand, ops: Map<string, Operation>): number | undefined {
  if (operand.kind === "imm12") return operand.value;
  if (operand.kind === "vreg") return undefined;
  const target = ops.get(operand.op);
  if (!target) return undefined;
  const def = target.defines[operand.define];
  if (def?.const !== undefined) return def.const;
  const kind = opKind(target.op);
  if (kind === "set_slot" || kind === "clear_slot") {
    const orefOp = target.operands.find(o => o.kind === "op");
    if (orefOp) return resolveConst(orefOp, ops);
    const vrefOp = target.operands.find(o => o.kind === "vreg");
    if (vrefOp?.kind === "vreg" && vrefOp.id.startsWith("c#")) {
      for (const o of ops.values()) {
        if (o.op === "const") {
          const d = o.defines.find(d => d.vreg === vrefOp.id);
          if (d?.const !== undefined) return d.const;
        }
      }
    }
  }
  return undefined;
}

export function foldImmediates(head: TimeNode, ops: Map<string, Operation>) {
  let cur: TimeNode | undefined = head;
  while (cur) {
    const oc = cur.op.op;
    if (typeof oc === "object" && "alu" in oc && cur.op.operands.length === 2) {
      const rhs = cur.op.operands[1];
      const val = resolveConst(rhs, ops);
      if (val !== undefined && val >= 0 && val <= 4095) {
        cur.op.operands[1] = { kind: "imm12", value: val };
      }
    }
    cur = cur.next;
  }
}

export function markReachable(rootIds: string[], ops: Map<string, Operation>): Set<string> {
  const live = new Set<string>();
  function mark(id: string) {
    if (live.has(id)) return;
    live.add(id);
    const o = ops.get(id);
    if (!o) return;
    for (const u of o.operands) {
      if (u.kind === "op") mark(u.op);
    }
    if (o.effect) mark(o.effect);
  }
  for (const r of rootIds) mark(r);
  return live;
}

export function sweep(head: TimeNode, live: Set<string>): TimeNode {
  let cur: TimeNode | undefined = head;
  let newHead = head;
  while (cur) {
    const next = cur.next;
    if (!live.has(cur.op.id)) {
      if (cur.prev) cur.prev.next = cur.next;
      if (cur.next) cur.next.prev = cur.prev;
      if (cur === newHead) newHead = cur.next!;
    }
    cur = next;
  }
  return newHead;
}

export function slotsEqual(a: SlotMap, b: SlotMap): boolean {
  if (a.size !== b.size) return false;
  for (const [k, slotA] of a) {
    const slotB = b.get(k);
    if (!slotB) return false;
    if (slotVreg(slotA) !== slotVreg(slotB)) return false;
    if (slotA.kind !== slotB.kind) return false;
  }
  return true;
}

export function fuseNoopPairs(head: TimeNode): TimeNode {
  let changed = true;
  let newHead = head;
  while (changed) {
    changed = false;
    let cur: TimeNode | undefined = newHead;
    while (cur && cur.next) {
      const a = cur;
      const b = cur.next;
      const aKind = opKind(a.op.op);
      const bKind = opKind(b.op.op);
      if ((aKind === "set_slot" || aKind === "clear_slot") &&
          (bKind === "set_slot" || bKind === "clear_slot") &&
          slotsEqual(a.before, b.after)) {
        const prev = a.prev;
        const next = b.next;
        if (prev) prev.next = next;
        if (next) next.prev = prev;
        if (a === newHead) newHead = next!;
        changed = true;
        cur = next;
      } else {
        cur = cur.next;
      }
    }
  }
  return newHead;
}
