import type { Operation, TimeNode, SlotMap, Operand } from "./types";
import { opKind, slotVreg, resolveOperandVreg } from "./slots";

export function resolveConst(operand: Operand, ops: Map<string, Operation>): number | undefined {
  if (operand.kind === "imm12") return operand.value;
  const vid = resolveOperandVreg(operand, ops);
  if (!vid || !vid.startsWith("c#")) return undefined;
  return parseInt(vid.slice(2), 10);
}

export function foldImmediates(nodes: TimeNode[], ops: Map<string, Operation>) {
  for (const cur of nodes) {
    const oc = cur.op.op;
    if (typeof oc === "object" && "alu" in oc && cur.op.operands.length === 2) {
      const rhs = cur.op.operands[1];
      const val = resolveConst(rhs, ops);
      if (val !== undefined && val >= 0 && val <= 4095) {
        cur.op.operands[1] = { kind: "imm12", value: val };
      }
    }
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

// Sweep dead nodes — returns filtered array. Also removes dead ops from the map.
export function sweep(nodes: TimeNode[], live: Set<string>, ops: Map<string, Operation>): TimeNode[] {
  return nodes.filter(n => {
    if (live.has(n.op.id)) return true;
    ops.delete(n.op.id);
    return false;
  });
}
