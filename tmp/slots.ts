import type { Slot, SlotMap, VRegId, OpCode, Operation, Operand, PRegSlot, ConstSlot, MemSlot, VRegSlot } from "./types";
import { fmtPreg, PREG_COUNT } from "./types";

export type OpKindStr = "param" | "const" | "alu" | "set_slot" | "clear_slot" | "load" | "brif" | "call" | "return";

export function opKind(oc: OpCode): OpKindStr {
  if (typeof oc === "string") return oc;
  if ("alu" in oc) return "alu";
  return oc.kind;
}

export function slotId(s: Slot): string {
  switch (s.kind) {
    case "preg": return fmtPreg(s);
    case "mem": return `m[${fmtPreg(s.base)}+${s.offset}]`;
    case "const": return `c#${s.value}`;
    case "vreg": return s.id;
  }
}

export function slotVreg(s: Slot): VRegId | null {
  if (s.kind === "preg") return typeof s.state === "string" ? s.state : null;
  return s.state;
}

export function emptySlotMap(): SlotMap {
  const m: SlotMap = new Map();
  for (let i = 0; i < PREG_COUNT; i++) {
    m.set(`w${i}`, { kind: "preg", num: i, width: 32, state: true });
  }
  return m;
}

export function cloneSlotMap(m: SlotMap): SlotMap {
  const clone: SlotMap = new Map();
  for (const [k, v] of m) clone.set(k, { ...v });
  return clone;
}

export function applyMicroOps(slots: SlotMap, o: Operation) {
  const oc = o.op;
  const kind = opKind(oc);

  // Write defines into the slot map. If a define has a preg, write a preg slot.
  // Otherwise fall back to a vreg slot (unassigned). Const defines get const slots.
  function writeDefines(defines: typeof o.defines) {
    for (const d of defines) {
      if (d.const !== undefined) {
        const slot: ConstSlot = { kind: "const", value: d.const, width: 32, state: d.vreg };
        slots.set(slotId(slot), slot);
      } else if (d.preg) {
        const slot: PRegSlot = { kind: "preg", ...d.preg, state: d.vreg };
        slots.set(slotId(slot), slot);
      } else {
        const vs: VRegSlot = { kind: "vreg", id: d.vreg, width: 32, state: d.vreg };
        slots.set(slotId(vs), vs);
      }
    }
  }

  switch (kind) {
    case "param":
    case "const":
    case "load":
    case "alu": {
      writeDefines(o.defines);
      break;
    }
    case "set_slot": {
      const s = oc as { kind: "set_slot"; base: typeof o.defines[0]["preg"]; offset: number };
      const vregOp = o.operands[1];
      if (vregOp?.kind === "vreg") {
        const slot: MemSlot = { kind: "mem", base: s.base!, offset: s.offset, width: 32, state: vregOp.id };
        slots.set(slotId(slot), slot);
      }
      break;
    }
    case "clear_slot": {
      const s = oc as { kind: "clear_slot"; base: typeof o.defines[0]["preg"]; offset: number };
      const key = slotId({ kind: "mem", base: s.base!, offset: s.offset, width: 32, state: "" });
      slots.delete(key);
      break;
    }
    case "call": {
      for (let i = 0; i < PREG_COUNT; i++) {
        slots.set(`w${i}`, { kind: "preg", num: i, width: 32, state: false });
      }
      for (const [k, slot] of [...slots]) {
        if (slot.kind === "vreg") slots.delete(k);
      }
      writeDefines(o.defines);
      break;
    }
  }
}

/// Resolve an operand to the vreg it references.
export function resolveOperandVreg(operand: Operand, ops: Map<string, Operation>): VRegId | null {
  if (operand.kind === "imm12") return null;
  if (operand.kind === "vreg") return operand.id;
  const target = ops.get(operand.op);
  if (!target) return null;
  const def = target.defines[operand.define];
  if (def) return def.vreg;
  const kind = opKind(target.op);
  if (kind === "set_slot" || kind === "clear_slot") {
    const vregOp = target.operands[1];
    if (vregOp?.kind === "vreg") return vregOp.id;
    const opOp = target.operands[0];
    if (opOp) return resolveOperandVreg(opOp, ops);
  }
  return null;
}
