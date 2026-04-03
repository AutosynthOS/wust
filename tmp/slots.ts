import type { Slot, SlotMap, VRegId, OpCode, Operation, Operand, ConstSlot, MemSlot, VRegSlot } from "./types";
import { fmtPreg } from "./types";

export function opKind(oc: OpCode): string {
  if (typeof oc === "string") return oc;
  if ("alu" in oc) return "alu";
  return oc.kind;
}

export function slotId(s: Slot): string {
  switch (s.kind) {
    case "preg": return `${s.width === 32 ? 'w' : 'x'}${s.num}`;
    case "mem": return `m[${fmtPreg(s.base)}+${s.offset}]`;
    case "const": return `c#${s.value}`;
    case "vreg": return s.id;
  }
}

export function slotVreg(s: Slot): VRegId | null {
  switch (s.kind) {
    case "preg": return typeof s.state === "string" ? s.state : null;
    case "mem": return s.state;
    case "const": return s.state;
    case "vreg": return s.state;
  }
}

export function emptySlotMap(): SlotMap {
  const m: SlotMap = new Map();
  for (let i = 0; i <= 30; i++) {
    m.set(`w${i}`, { kind: "preg", num: i, width: 32, state: true });
  }
  return m;
}

export function cloneSlotMap(m: SlotMap): SlotMap {
  return new Map([...m.entries()].map(([k, v]) => [k, { ...v }]));
}

export function applyMicroOps(slots: SlotMap, o: Operation) {
  const oc = o.op;
  const kind = opKind(oc);

  switch (kind) {
    case "param": {
      for (const d of o.defines) {
        if (d.preg) {
          slots.set(slotId({ kind: "preg", ...d.preg, state: d.vreg }),
            { kind: "preg", ...d.preg, state: d.vreg });
        }
      }
      break;
    }
    case "const": {
      for (const d of o.defines) {
        if (d.const !== undefined) {
          const slot: ConstSlot = { kind: "const", value: d.const, width: 32, state: d.vreg };
          slots.set(slotId(slot), slot);
        }
      }
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
    case "load": {
      for (const d of o.defines) {
        if (d.preg) {
          slots.set(slotId({ kind: "preg", ...d.preg, state: d.vreg }),
            { kind: "preg", ...d.preg, state: d.vreg });
        }
      }
      break;
    }
    case "call": {
      for (let i = 0; i <= 30; i++) {
        slots.set(`w${i}`, { kind: "preg", num: i, width: 32, state: false });
      }
      for (const [k, slot] of [...slots]) {
        if (slot.kind === "vreg") slots.delete(k);
      }
      for (const d of o.defines) {
        if (d.preg) {
          slots.set(slotId({ kind: "preg", ...d.preg, state: d.vreg }),
            { kind: "preg", ...d.preg, state: d.vreg });
        } else {
          const vs: VRegSlot = { kind: "vreg", id: d.vreg, width: 32, state: d.vreg };
          slots.set(slotId(vs), vs);
        }
      }
      break;
    }
    case "alu": {
      for (const d of o.defines) {
        if (d.preg) {
          slots.set(slotId({ kind: "preg", ...d.preg, state: d.vreg }),
            { kind: "preg", ...d.preg, state: d.vreg });
        } else {
          const vs: VRegSlot = { kind: "vreg", id: d.vreg, width: 32, state: d.vreg };
          slots.set(slotId(vs), vs);
        }
      }
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
    const vregOp = target.operands.find(o => o.kind === "vreg");
    if (vregOp?.kind === "vreg") return vregOp.id;
    const opOp = target.operands.find(o => o.kind === "op");
    if (opOp) return resolveOperandVreg(opOp, ops);
  }
  return null;
}
