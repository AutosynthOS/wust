import type { PReg, Operand, Operation, OpCode, SlotMap, TimeNode } from "./types";
import { fmtPreg } from "./types";
import { opKind, slotVreg, resolveOperandVreg } from "./slots";

export { fmtPreg };

export const C = {
  reset:   "\x1b[0m",
  dim:     "\x1b[2m",
  bold:    "\x1b[1m",
  red:     "\x1b[31m",
  green:   "\x1b[32m",
  yellow:  "\x1b[33m",
  blue:    "\x1b[34m",
  magenta: "\x1b[35m",
  cyan:    "\x1b[36m",
  white:   "\x1b[37m",
  teal:    "\x1b[38;5;43m",
  orange:  "\x1b[38;5;208m",
  gray:    "\x1b[38;5;245m",
  brown:   "\x1b[38;5;130m",
};

export function fmtOperand(o: Operand, ops: Map<string, Operation>, before?: SlotMap): string {
  if (o.kind === "imm12") return `${C.yellow}#${o.value}${C.reset}`;
  if (o.kind === "vreg") return `${C.cyan}${o.id}${C.reset}`;
  const target = ops.get(o.op);
  if (!target) return `${C.dim}${o.op}[${o.define}]${C.reset}`;
  const def = target.defines[o.define];
  let vid: string | null = def?.vreg ?? resolveOperandVreg(o, ops);
  if (!vid) return `${C.dim}${o.op}[${o.define}]${C.reset}`;
  if (vid.startsWith("c#")) return `${C.yellow}${vid}${C.reset}`;
  if (before) {
    for (const [, slot] of before) {
      if (slot.kind === "preg" && typeof slot.state === "string" && slot.state === vid) {
        return `${C.dim}${vid}${C.reset}:${C.magenta}${fmtPreg(slot)}${C.reset}`;
      }
    }
  }
  return `${C.red}${vid}${C.reset}`;
}

export function fmtOpCode(op: OpCode): string {
  if (typeof op === "string") return op;
  if ("alu" in op) return op.alu;
  if ("kind" in op) return `${op.kind} ${C.dim}[${fmtPreg(op.base)}+${op.offset}]${C.reset}`;
  return String(op);
}

export function fmtOp(o: Operation, ops: Map<string, Operation>, before?: SlotMap): string {
  const code = `${C.bold}${fmtOpCode(o.op)}${C.reset}`;
  const operands = o.operands.map(op => fmtOperand(op, ops, before)).join(", ");
  const defs = o.defines.map((d) => {
    const isConst = d.vreg.startsWith("c#");
    const hasPreg = !!d.preg;
    const vregColor = isConst ? C.orange : hasPreg ? C.gray : C.red;
    let s = `${vregColor}${d.vreg}${C.reset}`;
    if (d.preg) s += `${C.dim}:${C.magenta}${fmtPreg(d.preg)}${C.reset}`;
    if (d.const !== undefined && !isConst) s += ` ${C.orange}#${d.const}${C.reset}`;
    if (d.slot) s += ` ${C.dim}[${fmtPreg(d.slot.base)}+${d.slot.offset}]${C.reset}`;
    return s;
  }).join(", ");
  const defsStr = defs ? `${defs} ${C.dim}=${C.reset} ` : "";
  const effect = o.effect ? ` ${C.dim}[after ${o.effect}]${C.reset}` : "";
  return `${C.dim}${o.id}:${C.reset} ${defsStr}${code}(${operands})${effect}`;
}

export function fmtSlots(slots: SlotMap): string {
  const parts: string[] = [];
  for (const [k, slot] of slots) {
    const vid = slotVreg(slot);
    if (!vid) continue;
    let color = C.dim;
    switch (slot.kind) {
      case "preg":  color = C.magenta; break;
      case "mem":   color = C.brown; break;
      case "const": color = C.orange; break;
      case "vreg":  color = C.cyan; break;
    }
    if (k === vid) {
      const soloColor = slot.kind === "vreg" ? C.red : color;
      parts.push(`${soloColor}${k}${C.reset}`);
    } else {
      parts.push(`${color}${k}${C.reset}=${C.gray}${vid}${C.reset}`);
    }
  }
  const blocked: number[] = [];
  for (const [, slot] of slots) {
    if (slot.kind === "preg" && slot.state === false) blocked.push(slot.num);
  }
  if (blocked.length > 0) {
    blocked.sort((a, b) => a - b);
    const first = blocked[0], last = blocked[blocked.length - 1];
    if (last - first + 1 === blocked.length) {
      parts.push(`${C.red}w${first}..w${last}:blocked${C.reset}`);
    } else {
      parts.push(`${C.red}${blocked.map(n => `w${n}`).join(",")}:blocked${C.reset}`);
    }
  }
  return parts.join(", ");
}

export function stripAnsi(s: string): number {
  return s.replace(/\x1b\[[0-9;]*m/g, "").length;
}

export function printTimeline(label: string, head: TimeNode, ops: Map<string, Operation>) {
  console.log(`\n${C.bold}=== ${label} ===${C.reset}`);
  let maxWidth = 0;
  let cur: TimeNode | undefined = head;
  while (cur) {
    const line = `[${String(cur.order).padStart(2)}] ${fmtOp(cur.op, ops, cur.before)}`;
    maxWidth = Math.max(maxWidth, stripAnsi(line));
    cur = cur.next;
  }
  cur = head;
  while (cur) {
    const line = `  ${C.dim}[${String(cur.order).padStart(2)}]${C.reset} ${fmtOp(cur.op, ops, cur.before)}`;
    const padding = maxWidth - stripAnsi(line) + 4;
    const after = fmtSlots(cur.after);
    const sep = after ? `${" ".repeat(Math.max(padding, 2))}${C.dim}||>${C.reset} ${after}` : "";
    console.log(`${line}${sep}`);
    cur = cur.next;
  }
}
