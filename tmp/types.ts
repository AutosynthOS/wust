export type Width = 32 | 64;

export interface PReg {
  num: number;
  width: Width;
}

export function w(num: number): PReg { return { num, width: 32 }; }
export function x(num: number): PReg { return { num, width: 64 }; }

export interface PRegSlot {
  kind: "preg";
  num: number;
  width: Width;
  state: VRegId | true | false;
}

export interface MemSlot {
  kind: "mem";
  base: PReg;
  offset: number;
  width: Width;
  state: VRegId;
}

export interface ConstSlot {
  kind: "const";
  value: number;
  width: Width;
  state: VRegId;
}

export interface VRegSlot {
  kind: "vreg";
  id: string;
  width: Width;
  state: VRegId;
}

export type Slot = PRegSlot | MemSlot | ConstSlot | VRegSlot;

export type VRegId = string;

export type Operand =
  | { kind: "op"; op: string; define: number }
  | { kind: "imm12"; value: number }
  | { kind: "vreg"; id: VRegId };

export interface Define {
  vreg: VRegId;
  preg?: PReg;
  slot?: MemSlot;
  const?: number;
}

export interface Operation {
  id: string;
  op: OpCode;
  operands: Operand[];
  effect?: string;
  defines: Define[];
}

export type OpCode =
  | "param"
  | "const"
  | { kind: "set_slot"; base: PReg; offset: number }
  | { kind: "clear_slot"; base: PReg; offset: number }
  | { kind: "load"; base: PReg; offset: number }
  | { alu: "add" | "sub" | "mul" | "cmp_les" | "cmp_eq" }
  | "brif"
  | "call"
  | "return";

export type SlotMap = Map<string, Slot>;

export interface TimeNode {
  op: Operation;
  order: number;
  prev?: TimeNode;
  next?: TimeNode;
  contract: SlotMap;
  before: SlotMap;
  after: SlotMap;
}

export function fmtPreg(p: PReg): string {
  return p.width === 32 ? `w${p.num}` : `x${p.num}`;
}

export function oref(op: string, define: number = 0): Operand {
  return { kind: "op", op, define };
}
export function imm12(value: number): Operand {
  return { kind: "imm12", value };
}
export function vref(id: VRegId): Operand {
  return { kind: "vreg", id };
}
