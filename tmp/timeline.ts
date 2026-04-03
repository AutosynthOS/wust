import type { Operation, TimeNode, SlotMap, VRegId } from "./types";
import { opKind, slotVreg, cloneSlotMap, emptySlotMap, applyMicroOps, resolveOperandVreg } from "./slots";
import { C } from "./format";
import { fmtPreg } from "./types";

export function buildTimeline(
  opId: string,
  ops: Map<string, Operation>,
  visited: Map<string, TimeNode>,
  tail?: TimeNode,
): TimeNode {
  if (visited.has(opId)) return tail!;

  const operation = ops.get(opId);
  if (!operation) throw new Error(`unresolved op: ${opId}`);

  for (const operand of operation.operands) {
    if (operand.kind === "op") {
      tail = buildTimeline(operand.op, ops, visited, tail);
    }
  }
  if (operation.effect) {
    tail = buildTimeline(operation.effect, ops, visited, tail);
  }

  const node: TimeNode = { op: operation, order: 0, contract: new Map(), before: new Map(), after: new Map() };
  visited.set(opId, node);
  if (tail) { node.prev = tail; tail.next = node; }
  return node;
}

export function assignOrder(head: TimeNode) {
  let cur: TimeNode | undefined = head;
  let i = 1;
  while (cur) { cur.order = i++; cur = cur.next; }
}

export function findHead(node: TimeNode): TimeNode {
  while (node.prev) node = node.prev;
  return node;
}

function computeVregRanges(head: TimeNode, ops: Map<string, Operation>): Map<VRegId, { min: number; max: number }> {
  const ranges = new Map<VRegId, { min: number; max: number }>();
  let cur: TimeNode | undefined = head;
  while (cur) {
    for (const d of cur.op.defines) {
      const existing = ranges.get(d.vreg);
      if (!existing) ranges.set(d.vreg, { min: cur.order, max: cur.order });
    }
    for (const operand of cur.op.operands) {
      const vid = resolveOperandVreg(operand, ops);
      if (vid) {
        const existing = ranges.get(vid);
        if (existing) existing.max = Math.max(existing.max, cur.order);
      }
    }
    cur = cur.next;
  }
  return ranges;
}

export function propagateSlots(head: TimeNode, ops: Map<string, Operation>) {
  const vregRanges = computeVregRanges(head, ops);
  let cur: TimeNode | undefined = head;
  let prevAfter: SlotMap = emptySlotMap();

  while (cur) {
    const kind = opKind(cur.op.op);

    cur.contract = new Map();
    if (kind === "call" || kind === "return") {
      const vid = resolveOperandVreg(cur.op.operands[0], ops);
      if (vid) {
        cur.contract.set("w0", { kind: "preg", num: 0, width: 32, state: vid });
      }
    } else if (kind === "alu" || kind === "brif") {
      for (const operand of cur.op.operands) {
        if (operand.kind === "imm12") continue;
        const vid = resolveOperandVreg(operand, ops);
        if (!vid || vid.startsWith("c#")) continue;
        cur.contract.set(`need:${vid}`, { kind: "vreg", id: vid, width: 32, state: vid });
      }
    }

    cur.before = cloneSlotMap(prevAfter);
    for (const [k, slot] of cur.before) {
      if (slot.kind === "preg" && slot.state === false) {
        cur.before.set(k, { ...slot, state: true });
      }
    }
    for (const [k, slot] of [...cur.before]) {
      if (slot.kind === "vreg" || slot.kind === "const") {
        const vid = slotVreg(slot);
        const range = vid ? vregRanges.get(vid) : undefined;
        if (!range || cur.order > range.max) {
          cur.before.delete(k);
        }
      }
    }

    cur.after = cloneSlotMap(cur.before);
    applyMicroOps(cur.after, cur.op);

    prevAfter = cur.after;
    cur = cur.next;
  }
}

export function checkContracts(head: TimeNode) {
  let errors = 0;
  let cur: TimeNode | undefined = head;
  while (cur) {
    if (cur.contract.size > 0 && cur.prev) {
      const prevAfter = cur.prev.after;
      for (const [k, required] of cur.contract) {
        const reqVreg = slotVreg(required);
        if (!reqVreg) continue;
        if (k.startsWith("need:")) {
          let inPreg = false;
          for (const [, slot] of prevAfter) {
            if (slot.kind === "preg" && typeof slot.state === "string" && slot.state === reqVreg) {
              inPreg = true; break;
            }
          }
          if (!inPreg) {
            let where = `${C.dim}nowhere${C.reset}`;
            for (const [sk, slot] of prevAfter) {
              const sv = slotVreg(slot);
              if (sv === reqVreg) {
                if (slot.kind === "mem") where = `${C.blue}${sk}${C.reset} (needs load)`;
                else if (slot.kind === "vreg") where = `${C.red}vreg space${C.reset} (unallocated)`;
                break;
              }
            }
            console.log(`  ${C.red}CONTRACT${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: ${C.cyan}${reqVreg}${C.reset} needs a preg, found in ${where}`);
            errors++;
          }
        } else {
          const actual = prevAfter.get(k);
          const actVreg = actual ? slotVreg(actual) : null;
          if (reqVreg !== actVreg) {
            const actStr = actVreg ? `${C.red}${actVreg}${C.reset}` : `${C.dim}free${C.reset}`;
            console.log(`  ${C.red}CONTRACT${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: ${C.magenta}${k}${C.reset} needs ${C.cyan}${reqVreg}${C.reset} but has ${actStr}`);
            errors++;
          }
        }
      }
    }
    cur = cur.next;
  }
  if (errors === 0) {
    console.log(`\n${C.green}✓ All contracts satisfied${C.reset}`);
  } else {
    console.log(`\n${C.red}✗ ${errors} contract violation(s)${C.reset}`);
  }
}

export function checkScope(head: TimeNode, ops: Map<string, Operation>) {
  let errors = 0;
  let cur: TimeNode | undefined = head;
  while (cur) {
    const kind = opKind(cur.op.op);
    if (kind === "set_slot" || kind === "clear_slot") { cur = cur.next; continue; }
    for (const operand of cur.op.operands) {
      const vid = resolveOperandVreg(operand, ops);
      if (!vid) continue;
      let found = false;
      let inVreg = false;
      for (const [, slot] of cur.before) {
        const sv = slotVreg(slot);
        if (sv !== vid) continue;
        if (slot.kind === "vreg") { inVreg = true; continue; }
        found = true;
        break;
      }
      if (!found) {
        if (inVreg) {
          console.log(`  ${C.yellow}UNALLOC${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: operand ${C.cyan}${vid}${C.reset} is in vreg space (needs real slot)`);
        } else {
          console.log(`  ${C.red}ERROR${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: operand ${C.cyan}${vid}${C.reset} not in any slot`);
        }
        errors++;
      }
    }
    cur = cur.next;
  }
  if (errors === 0) {
    console.log(`\n${C.green}✓ All operands in scope${C.reset}`);
  } else {
    console.log(`\n${C.red}✗ ${errors} scope error(s)${C.reset}`);
  }
}
