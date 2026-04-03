import type { Operation, TimeNode, SlotMap, VRegId } from "./types";
import { opKind, slotVreg, cloneSlotMap, emptySlotMap, applyMicroOps, resolveOperandVreg } from "./slots";
import { C } from "./format";

// --- Building ---

// Build TimeNode objects for all ops reachable from roots.
// Does NOT set prev — that's done by topoSort.
export function buildNodes(
  roots: string[],
  ops: Map<string, Operation>,
): Map<string, TimeNode> {
  const visited = new Map<string, TimeNode>();
  function build(opId: string) {
    if (visited.has(opId)) return;
    const operation = ops.get(opId);
    if (!operation) throw new Error(`unresolved op: ${opId}`);
    const node: TimeNode = {
      op: operation, order: 0,
      inputs: new Map(), results: new Map(),
    };
    visited.set(opId, node);
    for (const operand of operation.operands) {
      if (operand.kind === "op") build(operand.op);
    }
    if (operation.effect) build(operation.effect);
  }
  for (const r of roots) build(r);
  return visited;
}

// Topologically sort nodes and set prev pointers.
// Every node's prev = the immediately preceding node in the total order.
// This guarantees all predecessors (operands + effects) are in the prev chain.
export function topoSortAndLink(visited: Map<string, TimeNode>, ops: Map<string, Operation>): TimeNode[] {
  const sorted: TimeNode[] = [];
  const seen = new Set<string>();
  function visit(id: string) {
    if (seen.has(id)) return;
    seen.add(id);
    const op = ops.get(id);
    if (!op) return;
    for (const operand of op.operands) {
      if (operand.kind === "op") visit(operand.op);
    }
    if (op.effect) visit(op.effect);
    const node = visited.get(id);
    if (node) sorted.push(node);
  }
  for (const id of visited.keys()) visit(id);

  // Set prev = previous node in the sorted order
  for (let i = 0; i < sorted.length; i++) {
    sorted[i].prev = i > 0 ? sorted[i - 1] : undefined;
  }
  return sorted;
}

// Collect all nodes from a visited map by walking prev chains.
// Returns nodes in dependency order (predecessors before successors).
export function collectNodes(visited: Map<string, TimeNode>): TimeNode[] {
  const seen = new Set<TimeNode>();
  const result: TimeNode[] = [];
  function walk(n: TimeNode) {
    if (seen.has(n)) return;
    seen.add(n);
    if (n.prev) walk(n.prev);
    result.push(n);
  }
  for (const n of visited.values()) walk(n);
  return result;
}

// Assign sequential order numbers.
export function assignOrder(nodes: TimeNode[]) {
  for (let i = 0; i < nodes.length; i++) {
    nodes[i].order = i + 1;
  }
}

// --- Slot state computation (upward exploration) ---

// Compute the slot state just before a node by walking up via prev,
// collecting the path, then replaying micro-ops forward.
export function getSlotsBefore(node: TimeNode): SlotMap {
  const path: TimeNode[] = [];
  let cur: TimeNode | undefined = node.prev;
  while (cur) { path.unshift(cur); cur = cur.prev; }

  let slots = emptySlotMap();
  for (const n of path) {
    // Unblock pregs from previous call
    for (const [k, slot] of slots) {
      if (slot.kind === "preg" && slot.state === false) {
        slots.set(k, { ...slot, state: true });
      }
    }
    applyMicroOps(slots, n.op);
  }

  // Final unblock for the target node's perspective
  for (const [k, slot] of slots) {
    if (slot.kind === "preg" && slot.state === false) {
      slots.set(k, { ...slot, state: true });
    }
  }
  return slots;
}

// Compute inputs + results for a single node.
export function computeNodeState(node: TimeNode, ops: Map<string, Operation>) {
  const kind = opKind(node.op.op);
  const before = getSlotsBefore(node);

  // Inputs: what this op requires to execute
  node.inputs = new Map();
  if (kind === "call" || kind === "return") {
    const vid = resolveOperandVreg(node.op.operands[0], ops);
    if (vid) {
      node.inputs.set("w0", { kind: "preg", num: 0, width: 32, state: vid });
    }
  } else if (kind === "alu" || kind === "brif") {
    for (const operand of node.op.operands) {
      if (operand.kind === "imm12") continue;
      const vid = resolveOperandVreg(operand, ops);
      if (!vid || vid.startsWith("c#")) continue;
      node.inputs.set(`need:${vid}`, { kind: "vreg", id: vid, width: 32, state: vid });
    }
  } else if (kind === "set_slot") {
    const vrefOp = node.op.operands[1];
    if (vrefOp) {
      const vid = resolveOperandVreg(vrefOp, ops);
      if (vid && !vid.startsWith("c#")) {
        node.inputs.set(`need:${vid}`, { kind: "vreg", id: vid, width: 32, state: vid });
      }
    }
  }

  // Results: slot state after this op executes
  node.results = cloneSlotMap(before);
  applyMicroOps(node.results, node.op);
}

// Compute state for all nodes.
export function computeAllStates(nodes: TimeNode[], ops: Map<string, Operation>) {
  for (const node of nodes) computeNodeState(node, ops);
}

// --- Block detection ---

export interface Block {
  label: string;
  nodes: TimeNode[];
}

// Detect blocks by reachability from each terminal.
// Walks ALL dependency edges (operands + effects), not just prev.
// Shared = reachable from all terminals = Entry.
// Exclusive = reachable from one terminal only = Case(N).
export function detectBlocks(nodes: TimeNode[], terminals: TimeNode[], ops: Map<string, Operation>): Block[] {
  const nodeMap = new Map<string, TimeNode>();
  for (const n of nodes) nodeMap.set(n.op.id, n);

  // Walk all deps from each terminal
  const reachable: Set<TimeNode>[] = terminals.map(() => new Set());
  for (let i = 0; i < terminals.length; i++) {
    const seen = new Set<string>();
    function walk(id: string) {
      if (seen.has(id)) return;
      seen.add(id);
      const node = nodeMap.get(id);
      if (node) reachable[i].add(node);
      const op = ops.get(id);
      if (!op) return;
      for (const operand of op.operands) {
        if (operand.kind === "op") walk(operand.op);
      }
      if (op.effect) walk(op.effect);
    }
    walk(terminals[i].op.id);
  }

  // Classify each node
  const entry: TimeNode[] = [];
  const branches: TimeNode[][] = terminals.map(() => []);
  for (const n of nodes) {
    const inAll = reachable.every(s => s.has(n));
    if (inAll) {
      entry.push(n);
    } else {
      for (let i = 0; i < terminals.length; i++) {
        if (reachable[i].has(n)) { branches[i].push(n); break; }
      }
    }
  }

  const blocks: Block[] = [];
  if (entry.length > 0) blocks.push({ label: "Entry", nodes: entry });
  for (let i = 0; i < branches.length; i++) {
    if (branches[i].length > 0) {
      blocks.push({ label: `Case(${i})`, nodes: branches[i] });
    }
  }
  return blocks;
}

// --- Checkers ---

export function checkContracts(nodes: TimeNode[]) {
  let errors = 0;
  for (const cur of nodes) {
    if (cur.inputs.size === 0 || !cur.prev) continue;
    const prevResults = cur.prev.results;
    for (const [k, required] of cur.inputs) {
      const reqVreg = slotVreg(required);
      if (!reqVreg) continue;
      if (k.startsWith("need:")) {
        let inPreg = false;
        for (const [, slot] of prevResults) {
          if (slot.kind === "preg" && typeof slot.state === "string" && slot.state === reqVreg) {
            inPreg = true; break;
          }
        }
        if (!inPreg) {
          let where = `${C.dim}nowhere${C.reset}`;
          for (const [sk, slot] of prevResults) {
            if (slotVreg(slot) === reqVreg) {
              if (slot.kind === "mem") where = `${C.blue}${sk}${C.reset} (needs load)`;
              else if (slot.kind === "vreg") where = `${C.red}vreg space${C.reset} (unallocated)`;
              break;
            }
          }
          console.log(`  ${C.red}CONTRACT${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: ${C.cyan}${reqVreg}${C.reset} needs a preg, found in ${where}`);
          errors++;
        }
      } else {
        const actual = prevResults.get(k);
        const actVreg = actual ? slotVreg(actual) : null;
        if (reqVreg !== actVreg) {
          const actStr = actVreg ? `${C.red}${actVreg}${C.reset}` : `${C.dim}free${C.reset}`;
          console.log(`  ${C.red}CONTRACT${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: ${C.magenta}${k}${C.reset} needs ${C.cyan}${reqVreg}${C.reset} but has ${actStr}`);
          errors++;
        }
      }
    }
  }
  if (errors === 0) console.log(`\n${C.green}✓ All contracts satisfied${C.reset}`);
  else console.log(`\n${C.red}✗ ${errors} contract violation(s)${C.reset}`);
}

export function checkScope(nodes: TimeNode[], ops: Map<string, Operation>) {
  let errors = 0;
  for (const cur of nodes) {
    const before = getSlotsBefore(cur);
    for (const operand of cur.op.operands) {
      const vid = resolveOperandVreg(operand, ops);
      if (!vid) continue;
      let found = false;
      let inVreg = false;
      for (const [, slot] of before) {
        if (slotVreg(slot) !== vid) continue;
        if (slot.kind === "vreg") { inVreg = true; continue; }
        found = true; break;
      }
      if (!found) {
        if (inVreg) console.log(`  ${C.yellow}UNALLOC${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: operand ${C.cyan}${vid}${C.reset} is in vreg space (needs real slot)`);
        else console.log(`  ${C.red}ERROR${C.reset} [${cur.order}] ${C.dim}${cur.op.id}${C.reset}: operand ${C.cyan}${vid}${C.reset} not in any slot`);
        errors++;
      }
    }
  }
  if (errors === 0) console.log(`\n${C.green}✓ All operands in scope${C.reset}`);
  else console.log(`\n${C.red}✗ ${errors} scope error(s)${C.reset}`);
}
