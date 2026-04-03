# Grid-Based Register Allocation

## The Core Idea

Register allocation is traditionally modeled as graph coloring — build an
interference graph, color it with K colors (registers), spill when you can't.
This is NP-hard in the general case and requires separate passes for scheduling,
spilling, coalescing, rematerialization, and live range splitting.

**We propose a different model: register allocation as pathfinding on a 2D grid.**

Every value in a program needs to travel from its definition to its last use.
The "space" it travels through has different lanes — physical registers (fast),
memory slots (slow), and constant immediates (free). The allocator finds the
cheapest path for each value through this space, simultaneously solving
scheduling, spilling, coalescing, and instruction ordering.

---

## The Grid

```
             time (instruction order) →

         ┌──────┬──────┬──────┬──────┬──────┬──────┬──────┐
   c:#N  │ free │ free │ free │ free │ free │ free │ free │  const space
         ├──────┼──────┼──────┼──────┼──────┼──────┼──────┤  (always free,
   c:#1  │ free │ free │ free │ free │ free │ free │ free │   immune to
         ├──────┼──────┼──────┼──────┼──────╪══════╪──────┤   walls)
   w0    │  v0  │  v0  │  v0  │  v1  │  v1  ║CALL  ║  v3  │
         ├──────┼──────┼──────┼──────┼──────╪══════╪──────┤  register space
   w1    │      │      │      │      │      ║CALL  ║      │  (fast, limited,
         ├──────┼──────┼──────┼──────┼──────╪══════╪──────┤   blocked by
   w2    │      │      │      │      │      ║CALL  ║      │   call walls)
         ├──────┼──────┼──────┼──────┼──────┼──────┼──────┤
   m0    │      │      │ [v0] │ [v0] │ [v0] │ [v0] │ [v0] │  memory space
         ├──────┼──────┼──────┼──────┼──────┼──────┼──────┤  (slow, unlimited,
   m1    │      │      │      │      │ [v1] │ [v1] │      │   crosses all
         ├──────┼──────┼──────┼──────┼──────┼──────┼──────┤   walls)
   m2    │      │      │      │      │      │      │      │
         └──────┴──────┴──────┴──────┴──────┴──────┴──────┘
           def    sub    store  call   store  CALL   load
           v0     v1     v0→m0  fib    v1→m1  fib    v0←m0
```

### Axes

- **X axis (horizontal):** Time / instruction order. Each column is an
  instruction or an available insertion point for spills/moves.
- **Y axis (vertical):** Slot space. Physical registers at the top (cheap),
  memory slots in the middle (expensive), constant immediates at the bottom
  (free).

### Slot Types

| Slot Type | Cost to Stay | Cost to Enter | Blocked by Calls | Capacity |
|-----------|-------------|---------------|-------------------|----------|
| Register  | 0           | mov = ~1      | Yes (wall)        | Fixed (28 on ARM64) |
| Memory    | 0           | store = ~3-4  | No                | Unlimited |
| Const     | 0           | 0             | No                | Unlimited |

### Movement Costs

Every horizontal move within the same slot is free (the value stays put).
Every vertical move is a real instruction with a cost:

| Movement          | Instruction     | Cost |
|-------------------|-----------------|------|
| reg → reg         | mov             | ~1   |
| reg → mem         | str (store)     | ~3   |
| mem → reg         | ldr (load)      | ~4   |
| const → reg       | movz (materialize) | ~1 |
| const → UImm12    | fold (free)     | 0    |
| mem → mem (x86)   | mov [a], [b]    | ~6   |
| mem → ALU (x86)   | add reg, [mem]  | ~5   |

---

## Walls

### Call Walls

A function call creates a vertical wall that spans all register slots.
Values cannot pass through register space across a call — they must
detour through memory:

```
         before call    CALL     after call
   w0:  ════v0════════╪═════╪════v3════════
   w1:  ══════════════╪═════╪══════════════
   m0:           ╔════╪═════╪════╗
                 ║    ╪ v0  ╪    ║
                store ╪     ╪  load
```

Value v0 starts in w0, hits the call wall, detours through m0 (store
before, load after), continues in w0 as v3.

### Partial Walls (Data-Driven Calling Conventions)

If we compile leaf functions first, we know exactly which registers
they touch. The wall narrows to only those registers:

```
Leaf fib() only touches w0, w1:

   w0:  ══════════╪═══╪══════════   blocked
   w1:  ══════════╪═══╪══════════   blocked
   w2:  ═══════════════════════════  OPEN — passes through free
   w3:  ═══════════════════════════  OPEN
```

Values in w2+ survive the call for free. Fewer spills, faster code.
Standard calling conventions are worst-case assumptions. Data-driven
conventions are exact knowledge.

### Instruction Walls

A register-to-register instruction (like `sub w0, w0, #1`) creates a
small wall in its destination register's row. If another value occupies
that row, it must move:

```
   w0:  ════v0════╪═v1═══════════   v0 evicted, v1 takes w0
                  ↓
   w1:  ══════════╪═══════════════   v0 could move here (mov cost)
   m0:  ══════════╪═══════════════   or here (store cost)
```

---

## Branches and Phi Nodes

A branch forks the grid into parallel timelines:

```
                BrIf
                 │
         ┌───────┴───────┐
         │               │
       Case(0)         Case(1)
                         │
   w0:   ══A═══     ══B═══C═══D═══
   w1:               ══E═══
   m0:                     ══F══
         │               │
         └───────┬───────┘
                 │
               merge
```

Each timeline has its own walls, paths, and costs. They run
independently.

**Phi nodes are merge constraints.** At the merge point, values from
both timelines must arrive at the same slot:

```
Case(0): result in w0
Case(1): result in w1
Merge:   phi requires same slot → insert mov on one path
```

The pathfinder sees: "at the merge column, both paths must converge
to the same Y position." If they don't, a move is inserted on the
cheaper path. No special phi-elimination pass — it falls out of the
cost model.

---

## What Falls Out of the Cost Model

Every traditional compiler optimization becomes a cost gradient that
the pathfinder follows naturally:

### Spill/Reload
A value hits a call wall → must detour through memory. The pathfinder
routes it through the cheapest memory slot. No separate spill pass.

### Coalescing
If a mov's source and destination are the same register → cost 0. The
pathfinder naturally avoids unnecessary moves by keeping values in the
same slot.

### Live Range Splitting
A value under high register pressure dips to memory mid-range, freeing
a register for something hotter, then reloads later. The pathfinder
finds this route when the blocking cost exceeds the store+load cost.

### Rematerialization
A constant or cheap-to-compute value doesn't need a continuous path.
It can be re-created at any point:

```
   w0:  ═══v0═══          ═══v0═══    (rematerialize, cost = 1)
              (gap — register freed for other values)
```

For constants: rematerialization cost ≈ 1 (movz). For pure ALU ops
whose operands are still live: cost = instruction latency. The
pathfinder picks rematerialization when it's cheaper than keeping the
value alive through high-pressure regions.

### Loop-Invariant Code Motion
Loop back-edges multiply costs. If a value is in memory inside a loop:

```
Loop body (×1000 iterations):
   m0: cost per iteration = load + store = ~8
   w0: cost per iteration = 0

Total: m0 = 8000, w0 = 0
```

The pathfinder loads the value into a register BEFORE the loop (cost 4
once) to avoid paying 8000 inside. LICM falls out of the cost
function.

### Register Promotion
A frequently-accessed memory location gets "promoted" to a register
for a hot region. Just the pathfinder seeing that the register path
is cheaper over many accesses.

### Immediate Folding
A constant that fits in UImm12 travels in const space for free and
"enters" an ALU instruction at zero cost. A constant that doesn't fit
must materialize into a register (cost 1). The pathfinder picks the
cheapest option based on the instruction's operand constraints.

### Instruction Scheduling
The X axis IS the instruction order. Instructions can reorder as long
as operands flow downward. The pathfinder places each instruction at
the position that minimizes total path cost — which naturally accounts
for register pressure, latency hiding, and dependency chains.

---

## Machine Cost Tables

The entire backend is parameterized by a cost table:

```rust
trait MachineCosts {
    fn reg_to_reg(&self) -> u32;
    fn reg_to_mem(&self, slot: &SlotRef) -> u32;
    fn mem_to_reg(&self, slot: &SlotRef) -> u32;
    fn const_to_reg(&self, val: i64) -> u32;
    fn mem_to_mem(&self) -> Option<u32>;        // x86 only
    fn mem_to_alu(&self) -> Option<u32>;        // x86 memory operands
    fn adjacent_store_discount(&self) -> u32;   // LDP/STP on ARM64
    fn loop_multiplier(&self, depth: u32) -> u32;
}
```

Different chips, different costs, different code:

- **ARM64 Cortex-A72:** store=3, load=4, mov=1
- **Apple M4:** store=2, load=3 (better write buffer)
- **x86-64:** memory ALU operands available, sometimes cheaper than load+op
- **RISC-V:** similar to ARM64, different register count

Same algorithm. Swap the cost table. The pathfinder produces
architecture-optimal code.

---

## Complexity

Register allocation by graph coloring is NP-hard (Chaitin 1981).
Multi-agent pathfinding on a grid is also NP-hard in the general case.

**But real programs aren't the general case:**

- WASM functions are small (10-200 opcodes)
- SSA form produces structured interference (chordal graphs)
- Call walls partition the problem into independent chunks
- The register set is fixed and small (~28 GPRs on ARM64)
- Greedy pathfinding with good heuristics is near-optimal in practice

Modern SAT solvers handle millions of variables because real instances
have structure. Similarly, the grid model exploits the structure of
real programs — call boundaries create natural partitions, loops have
regular patterns, and most live ranges are short.

For a WASM JIT compiling small functions, the grid is tiny. Even
brute-force might be feasible. Greedy A* with cost heuristics is
likely sufficient for production quality.

---

## Comparison with Existing Approaches

| Approach | Scheduling | Allocation | Spilling | Coalescing | LICM | Folding |
|----------|-----------|------------|----------|------------|------|---------|
| Traditional (LLVM) | Separate pass | Graph coloring | Separate | Separate | Separate | Separate |
| Linear Scan | Fixed order | Greedy scan | Integrated | Limited | No | No |
| PBQP | Separate | Cost matrix | Integrated | Integrated | No | No |
| Unison | Combined | Combined | Combined | Combined | No | No |
| **Grid Pathfinding** | **Unified** | **Unified** | **Unified** | **Unified** | **Unified** | **Unified** |

The grid model unifies ALL of these into one optimization:
pathfinding with machine-specific cost tables.

---

## Implementation Sketch

1. **Build the IR graph** — hash-interned nodes with data edges and
   effect chains. SetSlot/ClearSlot track memory positions.

2. **Construct the grid topology** — X axis from the effect chain
   (execution order), Y axis from the machine's slot space (registers +
   memory + constants). Call walls from effect chain analysis.

3. **Place fixed points** — function params (entry in specific regs),
   call arguments (must reach specific regs), return values (must reach
   w0), instruction operand constraints.

4. **Run the pathfinder** — for each value, find the cheapest path from
   define to last use, respecting walls and slot constraints. Greedy or
   A* with machine cost heuristics.

5. **Emit instructions** — the grid solution directly maps to machine
   code. Horizontal movement = value stays put. Vertical movement =
   mov/store/load/materialize. The X axis gives instruction order.

---

## Open Questions

- **Optimal vs greedy:** Is greedy pathfinding sufficient, or do we need
  backtracking / global optimization? For small WASM functions, greedy
  is likely fine.

- **Loop cost estimation:** How to estimate iteration counts for loop
  multipliers? Static heuristics, profile-guided, or fixed multiplier?

- **Branch probability:** Hot vs cold paths should have different cost
  weights. How to integrate branch prediction into the grid?

- **Multi-value pathfinding interactions:** Routing one value affects
  others. Process in priority order (most constrained first)? Iterate
  to convergence?

- **Incremental updates:** When a path changes, which other paths need
  re-routing? Can we do local updates instead of global re-solve?
