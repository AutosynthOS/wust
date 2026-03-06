# `autosynth-codegen`

A generic, cross-architecture code generation library. Originally designed for compiling WebAssembly to native code in `wust`, but architecture- and domain-agnostic by design.

## Design Goals

- **Backend-agnostic.** A single IR compiles to any supported architecture through a `Backend` trait. Adding a new target means implementing the trait — no changes to the IR, register allocator, or compilation pipeline.

- **Agnostic call ABIs.** Call conventions are caller-defined, not baked into the codegen. The caller decides how arguments are passed, how frames are laid out, and how results are returned.

- **Customizable register allocation.** Global/reserved registers are declared by the caller, not hardcoded. Scratch register pools, spill slot policies, and eviction strategies are configurable per-compilation.

- **Hot-code reloading and JIT compilation.** Functions compile independently into a shared code buffer. Patch points enable lazy compilation, hot code swapping, and deferred cold-path emission — recompile one function without touching the rest.

- **First-class observability.** Annotations, markers, and labels are part of the backend interface — not bolted on after the fact. Every emitted instruction can carry a human-readable label. Disassembly rendering with control-flow visualization is built-in.

- **Zero domain assumptions.** The crate knows nothing about wasm, fuel, suspend/resume, frame layouts, or any specific runtime. It compiles an IR. What that code *means* is the caller's problem.

- **Caller-driven emission.** The codegen provides building blocks — the caller drives the loop. No fixed pipeline. The caller can interleave its own instructions (fuel checks, frame management, cold stubs) with lowered IR output.

- **Patchable code.** Branch targets and call sites return `PatchPoint`s that can be rewritten after emission. This is the mechanism behind hot swapping, lazy compilation, and deferred cold paths.

- **Per-function granularity.** Functions are the unit of compilation. A jump table at the start of the code buffer dispatches calls via patchable entries — enabling per-function recompilation without relinking.

- **Width-aware codegen.** Loads, stores, moves, and spills are type-width-aware (32-bit vs 64-bit). No wasted memory from 8-byte spills of 4-byte values.

- **Stack-aware codegen.** Stack frames are laid out in a type-width-aware way, allowing the consumer to determine stack layout, alignment, offsets and virtual register slot locations at compile time.

- **Suspend/Resume-aware codegen.** The consumer can implement frontend-specific suspend/resume semantics and block types to allow for universal stack-based suspend/restore functionalities into consumer applications.
