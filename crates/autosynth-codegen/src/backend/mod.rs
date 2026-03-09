//! Backend module — legacy code, being replaced by autosynth-backend crate.
//!
//! The old aarch64 backend and `BackendEmitter` trait have been superseded
//! by the `autosynth-backend` / `autosynth-backend-aarch64` crates and the
//! orchestrator pipeline. This module is retained only for the `fib_lower`
//! test which still uses the old disasm pipeline.
