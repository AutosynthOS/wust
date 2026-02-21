//! Component model runtime.
//!
//! Implements instantiation and invocation of WebAssembly components.
//!
//! - [`link`] — alias and export resolution (core func → core instance export)
//! - [`instance`] — live state, instantiation, and export resolution

mod link;
pub(crate) mod instance;
mod trampoline;
mod imports;

pub use crate::parse::types::{ComponentArg, ComponentImportDef, ComponentImportKind, ComponentResultType, ComponentValue};
pub(crate) use crate::parse::types::StringEncoding;
pub use instance::ComponentInstance;
pub(crate) use instance::CoreInstance;
