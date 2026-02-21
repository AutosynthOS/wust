//! Component binary parsing phase.
//!
//! Transforms raw component bytes into a [`ParsedComponent`] — a structured
//! representation of all sections, ready for the resolve phase.

mod parse;
pub(crate) mod types;

pub(crate) use parse::parse_and_validate;
