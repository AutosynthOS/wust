//! Component binary parsing phase.
//!
//! Transforms raw component bytes into a [`ParsedComponent`] — a structured
//! representation of all sections, ready for the resolve phase.

pub(crate) mod types;
mod parse;

pub(crate) use parse::parse_component_sections;
