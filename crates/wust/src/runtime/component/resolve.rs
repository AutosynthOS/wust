//! Resolve phase: apply static aliases and parse inner components.
//!
//! Takes a parsed `Component` and an ancestor chain, and produces a
//! `ResolvedComponent` where all outer aliases (self and ancestor) are
//! applied and inner components that are natively defined (not obtained
//! via outer alias) are recursively parsed and resolved.

use std::collections::HashSet;
use std::rc::Rc;

use crate::parse::types::*;

/// Resolve all static aliases in a component and parse inner components.
///
/// `ancestors[0]` is the direct parent, `ancestors[1]` is the grandparent,
/// etc. For top-level components, `ancestors` is empty.
///
/// # Algorithm
///
/// 1. Apply self aliases (count=1 outer aliases that reference the same
///    component's index space — used at the top level).
/// 2. Apply outer aliases from ancestors (count=N references ancestor N-1).
/// 3. Parse each natively-defined inner component and resolve it. Inner
///    components obtained via outer alias are left as `None` to avoid
///    infinite recursion — they will be resolved during instantiation
///    with the correct ancestor chain.
pub(crate) fn resolve(
    component: ParsedComponent,
    ancestors: &[&ParsedComponent],
) -> Result<ResolvedComponent, String> {
    let mut def = component;

    // 1. Apply self aliases only at the top level (no ancestors).
    //    For inner components, count=1 means "parent" and is handled by
    //    apply_outer_aliases.
    if ancestors.is_empty() {
        apply_self_aliases(&mut def);
    }

    // Collect inner component indices that are filled by outer aliases.
    // These should NOT be eagerly resolved — they reference ancestors
    // and would create infinite recursion if parsed and re-resolved.
    let mut aliased_component_slots: HashSet<usize> = HashSet::new();
    for alias in &def.outer_aliases {
        if alias.kind == OuterAliasKind::Component {
            aliased_component_slots.insert(alias.placeholder_index as usize);
        }
    }

    // 2. Apply outer aliases from ancestors.
    apply_outer_aliases(&mut def, ancestors);

    // 3. Parse and resolve inner components.
    let mut inner_ancestors: Vec<&ParsedComponent> = Vec::with_capacity(ancestors.len() + 1);
    inner_ancestors.push(&def);
    inner_ancestors.extend_from_slice(ancestors);

    let mut inner = Vec::with_capacity(def.inner_components.len());
    for (idx, bytes) in def.inner_components.iter().enumerate() {
        if bytes.is_empty() {
            // Empty placeholder — resolved during instantiation.
            inner.push(None);
        } else if aliased_component_slots.contains(&idx) {
            // Outer-alias slot — skip to avoid infinite recursion.
            // Will be resolved during instantiation with the correct
            // ancestor context.
            inner.push(None);
        } else {
            let parsed = super::ParsedComponent::from_bytes_no_validate(bytes)?;
            let resolved = resolve(parsed, &inner_ancestors)?;
            inner.push(Some(Rc::new(resolved)));
        }
    }

    Ok(ResolvedComponent { def, inner })
}

/// Apply self-referencing outer aliases (count=1 at top level).
///
/// For standalone components, `count=1` outer aliases reference earlier
/// items in the same component. This copies the source bytes into the
/// placeholder slots.
fn apply_self_aliases(component: &mut ParsedComponent) {
    for alias in &component.outer_aliases.clone() {
        if alias.count != 1 {
            continue;
        }
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            OuterAliasKind::CoreModule => {
                if let Some(bytes) = component.core_modules.get(src_idx).cloned() {
                    if let Some(slot) = component.core_modules.get_mut(dst_idx) {
                        *slot = bytes;
                    }
                }
            }
            OuterAliasKind::Component => {
                if let Some(bytes) = component.inner_components.get(src_idx).cloned() {
                    if let Some(slot) = component.inner_components.get_mut(dst_idx) {
                        *slot = bytes;
                    }
                }
            }
            OuterAliasKind::Type | OuterAliasKind::CoreType => {}
        }
    }
}

/// Apply outer aliases from an ancestor chain.
///
/// For an outer alias with count N, looks up ancestors[N-1] and copies
/// the source bytes into the child's placeholder slot.
fn apply_outer_aliases(child: &mut ParsedComponent, ancestors: &[&ParsedComponent]) {
    for alias in &child.outer_aliases.clone() {
        let ancestor_idx = (alias.count as usize).wrapping_sub(1);
        let Some(ancestor) = ancestors.get(ancestor_idx) else {
            continue;
        };
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            OuterAliasKind::CoreModule => {
                if let Some(bytes) = ancestor.core_modules.get(src_idx) {
                    if let Some(slot) = child.core_modules.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
            }
            OuterAliasKind::Component => {
                if let Some(bytes) = ancestor.inner_components.get(src_idx) {
                    if let Some(slot) = child.inner_components.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
            }
            OuterAliasKind::Type | OuterAliasKind::CoreType => {}
        }
    }
}
