//! Alias resolution for component instances.
//!
//! Handles resolution of outer aliases, aliased core modules, and aliased
//! inner components. Operates on `Component` (parsed data) and
//! `ComponentInstance` (live state) to copy bytes from parent/ancestor
//! scopes into the correct index slots.

use std::collections::HashMap;

use super::instance::ComponentInstance;
use super::types::*;

/// Resolve aliased items from component instance exports.
///
/// Generic helper that both `resolve_aliased_core_modules` and
/// `resolve_aliased_inner_components` delegate to. The differences
/// between those callers are parameterized as:
/// - `aliased_map`: which aliased map to iterate
/// - `get_child_exports`: extracts the exported map from a child instance
/// - `find_in_parsed`: finds bytes from a parsed inner component by name
/// - `resolved_map`: which resolved map to insert into
fn resolve_aliased_items(
    child_instances: &[ComponentInstance],
    component: &Component,
    parsed_inner_components: &HashMap<u32, Component>,
    aliased_map: &HashMap<u32, (u32, String)>,
    get_child_exports: impl Fn(&ComponentInstance) -> &HashMap<String, Vec<u8>>,
    find_in_parsed: impl Fn(&Component, &str) -> Option<Vec<u8>>,
    resolved_map: &mut HashMap<u32, Vec<u8>>,
) -> Result<(), String> {
    for (idx, (comp_inst_idx, export_name)) in aliased_map {
        let total_idx = *comp_inst_idx as usize;

        // Check if the child instance already has the exported item.
        if total_idx < child_instances.len() {
            if let Some(bytes) =
                get_child_exports(&child_instances[total_idx]).get(export_name.as_str())
            {
                if !bytes.is_empty() {
                    resolved_map.insert(*idx, bytes.clone());
                    continue;
                }
            }
        }

        // Fall back to parsed inner component lookup.
        let def_idx = if total_idx >= component.instance_import_count as usize {
            total_idx - component.instance_import_count as usize
        } else {
            continue;
        };

        if def_idx >= component.component_instances.len() {
            continue;
        }

        if let ComponentInstanceDef::Instantiate { component_index, .. } =
            &component.component_instances[def_idx]
        {
            if let Some(inner) = parsed_inner_components.get(component_index) {
                if let Some(bytes) = find_in_parsed(inner, export_name) {
                    resolved_map.insert(*idx, bytes);
                }
            }
        }
    }
    Ok(())
}

/// Resolve core modules that are aliased from component instance exports.
///
/// For each entry in `component.aliased_core_modules`, looks up the
/// referenced child component instance's exported_modules first, then
/// falls back to the parsed inner component's core_modules.
pub(super) fn resolve_aliased_core_modules(
    inst: &mut ComponentInstance,
    component: &Component,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<(), String> {
    resolve_aliased_items(
        &inst.child_instances,
        component,
        parsed_inner_components,
        &component.aliased_core_modules,
        |ci| &ci.exported_modules,
        |inner, name| {
            find_exported_bytes(inner, name, ComponentExternalKind::Module, &inner.core_modules)
        },
        &mut inst.resolved_modules,
    )
}

/// Look up inner component bytes by index, checking multiple sources.
///
/// Checks in order: resolved_components, inner_components, on-demand
/// alias resolution from component instance exports.
pub(super) fn get_inner_component_bytes(
    inst: &mut ComponentInstance,
    component: &Component,
    comp_idx: u32,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<Vec<u8>, String> {
    // Check already-resolved components.
    if let Some(bytes) = inst.resolved_components.get(&comp_idx) {
        if !bytes.is_empty() {
            return Ok(bytes.clone());
        }
    }

    // Check the component's inner_components list.
    if let Some(bytes) = component.inner_components.get(comp_idx as usize) {
        if !bytes.is_empty() {
            return Ok(bytes.clone());
        }
    }

    // Try on-demand alias resolution.
    if let Some(bytes) =
        resolve_component_alias_on_demand(inst, component, comp_idx, parsed_inner_components)?
    {
        return Ok(bytes);
    }

    Err(format!(
        "inner component index {} out of bounds (inner_components len={}, inner_comp_empty=[{}], resolved_components={:?}, aliased={:?}, imports={:?}, comp_instances={}, outer_aliases=[{}])",
        comp_idx,
        component.inner_components.len(),
        component
            .inner_components
            .iter()
            .enumerate()
            .map(|(i, b)| format!("{}:{}", i, b.is_empty()))
            .collect::<Vec<_>>()
            .join(","),
        inst.resolved_components.keys().collect::<Vec<_>>(),
        component
            .aliased_inner_components
            .keys()
            .collect::<Vec<_>>(),
        component
            .imports
            .iter()
            .map(|i| format!("{}:{:?}", i.name, i.kind))
            .collect::<Vec<_>>(),
        component.component_instances.len(),
        component
            .outer_aliases
            .iter()
            .map(|a| format!(
                "kind={:?} count={} index={} placeholder={}",
                a.kind, a.count, a.index, a.placeholder_index
            ))
            .collect::<Vec<_>>()
            .join(", "),
    ))
}

/// Try to resolve a single aliased inner component on demand.
///
/// If the component at `comp_idx` is aliased from a component instance
/// export, look up the referenced child instance's exported_components
/// first, then fall back to parsed inner component lookup.
fn resolve_component_alias_on_demand(
    inst: &mut ComponentInstance,
    component: &Component,
    comp_idx: u32,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<Option<Vec<u8>>, String> {
    let Some((comp_inst_idx, export_name)) = component.aliased_inner_components.get(&comp_idx)
    else {
        return Ok(None);
    };
    let total_idx = *comp_inst_idx as usize;

    // Check child instance's exported_components first.
    if total_idx < inst.child_instances.len() {
        if let Some(bytes) = inst.child_instances[total_idx]
            .exported_components
            .get(export_name.as_str())
        {
            if !bytes.is_empty() {
                inst.resolved_components.insert(comp_idx, bytes.clone());
                return Ok(Some(bytes.clone()));
            }
        }
    }

    let def_idx = if total_idx >= component.instance_import_count as usize {
        total_idx - component.instance_import_count as usize
    } else {
        return Ok(None);
    };
    if def_idx >= component.component_instances.len() {
        return Ok(None);
    }
    if let ComponentInstanceDef::Instantiate { component_index, .. } =
        &component.component_instances[def_idx]
    {
        if let Some(inner) = parsed_inner_components.get(component_index) {
            if let Some(comp_bytes) = find_exported_bytes(inner, export_name, ComponentExternalKind::Component, &inner.inner_components) {
                inst.resolved_components
                    .insert(comp_idx, comp_bytes.clone());
                return Ok(Some(comp_bytes));
            }
        }
    }
    Ok(None)
}

/// Look up a pre-resolved Component from a child instance's export.
///
/// If the component at `comp_idx` is aliased from a child instance's export,
/// and that child has a pre-resolved version (with correct outer aliases),
/// return it. This avoids re-parsing raw bytes in a different ancestor context
/// where outer aliases would resolve incorrectly.
pub(super) fn find_pre_resolved_from_alias(
    inst: &ComponentInstance,
    component: &Component,
    comp_idx: u32,
) -> Option<Component> {
    let (comp_inst_idx, export_name) = component.aliased_inner_components.get(&comp_idx)?;
    let total_idx = *comp_inst_idx as usize;
    if total_idx < inst.child_instances.len() {
        if let Some(pre) = inst.child_instances[total_idx]
            .exported_pre_resolved
            .get(export_name.as_str())
        {
            return Some(pre.clone());
        }
    }
    None
}

/// Resolve inner components that are aliased from component instance exports.
///
/// For each entry in `component.aliased_inner_components`, looks up the
/// referenced child component instance's exported_components first, then
/// falls back to the parsed inner component's inner_components.
pub(super) fn resolve_aliased_inner_components(
    inst: &mut ComponentInstance,
    component: &Component,
    parsed_inner_components: &HashMap<u32, Component>,
) -> Result<(), String> {
    resolve_aliased_items(
        &inst.child_instances,
        component,
        parsed_inner_components,
        &component.aliased_inner_components,
        |ci| &ci.exported_components,
        |inner, name| {
            find_exported_bytes(
                inner,
                name,
                ComponentExternalKind::Component,
                &inner.inner_components,
            )
        },
        &mut inst.resolved_components,
    )
}

/// Find bytes for a named export of a given kind from a parsed component.
///
/// Scans `component.exports` for an entry matching `export_name` and `kind`,
/// then indexes into `source_vec` to retrieve the corresponding bytes.
pub(super) fn find_exported_bytes(
    component: &Component,
    export_name: &str,
    kind: ComponentExternalKind,
    source_vec: &[Vec<u8>],
) -> Option<Vec<u8>> {
    for export in &component.exports {
        if export.name == export_name && export.kind == kind {
            return source_vec.get(export.index as usize).cloned();
        }
    }
    None
}

/// Resolve outer aliases in a child component using an ancestor chain.
///
/// `ancestors[0]` is the direct parent, `ancestors[1]` is the grandparent,
/// etc. For an outer alias with count N, we look up ancestors[N-1].
///
/// For count=1, copies from the direct parent. For count > 1, copies from
/// the appropriate ancestor, enabling deep nesting of outer aliases.
pub(super) fn resolve_outer_aliases(child: &mut Component, ancestors: &[&Component]) {
    for alias in &child.outer_aliases.clone() {
        let ancestor_idx = (alias.count as usize).wrapping_sub(1);
        let Some(ancestor) = ancestors.get(ancestor_idx) else {
            continue;
        };
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index as usize;
        match alias.kind {
            super::types::OuterAliasKind::CoreModule => {
                if let Some(bytes) = ancestor.core_modules.get(src_idx) {
                    if let Some(slot) = child.core_modules.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
            }
            super::types::OuterAliasKind::Component => {
                if let Some(bytes) = ancestor.inner_components.get(src_idx) {
                    if let Some(slot) = child.inner_components.get_mut(dst_idx) {
                        *slot = bytes.clone();
                    }
                }
                // Pre-resolve the obtained inner component so its outer
                // aliases are resolved against the correct (defining)
                // ancestor chain.  Without this, passing the component as
                // an arg to a different parent would re-resolve outer
                // aliases against the wrong context, causing infinite
                // recursion or incorrect component substitution.
                if let Some(pre) = ancestor.pre_resolved_inner.get(&(src_idx as u32)) {
                    child.pre_resolved_inner.insert(dst_idx as u32, pre.clone());
                } else if let Some(bytes) = ancestor.inner_components.get(src_idx) {
                    if !bytes.is_empty() {
                        if let Ok(mut parsed) = super::Component::from_bytes_no_validate(bytes) {
                            // The inner component was defined inside
                            // `ancestor`, so its count=1 aliases reference
                            // ancestor's own context = ancestors[ancestor_idx..].
                            resolve_outer_aliases(&mut parsed, &ancestors[ancestor_idx..]);
                            child
                                .pre_resolved_inner
                                .insert(dst_idx as u32, Box::new(parsed));
                        }
                    }
                }
            }
            super::types::OuterAliasKind::Type | super::types::OuterAliasKind::CoreType => {
                // Type aliases don't need runtime resolution.
            }
        }
    }
}

/// Recursively pre-resolve inner components' outer aliases.
///
/// After resolving a component's own outer aliases, its inner components may
/// still have unresolved outer aliases that reference ancestors further up the
/// chain. This function parses each inner component and resolves its outer
/// aliases using the correct ancestor chain.
pub(super) fn pre_resolve_inner_components(
    component: &mut Component,
    parent_ancestors: &[&Component],
) {
    for idx in 0..component.inner_components.len() {
        let bytes = &component.inner_components[idx];
        if bytes.is_empty() {
            continue;
        }
        if component.pre_resolved_inner.contains_key(&(idx as u32)) {
            continue;
        }
        let Ok(mut parsed) = super::Component::from_bytes_no_validate(bytes) else {
            continue;
        };
        if parsed.outer_aliases.is_empty() && !has_deep_outer_aliases(&parsed) {
            continue;
        }
        let mut inner_ancestors: Vec<&Component> = Vec::with_capacity(parent_ancestors.len() + 1);
        inner_ancestors.push(component);
        inner_ancestors.extend_from_slice(parent_ancestors);
        resolve_outer_aliases(&mut parsed, &inner_ancestors);
        pre_resolve_inner_components(&mut parsed, &inner_ancestors);
        component
            .pre_resolved_inner
            .insert(idx as u32, Box::new(parsed));
    }
}

/// Check whether any inner component has outer aliases that need resolution.
pub(super) fn has_deep_outer_aliases(component: &Component) -> bool {
    for bytes in &component.inner_components {
        if bytes.is_empty() {
            continue;
        }
        if let Ok(parsed) = super::Component::from_bytes_no_validate(bytes) {
            if !parsed.outer_aliases.is_empty() {
                return true;
            }
            if has_deep_outer_aliases(&parsed) {
                return true;
            }
        }
    }
    false
}

/// Resolve self-referencing outer aliases in a top-level component.
///
/// When a component uses `alias outer $self $item`, it creates an outer alias
/// with count=1 that references an item in the same component. Since there is
/// no parent, we resolve these by looking up the source index in the component's
/// own index space and storing the result in `resolved_modules` / `resolved_components`.
pub(super) fn resolve_self_aliases(inst: &mut ComponentInstance, component: &Component) {
    for alias in &component.outer_aliases {
        if alias.count != 0 {
            continue;
        }
        let src_idx = alias.index as usize;
        let dst_idx = alias.placeholder_index;
        match alias.kind {
            super::types::OuterAliasKind::CoreModule => {
                if let Some(bytes) = component.core_modules.get(src_idx) {
                    if !bytes.is_empty() {
                        inst.resolved_modules.insert(dst_idx, bytes.clone());
                    }
                }
            }
            super::types::OuterAliasKind::Component => {
                if let Some(bytes) = component.inner_components.get(src_idx) {
                    if !bytes.is_empty() {
                        inst.resolved_components.insert(dst_idx, bytes.clone());
                    }
                }
            }
            super::types::OuterAliasKind::Type | super::types::OuterAliasKind::CoreType => {}
        }
    }
}

