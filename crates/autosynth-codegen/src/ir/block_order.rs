use std::collections::{BTreeMap, HashSet};
use autosynth_ir::BlockId;

/// Compute reverse postorder of the block graph.
///
/// Visits else before then for br_if blocks so the fall-through
/// target is placed immediately after the branch.
pub fn rpo(
    entry: BlockId,
    successors: &BTreeMap<BlockId, Vec<BlockId>>,
) -> Vec<BlockId> {
    let mut visited = HashSet::new();
    let mut postorder = Vec::new();
    dfs(entry, successors, &mut visited, &mut postorder);
    postorder.reverse();
    postorder
}

fn dfs(
    id: BlockId,
    successors: &BTreeMap<BlockId, Vec<BlockId>>,
    visited: &mut HashSet<BlockId>,
    postorder: &mut Vec<BlockId>,
) {
    if !visited.insert(id) {
        return;
    }
    if let Some(succs) = successors.get(&id) {
        for &succ in succs.iter().rev() {
            dfs(succ, successors, visited, postorder);
        }
    }
    postorder.push(id);
}
