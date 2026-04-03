use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefPure};
use std::rc::Rc;

use crate::state::VRegState;

/// The interned node — holds the precomputed hash, the state, and a
/// human-readable ID. Comparison and hashing use the precomputed hash
/// for O(1) identity checks.
#[derive(Clone)]
pub struct Node {
    pub hash: u64,
    pub state: VRegState,
    pub id: u32,
}

/// A reference-counted handle to an interned node.
///
/// Operands hold strong NodeRefs → the tree from roots keeps live nodes
/// alive. Dead subtrees (unreferenced by any root) drop automatically.
///
/// Equality and hashing are based on the structural hash, not pointer
/// identity — two NodeRefs with the same hash are the same value (CSE).
#[derive(Clone)]
pub struct NodeRef(pub Rc<Node>);

impl NodeRef {
    pub fn hash_val(&self) -> u64 {
        self.0.hash
    }

    pub fn id(&self) -> u32 {
        self.0.id
    }

    pub fn state(&self) -> &VRegState {
        &self.0.state
    }
}

impl PartialEq for NodeRef {
    fn eq(&self, other: &Self) -> bool {
        self.0.hash == other.0.hash
    }
}

impl Eq for NodeRef {}

impl PartialOrd for NodeRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NodeRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.hash.cmp(&other.0.hash)
    }
}

impl Hash for NodeRef {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.0.hash.hash(hasher);
    }
}

impl Deref for NodeRef {
    type Target = Node;

    fn deref(&self) -> &Node {
        &self.0
    }
}

impl fmt::Debug for NodeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0.id)
    }
}
