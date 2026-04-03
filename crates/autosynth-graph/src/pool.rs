use std::collections::HashMap;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::rc::{Rc, Weak};

use crate::node::{Node, NodeRef};
use crate::op::{Op, Operand, VCode};
use crate::state::{Define, VRegState};
use autosynth_isa::Width;

/// Intern pool — dedup cache backed by weak refs.
///
/// Nodes are Rc-backed. The pool stores Weak refs for CSE dedup.
/// Live nodes are kept alive by strong refs from root trees.
/// Dead nodes (unreferenced) have their weak refs expire naturally.
pub struct Pool {
    pub cache: HashMap<u64, Weak<Node>>,
    next_id: u32,
}

impl Pool {
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
            next_id: 0,
        }
    }

    /// Intern a VRegState. Returns a NodeRef.
    ///
    /// If a structurally identical node is still alive, returns a clone
    /// of the existing Rc (CSE). Otherwise creates a new node.
    pub fn intern(&mut self, state: VRegState) -> NodeRef {
        let hash = Self::hash_state(&state);

        // Check for existing live node with same hash (CSE)
        if let Some(weak) = self.cache.get(&hash) {
            if let Some(strong) = weak.upgrade() {
                return NodeRef(strong);
            }
        }

        let id = self.next_id;
        self.next_id += 1;
        let node = Rc::new(Node { hash, state, id });
        self.cache.insert(hash, Rc::downgrade(&node));
        NodeRef(node)
    }

    /// Define a constant value.
    pub fn define_const(&mut self, val: i64, width: Width) -> NodeRef {
        self.intern(VRegState {
            r#const: Some(val),
            ..VRegState::new(width)
        })
    }

    /// Define a parameter arriving in a PReg.
    pub fn define_param(&mut self, preg: autosynth_isa::PReg, width: Width) -> NodeRef {
        self.intern(VRegState {
            preg: Some(preg),
            ..VRegState::new(width)
        })
    }

    /// Apply a unary operation.
    pub fn unary(&mut self, code: VCode, input: NodeRef) -> NodeRef {
        let width = input.state().width;
        self.intern(VRegState {
            op: Some(Op {
                code,
                uses: smallvec::smallvec![Operand::VReg(input)],
                effect: None,
            }),
            ..VRegState::new(width)
        })
    }

    /// Apply a binary operation.
    pub fn binary(&mut self, code: VCode, lhs: NodeRef, rhs: NodeRef) -> NodeRef {
        let width = lhs.state().width;
        self.intern(VRegState {
            op: Some(Op {
                code,
                uses: smallvec::smallvec![Operand::VReg(lhs), Operand::VReg(rhs)],
                effect: None,
            }),
            ..VRegState::new(width)
        })
    }

    /// Set a stack slot on a value.
    pub fn set_slot(&mut self, input: NodeRef, slot: crate::state::SlotRef) -> NodeRef {
        let mut state = input.state().clone();
        state.define = Define::Ref(input.clone());
        state.slot = Some(slot);
        state.op = Some(Op {
            code: VCode::SetSlot,
            uses: smallvec::smallvec![Operand::VReg(input)],
            effect: None,
        });
        self.intern(state)
    }

    /// Clear a stack slot on a value.
    pub fn clear_slot(&mut self, input: NodeRef) -> NodeRef {
        let mut state = input.state().clone();
        state.define = Define::Ref(input.clone());
        state.slot = None;
        state.op = Some(Op {
            code: VCode::ClearSlot,
            uses: smallvec::smallvec![Operand::VReg(input)],
            effect: None,
        });
        self.intern(state)
    }

    /// Set a target PReg constraint on a value — "this value must end up here."
    pub fn set_target(&mut self, input: NodeRef, target: autosynth_isa::PReg) -> NodeRef {
        let mut state = input.state().clone();
        state.define = Define::Ref(input.clone());
        state.target = Some(target);
        state.op = Some(Op {
            code: VCode::SetTarget(target),
            uses: smallvec::smallvec![Operand::VReg(input)],
            effect: None,
        });
        self.intern(state)
    }

    /// Assign a PReg to a value.
    pub fn assign_preg(&mut self, input: NodeRef, preg: autosynth_isa::PReg) -> NodeRef {
        let mut state = input.state().clone();
        state.define = Define::Ref(input);
        state.preg = Some(preg);
        self.intern(state)
    }

    /// Chase Define::Ref to the root definition.
    pub fn define_root(node: &NodeRef) -> &NodeRef {
        match &node.state().define {
            Define::Root => node,
            Define::Ref(parent) => Self::define_root(parent),
        }
    }

    /// Short human-readable label — uses the Define root's ID.
    pub fn label(node: &NodeRef) -> String {
        let root = Self::define_root(node);
        let id = root.id();
        let state = root.state();
        let suffix = if let Some(preg) = state.preg {
            format!(":x{}", preg.0)
        } else if let Some(val) = state.r#const {
            format!(":{val:#}")
        } else {
            String::new()
        };
        format!("v{id}{suffix}")
    }

    /// Format an operand for display.
    pub fn fmt_operand(u: &Operand) -> String {
        match u {
            Operand::VReg(r) => Self::label(r),
            Operand::UImm12(imm) => format!("#{}", imm.value()),
        }
    }

    /// Format a node with its operation for display.
    pub fn fmt_node(node: &NodeRef) -> String {
        let state = node.state();
        let label = Self::label(node);
        let Some(op) = &state.op else {
            if let Some(preg) = state.preg {
                return format!("{label} = param(x{})", preg.0);
            }
            if let Some(val) = state.r#const {
                return format!("{label} = const({val})");
            }
            return format!("{label} = ???");
        };

        let uses: Vec<String> = op.uses.iter().map(|u| Self::fmt_operand(u)).collect();
        let uses_str = uses.join(", ");

        let effect_str = match &op.effect {
            Some(e) => format!(" [after {}]", Self::label(e)),
            None => String::new(),
        };

        match op.code {
            VCode::SetSlot => {
                let slot = state.slot.as_ref().unwrap();
                format!(
                    "{label} = set_slot({uses_str}, [x{}+{}]){effect_str}",
                    slot.base.0, slot.offset
                )
            }
            VCode::ClearSlot => format!("{label} = clear_slot({uses_str}){effect_str}"),
            VCode::SetTarget(preg) => {
                format!("{label} = set_target({uses_str}, x{}){effect_str}", preg.0)
            }
            VCode::Phi => format!("{label} = phi({uses_str}){effect_str}"),
            VCode::UseCallResult => format!("{label} = use_call_result({uses_str}){effect_str}"),
            VCode::Alu(alu) => format!("{label} = {alu:?}({uses_str}){effect_str}"),
            VCode::Call(idx) => format!("{label} = call ${idx}({uses_str}){effect_str}"),
            VCode::Return => format!("{label} = return({uses_str}){effect_str}"),
            VCode::Needs => format!("{label} = needs({uses_str}){effect_str}"),
            other => format!("{label} = {other:?}({uses_str}){effect_str}"),
        }
    }

    fn hash_state(state: &VRegState) -> u64 {
        let mut hasher = DefaultHasher::new();
        state.hash(&mut hasher);
        hasher.finish()
    }
}
