use std::collections::HashMap;
use std::hash::{Hash, Hasher, DefaultHasher};
use crate::state::VRegState;
use crate::op::{Op, OpCode};
use smallvec::SmallVec;
use autosynth_isa::Width;

/// A handle to an interned VRegState. Identity via hash.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VRegRef(pub u64);

/// Intern pool — the program is a set of interned VRegStates.
pub struct Pool {
    states: HashMap<u64, VRegState>,
}

impl Pool {
    pub fn new() -> Self {
        Self { states: HashMap::new() }
    }

    /// Intern a VRegState. Returns the VRegRef handle.
    /// If an identical state already exists, returns its handle.
    pub fn intern(&mut self, state: VRegState) -> VRegRef {
        let hash = self.hash_state(&state);
        self.states.entry(hash).or_insert(state);
        VRegRef(hash)
    }

    /// Look up a VRegState by its handle.
    pub fn get(&self, r: VRegRef) -> &VRegState {
        &self.states[&r.0]
    }

    /// Define a constant value.
    pub fn define_const(&mut self, val: i64, width: Width) -> VRegRef {
        self.intern(VRegState {
            r#const: Some(val),
            ..VRegState::new(width)
        })
    }

    /// Define a parameter arriving in a PReg.
    pub fn define_param(&mut self, preg: autosynth_isa::PReg, width: Width) -> VRegRef {
        self.intern(VRegState {
            preg: Some(preg),
            ..VRegState::new(width)
        })
    }

    /// Apply a unary operation.
    pub fn unary(&mut self, code: OpCode, input: VRegRef) -> VRegRef {
        let input_state = self.get(input);
        let width = input_state.width;
        self.intern(VRegState {
            op: Some(Op {
                code,
                uses: smallvec::smallvec![input],
            }),
            ..VRegState::new(width)
        })
    }

    /// Apply a binary operation.
    pub fn binary(&mut self, code: OpCode, lhs: VRegRef, rhs: VRegRef) -> VRegRef {
        let lhs_state = self.get(lhs);
        let width = lhs_state.width;
        self.intern(VRegState {
            op: Some(Op {
                code,
                uses: smallvec::smallvec![lhs, rhs],
            }),
            ..VRegState::new(width)
        })
    }

    /// Set a stack slot on a value. Returns a new VRegRef with the slot set.
    pub fn set_slot(&mut self, input: VRegRef, slot: crate::state::SlotRef) -> VRegRef {
        let mut state = self.get(input).clone();
        state.slot = Some(slot);
        state.op = Some(Op {
            code: OpCode::SetSlot,
            uses: smallvec::smallvec![input],
        });
        self.intern(state)
    }

    /// Assign a PReg to a value. Returns a new VRegRef.
    pub fn assign_preg(&mut self, input: VRegRef, preg: autosynth_isa::PReg) -> VRegRef {
        let mut state = self.get(input).clone();
        state.preg = Some(preg);
        self.intern(state)
    }

    fn hash_state(&self, state: &VRegState) -> u64 {
        let mut hasher = DefaultHasher::new();
        state.hash(&mut hasher);
        hasher.finish()
    }
}
