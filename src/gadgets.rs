use plonky2::{
    field::{extension::Extendable},
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
    plonk::{
        circuit_builder::CircuitBuilder,
    },
};

// Assuming U32Target is defined somewhere like this:
// pub struct U32Target(pub Target);

use crate::gates::{ChGate, MajGate};
// Re-export the gate for convenience
use crate::gates::{Xor3Gate};

pub trait XorOps<F: RichField + Extendable<D>, const D: usize> {
    fn add_xor3(
        &mut self,
        a: BoolTarget,
        b: BoolTarget,
        c: BoolTarget
    ) -> BoolTarget;
    fn add_maj(
        &mut self,
        a: BoolTarget,
        b: BoolTarget,
        c: BoolTarget,
    ) -> BoolTarget;
    fn add_ch(
        &mut self,
        a: BoolTarget,
        b: BoolTarget,
        c: BoolTarget,
    ) -> BoolTarget;
}

impl<F: RichField + Extendable<D>, const D: usize> XorOps<F, D> for CircuitBuilder<F, D> {
    fn add_xor3(
        &mut self,
        a: BoolTarget,
        b: BoolTarget,
        c: BoolTarget
    ) -> BoolTarget {
        let gate = Xor3Gate::new_from_config(&self.config);
        let constants = vec![];
        let (gate, i) = self.find_slot(gate, &constants, &constants);
        let op_ind = i;
        let wire_a = Target::wire(gate, 0 + op_ind * 4);
        let wire_b = Target::wire(gate, 1 + op_ind * 4);
        let wire_c = Target::wire(gate, 2 + op_ind * 4);
        self.connect(a.target, wire_a);
        self.connect(b.target, wire_b);
        self.connect(c.target, wire_c);
        BoolTarget::new_unsafe(Target::wire(gate, 3 + op_ind * 4))
    }
    fn add_maj(
        &mut self,
        a: BoolTarget,
        b: BoolTarget,
        c: BoolTarget,
    ) -> BoolTarget {
        let gate = MajGate::new_from_config(&self.config);
        let constants = vec![];
        let (gate, i) = self.find_slot(gate, &constants, &constants);
        let op_ind = i;
        let wire_a = Target::wire(gate, 0 + op_ind * 4);
        let wire_b = Target::wire(gate, 1 + op_ind * 4);
        let wire_c = Target::wire(gate, 2 + op_ind * 4);
        self.connect(a.target, wire_a);
        self.connect(b.target, wire_b);
        self.connect(c.target, wire_c);
        BoolTarget::new_unsafe(Target::wire(gate, 3 + op_ind * 4))
    }
    fn add_ch(
        &mut self,
        a: BoolTarget,
        b: BoolTarget,
        c: BoolTarget,
    ) -> BoolTarget {
        let gate = ChGate::new_from_config(&self.config);
        let constants = vec![];
        let (gate, i) = self.find_slot(gate, &constants, &constants);
        let op_ind = i;
        let wire_a = Target::wire(gate, 0 + op_ind * 4);
        let wire_b = Target::wire(gate, 1 + op_ind * 4);
        let wire_c = Target::wire(gate, 2 + op_ind * 4);
        self.connect(a.target, wire_a);
        self.connect(b.target, wire_b);
        self.connect(c.target, wire_c);
        BoolTarget::new_unsafe(Target::wire(gate, 3 + op_ind * 4))
    }
}
