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
pub use crate::gates::Xor3Gate;

pub trait XorOps<F: RichField + Extendable<D>, const D: usize> {
    fn add_xor3(
        &mut self,
        a: Vec<BoolTarget>,
        b: Vec<BoolTarget>,
        c: Vec<BoolTarget>,
    ) -> Vec<BoolTarget>;
    fn add_maj(
        &mut self,
        a: Vec<BoolTarget>,
        b: Vec<BoolTarget>,
        c: Vec<BoolTarget>,
    ) -> Vec<BoolTarget>;
    fn add_ch(
        &mut self,
        a: Vec<BoolTarget>,
        b: Vec<BoolTarget>,
        c: Vec<BoolTarget>,
    ) -> Vec<BoolTarget>;
}

impl<F: RichField + Extendable<D>, const D: usize> XorOps<F, D> for CircuitBuilder<F, D> {
    fn add_xor3(
        &mut self,
        a: Vec<BoolTarget>,
        b: Vec<BoolTarget>,
        c: Vec<BoolTarget>,
    ) -> Vec<BoolTarget> {
        let gate = Xor3Gate::<F, D>::new_from_config(&self.config);
        let row = self.add_gate(gate, vec![]);
        let mut res = Vec::new();
        for i in 0..16 {
            self.connect(a[i].target, Target::wire(row, 0 + i * 4));
            self.connect(b[i].target, Target::wire(row, 1 + i * 4));
            self.connect(c[i].target, Target::wire(row, 2 + i * 4));
            res.push(BoolTarget::new_unsafe(Target::wire(row, 3 + i * 4)));
        }
        res
    }
    fn add_maj(
        &mut self,
        a: Vec<BoolTarget>,
        b: Vec<BoolTarget>,
        c: Vec<BoolTarget>,
    ) -> Vec<BoolTarget> {
        let gate = MajGate::<F, D>::new_from_config(&self.config);
        let row = self.add_gate(gate, vec![]);
        let mut res = Vec::new();
        for i in 0..16 {
            self.connect(a[i].target, Target::wire(row, 0 + i * 4));
            self.connect(b[i].target, Target::wire(row, 1 + i * 4));
            self.connect(c[i].target, Target::wire(row, 2 + i * 4));
            res.push(BoolTarget::new_unsafe(Target::wire(row, 3 + i * 4)));
        }
        res
    }
    fn add_ch(
        &mut self,
        a: Vec<BoolTarget>,
        b: Vec<BoolTarget>,
        c: Vec<BoolTarget>,
    ) -> Vec<BoolTarget> {
        let gate = ChGate::<F, D>::new_from_config(&self.config);
        let row = self.add_gate(gate, vec![]);
        let mut res = Vec::new();
        for i in 0..16 {
            self.connect(a[i].target, Target::wire(row, 0 + i * 4));
            self.connect(b[i].target, Target::wire(row, 1 + i * 4));
            self.connect(c[i].target, Target::wire(row, 2 + i * 4));
            res.push(BoolTarget::new_unsafe(Target::wire(row, 3 + i * 4)));
        }
        res
    }
}
