use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::target::{BoolTarget, Target},
    plonk::circuit_builder::CircuitBuilder,
    util::log_floor,
};

// Assuming U32Target is defined somewhere like this:
// pub struct U32Target(pub Target);

use crate::gates::{BaseSplitGeneratorOptimized, BaseSumGateOptimized, ChGate, MajGate};
// Re-export the gate for convenience
use crate::gates::Xor3Gate;
use core::borrow::Borrow;
use itertools::Itertools;

pub trait XorOps<F: RichField + Extendable<D>, const D: usize> {
    fn add_xor3(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget;
    fn add_maj(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget;
    fn add_ch(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget;
    fn le_sum_optimized(&mut self, bits: impl Iterator<Item = impl Borrow<BoolTarget>>) -> Target;
    fn split_le_base_optimized<const B: usize>(
        &mut self,
        x: Target,
        num_limbs: usize,
    ) -> Vec<Target>;
}

impl<F: RichField + Extendable<D>, const D: usize> XorOps<F, D> for CircuitBuilder<F, D> {
    fn add_xor3(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget {
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
    fn add_maj(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget {
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
    fn add_ch(&mut self, a: BoolTarget, b: BoolTarget, c: BoolTarget) -> BoolTarget {
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

    /// Takes an iterator of bits `(b_i)` and returns `sum b_i * 2^i`, i.e.,
    /// the number with little-endian bit representation given by `bits`.

    fn le_sum_optimized(&mut self, bits: impl Iterator<Item = impl Borrow<BoolTarget>>) -> Target {
        let bits = bits.map(|b| *b.borrow()).collect_vec();
        let num_bits = bits.len();
        assert!(
            num_bits <= log_floor(F::ORDER, 2),
            "{} bits may overflow the field",
            num_bits
        );
        if num_bits == 0 {
            return self.zero();
        }

        debug_assert!(
            BaseSumGateOptimized::<2>::START_LIMBS + num_bits <= self.config.num_routed_wires,
            "Not enough routed wires."
        );
        let gate_type = BaseSumGateOptimized::<2>::new_from_config(&self.config, num_bits + 2);
        let constants = vec![];
        let (row, i) = self.find_slot(gate_type, &constants, &constants);
        let offset = i * (gate_type.num_limbs + 1);
        for (limb, wire) in bits.iter().zip(
            BaseSumGateOptimized::<2>::START_LIMBS + offset
                ..BaseSumGateOptimized::<2>::START_LIMBS + num_bits + offset,
        ) {
            self.connect(limb.target, Target::wire(row, wire));
        }
        for l in (BaseSumGateOptimized::<2>::START_LIMBS + offset
            ..BaseSumGateOptimized::<2>::START_LIMBS + gate_type.num_limbs + offset)
            .skip(num_bits)
        {
            self.assert_zero(Target::wire(row, l));
        }
        Target::wire(row, BaseSumGateOptimized::<2>::WIRE_SUM + offset)
    }

    fn split_le_base_optimized<const B: usize>(
        &mut self,
        x: Target,
        num_limbs: usize,
    ) -> Vec<Target> {
        let gate_type = BaseSumGateOptimized::<B>::new_from_config(&self.config, num_limbs);
        let constants = vec![];
        let (row, i) = self.find_slot(gate_type, &constants, &constants);
        let offset = i * (gate_type.num_limbs + 1);
        let sum = Target::wire(row, BaseSumGateOptimized::<B>::WIRE_SUM + offset);
        self.connect(x, sum);
        self.add_simple_generator(BaseSplitGeneratorOptimized::<B> {
            row: row,
            i: i,
            num_limbs: gate_type.num_limbs,
        });
        Target::wires_from_range(row, gate_type.limbs(i))
    }
}
