use anyhow::Result;
use core::ops::Range;
use std::marker::PhantomData;

use plonky2::{
    field::{extension::Extendable, types::Field},
    gates::gate::Gate,
    hash::hash_types::RichField,
    iop::{
        ext_target::ExtensionTarget,
        generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData},
        plonk_common::{reduce_with_powers, reduce_with_powers_ext_circuit},
        vars::{EvaluationTargets, EvaluationVars},
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};

#[derive(Copy, Clone, Debug)]
pub struct Xor3Gate<F: RichField + Extendable<D>, const D: usize> {
    // W: size of chunks
    pub num_ops: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Xor3Gate<F, D> {
    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 4;
        config.num_routed_wires / wires_per_op
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Default for Xor3Gate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Xor3Gate<F, D> {
    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom: PhantomData,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for Xor3Gate<F, D> {
    fn id(&self) -> String {
        format!("Xor3()")
    }

    fn num_wires(&self) -> usize {
        self.num_ops * 4
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        4
    }
    fn num_constraints(&self) -> usize {
        self.num_ops
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        for i in 0..self.num_ops {
            let op_ind = i;
            let a = vars.local_wires[0 + op_ind * 4];
            let b = vars.local_wires[1 + op_ind * 4];
            let c = vars.local_wires[2 + op_ind * 4];
            let o = vars.local_wires[3 + op_ind * 4];

            // Direct formula - no intermediate wires needed
            let u = a - b;
            let d = u * u;
            let v = d - c;
            let expected = v * v;
            res.push(o - expected);
        }
        res
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut res = Vec::new();
        for i in 0..self.num_ops {
            let op_ind = i;
            let a = vars.local_wires[0 + op_ind * 4];
            let b = vars.local_wires[1 + op_ind * 4];
            let c = vars.local_wires[2 + op_ind * 4];
            let o = vars.local_wires[3 + op_ind * 4];

            // Build the same computation using circuit operations
            let u = builder.sub_extension(a, b); // u = a - b
            let d = builder.mul_extension(u, u); // d = u * u = (a-b)^2
            let v = builder.sub_extension(d, c); // v = d - c = (a-b)^2 - c
            let expected = builder.mul_extension(v, v); // expected = v * v = ((a-b)^2 - c)^2

            // Return the constraint: o - expected = 0
            let constraint = builder.sub_extension(o, expected);
            res.push(constraint);
        }

        res
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.num_ops)
            .map(|i| {
                WitnessGeneratorRef::new(
                    Xor3Generator::<F, D> {
                        row,
                        i,
                        _phantom: PhantomData,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    // Nothing special in serialized form
    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            num_ops: src
                .read_usize()
                .expect("Failed to read num_ops from serialized Xor3Gate"),
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
struct Xor3Generator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    i: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for Xor3Generator<F, D> {
    fn id(&self) -> String {
        format!("Xor3Generator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        let op_ind = self.i;
        res.push(Target::wire(self.row, 0 + op_ind * 4));
        res.push(Target::wire(self.row, 1 + op_ind * 4));
        res.push(Target::wire(self.row, 2 + op_ind * 4));

        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let op_ind = self.i;
        let a = witness.get_target(Target::wire(self.row, 0 + op_ind * 4));
        let b = witness.get_target(Target::wire(self.row, 1 + op_ind * 4));
        let c = witness.get_target(Target::wire(self.row, 2 + op_ind * 4));
        let o = (a.to_canonical_u64() ^ b.to_canonical_u64() ^ c.to_canonical_u64()) & 1;

        out_buffer.set_target(
            Target::wire(self.row, 3 + op_ind * 4),
            F::from_canonical_u64(o),
        )?;
        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        Ok(Self {
            row,
            i,
            _phantom: PhantomData,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MajGate<F: RichField + Extendable<D>, const D: usize> {
    num_ops: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> MajGate<F, D> {
    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 4;
        config.num_routed_wires / wires_per_op
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Default for MajGate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

impl<F: RichField + Extendable<D>, const D: usize> MajGate<F, D> {
    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom: PhantomData,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for MajGate<F, D> {
    fn id(&self) -> String {
        format!("Maj()")
    }

    fn num_wires(&self) -> usize {
        self.num_ops * 4
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        3
    }
    fn num_constraints(&self) -> usize {
        self.num_ops
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        for i in 0..self.num_ops {
            let a = vars.local_wires[0 + i * 4];
            let b = vars.local_wires[1 + i * 4];
            let c = vars.local_wires[2 + i * 4];
            let o = vars.local_wires[3 + i * 4];

            // Direct formula - no intermediate wires needed
            let expected = a * b + a * c + b * c - a * b * c * F::Extension::from_canonical_u64(2);
            res.push(o - expected);
        }

        res
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut res = Vec::new();
        for i in 0..self.num_ops {
            let a = vars.local_wires[0 + i * 4];
            let b = vars.local_wires[1 + i * 4];
            let c = vars.local_wires[2 + i * 4];
            let o = vars.local_wires[3 + i * 4];

            // Build the same computation using circuit operations
            let two = builder.constant_extension(F::Extension::from_canonical_u64(2));
            let m = builder.mul_extension(b, c);
            let two_m = builder.mul_extension(two, m);
            let b_add_c = builder.add_extension(b, c);
            let b_add_c_sub_two_m = builder.sub_extension(b_add_c, two_m);
            let a_mul_b_add_c_sub_two_m = builder.mul_extension(a, b_add_c_sub_two_m);
            let r = builder.add_extension(a_mul_b_add_c_sub_two_m, m);

            // Return the constraint: o - expected = 0
            let constraint = builder.sub_extension(o, r);
            res.push(constraint);
        }
        res
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.num_ops)
            .map(|i| {
                WitnessGeneratorRef::new(
                    MajGenerator::<F, D> {
                        row,
                        i,
                        _phantom: PhantomData,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    // Nothing special in serialized form
    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            num_ops: src
                .read_usize()
                .expect("Failed to read num_ops from serialized MajGate"),
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
struct MajGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    i: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for MajGenerator<F, D> {
    fn id(&self) -> String {
        format!("MajGenerator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        res.push(Target::wire(self.row, 0 + self.i * 4));
        res.push(Target::wire(self.row, 1 + self.i * 4));
        res.push(Target::wire(self.row, 2 + self.i * 4));
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let a = witness.get_target(Target::wire(self.row, 0 + self.i * 4));
        let b = witness.get_target(Target::wire(self.row, 1 + self.i * 4));
        let c = witness.get_target(Target::wire(self.row, 2 + self.i * 4));
        let o = ((a.to_canonical_u64() & b.to_canonical_u64())
            ^ (a.to_canonical_u64() & c.to_canonical_u64())
            ^ (b.to_canonical_u64() & c.to_canonical_u64()))
            & 1;

        out_buffer.set_target(
            Target::wire(self.row, 3 + self.i * 4),
            F::from_canonical_u64(o),
        )?;

        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        Ok(Self {
            row,
            i,
            _phantom: PhantomData,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ChGate<F: RichField + Extendable<D>, const D: usize> {
    num_ops: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> ChGate<F, D> {
    pub fn new_from_config(config: &CircuitConfig) -> Self {
        Self {
            num_ops: Self::num_ops(config),
            _phantom: PhantomData,
        }
    }
    /// Determine the maximum number of operations that can fit in one gate for the given config.
    pub(crate) const fn num_ops(config: &CircuitConfig) -> usize {
        let wires_per_op = 4;
        config.num_routed_wires / wires_per_op
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Default for ChGate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for ChGate<F, D> {
    fn id(&self) -> String {
        format!("Ch()")
    }

    fn num_wires(&self) -> usize {
        self.num_ops * 4
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        2
    }
    fn num_constraints(&self) -> usize {
        self.num_ops
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        for i in 0..self.num_ops {
            let a = vars.local_wires[0 + i * 4];
            let b = vars.local_wires[1 + i * 4];
            let c = vars.local_wires[2 + i * 4];
            let o = vars.local_wires[3 + i * 4];

            // Direct formula - no intermediate wires needed
            let expected = a * (b - c) + c;
            res.push(o - expected);
        }

        res
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let mut res = Vec::new();
        for i in 0..self.num_ops {
            let a = vars.local_wires[0 + i * 4];
            let b = vars.local_wires[1 + i * 4];
            let c = vars.local_wires[2 + i * 4];
            let o = vars.local_wires[3 + i * 4];

            // Build the same computation using circuit operations
            let b_sub_c = builder.sub_extension(b, c);
            let a_mul_b_sub_c = builder.mul_extension(a, b_sub_c);
            let r = builder.add_extension(a_mul_b_sub_c, c);

            // Return the constraint: o - expected = 0
            let constraint = builder.sub_extension(o, r);
            res.push(constraint);
        }
        res
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.num_ops)
            .map(|i| {
                WitnessGeneratorRef::new(
                    ChGenerator::<F, D> {
                        row,
                        i,
                        _phantom: PhantomData,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    // Nothing special in serialized form
    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            num_ops: src
                .read_usize()
                .expect("Failed to read num_ops from serialized ChGate"),
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
struct ChGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    i: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for ChGenerator<F, D> {
    fn id(&self) -> String {
        format!("ChGenerator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();

        res.push(Target::wire(self.row, 0 + self.i * 4));
        res.push(Target::wire(self.row, 1 + self.i * 4));
        res.push(Target::wire(self.row, 2 + self.i * 4));

        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let a = witness.get_target(Target::wire(self.row, 0 + self.i * 4));
        let b = witness.get_target(Target::wire(self.row, 1 + self.i * 4));
        let c = witness.get_target(Target::wire(self.row, 2 + self.i * 4));
        let o = a.to_canonical_u64() * (b.to_canonical_u64() - c.to_canonical_u64())
            + c.to_canonical_u64();

        out_buffer.set_target(
            Target::wire(self.row, 3 + self.i * 4),
            F::from_canonical_u64(o),
        )?;

        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        Ok(Self {
            row,
            i,
            _phantom: PhantomData,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct BaseSumGateOptimized<const B: usize> {
    pub num_limbs: usize,
    pub num_ops: usize,
}

impl<const B: usize> BaseSumGateOptimized<B> {
    pub(crate) const fn num_ops(config: &CircuitConfig, num_limbs: usize) -> usize {
        let wires_per_op = num_limbs + 1;
        config.num_routed_wires / wires_per_op
    }

    pub(crate) fn new(num_limbs: usize, num_ops: usize) -> Self {
        Self { num_limbs, num_ops }
    }
    pub fn new_from_config(config: &CircuitConfig, num_limbs: usize) -> Self {
        let num_ops = Self::num_ops(config, num_limbs);
        Self { num_limbs, num_ops }
    }

    pub(crate) const WIRE_SUM: usize = 0;
    pub(crate) const START_LIMBS: usize = 1;

    /// Returns the index of the `i`th limb wire.
    pub(crate) const fn limbs(&self, i: usize) -> Range<usize> {
        let offset = i * (self.num_limbs + 1);
        Self::START_LIMBS + offset..Self::START_LIMBS + self.num_limbs + offset
    }
}

impl<F: RichField + Extendable<D>, const D: usize, const B: usize> Gate<F, D>
    for BaseSumGateOptimized<B>
{
    fn id(&self) -> String {
        format!("{self:?} + Base: {B}")
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.num_limbs)?;
        dst.write_usize(self.num_ops)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let num_limbs = src.read_usize()?;
        let num_ops = src.read_usize()?;
        Ok(Self { num_limbs, num_ops })
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut constraints = Vec::new();
        for i in 0..self.num_ops {
            let offset: usize = i * (self.num_limbs + 1);
            let sum = vars.local_wires[Self::WIRE_SUM + offset];
            let limbs = vars.local_wires[self.limbs(i)].to_vec();
            let computed_sum = reduce_with_powers(&limbs, F::Extension::from_canonical_usize(B));
            constraints.push(computed_sum - sum);
            for limb in limbs {
                constraints.push(
                    (0..B)
                        .map(|i| limb - F::Extension::from_canonical_usize(i))
                        .product(),
                );
            }
        }

        constraints
    }

    fn eval_unfiltered_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: EvaluationTargets<D>,
    ) -> Vec<ExtensionTarget<D>> {
        let base = builder.constant(F::from_canonical_usize(B));
        let mut constraints = Vec::new();
        for i in 0..self.num_ops {
            let offset = i * (self.num_limbs + 1);
            let sum = vars.local_wires[Self::WIRE_SUM + offset];
            let limbs = vars.local_wires[self.limbs(i)].to_vec();
            let computed_sum = reduce_with_powers_ext_circuit(builder, &limbs, base);
            constraints.push(builder.sub_extension(computed_sum, sum));
            for limb in limbs {
                constraints.push({
                    let mut acc = builder.one_extension();
                    (0..B).for_each(|i| {
                        // We update our accumulator as:
                        // acc' = acc (x - i)
                        //      = acc x + (-i) acc
                        // Since -i is constant, we can do this in one arithmetic_extension call.
                        let neg_i = -F::from_canonical_usize(i);
                        acc = builder.arithmetic_extension(F::ONE, neg_i, acc, limb, acc)
                    });
                    acc
                });
            }
        }

        constraints
    }

    fn generators(&self, row: usize, _local_constants: &[F]) -> Vec<WitnessGeneratorRef<F, D>> {
        (0..self.num_ops)
            .map(|i| {
                WitnessGeneratorRef::new(
                    BaseSumGeneratorOptimized::<B> {
                        row,
                        i,
                        num_limbs: self.num_limbs,
                    }
                    .adapter(),
                )
            })
            .collect()
    }

    // 1 for the sum then `num_limbs` for the limbs.
    fn num_wires(&self) -> usize {
        (1 + self.num_limbs) * self.num_ops
    }

    fn num_constants(&self) -> usize {
        0
    }

    // Bounded by the range-check (x-0)*(x-1)*...*(x-B+1).
    fn degree(&self) -> usize {
        B
    }

    // 1 for checking the sum then `num_limbs` for range-checking the limbs.
    fn num_constraints(&self) -> usize {
        (1 + self.num_limbs) * self.num_ops
    }
}

#[derive(Debug, Default)]
pub struct BaseSumGeneratorOptimized<const B: usize> {
    row: usize,
    i: usize,
    num_limbs: usize,
}

impl<F: RichField + Extendable<D>, const B: usize, const D: usize> SimpleGenerator<F, D>
    for BaseSumGeneratorOptimized<B>
{
    fn id(&self) -> String {
        format!("BaseSumGenerator + Base: {B}")
    }

    fn dependencies(&self) -> Vec<Target> {
        let offset = self.i * (self.num_limbs + 1);
        let mut res = Vec::new();
        for j in 0..self.num_limbs {
            res.push(Target::wire(
                self.row,
                BaseSumGateOptimized::<B>::START_LIMBS + j + offset,
            ));
        }
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let offset = self.i * (self.num_limbs + 1);
        let limbs: Vec<BoolTarget> = (0..self.num_limbs)
            .map(|j| {
                BoolTarget::new_unsafe(Target::wire(
                    self.row,
                    BaseSumGateOptimized::<B>::START_LIMBS + j + offset,
                ))
            })
            .collect();
        let sum = limbs
            .iter()
            .map(|&t| witness.get_bool_target(t))
            .rev()
            .fold(F::ZERO, |acc, limb| {
                acc * F::from_canonical_usize(B) + F::from_bool(limb)
            });

        out_buffer.set_target(
            Target::wire(self.row, BaseSumGateOptimized::<B>::WIRE_SUM + offset),
            sum,
        )
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)?;
        dst.write_usize(self.num_limbs)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        let num_limbs = src.read_usize()?;
        Ok(Self { row, i, num_limbs })
    }
}

#[derive(Debug, Default)]
pub struct BaseSplitGeneratorOptimized<const B: usize> {
    pub row: usize,
    pub i: usize,
    pub num_limbs: usize,
}

impl<F: RichField + Extendable<D>, const B: usize, const D: usize> SimpleGenerator<F, D>
    for BaseSplitGeneratorOptimized<B>
{
    fn id(&self) -> String {
        format!("BaseSplitGenerator + Base: {B}")
    }

    fn dependencies(&self) -> Vec<Target> {
        let offset = self.i * (self.num_limbs + 1);
        vec![Target::wire(
            self.row,
            BaseSumGateOptimized::<B>::WIRE_SUM + offset,
        )]
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        let offset = self.i * (self.num_limbs + 1);
        let sum_value = witness
            .get_target(Target::wire(
                self.row,
                BaseSumGateOptimized::<B>::WIRE_SUM + offset,
            ))
            .to_canonical_u64();
        debug_assert_eq!(
            (0..self.num_limbs).fold(sum_value, |acc, _| acc / (B as u64)),
            0,
            "Integer too large to fit in given number of limbs"
        );

        let limbs = (BaseSumGateOptimized::<B>::START_LIMBS + offset
            ..BaseSumGateOptimized::<B>::START_LIMBS + self.num_limbs + offset)
            .map(|i| Target::wire(self.row, i));
        let limbs_value = (0..self.num_limbs)
            .scan(sum_value, |acc, _| {
                let tmp = *acc % (B as u64);
                *acc /= B as u64;
                Some(F::from_canonical_u64(tmp))
            })
            .collect::<Vec<_>>();

        for (b, b_value) in limbs.zip(limbs_value) {
            out_buffer
                .set_target(b, b_value)
                .expect(&format!("Failed to set target {:?} to {:?}", b, b_value));
        }

        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)?;
        dst.write_usize(self.i)?;
        dst.write_usize(self.num_limbs)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        let i = src.read_usize()?;
        let num_limbs = src.read_usize()?;
        Ok(Self { row, i, num_limbs })
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use crate::gates::BaseSumGateOptimized;
    use plonky2::field::goldilocks_field::GoldilocksField;
    use plonky2::gates::gate_testing::{test_eval_fns, test_low_degree};
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn low_degree() {
        test_low_degree::<GoldilocksField, _, 4>(BaseSumGateOptimized::<6>::new(11, 5))
    }

    #[test]
    fn eval_fns() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        test_eval_fns::<F, C, _, D>(BaseSumGateOptimized::<6>::new(11, 5))
    }
}
