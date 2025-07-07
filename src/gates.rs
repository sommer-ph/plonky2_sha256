use anyhow::Result;
use std::marker::PhantomData;

use plonky2::{
    field::{extension::Extendable, types::Field},
    gates::gate::{Gate},
    hash::hash_types::RichField,
    iop::{
        ext_target::ExtensionTarget,
        generator::{GeneratedValues, SimpleGenerator, WitnessGeneratorRef},
        target::Target,
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CommonCircuitData},
        vars::{EvaluationTargets, EvaluationVars},
    },
    util::serialization::{Buffer, IoResult, Read, Write},
};

#[derive(Copy, Clone, Debug)]
pub struct Xor3Gate<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Default for Xor3Gate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Xor3Gate<F, D> {
    pub fn new_from_config(_config: &CircuitConfig) -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for Xor3Gate<F, D> {
    fn id(&self) -> String {
        format!("Xor3()")
    }

    fn num_wires(&self) -> usize {
        64
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        4
    }
    fn num_constraints(&self) -> usize {
        16
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        for i in 0..16 {
            let a = vars.local_wires[0 + i * 4];
            let b = vars.local_wires[1 + i * 4];
            let c = vars.local_wires[2 + i * 4];
            let o = vars.local_wires[3 + i * 4];

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
        for i in 0..16 {
            let a = vars.local_wires[0 + i * 4];
            let b = vars.local_wires[1 + i * 4];
            let c = vars.local_wires[2 + i * 4];
            let o = vars.local_wires[3 + i * 4];

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
        vec![WitnessGeneratorRef::new(
            Xor3Generator::<F, D> {
                row,
                _phantom: PhantomData,
            }
            .adapter(),
        )]
    }

    // Nothing special in serialized form
    fn serialize(
        &self,
        _dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<()> {
        Ok(())
    }

    fn deserialize(_src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
struct Xor3Generator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for Xor3Generator<F, D> {
    fn id(&self) -> String {
        format!("Xor3Generator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        for i in 0..16 {
            res.push(Target::wire(self.row, 0 + i * 4));
            res.push(Target::wire(self.row, 1 + i * 4));
            res.push(Target::wire(self.row, 2 + i * 4));
        }
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        for i in 0..16 {
            let a = witness.get_target(Target::wire(self.row, 0 + i * 4));
            let b = witness.get_target(Target::wire(self.row, 1 + i * 4));
            let c = witness.get_target(Target::wire(self.row, 2 + i * 4));
            let o = (a.to_canonical_u64() ^ b.to_canonical_u64() ^ c.to_canonical_u64()) & 1;

            out_buffer.set_target(Target::wire(self.row, 3 + i * 4), F::from_canonical_u64(o))?;
        }

        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        Ok(Self {
            row,
            _phantom: PhantomData,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct MajGate<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Default for MajGate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

impl<F: RichField + Extendable<D>, const D: usize> MajGate<F, D> {
    pub fn new_from_config(_config: &CircuitConfig) -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for MajGate<F, D> {
    fn id(&self) -> String {
        format!("Maj()")
    }

    fn num_wires(&self) -> usize {
        64
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        3
    }
    fn num_constraints(&self) -> usize {
        16
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        for i in 0..16 {
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
        for i in 0..16 {
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
        vec![WitnessGeneratorRef::new(
            MajGenerator::<F, D> {
                row,
                _phantom: PhantomData,
            }
            .adapter(),
        )]
    }

    // Nothing special in serialized form
    fn serialize(
        &self,
        _dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<()> {
        Ok(())
    }

    fn deserialize(_src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
struct MajGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for MajGenerator<F, D> {
    fn id(&self) -> String {
        format!("MajGenerator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        for i in 0..16 {
            res.push(Target::wire(self.row, 0 + i * 4));
            res.push(Target::wire(self.row, 1 + i * 4));
            res.push(Target::wire(self.row, 2 + i * 4));
        }
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        for i in 0..16 {
            let a = witness.get_target(Target::wire(self.row, 0 + i * 4));
            let b = witness.get_target(Target::wire(self.row, 1 + i * 4));
            let c = witness.get_target(Target::wire(self.row, 2 + i * 4));
            let o = ((a.to_canonical_u64() & b.to_canonical_u64())
                ^ (a.to_canonical_u64() & c.to_canonical_u64())
                ^ (b.to_canonical_u64() & c.to_canonical_u64()))
                & 1;

            out_buffer.set_target(Target::wire(self.row, 3 + i * 4), F::from_canonical_u64(o))?;
        }

        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        Ok(Self {
            row,
            _phantom: PhantomData,
        })
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ChGate<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> Default for ChGate<F, D> {
    fn default() -> Self {
        Self::new_from_config(&CircuitConfig::standard_recursion_config())
    }
}

impl<F: RichField + Extendable<D>, const D: usize> ChGate<F, D> {
    pub fn new_from_config(_config: &CircuitConfig) -> Self {
        Self {
            _phantom: PhantomData,
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Gate<F, D> for ChGate<F, D> {
    fn id(&self) -> String {
        format!("Ch()")
    }

    fn num_wires(&self) -> usize {
        64
    }
    fn num_constants(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        2
    }
    fn num_constraints(&self) -> usize {
        16
    }

    fn eval_unfiltered(&self, vars: EvaluationVars<F, D>) -> Vec<F::Extension> {
        let mut res = Vec::new();
        for i in 0..16 {
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
        for i in 0..16 {
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
        vec![WitnessGeneratorRef::new(
            ChGenerator::<F, D> {
                row,
                _phantom: PhantomData,
            }
            .adapter(),
        )]
    }

    // Nothing special in serialized form
    fn serialize(
        &self,
        _dst: &mut Vec<u8>,
        _common_data: &CommonCircuitData<F, D>,
    ) -> IoResult<()> {
        Ok(())
    }

    fn deserialize(_src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        Ok(Self {
            _phantom: PhantomData,
        })
    }
}

// Witness generator for the gate
#[derive(Debug, Clone)]
struct ChGenerator<F: RichField + Extendable<D>, const D: usize> {
    row: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> SimpleGenerator<F, D> for ChGenerator<F, D> {
    fn id(&self) -> String {
        format!("ChGenerator(row={})", self.row)
    }

    fn dependencies(&self) -> Vec<Target> {
        let mut res = Vec::new();
        for i in 0..16 {
            res.push(Target::wire(self.row, 0 + i * 4));
            res.push(Target::wire(self.row, 1 + i * 4));
            res.push(Target::wire(self.row, 2 + i * 4));
        }
        res
    }

    fn run_once(
        &self,
        witness: &PartitionWitness<F>,
        out_buffer: &mut GeneratedValues<F>,
    ) -> Result<()> {
        for i in 0..16 {
            let a = witness.get_target(Target::wire(self.row, 0 + i * 4));
            let b = witness.get_target(Target::wire(self.row, 1 + i * 4));
            let c = witness.get_target(Target::wire(self.row, 2 + i * 4));
            let o = a.to_canonical_u64() * (b.to_canonical_u64() - c.to_canonical_u64())
                + c.to_canonical_u64();

            out_buffer.set_target(Target::wire(self.row, 3 + i * 4), F::from_canonical_u64(o))?;
        }

        // Set the witness values
        Ok(())
    }

    fn serialize(&self, dst: &mut Vec<u8>, _common_data: &CommonCircuitData<F, D>) -> IoResult<()> {
        dst.write_usize(self.row)
    }

    fn deserialize(src: &mut Buffer, _common_data: &CommonCircuitData<F, D>) -> IoResult<Self> {
        let row = src.read_usize()?;
        Ok(Self {
            row,
            _phantom: PhantomData,
        })
    }
}
