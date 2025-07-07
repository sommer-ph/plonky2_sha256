use anyhow::Result;
use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget},
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::circuit_builder::CircuitBuilder,
};
use plonky2_u32::{
    gadgets::arithmetic_u32::{CircuitBuilderU32, U32Target},
    witness::WitnessU32,
};
use std::rc::Rc;
use std::{cell::RefCell};

use crate::{gadgets::XorOps};

#[rustfmt::skip]
pub const H256: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
];

/// Constants necessary for SHA-256 family of digests.
#[rustfmt::skip]
pub const K256: [u32; 64] = [
    0x428A2F98, 0x71374491, 0xB5C0FBCF, 0xE9B5DBA5,
    0x3956C25B, 0x59F111F1, 0x923F82A4, 0xAB1C5ED5,
    0xD807AA98, 0x12835B01, 0x243185BE, 0x550C7DC3,
    0x72BE5D74, 0x80DEB1FE, 0x9BDC06A7, 0xC19BF174,
    0xE49B69C1, 0xEFBE4786, 0x0FC19DC6, 0x240CA1CC,
    0x2DE92C6F, 0x4A7484AA, 0x5CB0A9DC, 0x76F988DA,
    0x983E5152, 0xA831C66D, 0xB00327C8, 0xBF597FC7,
    0xC6E00BF3, 0xD5A79147, 0x06CA6351, 0x14292967,
    0x27B70A85, 0x2E1B2138, 0x4D2C6DFC, 0x53380D13,
    0x650A7354, 0x766A0ABB, 0x81C2C92E, 0x92722C85,
    0xA2BFE8A1, 0xA81A664B, 0xC24B8B70, 0xC76C51A3,
    0xD192E819, 0xD6990624, 0xF40E3585, 0x106AA070,
    0x19A4C116, 0x1E376C08, 0x2748774C, 0x34B0BCB5,
    0x391C0CB3, 0x4ED8AA4A, 0x5B9CCA4F, 0x682E6FF3,
    0x748F82EE, 0x78A5636F, 0x84C87814, 0x8CC70208,
    0x90BEFFFA, 0xA4506CEB, 0xBEF9A3F7, 0xC67178F2
];

/// Inner mutable state for lazy evaluation
struct LazyU32WithBitsInner<F: RichField + Extendable<D>, const D: usize> {
    u32_target: Option<U32Target>,
    bits: Option<Vec<BoolTarget>>,
    builder: *mut CircuitBuilder<F, D>,
}

/// Represents a U32 value with lazy bit decomposition
pub struct LazyU32WithBits<F: RichField + Extendable<D>, const D: usize> {
    inner: Rc<RefCell<LazyU32WithBitsInner<F, D>>>,
}

impl<F: RichField + Extendable<D>, const D: usize> Clone for LazyU32WithBits<F, D> {
    fn clone(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
}

impl<F: RichField + Extendable<D>, const D: usize> LazyU32WithBits<F, D> {
    /// Create from a U32Target (bits will be computed lazily)
    pub fn from_u32(builder: &mut CircuitBuilder<F, D>, u32_target: U32Target) -> Self {
        Self {
            inner: Rc::new(RefCell::new(LazyU32WithBitsInner {
                u32_target: Some(u32_target),
                bits: None,
                builder: builder as *mut _,
            })),
        }
    }

    /// Create from bits (u32 will be computed lazily)
    pub fn from_bits(builder: &mut CircuitBuilder<F, D>, bits: Vec<BoolTarget>) -> Self {
        assert_eq!(bits.len(), 32);
        Self {
            inner: Rc::new(RefCell::new(LazyU32WithBitsInner {
                u32_target: None,
                bits: Some(bits),
                builder: builder as *mut _,
            })),
        }
    }

    /// Get the U32Target, computing it from bits if necessary
    pub fn get_u32(&self) -> U32Target {
        let mut inner = self.inner.borrow_mut();
        match inner.u32_target {
            Some(u32) => u32,
            None => {
                // Compute from bits
                let builder = unsafe { &mut *inner.builder };
                let bits = inner.bits.as_ref().unwrap();
                let u32_target = bits_to_u32_target(builder, bits.clone());
                inner.u32_target = Some(u32_target);
                u32_target
            }
        }
    }

    /// Get the bits, computing them from U32 if necessary
    pub fn get_bits(&self) -> Vec<BoolTarget> {
        let mut inner = self.inner.borrow_mut();
        match &inner.bits {
            Some(bits) => bits.clone(),
            None => {
                // Compute from u32
                let u32_target = inner.u32_target.unwrap();
                let builder = unsafe { &mut *inner.builder };
                let bits = u32_to_bits_target::<F, D, 2>(builder, &u32_target);
                inner.bits = Some(bits.clone());
                bits
            }
        }
    }
}

pub fn array_to_bits(bytes: &[u8]) -> Vec<bool> {
    let len = bytes.len();
    let mut ret = Vec::new();
    for byte in bytes.iter().take(len) {
        for j in 0..8 {
            let b = (byte >> (7 - j)) & 1;
            ret.push(b == 1);
        }
    }
    ret
}

pub fn u32_to_bits_target<F: RichField + Extendable<D>, const D: usize, const B: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &U32Target,
) -> Vec<BoolTarget> {
    let mut res = Vec::new();
    let bit_targets = builder.split_le_base::<B>(a.0, 32);
    for i in (0..32).rev() {
        res.push(BoolTarget::new_unsafe(bit_targets[i]));
    }
    res
}

pub fn bits_to_u32_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    bits_target: Vec<BoolTarget>,
) -> U32Target {
    let bit_len = bits_target.len();
    assert_eq!(bit_len, 32);
    U32Target(builder.le_sum(bits_target[0..32].iter().rev()))
}

// define ROTATE(x, y)  (((x)>>(y)) | ((x)<<(32-(y))))
fn rotate32(y: usize) -> Vec<usize> {
    let mut res = Vec::new();
    for i in 32 - y..32 {
        res.push(i);
    }
    for i in 0..32 - y {
        res.push(i);
    }
    res
}

// x>>y
// Assume: 0 at index 32
fn shift32(y: usize) -> Vec<usize> {
    let mut res = Vec::new();
    for _ in 32 - y..32 {
        res.push(32);
    }
    for i in 0..32 - y {
        res.push(i);
    }
    res
}

fn xor3_with_permutation<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a_bits: &Vec<BoolTarget>,
    p1: &Vec<usize>,
    p2: &Vec<usize>,
    p3: &Vec<usize>,
) -> Vec<BoolTarget> {
    let mut res = Vec::new();
    for j in 0..2 {
        let mut a1 = Vec::new();
        let mut a2 = Vec::new();
        let mut a3 = Vec::new();
        for i in 0..16 {
            a1.push(a_bits[p1[i + j * 16]]);
            a2.push(a_bits[p2[i + j * 16]]);
            a3.push(a_bits[p3[i + j * 16]]);
        }
        res.extend(builder.add_xor3(a1, a2, a3));
    }
    res
}

//#define Sigma0(x)    (ROTATE((x), 2) ^ ROTATE((x),13) ^ ROTATE((x),22))
fn big_sigma0_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    let a_bits = a.get_bits(); // Only decompose when needed
    let rotate2 = rotate32(2);
    let rotate13 = rotate32(13);
    let rotate22 = rotate32(22);
    let res_bits = xor3_with_permutation(builder, &a_bits, &rotate2, &rotate13, &rotate22);
    LazyU32WithBits::from_bits(builder, res_bits)
}

//#define Sigma1(x)    (ROTATE((x), 6) ^ ROTATE((x),11) ^ ROTATE((x),25))
fn big_sigma1_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    let a_bits = a.get_bits();
    let rotate6 = rotate32(6);
    let rotate11 = rotate32(11);
    let rotate25 = rotate32(25);
    let res_bits = xor3_with_permutation(builder, &a_bits, &rotate6, &rotate11, &rotate25);
    LazyU32WithBits::from_bits(builder, res_bits)
}

//#define sigma0(x)    (ROTATE((x), 7) ^ ROTATE((x),18) ^ ((x)>> 3))
fn sigma0_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    let mut a_bits = a.get_bits();
    a_bits.push(builder.constant_bool(false));
    let rotate7 = rotate32(7);
    let rotate18 = rotate32(18);
    let shift3 = shift32(3);
    let res_bits = xor3_with_permutation(builder, &a_bits, &rotate7, &rotate18, &shift3);
    LazyU32WithBits::from_bits(builder, res_bits)
}

//#define sigma1(x)    (ROTATE((x),17) ^ ROTATE((x),19) ^ ((x)>>10))
fn sigma1_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    let mut a_bits = a.get_bits();
    a_bits.push(builder.constant_bool(false));
    let rotate17 = rotate32(17);
    let rotate19 = rotate32(19);
    let shift10 = shift32(10);
    let res_bits = xor3_with_permutation(builder, &a_bits, &rotate17, &rotate19, &shift10);
    LazyU32WithBits::from_bits(builder, res_bits)
}

/*
ch = a&b ^ (!a)&c
   = a*(b-c) + c
 */
fn ch_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
    b: &LazyU32WithBits<F, D>,
    c: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    let a_bits = a.get_bits();
    let b_bits = b.get_bits();
    let c_bits = c.get_bits();

    let mut res_bits = Vec::new();
    res_bits.extend(builder.add_ch(
        a_bits[0..16].to_vec(),
        b_bits[0..16].to_vec(),
        c_bits[0..16].to_vec(),
    ));
    res_bits.extend(builder.add_ch(
        a_bits[16..32].to_vec(),
        b_bits[16..32].to_vec(),
        c_bits[16..32].to_vec(),
    ));
    LazyU32WithBits::from_bits(builder, res_bits)
}

/*
maj = a&b ^ a&c ^ b&c
    = a*b   +  a*c  +  b*c  -  2*a*b*c
    = a*( b + c - 2*b*c ) + b*c
    = a*( b + c - 2*m ) + m
where m = b*c
 */
fn maj_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
    b: &LazyU32WithBits<F, D>,
    c: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    let a_bits = a.get_bits();
    let b_bits = b.get_bits();
    let c_bits = c.get_bits();

    let mut res_bits = Vec::new();
    res_bits.extend(builder.add_maj(
        a_bits[0..16].to_vec(),
        b_bits[0..16].to_vec(),
        c_bits[0..16].to_vec(),
    ));
    res_bits.extend(builder.add_maj(
        a_bits[16..32].to_vec(),
        b_bits[16..32].to_vec(),
        c_bits[16..32].to_vec(),
    ));
    LazyU32WithBits::from_bits(builder, res_bits)
}

fn add_u32_lazy<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: &LazyU32WithBits<F, D>,
    b: &LazyU32WithBits<F, D>,
) -> LazyU32WithBits<F, D> {
    // Only get U32 representations for addition
    let (res, _carry) = builder.add_u32(a.get_u32(), b.get_u32());
    LazyU32WithBits::from_u32(builder, res)
}

pub struct Sha256Targets {
    pub message: Vec<BoolTarget>,
    pub digest: Vec<BoolTarget>,
}

// padded_msg_len = block_count x 512 bits
// Size: msg_len_in_bits (L) |  p bits   | 64 bits
// Bits:      msg            | 100...000 |    L
pub fn make_circuits<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    msg_len_in_bits: u64,
) -> Sha256Targets {
    let mut message = Vec::new();
    let mut digest = Vec::new();
    let block_count = (msg_len_in_bits + 65 + 511) / 512;
    let padded_msg_len = 512 * block_count;
    let p = padded_msg_len - 64 - msg_len_in_bits;
    assert!(p > 1);

    for _ in 0..msg_len_in_bits {
        message.push(builder.add_virtual_bool_target_unsafe());
    }
    message.push(builder.constant_bool(true));
    for _ in 0..p - 1 {
        message.push(builder.constant_bool(false));
    }
    for i in 0..64 {
        let b = (msg_len_in_bits >> (63 - i)) & 1;
        message.push(builder.constant_bool(b == 1));
    }

    // init states with lazy evaluation
    let mut state = Vec::new();
    for c in &H256 {
        let u32_target = builder.constant_u32(*c);
        state.push(LazyU32WithBits::from_u32(builder, u32_target));
    }

    let mut k256 = Vec::new();
    for k in &K256 {
        k256.push(builder.constant_u32(*k));
    }

    for blk in 0..block_count {
        let mut x = Vec::new();

        // Clone state variables
        let mut a = state[0].clone();
        let mut b = state[1].clone();
        let mut c = state[2].clone();
        let mut d = state[3].clone();
        let mut e = state[4].clone();
        let mut f = state[5].clone();
        let mut g = state[6].clone();
        let mut h = state[7].clone();

        for i in 0..16 {
            let index = blk as usize * 512 + i * 32;
            let u32_target = builder.le_sum(message[index..index + 32].iter().rev());
            x.push(LazyU32WithBits::from_u32(builder, U32Target(u32_target)));

            let mut t1 = h.clone();
            let big_sigma1_e = big_sigma1_lazy(builder, &e);
            t1 = add_u32_lazy(builder, &t1, &big_sigma1_e);
            let ch_e_f_g = ch_lazy(builder, &e, &f, &g);
            t1 = add_u32_lazy(builder, &t1, &ch_e_f_g);
            let k256_lazy = LazyU32WithBits::from_u32(builder, k256[i]);
            t1 = add_u32_lazy(builder, &t1, &k256_lazy);
            t1 = add_u32_lazy(builder, &t1, &x[i]);

            let mut t2 = big_sigma0_lazy(builder, &a);
            let maj_a_b_c = maj_lazy(builder, &a, &b, &c);
            t2 = add_u32_lazy(builder, &t2, &maj_a_b_c);

            h = g;
            g = f;
            f = e;
            e = add_u32_lazy(builder, &d, &t1);
            d = c;
            c = b;
            b = a;
            a = add_u32_lazy(builder, &t1, &t2);
        }

        for i in 16..64 {
            let s0 = sigma0_lazy(builder, &x[(i + 1) & 0x0f]);
            let s1 = sigma1_lazy(builder, &x[(i + 14) & 0x0f]);

            let s0_add_s1 = add_u32_lazy(builder, &s0, &s1);
            let s0_add_s1_add_x = add_u32_lazy(builder, &s0_add_s1, &x[(i + 9) & 0xf]);
            x[i & 0xf] = add_u32_lazy(builder, &x[i & 0xf], &s0_add_s1_add_x);

            let big_sigma0_a = big_sigma0_lazy(builder, &a);
            let big_sigma1_e = big_sigma1_lazy(builder, &e);
            let ch_e_f_g = ch_lazy(builder, &e, &f, &g);
            let maj_a_b_c = maj_lazy(builder, &a, &b, &c);

            let h_add_sigma1 = add_u32_lazy(builder, &h, &big_sigma1_e);
            let h_add_sigma1_add_ch_e_f_g = add_u32_lazy(builder, &h_add_sigma1, &ch_e_f_g);
            let k256_lazy = LazyU32WithBits::from_u32(builder, k256[i]);
            let h_add_sigma1_add_ch_e_f_g_add_k256 =
                add_u32_lazy(builder, &h_add_sigma1_add_ch_e_f_g, &k256_lazy);

            let t1 = add_u32_lazy(builder, &x[i & 0xf], &h_add_sigma1_add_ch_e_f_g_add_k256);
            let t2 = add_u32_lazy(builder, &big_sigma0_a, &maj_a_b_c);

            h = g;
            g = f;
            f = e;
            e = add_u32_lazy(builder, &d, &t1);
            d = c;
            c = b;
            b = a;
            a = add_u32_lazy(builder, &t1, &t2);
        }

        state[0] = add_u32_lazy(builder, &state[0], &a);
        state[1] = add_u32_lazy(builder, &state[1], &b);
        state[2] = add_u32_lazy(builder, &state[2], &c);
        state[3] = add_u32_lazy(builder, &state[3], &d);
        state[4] = add_u32_lazy(builder, &state[4], &e);
        state[5] = add_u32_lazy(builder, &state[5], &f);
        state[6] = add_u32_lazy(builder, &state[6], &g);
        state[7] = add_u32_lazy(builder, &state[7], &h);
    }

    // Only decompose to bits for the final digest output
    for i in 0..8 {
        let bits = state[i].get_bits();
        digest.extend_from_slice(&bits);
    }

    Sha256Targets { message, digest }
}

pub struct VariableLengthSha256Targets {
    pub message: Vec<BoolTarget>,
    pub digest: Vec<BoolTarget>,
    pub msg_len: U32Target,
    pub msg_blocks: U32Target,
}

pub fn make_variable_length_circuits<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    max_total_bits: usize,
) -> VariableLengthSha256Targets {
    assert!(
        max_total_bits % 512 == 0,
        "max_total_bits must be a multiple of 512 (got {})",
        max_total_bits
    );
    let tot_blocks = max_total_bits / 512;
    let mut message = Vec::new();
    let mut digest = Vec::new();

    let msg_len = builder.add_virtual_u32_target();
    let msg_blocks = builder.add_virtual_u32_target();

    for _ in 0..max_total_bits {
        message.push(builder.add_virtual_bool_target_unsafe());
    }

    // init states with lazy evaluation
    let mut state = Vec::new();
    for c in &H256 {
        let u32_target = builder.constant_u32(*c);
        state.push(LazyU32WithBits::from_u32(builder, u32_target));
    }

    let mut k256 = Vec::new();
    for k in &K256 {
        k256.push(builder.constant_u32(*k));
    }

    let mut do_block = builder.constant_bool(true);
    for blk in 0..tot_blocks {
        let mut x = Vec::new();

        // Clone state variables
        let mut a = state[0].clone();
        let mut b = state[1].clone();
        let mut c = state[2].clone();
        let mut d = state[3].clone();
        let mut e = state[4].clone();
        let mut f = state[5].clone();
        let mut g = state[6].clone();
        let mut h = state[7].clone();

        let blk_target = builder.constant_u32(blk as u32);

        let after_msg_block = builder.is_equal(blk_target.0, msg_blocks.0);
        let not_after_msg_block = builder.not(after_msg_block);
        do_block = builder.and(do_block, not_after_msg_block);

        for i in 0..16 {
            let index = blk as usize * 512 + i * 32;
            let u32_target = builder.le_sum(message[index..index + 32].iter().rev());
            x.push(LazyU32WithBits::from_u32(builder, U32Target(u32_target)));

            let mut t1 = h.clone();
            let big_sigma1_e = big_sigma1_lazy(builder, &e);
            t1 = add_u32_lazy(builder, &t1, &big_sigma1_e);
            let ch_e_f_g = ch_lazy(builder, &e, &f, &g);
            t1 = add_u32_lazy(builder, &t1, &ch_e_f_g);
            let k256_lazy = LazyU32WithBits::from_u32(builder, k256[i]);
            t1 = add_u32_lazy(builder, &t1, &k256_lazy);
            t1 = add_u32_lazy(builder, &t1, &x[i]);

            let mut t2 = big_sigma0_lazy(builder, &a);
            let maj_a_b_c = maj_lazy(builder, &a, &b, &c);
            t2 = add_u32_lazy(builder, &t2, &maj_a_b_c);

            h = g;
            g = f;
            f = e;
            e = add_u32_lazy(builder, &d, &t1);
            d = c;
            c = b;
            b = a;
            a = add_u32_lazy(builder, &t1, &t2);
        }

        for i in 16..64 {
            let s0 = sigma0_lazy(builder, &x[(i + 1) & 0x0f]);
            let s1 = sigma1_lazy(builder, &x[(i + 14) & 0x0f]);

            let s0_add_s1 = add_u32_lazy(builder, &s0, &s1);
            let s0_add_s1_add_x = add_u32_lazy(builder, &s0_add_s1, &x[(i + 9) & 0xf]);
            x[i & 0xf] = add_u32_lazy(builder, &x[i & 0xf], &s0_add_s1_add_x);

            let big_sigma0_a = big_sigma0_lazy(builder, &a);
            let big_sigma1_e = big_sigma1_lazy(builder, &e);
            let ch_e_f_g = ch_lazy(builder, &e, &f, &g);
            let maj_a_b_c = maj_lazy(builder, &a, &b, &c);

            let h_add_sigma1 = add_u32_lazy(builder, &h, &big_sigma1_e);
            let h_add_sigma1_add_ch_e_f_g = add_u32_lazy(builder, &h_add_sigma1, &ch_e_f_g);
            let k256_lazy = LazyU32WithBits::from_u32(builder, k256[i]);
            let h_add_sigma1_add_ch_e_f_g_add_k256 =
                add_u32_lazy(builder, &h_add_sigma1_add_ch_e_f_g, &k256_lazy);

            let t1 = add_u32_lazy(builder, &x[i & 0xf], &h_add_sigma1_add_ch_e_f_g_add_k256);
            let t2 = add_u32_lazy(builder, &big_sigma0_a, &maj_a_b_c);

            h = g;
            g = f;
            f = e;
            e = add_u32_lazy(builder, &d, &t1);
            d = c;
            c = b;
            b = a;
            a = add_u32_lazy(builder, &t1, &t2);
        }

        let z = [a, b, c, d, e, f, g, h];

        for i in 0..8 {
            let new_state = add_u32_lazy(builder, &state[i], &z[i]);
            // Use select to conditionally update state based on do_block
            let new_u32 = builder.select(do_block, new_state.get_u32().0, state[i].get_u32().0);
            state[i] = LazyU32WithBits::from_u32(builder, U32Target(new_u32));
        }
    }

    // Only decompose to bits for the final digest output
    for i in 0..8 {
        let bits = state[i].get_bits();
        digest.extend_from_slice(&bits);
    }

    VariableLengthSha256Targets {
        message,
        digest,
        msg_len,
        msg_blocks,
    }
}
pub fn fill_variable_length_circuits<F: RichField + Extendable<D>, const D: usize>(
    pw: &mut PartialWitness<F>,
    msg: &[u8],
    max_total_bits: usize,
    targets: &VariableLengthSha256Targets,
) -> Result<()> {
    assert!(
        max_total_bits % 512 == 0,
        "max_total_bits must be a multiple of 512 (got {})",
        max_total_bits
    );

    let msg_bits = array_to_bits(msg);
    let msg_blocks = (msg_bits.len() + 65 + 511) / 512;
    let msg_bits_len = msg_bits.len();

    assert_eq!(
        max_total_bits,
        targets.message.len(),
        "max_total_bits ({}) must match message target length ({})",
        max_total_bits,
        targets.message.len()
    );
    assert!(
        max_total_bits >= msg_blocks * 512,
        "Message too long: needs {} bits but circuit only supports {} bits",
        msg_blocks * 512,
        max_total_bits
    );

    pw.set_u32_target(targets.msg_len, msg_bits_len as u32)?;
    pw.set_u32_target(targets.msg_blocks, msg_blocks as u32)?;

    for i in 0..max_total_bits {
        let bit = if i < msg_bits_len {
            msg_bits[i]
        } else if i == msg_bits_len {
            true // the mandatory `1` bit
        } else if i >= msg_blocks * 512 - 64 {
            // length encoding, big-endian
            ((msg_bits_len >> (msg_blocks * 512 - i - 1)) & 1) == 1
        } else {
            false
        };
        pw.set_bool_target(targets.message[i], bit)?;
    }
    Ok(())
}

#[cfg(test)]
pub mod tests {
    use plonky2::{
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::CircuitConfig,
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };
    use sha2::Digest;

    use crate::circuit::{
        array_to_bits, fill_variable_length_circuits, make_circuits, make_variable_length_circuits,
        EXAMPLE_MESSAGE,
    };

    #[test]
    fn test_sha256_circuit() -> anyhow::Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::wide_ecc_config());

        let msg = EXAMPLE_MESSAGE;

        let digest = sha2::Sha256::digest(&msg);
        let msg_len_in_bits = (msg.len() * 8) as usize;

        // Create SHA256 circuit using your make_circuits function
        let sha256_targets = make_circuits(&mut builder, msg_len_in_bits as u64);

        // Create witness
        let mut pw = PartialWitness::new();

        // Convert message bytes to bits and set as witness
        let msg_bits = array_to_bits(&msg);
        for (i, &bit) in msg_bits.iter().enumerate().take(msg_len_in_bits as usize) {
            pw.set_bool_target(sha256_targets.message[i], bit)?;
        }

        // Convert expected digest bytes to bits and set as witness
        let expected_digest_bits = array_to_bits(&digest);
        for (i, expected_digest_bit) in expected_digest_bits.iter().enumerate() {
            if *expected_digest_bit {
                builder.assert_one(sha256_targets.digest[i].target);
            } else {
                builder.assert_zero(sha256_targets.digest[i].target);
            }
        }

        println!(
            "Constructing inner proof with {} gates",
            builder.num_gates()
        );

        // Build the circuit
        let data = builder.build::<C>();

        // Generate proof
        let proof = data.prove(pw)?;

        // Verify proof
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_sha256_circuit_short() -> anyhow::Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::standard_recursion_config());

        let msg = [
            132, 106, 83, 105, 103, 110, 97, 116, 117, 114, 101, 49, 67, 161, 1, 38, 64, 89, 11,
            59, 216, 24, 89, 11, 54, 166, 103, 118, 101, 114, 115, 105, 111, 110, 99, 49, 46, 48,
            111, 100, 105, 103, 101, 115, 116, 65, 108, 103, 111, 114, 105, 116, 104, 109, 103, 83,
            72, 65, 45, 50, 53, 54, 108, 118, 97, 108, 117, 101, 68, 105, 103, 101, 115, 116, 115,
            162, 113, 111, 114, 103, 46, 105, 115, 111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49,
            184, 37, 26, 0, 29, 90, 114, 88, 32, 0, 23, 37,
        ];
        let digest = sha2::Sha256::digest(&msg);
        let msg_len_in_bits = (msg.len() * 8) as usize;

        // Create SHA256 circuit using your make_circuits function
        let sha256_targets = make_circuits(&mut builder, msg_len_in_bits as u64);

        // Create witness
        let mut pw = PartialWitness::new();

        // Convert message bytes to bits and set as witness
        let msg_bits = array_to_bits(&msg);
        for (i, &bit) in msg_bits.iter().enumerate().take(msg_len_in_bits as usize) {
            pw.set_bool_target(sha256_targets.message[i], bit)?;
        }

        // Convert expected digest bytes to bits and set as witness
        let expected_digest_bits = array_to_bits(&digest);
        for (i, expected_digest_bit) in expected_digest_bits.iter().enumerate() {
            if *expected_digest_bit {
                builder.assert_one(sha256_targets.digest[i].target);
            } else {
                builder.assert_zero(sha256_targets.digest[i].target);
            }
        }

        println!(
            "Constructing inner proof with {} gates",
            builder.num_gates()
        );

        // Build the circuit
        let data = builder.build::<C>();

        // Generate proof
        let proof = data.prove(pw)?;

        // Verify proof
        data.verify(proof)?;

        Ok(())
    }

    #[test]
    fn test_variable_length_sha256_circuit() -> anyhow::Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let mut builder = CircuitBuilder::<F, D>::new(CircuitConfig::wide_ecc_config());

        let msg = EXAMPLE_MESSAGE;

        let digest = sha2::Sha256::digest(&msg);

        let tot_bits = 512 * 48; // 48 blocks, instead of 47 blocks which is needed

        // Create SHA256 circuit using your make_circuits function
        let sha256_targets = make_variable_length_circuits(&mut builder, tot_bits);

        // Create witness
        let mut pw = PartialWitness::new();

        fill_variable_length_circuits::<F, D>(&mut pw, &msg, tot_bits, &sha256_targets)?;

        // Convert expected digest bytes to bits and set as witness
        let expected_digest_bits = array_to_bits(&digest);
        for (i, expected_digest_bit) in expected_digest_bits.iter().enumerate() {
            if *expected_digest_bit {
                builder.assert_one(sha256_targets.digest[i].target);
            } else {
                builder.assert_zero(sha256_targets.digest[i].target);
            }
        }

        println!(
            "Constructing inner proof with {} gates",
            builder.num_gates()
        );

        // Build the circuit
        let data = builder.build::<C>();

        // Generate proof
        let proof = data.prove(pw)?;

        // Verify proof
        data.verify(proof)?;

        Ok(())
    }
}

pub const EXAMPLE_MESSAGE: [u8; 2895] = [
    132, 106, 83, 105, 103, 110, 97, 116, 117, 114, 101, 49, 67, 161, 1, 38, 64, 89, 11, 59, 216,
    24, 89, 11, 54, 166, 103, 118, 101, 114, 115, 105, 111, 110, 99, 49, 46, 48, 111, 100, 105,
    103, 101, 115, 116, 65, 108, 103, 111, 114, 105, 116, 104, 109, 103, 83, 72, 65, 45, 50, 53,
    54, 108, 118, 97, 108, 117, 101, 68, 105, 103, 101, 115, 116, 115, 162, 113, 111, 114, 103, 46,
    105, 115, 111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49, 184, 37, 26, 0, 29, 90, 114, 88, 32, 0,
    23, 37, 162, 181, 131, 222, 171, 211, 23, 65, 85, 142, 70, 53, 49, 162, 57, 178, 226, 189, 22,
    158, 8, 172, 30, 58, 214, 172, 211, 63, 92, 26, 5, 51, 186, 144, 88, 32, 79, 33, 61, 17, 144,
    2, 164, 206, 42, 162, 44, 93, 104, 206, 187, 233, 138, 81, 28, 94, 26, 112, 124, 95, 199, 6,
    228, 190, 121, 138, 155, 148, 26, 9, 70, 177, 129, 88, 32, 168, 151, 237, 146, 99, 229, 5, 234,
    151, 165, 1, 85, 7, 180, 190, 160, 121, 72, 126, 111, 9, 196, 55, 179, 7, 87, 236, 61, 82, 169,
    230, 107, 26, 11, 59, 27, 255, 88, 32, 117, 247, 169, 196, 28, 191, 167, 95, 196, 64, 220, 230,
    155, 67, 148, 148, 142, 174, 117, 123, 207, 65, 89, 88, 95, 90, 254, 96, 69, 202, 92, 19, 26,
    16, 141, 148, 203, 88, 32, 26, 213, 99, 181, 216, 243, 106, 124, 137, 60, 194, 4, 31, 76, 253,
    171, 16, 53, 252, 140, 145, 145, 133, 209, 245, 110, 76, 27, 98, 246, 6, 129, 26, 18, 76, 19,
    4, 88, 32, 235, 206, 216, 83, 13, 46, 4, 70, 126, 176, 2, 235, 220, 52, 180, 168, 237, 35, 186,
    125, 201, 40, 202, 176, 90, 93, 198, 187, 100, 51, 155, 117, 26, 31, 37, 41, 180, 88, 32, 206,
    9, 179, 23, 18, 221, 168, 15, 211, 52, 82, 53, 189, 24, 187, 138, 194, 198, 132, 84, 215, 212,
    127, 9, 120, 226, 155, 252, 186, 6, 41, 152, 26, 32, 190, 247, 249, 88, 32, 184, 39, 8, 231,
    34, 192, 73, 200, 187, 145, 248, 117, 32, 173, 67, 214, 76, 115, 136, 63, 230, 240, 14, 245,
    97, 171, 199, 78, 189, 148, 227, 9, 26, 32, 245, 148, 173, 88, 32, 172, 204, 194, 244, 203, 52,
    178, 19, 135, 138, 142, 165, 165, 27, 212, 249, 102, 29, 209, 42, 206, 152, 66, 103, 90, 4,
    191, 58, 103, 167, 227, 102, 26, 36, 2, 101, 16, 88, 32, 212, 84, 117, 192, 25, 251, 162, 124,
    233, 228, 85, 72, 205, 242, 231, 113, 55, 42, 63, 170, 157, 225, 38, 164, 180, 60, 42, 14, 93,
    100, 128, 143, 26, 37, 19, 24, 221, 88, 32, 225, 171, 153, 134, 121, 65, 185, 166, 83, 200,
    112, 35, 154, 119, 52, 131, 201, 198, 33, 228, 134, 225, 132, 123, 169, 7, 249, 51, 97, 191, 3,
    164, 26, 39, 227, 109, 167, 88, 32, 174, 150, 58, 182, 132, 43, 25, 157, 167, 55, 130, 155, 11,
    66, 127, 243, 162, 241, 64, 213, 185, 158, 236, 122, 236, 37, 157, 162, 73, 85, 67, 1, 26, 39,
    246, 69, 67, 88, 32, 196, 91, 141, 230, 214, 186, 89, 204, 153, 136, 24, 135, 72, 36, 4, 11,
    138, 245, 63, 118, 24, 119, 95, 42, 173, 177, 183, 143, 155, 160, 13, 129, 26, 42, 132, 127,
    127, 88, 32, 251, 82, 151, 230, 221, 106, 220, 216, 186, 15, 22, 153, 253, 177, 69, 136, 79,
    114, 244, 10, 79, 9, 183, 134, 145, 112, 16, 164, 70, 52, 50, 149, 26, 55, 198, 235, 212, 88,
    32, 93, 191, 141, 69, 76, 113, 207, 38, 205, 160, 243, 220, 131, 12, 203, 140, 167, 33, 3, 124,
    245, 25, 38, 207, 82, 17, 69, 138, 77, 60, 24, 97, 26, 60, 7, 70, 206, 88, 32, 50, 69, 63, 130,
    245, 185, 21, 89, 253, 239, 134, 109, 44, 89, 100, 11, 69, 13, 125, 195, 23, 42, 122, 86, 50,
    202, 227, 235, 225, 92, 123, 139, 26, 60, 59, 125, 23, 88, 32, 189, 69, 36, 135, 113, 16, 146,
    125, 252, 88, 72, 22, 192, 213, 7, 173, 156, 3, 103, 152, 139, 1, 199, 199, 236, 213, 9, 1,
    166, 147, 121, 208, 26, 64, 139, 72, 16, 88, 32, 191, 23, 215, 183, 15, 163, 46, 36, 212, 2,
    69, 162, 188, 122, 56, 124, 135, 69, 156, 79, 0, 216, 198, 223, 90, 170, 59, 44, 38, 7, 30,
    213, 26, 72, 141, 193, 46, 88, 32, 149, 235, 216, 215, 68, 204, 134, 76, 86, 60, 167, 72, 232,
    226, 3, 223, 19, 229, 137, 19, 104, 105, 117, 18, 249, 243, 171, 61, 75, 160, 220, 33, 26, 80,
    179, 160, 152, 88, 32, 22, 106, 42, 179, 74, 192, 12, 8, 222, 1, 134, 223, 19, 0, 134, 109,
    145, 12, 38, 133, 206, 19, 120, 137, 247, 131, 238, 166, 38, 232, 152, 218, 26, 84, 2, 61, 60,
    88, 32, 163, 235, 203, 202, 189, 191, 219, 33, 114, 74, 230, 18, 5, 56, 138, 6, 31, 79, 77,
    160, 180, 6, 253, 213, 141, 244, 251, 143, 19, 203, 127, 42, 26, 88, 131, 199, 83, 88, 32, 211,
    60, 87, 185, 164, 108, 175, 29, 145, 33, 190, 195, 39, 33, 86, 215, 89, 83, 33, 43, 144, 43,
    98, 142, 197, 180, 89, 245, 55, 27, 159, 50, 26, 91, 17, 203, 23, 88, 32, 194, 27, 93, 207,
    130, 141, 223, 251, 131, 1, 150, 81, 117, 223, 205, 238, 238, 145, 50, 67, 83, 56, 54, 73, 66,
    239, 27, 122, 157, 243, 215, 141, 26, 98, 17, 110, 140, 88, 32, 140, 60, 196, 229, 113, 72,
    101, 197, 5, 86, 207, 139, 46, 60, 25, 58, 42, 247, 55, 101, 83, 56, 171, 108, 160, 100, 30,
    116, 156, 80, 127, 68, 26, 101, 13, 47, 218, 88, 32, 149, 142, 243, 3, 14, 58, 171, 158, 225,
    23, 110, 213, 201, 131, 238, 219, 189, 36, 107, 179, 71, 138, 140, 129, 6, 68, 63, 109, 198,
    247, 88, 145, 26, 102, 183, 189, 149, 88, 32, 77, 186, 200, 252, 159, 18, 48, 202, 90, 180,
    246, 80, 50, 246, 2, 203, 98, 57, 24, 247, 246, 105, 248, 35, 242, 107, 97, 100, 24, 107, 82,
    135, 26, 104, 72, 31, 153, 88, 32, 40, 137, 176, 125, 248, 196, 103, 229, 48, 118, 15, 46, 51,
    41, 222, 89, 118, 81, 224, 254, 184, 36, 120, 59, 217, 219, 214, 200, 200, 134, 187, 173, 26,
    104, 243, 40, 182, 88, 32, 83, 200, 172, 130, 180, 107, 35, 21, 252, 3, 185, 100, 89, 227, 32,
    109, 206, 220, 97, 133, 236, 141, 199, 115, 134, 197, 23, 216, 176, 170, 221, 101, 26, 109,
    131, 155, 196, 88, 32, 111, 110, 103, 60, 59, 210, 78, 128, 89, 9, 80, 221, 57, 175, 165, 32,
    58, 131, 72, 222, 190, 48, 225, 149, 42, 233, 183, 71, 124, 44, 96, 157, 26, 110, 39, 161, 94,
    88, 32, 122, 165, 97, 6, 40, 155, 139, 197, 45, 230, 240, 88, 74, 159, 37, 121, 164, 21, 45,
    133, 192, 15, 86, 3, 148, 222, 113, 230, 161, 243, 136, 247, 26, 116, 214, 212, 97, 88, 32, 41,
    64, 139, 151, 160, 171, 112, 67, 69, 142, 163, 249, 74, 200, 152, 33, 141, 188, 98, 144, 60,
    244, 97, 31, 139, 7, 236, 109, 251, 209, 168, 233, 26, 117, 56, 194, 106, 88, 32, 145, 22, 121,
    126, 152, 254, 56, 247, 12, 33, 54, 181, 130, 112, 221, 14, 29, 188, 7, 97, 231, 246, 71, 237,
    43, 70, 61, 122, 118, 125, 224, 84, 26, 117, 176, 165, 136, 88, 32, 172, 253, 147, 205, 134,
    219, 168, 156, 85, 29, 4, 74, 99, 196, 60, 153, 27, 197, 246, 142, 173, 188, 173, 129, 29, 199,
    15, 209, 61, 80, 214, 249, 26, 122, 115, 88, 180, 88, 32, 120, 180, 131, 35, 206, 217, 212,
    183, 42, 124, 233, 30, 221, 222, 214, 15, 56, 75, 11, 143, 199, 70, 235, 8, 161, 127, 251, 171,
    42, 22, 165, 48, 26, 125, 66, 8, 38, 88, 32, 245, 115, 174, 229, 40, 175, 104, 165, 56, 127,
    215, 139, 91, 14, 121, 104, 249, 159, 226, 7, 103, 82, 51, 166, 238, 86, 28, 226, 190, 133,
    153, 49, 26, 126, 184, 21, 149, 88, 32, 21, 137, 175, 237, 34, 93, 254, 68, 140, 40, 0, 246,
    94, 17, 224, 31, 182, 92, 158, 14, 212, 3, 62, 228, 185, 120, 102, 226, 253, 107, 234, 44, 26,
    127, 211, 18, 34, 88, 32, 159, 27, 163, 39, 242, 219, 92, 132, 147, 43, 200, 138, 14, 151, 167,
    248, 195, 198, 184, 71, 99, 162, 139, 26, 145, 118, 157, 223, 26, 170, 109, 104, 119, 111, 114,
    103, 46, 105, 115, 111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49, 46, 97, 97, 109, 118, 97, 184,
    28, 26, 1, 217, 132, 206, 88, 32, 205, 124, 69, 171, 211, 108, 76, 173, 200, 214, 182, 222, 39,
    167, 226, 168, 23, 41, 114, 35, 236, 95, 202, 173, 199, 234, 76, 84, 35, 48, 58, 240, 26, 8,
    255, 11, 195, 88, 32, 62, 191, 17, 238, 143, 108, 126, 7, 214, 152, 107, 146, 40, 207, 238, 1,
    97, 202, 43, 229, 24, 35, 227, 3, 158, 221, 10, 152, 233, 87, 167, 47, 26, 10, 248, 212, 141,
    88, 32, 172, 43, 175, 195, 57, 138, 245, 28, 177, 125, 39, 152, 153, 227, 90, 126, 108, 143,
    169, 140, 238, 210, 177, 51, 253, 241, 34, 206, 64, 108, 91, 19, 26, 11, 223, 37, 249, 88, 32,
    251, 111, 29, 129, 23, 135, 255, 253, 26, 109, 203, 19, 183, 231, 108, 248, 210, 97, 82, 7, 3,
    219, 165, 145, 31, 83, 96, 30, 205, 82, 202, 32, 26, 13, 103, 170, 130, 88, 32, 152, 223, 43,
    248, 47, 153, 240, 56, 128, 176, 118, 203, 235, 70, 7, 174, 123, 149, 166, 228, 167, 12, 65,
    253, 143, 241, 237, 251, 93, 153, 224, 219, 26, 15, 46, 96, 115, 88, 32, 245, 107, 239, 71,
    157, 65, 18, 213, 233, 166, 88, 242, 154, 98, 67, 148, 153, 94, 23, 8, 127, 4, 86, 221, 240,
    236, 198, 250, 20, 175, 146, 185, 26, 22, 12, 92, 86, 88, 32, 69, 165, 231, 235, 43, 28, 100,
    27, 168, 205, 146, 52, 254, 171, 11, 107, 3, 100, 80, 3, 75, 105, 12, 241, 95, 66, 148, 232,
    207, 163, 96, 67, 26, 30, 60, 153, 139, 88, 32, 238, 152, 224, 55, 11, 22, 78, 208, 45, 15, 38,
    162, 140, 186, 98, 42, 65, 73, 97, 82, 85, 115, 44, 135, 50, 77, 249, 227, 182, 143, 243, 148,
    26, 39, 163, 205, 187, 88, 32, 195, 3, 138, 214, 14, 70, 62, 117, 94, 207, 95, 203, 221, 72,
    204, 12, 174, 202, 107, 249, 194, 70, 45, 100, 24, 87, 239, 217, 189, 141, 19, 18, 26, 40, 5,
    57, 184, 88, 32, 110, 167, 197, 32, 222, 164, 154, 54, 161, 28, 153, 131, 63, 236, 155, 149,
    153, 155, 170, 9, 109, 57, 48, 62, 41, 131, 167, 219, 65, 8, 95, 205, 26, 43, 187, 39, 172, 88,
    32, 37, 71, 227, 27, 232, 191, 254, 249, 26, 98, 76, 255, 183, 147, 110, 20, 219, 77, 208, 170,
    47, 215, 68, 138, 130, 116, 108, 230, 219, 157, 115, 78, 26, 45, 3, 244, 3, 88, 32, 201, 49,
    168, 66, 235, 108, 13, 230, 34, 141, 29, 142, 234, 247, 198, 255, 42, 42, 118, 199, 155, 188,
    218, 5, 85, 212, 241, 106, 168, 160, 233, 24, 26, 51, 164, 43, 38, 88, 32, 80, 50, 96, 61, 8,
    227, 179, 14, 204, 131, 186, 31, 66, 0, 245, 239, 220, 241, 145, 236, 177, 244, 138, 34, 242,
    221, 52, 41, 186, 4, 189, 28, 26, 54, 237, 213, 90, 88, 32, 77, 157, 208, 219, 24, 133, 150,
    123, 181, 59, 102, 215, 176, 165, 230, 145, 111, 144, 172, 41, 83, 195, 148, 123, 88, 116, 251,
    61, 10, 105, 216, 9, 26, 56, 203, 42, 67, 88, 32, 230, 187, 113, 27, 121, 122, 126, 31, 71,
    210, 174, 124, 110, 171, 42, 0, 177, 105, 120, 223, 28, 255, 184, 242, 227, 201, 42, 50, 188,
    234, 214, 197, 26, 58, 230, 34, 31, 88, 32, 252, 59, 14, 92, 242, 245, 53, 163, 121, 34, 114,
    195, 6, 78, 209, 40, 94, 211, 232, 218, 4, 117, 53, 218, 155, 254, 194, 43, 52, 223, 217, 30,
    26, 77, 11, 202, 209, 88, 32, 5, 48, 99, 78, 125, 216, 185, 121, 78, 59, 147, 217, 187, 83,
    101, 86, 190, 198, 227, 64, 136, 223, 139, 249, 17, 88, 47, 44, 73, 183, 10, 72, 26, 77, 28,
    37, 189, 88, 32, 145, 254, 192, 168, 89, 203, 41, 82, 194, 12, 110, 0, 195, 219, 78, 178, 51,
    123, 185, 17, 131, 56, 169, 78, 122, 81, 219, 117, 100, 224, 118, 166, 26, 78, 188, 33, 204,
    88, 32, 111, 200, 190, 208, 27, 141, 77, 95, 148, 89, 212, 145, 75, 210, 66, 235, 87, 112, 50,
    50, 140, 158, 126, 36, 86, 225, 34, 22, 211, 208, 67, 217, 26, 83, 126, 41, 225, 88, 32, 203,
    35, 64, 159, 67, 85, 221, 255, 164, 241, 61, 162, 137, 179, 145, 81, 11, 18, 15, 67, 190, 188,
    46, 142, 121, 120, 214, 25, 166, 95, 99, 182, 26, 85, 97, 151, 192, 88, 32, 83, 62, 160, 118,
    35, 226, 229, 28, 194, 83, 83, 109, 127, 149, 48, 159, 22, 57, 42, 223, 214, 111, 43, 147, 252,
    241, 65, 78, 69, 50, 85, 227, 26, 93, 29, 158, 115, 88, 32, 176, 76, 92, 214, 10, 181, 179,
    194, 15, 83, 192, 166, 132, 181, 157, 240, 11, 169, 193, 145, 156, 240, 142, 190, 235, 175,
    238, 232, 166, 24, 178, 248, 26, 112, 52, 183, 253, 88, 32, 136, 241, 71, 66, 180, 80, 168, 44,
    148, 135, 113, 158, 55, 167, 48, 4, 215, 155, 30, 173, 184, 53, 58, 77, 44, 13, 242, 37, 0, 92,
    10, 217, 26, 113, 49, 205, 160, 88, 32, 22, 227, 253, 244, 146, 108, 191, 68, 240, 184, 138,
    179, 136, 3, 169, 42, 210, 235, 218, 98, 14, 209, 220, 65, 55, 37, 3, 141, 5, 53, 158, 135, 26,
    115, 14, 74, 87, 88, 32, 225, 82, 215, 38, 25, 180, 50, 89, 157, 193, 251, 72, 100, 40, 79,
    176, 225, 45, 76, 205, 126, 163, 86, 244, 67, 174, 219, 6, 188, 224, 58, 204, 26, 118, 245, 25,
    197, 88, 32, 141, 10, 92, 157, 110, 227, 137, 6, 116, 204, 111, 248, 123, 78, 154, 1, 175, 198,
    235, 94, 26, 37, 143, 65, 168, 237, 165, 94, 20, 96, 56, 255, 26, 121, 213, 188, 92, 88, 32,
    100, 51, 157, 121, 59, 247, 130, 233, 125, 174, 146, 190, 9, 123, 81, 232, 225, 166, 232, 202,
    127, 45, 95, 245, 185, 154, 63, 110, 185, 86, 93, 53, 26, 127, 125, 179, 36, 88, 32, 158, 117,
    112, 157, 43, 11, 91, 15, 36, 201, 238, 106, 111, 66, 170, 96, 20, 59, 60, 10, 63, 197, 73, 20,
    156, 105, 110, 114, 72, 125, 6, 123, 109, 100, 101, 118, 105, 99, 101, 75, 101, 121, 73, 110,
    102, 111, 161, 105, 100, 101, 118, 105, 99, 101, 75, 101, 121, 164, 1, 2, 32, 1, 33, 88, 32,
    89, 252, 92, 128, 6, 172, 82, 163, 148, 121, 193, 170, 186, 203, 189, 29, 86, 252, 185, 143,
    238, 170, 24, 35, 52, 196, 91, 58, 118, 9, 2, 158, 34, 88, 32, 63, 80, 30, 94, 32, 131, 12,
    112, 181, 162, 255, 58, 6, 144, 162, 46, 151, 130, 187, 44, 26, 118, 254, 121, 137, 82, 218,
    236, 89, 158, 221, 77, 103, 100, 111, 99, 84, 121, 112, 101, 117, 111, 114, 103, 46, 105, 115,
    111, 46, 49, 56, 48, 49, 51, 46, 53, 46, 49, 46, 109, 68, 76, 108, 118, 97, 108, 105, 100, 105,
    116, 121, 73, 110, 102, 111, 163, 102, 115, 105, 103, 110, 101, 100, 192, 116, 50, 48, 50, 51,
    45, 49, 49, 45, 48, 55, 84, 49, 53, 58, 52, 49, 58, 48, 54, 90, 105, 118, 97, 108, 105, 100,
    70, 114, 111, 109, 192, 116, 50, 48, 50, 51, 45, 49, 49, 45, 48, 55, 84, 49, 53, 58, 52, 49,
    58, 48, 54, 90, 106, 118, 97, 108, 105, 100, 85, 110, 116, 105, 108, 192, 116, 50, 48, 50, 51,
    45, 49, 49, 45, 48, 55, 84, 49, 53, 58, 52, 49, 58, 48, 54, 90,
];
