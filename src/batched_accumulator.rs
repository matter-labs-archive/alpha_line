/// Memory constrained accumulator that checks parts of the initial information in parts that fit to memory
/// and then contributes to entropy in parts as well

extern crate pairing;
extern crate rand;
extern crate crossbeam;
extern crate num_cpus;
extern crate blake2;
extern crate generic_array;
extern crate typenum;
extern crate byteorder;
extern crate ff;
extern crate memmap;
extern crate itertools;

use itertools::Itertools;
use memmap::{Mmap, MmapMut};
use ff::{Field, PrimeField};
use byteorder::{ReadBytesExt, BigEndian};
use rand::{SeedableRng, Rng, Rand};
use rand::chacha::ChaChaRng;
use pairing::bn256::{Bn256};
use pairing::*;
use std::io::{self, Read, Write};
use std::sync::{Arc, Mutex};
use generic_array::GenericArray;
use typenum::consts::U64;
use blake2::{Blake2b, Digest};
use std::fmt;

use super::keypair::*;
use super::utils::*;
use super::parameters::*;

pub enum AccumulatorState{
    Empty,
    NonEmpty,
    Transformed,
}

/// The `Accumulator` is an object that participants of the ceremony contribute
/// randomness to. This object contains powers of trapdoor `tau` in G1 and in G2 over
/// fixed generators, and additionally in G1 over two other generators of exponents
/// `alpha` and `beta` over those fixed generators. In other words:
///
/// * (τ, τ<sup>2</sup>, ..., τ<sup>2<sup>22</sup> - 2</sup>, α, ατ, ατ<sup>2</sup>, ..., ατ<sup>2<sup>21</sup> - 1</sup>, β, βτ, βτ<sup>2</sup>, ..., βτ<sup>2<sup>21</sup> - 1</sup>)<sub>1</sub>
/// * (β, τ, τ<sup>2</sup>, ..., τ<sup>2<sup>21</sup> - 1</sup>)<sub>2</sub>
pub struct BachedAccumulator<E: Engine, P: CeremonyParameters> {
    pub g1_x_powers: Vec<E::G1Affine>,
    pub g1_alpha_x_powers: Vec<E::G1Affine>,
    pub g2_x_powers: Vec<E::G2Affine>,
    pub g2_alpha_x_powers: Vec<E::G2Affine>,
    pub g2_alpha: E::G2Affine,
    /// Hash chain hash
    pub hash: GenericArray<u8, U64>,
    /// Keep parameters here as a marker
    marker: std::marker::PhantomData<P>,
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    /// Calcualte the contibution hash from the resulting file. Original powers of tau implementaiton
    /// used a specially formed writer to write to the file and calculate a hash on the fly, but memory-constrained
    /// implementation now writes without a particular order, so plain recalculation at the end 
    /// of the procedure is more efficient
    pub fn calculate_hash(
        input_map: &Mmap
    ) -> GenericArray<u8, U64> {
        let chunk_size = 1 << 30; // read by 1GB from map
        let mut hasher = Blake2b::default();
        for chunk in input_map.chunks(chunk_size) {
            hasher.input(&chunk);
        }

        hasher.result()
    }
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    pub fn empty() -> Self {
        Self {
            g1_x_powers: vec![],
            g1_alpha_x_powers: vec![],
            g2_x_powers: vec![],
            g2_alpha_x_powers: vec![],
            g2_alpha: E::G2Affine::zero(),
            hash: blank_hash(),
            marker: std::marker::PhantomData::<P>{}
        }
    }
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    fn g1_size(compression: UseCompression) -> usize {
        match compression {
            UseCompression::Yes => {
                return P::G1_COMPRESSED_BYTE_SIZE;
            },
            UseCompression::No => {
                return P::G1_UNCOMPRESSED_BYTE_SIZE;
            }
        }
    } 

    fn g2_size(compression: UseCompression) -> usize {
        match compression {
            UseCompression::Yes => {
                return P::G2_COMPRESSED_BYTE_SIZE;
            },
            UseCompression::No => {
                return P::G2_UNCOMPRESSED_BYTE_SIZE;
            }
        }
    } 

    fn get_size(element_type: ElementType, compression: UseCompression) -> usize {
        let size = match element_type {
            ElementType::G1_alpha_x | ElementType::G1_x => { Self::g1_size(compression) },
            ElementType::G2_alpha_x | ElementType::G2_x | ElementType::G2_alpha => { Self::g2_size(compression) }
        };

        size
    }

    /// File expected structure
    /// HASH_SIZE bytes for the hash of the contribution
    /// 2*D of G1 points as g^(x^i)
    /// 2*D of G1 points as g^(alpha*x^i)
    /// 2*D of G2 points as h^(x^i), there is no h^(x^0) = h
    /// 2*D + 1 of G2 points as h^(alpha*x^i)
    /// One G2 point for beta
    /// Public key appended to the end of file, but it's irrelevant for an accumulator itself
    
    fn calculate_mmap_position(index: usize, element_type: ElementType, compression: UseCompression) -> usize {
        let g1_size = Self::g1_size(compression);
        let g2_size = Self::g2_size(compression);
        assert!(index < P::D*2, format!("Index for element must be below {}, while it's {}", P::D*2, index));
        let d = P::D;
        let position = match element_type {
            ElementType::G1_x => {
                let mut position = 0;
                position += g1_size * index;

                position
            },
            ElementType::G1_alpha_x => {
                let mut position = 0;
                position += g1_size * 2 * d;
                position += g1_size * index;

                position
            },
            ElementType::G2_x => {
                let mut position = 0;
                position += g1_size * 2 * d;
                position += g1_size * 2 * d;
                position += g2_size * index;

                position   
            },
            ElementType::G2_alpha_x => {
                let mut position = 0;
                position += g1_size * 2 * d;
                position += g1_size * 2 * d;
                position += g2_size * 2 * d;
                position += g2_size * index;

                position   
            },
            ElementType::G2_alpha => {
                let mut position = 0;
                position += g1_size * 2 * d;
                position += g1_size * 2 * d;
                position += g2_size * 2 * d;
                position += g2_size * 2 * d;

                position   
            },
        };

        position + P::HASH_SIZE
    }
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    /// Verifies a transformation of the `Accumulator` with the `PublicKey`, given a 64-byte transcript `digest`.
    pub fn verify_transformation(
        input_map: &Mmap,
        output_map: &Mmap,
        key: &PublicKey<E>, 
        digest: &[u8],
        input_is_compressed: UseCompression,
        output_is_compressed: UseCompression,
        check_input_for_correctness: CheckForCorrectness,
        check_output_for_correctness: CheckForCorrectness,
    ) -> bool
    {
        use itertools::MinMaxResult::{MinMax};
        assert_eq!(digest.len(), 64);

        let x_g2_s = compute_g2_s::<E>(&digest, &key.x_g1.0, &key.x_g1.1, 0);
        let alpha_g2_s = compute_g2_s::<E>(&digest, &key.alpha_x_g1.0, &key.alpha_x_g1.1, 1);
        // Check the proofs-of-knowledge for x and alpha
        
        // g1^s / g1^(s*x) = g2^s / g2^(s*x)
        if !same_ratio(key.x_g1, (x_g2_s, key.x_g2)) {
            println!("Invalid ratio for knowledge of x");
            return false;
        }
        // g1^s' / g1^(s'*alpha) = g2^s' / g2^(s'*alpha)
        if !same_ratio(key.alpha_x_g1, (alpha_g2_s, key.alpha_x_g2)) {
            println!("Invalid ratio for knowledge of alpha");
            return false;
        }

        // Load accumulators AND perform computations

        let mut before = Self::empty();
        let mut after = Self::empty();

        let expected_position_for_minus_two = power_to_zero_index::<P>(-2i64);
        // these checks only touch a part of the accumulator, so read two elements
        {
            let chunk_size = 4;
            before.read_chunk(expected_position_for_minus_two, chunk_size, input_is_compressed, check_input_for_correctness, &input_map).expect("must read a first chunk");
            after.read_chunk(expected_position_for_minus_two, chunk_size, output_is_compressed, check_output_for_correctness, &output_map).expect("must read a first chunk");

            // after.g1_x_powers = [g^(x^-2 * x_old^-2),
            //                      g^(x^-1 * x_old^-1),
            //                      g^(x^1 * x_old^1),
            //                      g^(x^2 * x_old^2)]

            // after.g2_x_powers = [h^(x^-2 * x_old^-2),
            //                      h^(x^-1 * x_old^-1),
            //                      h^(x^1 * x_old^1),
            //                      h^(x^2 * x_old^2)]

            // after.g1_alpha_x_powers = [g^(x^-2 * x_old^-2 * alpha*alpha_old),
            //                            g^(x^-1 * x_old^-1 * alpha*alpha_old),
            //                            g^(x^1 * x_old^1 * alpha*alpha_old),
            //                            g^(x^2 * x_old^2 * alpha*alpha_old)]

            // after.g2_alpha_x_powers = [h^(x^-2 * x_old^-2 * alpha*alpha_old),
            //                            h^(x^-1 * x_old^-1 * alpha*alpha_old),
            //                            h^(x^1 * x_old^1 * alpha*alpha_old),
            //                            h^(x^2 * x_old^2 * alpha*alpha_old)]

            // after.g2_alpha = h^(alpha * alpha_old)

            // before.g1_x_powers = [g^(x_old^-2),
            //                      g^(x_old^-1),
            //                      g^(x_old^1),
            //                      g^(x_old^1)]

            // before.g2_x_powers = [h^(x_old^-2),
            //                      h^(x_old^-1),
            //                      h^(x_old^1),
            //                      h^(x_old^2)]

            // before.g1_alpha_x_powers = [g^(x_old^-2 * alpha_old),
            //                            g^(x_old^-1 * alpha_old),
            //                            g^(x_old^1 * alpha_old),
            //                            g^(x_old^2 * alpha_old)]

            // before.g2_alpha_x_powers = [h^(x_old^-2 * alpha_old),
            //                            h^(x_old^-1 * alpha_old),
            //                            h^(x_old^1 * alpha_old),
            //                            h^(x_old^2 * alpha_old)]

            // before.g2_alpha = h^(alpha_old)

            // Trivial check for an alpha contribution
            // alpha_old*H -> alpha_old*alpha*H in G2
            if !same_ratio(key.alpha_x_g1, (before.g2_alpha, after.g2_alpha)) {
                println!("s*g / alpha*s*g != alpha_old*h / alpha*alpha_old*h");
                return false;
            }

            // one can imagine the following checks before checking for the same powers:
            // after.g1_x_power[2] / before.g1_x_power[2] = ~x = key.x_g2_s / x_g2_s
            // after.g1_x_power[1] / before.g1_x_power[1] = ~x^(-1) = x_g2_s / key.x_g2_s - just the inverse

            if !same_ratio((after.g1_x_powers[2], before.g1_x_powers[2]), (key.x_g2, x_g2_s)) {
                println!("Invalid ratio after.g1_x_power[1] / before.g1_x_power[1] = ~x = key.x_g2_s / x_g2_s");
                return false;
            }

            if !same_ratio((after.g1_x_powers[1], before.g1_x_powers[1]), (x_g2_s, key.x_g2)) {
                println!("Invalid ratio after.g1_x_power[0] / before.g1_x_power[0] = ~x^(-1) = x_g2_s / key.x_g2_s");
                return false;
            }

            // and the same for g2
            if !same_ratio((key.x_g1.1, key.x_g1.0), (after.g2_x_powers[2], before.g2_x_powers[2])) {
                println!("Invalid ratio (key.x_g1.1, key.x_g1.0) = ~x = after.g2_x_powers[2] / before.g2_x_power[2]");
                return false;
            }

            if !same_ratio(key.x_g1, (after.g2_x_powers[1], before.g2_x_powers[1])) {
                println!("Invalid ratio key.x_g1 = key.x_g1_s / key.x_g1_s_x = ~x^(-1) = after.g2_x_power[1] / before.g2_x_power[1]");
                return false;
            }

            // after.g1_alpha_x_power[3] / after.g1_alpha_x_power[2] = ~x*x_old = after.g2_x_power[2] / g2
            // after.g1_alpha_x_power[1] / after.g1_alpha_x_power[0] = ~x*x_old = after.g2_x_power[2] / g2

            if !same_ratio((after.g1_alpha_x_powers[3], after.g1_alpha_x_powers[2]), (after.g2_x_powers[2], E::G2Affine::one())) {
                println!("Invalid ratio after.g1_alpha_x_power[3] / after.g1_alpha_x_power[2] = ~x*x_old = after.g2_x_power[2] / g2");
                return false;
            }

            if !same_ratio((after.g1_alpha_x_powers[1], after.g1_alpha_x_powers[0]), (after.g2_x_powers[2], E::G2Affine::one())) {
                println!("Invalid ratio after.g1_alpha_x_power[1] / after.g1_alpha_x_power[0] = ~x*x_old = after.g2_x_power[2] / g2");
                return false;
            }            
            // and same for g2
            if !same_ratio((after.g1_x_powers[2], E::G1Affine::one()), (after.g2_alpha_x_powers[3], after.g2_alpha_x_powers[2]), ) {
                println!("Invalid ratio after.g1_alpha_x_power[3] / after.g1_alpha_x_power[2] = ~x*x_old = after.g2_x_power[2] / g2");
                return false;
            }

            if !same_ratio((after.g1_x_powers[2], E::G1Affine::one()), (after.g2_alpha_x_powers[1], after.g2_alpha_x_powers[0])) {
                println!("Invalid ratio after.g1_alpha_x_power[1] / after.g1_alpha_x_power[0] = ~x*x_old = after.g2_x_power[2] / g2");
                return false;
            }

            // after.g1_alpha_x_power[2] / after.g1_x_power[2] = ~alpha*alpha_old = after.g2_alpha / g2
            // after.g1_alpha_x_power[1] / after.g1_x_power[1] = ~alpha*alpha_old = after.g2_alpha / g2

            if !same_ratio((after.g1_alpha_x_powers[2], after.g1_x_powers[2]), (after.g2_alpha, E::G2Affine::one())) {
                println!("Invalid ratio after.g1_alpha_x_power[2] / after.g1_x_power[2] = ~alpha*alpha_old = after.g2_alpha / g2");
                return false;
            }

            if !same_ratio((after.g1_alpha_x_powers[1], after.g1_x_powers[1]), (after.g2_alpha, E::G2Affine::one())) {
                println!("Invalid ratio after.g1_alpha_x_power[1] / after.g1_x_power[1] = ~alpha*alpha_old = after.g2_alpha / g2");
                return false;
            }
            // here same trick for g2 is not possible due to lack of g1^(alpha * alpha_old) in an accumulator,
            // so we check same ration in g1 and g2
            if !same_ratio((after.g1_alpha_x_powers[2], after.g1_x_powers[2]), (after.g2_alpha_x_powers[2], after.g2_x_powers[2])) {
                println!("Invalid ratio after.g1_alpha_x_power[2] / after.g1_x_power[2] = ~alpha*alpha_old = after.g2_alpha_x_power[2] / after.g2_x_power[2]");
                return false;
            }

            if !same_ratio((after.g1_alpha_x_powers[1], after.g1_x_powers[1]), (after.g2_alpha_x_powers[1], after.g2_x_powers[1])) {
                println!("Invalid ratio after.g1_alpha_x_power[1] / after.g1_x_power[1] = ~alpha*alpha_old = after.g2_alpha_x_power[1] / after.g2_x_power[1]");
                return false;
            }
        }

        let x_powers_g2_1 = after.g2_x_powers[2].clone();
        let x_powers_g2_2 = after.g2_x_powers[3].clone();
        let x_powers_g1_1 = after.g1_x_powers[2].clone();
        let x_powers_g1_2 = after.g1_x_powers[3].clone();

        // Read by parts and just verify same ratios. Cause of two fixed variables above with x_powers_g2_2 = x_powers_g2_1 ^ x
        // one does not need to care about some overlapping
        
        for chunk in &(0..P::D).into_iter().chunks(P::EMPIRICAL_BATCH_SIZE) {
            if let MinMax(start, end) = chunk.minmax() {
                let size = end - start + 1;
                before.read_chunk(start, size, input_is_compressed, check_input_for_correctness, &input_map).expect("must read a first chunk");
                after.read_chunk(start, size, output_is_compressed, check_output_for_correctness, &output_map).expect("must read a first chunk");
                println!("Processing powers from {} to {}", zero_index_to_power::<P>(start), zero_index_to_power::<P>(end));
                // Are the powers of tau correct?
                if !same_ratio(power_pairs(&after.g1_x_powers), (x_powers_g2_1, x_powers_g2_2)) {
                    println!("Invalid ratio power_pairs(&after.tau_powers_g1), (tau_powers_g2_0, tau_powers_g2_1)");
                    return false;
                }
                if !same_ratio(power_pairs(&after.g2_x_powers), (x_powers_g1_1, x_powers_g1_2)) {
                    println!("Invalid ratio power_pairs(&after.tau_powers_g2), (tau_powers_g1_0, tau_powers_g1_1)");
                    return false;
                }
                if !same_ratio(power_pairs(&after.g1_alpha_x_powers), (x_powers_g2_1, x_powers_g2_2)) {
                    println!("Invalid ratio power_pairs(&after.alpha_tau_powers_g1), (tau_powers_g2_0, tau_powers_g2_1)");
                    return false;
                }
                if !same_ratio(power_pairs(&after.g2_alpha_x_powers), (x_powers_g1_1, x_powers_g1_2)) {
                    println!("Invalid ratio power_pairs(&after.beta_tau_powers_g1), (tau_powers_g2_0, tau_powers_g2_1)");
                    return false;
                }
            } else {
                panic!("Chunk does not have a min and max");
            }
        }

        println!("Negative powers are ok");

        for chunk in &(P::D..P::D*2).into_iter().chunks(P::EMPIRICAL_BATCH_SIZE) {
            if let MinMax(start, end) = chunk.minmax() {
                let size = end - start + 1;
                before.read_chunk(start, size, input_is_compressed, check_input_for_correctness, &input_map).expect("must read a first chunk");
                after.read_chunk(start, size, output_is_compressed, check_output_for_correctness, &output_map).expect("must read a first chunk");
                println!("Processing powers from {} to {}", zero_index_to_power::<P>(start), zero_index_to_power::<P>(end));
                // Are the powers of tau correct?
                if !same_ratio(power_pairs(&after.g1_x_powers), (x_powers_g2_1, x_powers_g2_2)) {
                    println!("Invalid ratio power_pairs(&after.tau_powers_g1), (tau_powers_g2_0, tau_powers_g2_1)");
                    return false;
                }
                if !same_ratio(power_pairs(&after.g2_x_powers), (x_powers_g1_1, x_powers_g1_2)) {
                    println!("Invalid ratio power_pairs(&after.tau_powers_g2), (tau_powers_g1_0, tau_powers_g1_1)");
                    return false;
                }
                if !same_ratio(power_pairs(&after.g1_alpha_x_powers), (x_powers_g2_1, x_powers_g2_2)) {
                    println!("Invalid ratio power_pairs(&after.alpha_tau_powers_g1), (tau_powers_g2_0, tau_powers_g2_1)");
                    return false;
                }
                if !same_ratio(power_pairs(&after.g2_alpha_x_powers), (x_powers_g1_1, x_powers_g1_2)) {
                    println!("Invalid ratio power_pairs(&after.beta_tau_powers_g1), (tau_powers_g2_0, tau_powers_g2_1)");
                    return false;
                }
            } else {
                panic!("Chunk does not have a min and max");
            }
        }

        println!("Positive powers are ok");

        true
    }

    pub fn decompress(
        input_map: &Mmap,
        output_map: &mut MmapMut,
        check_input_for_correctness: CheckForCorrectness,
    ) -> io::Result<()>
    {
        use itertools::MinMaxResult::{MinMax};

        let mut accumulator = Self::empty();
    
        for chunk in &(0..P::D*2).into_iter().chunks(P::EMPIRICAL_BATCH_SIZE) {
            if let MinMax(start, end) = chunk.minmax() {
                let size = end - start + 1;
                accumulator.read_chunk(start, size, UseCompression::Yes, check_input_for_correctness, &input_map).expect("Must read a chunk");
                accumulator.write_chunk(start, UseCompression::No, output_map)?;
            } else {
                panic!("Chunk does not have a min and max");
            }
        }
        
        Ok(())
    }
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
        pub fn read_chunk (
        &mut self,
        from: usize,
        size: usize,
        compression: UseCompression,
        checked: CheckForCorrectness,
        input_map: &Mmap,
    ) -> Result<(), DeserializationError>
    {
        self.g1_x_powers = match compression {
            UseCompression::Yes => {
                self.read_points_chunk::<<E::G1Affine as CurveAffine>::Compressed>(from, size, ElementType::G1_x, compression, checked, &input_map)?
            },
            UseCompression::No => {
                self.read_points_chunk::<<E::G1Affine as CurveAffine>::Uncompressed>(from, size, ElementType::G1_x, compression, checked, &input_map)?
            },

        };

        self.g1_alpha_x_powers = match compression {
            UseCompression::Yes => {
                self.read_points_chunk::<<E::G1Affine as CurveAffine>::Compressed>(from, size, ElementType::G1_alpha_x, compression, checked, &input_map)?
            },
            UseCompression::No => {
                self.read_points_chunk::<<E::G1Affine as CurveAffine>::Uncompressed>(from, size, ElementType::G1_alpha_x, compression, checked, &input_map)?
            },

        };

        self.g2_x_powers = match compression {
            UseCompression::Yes => {
                self.read_points_chunk::<<E::G2Affine as CurveAffine>::Compressed>(from, size, ElementType::G2_x, compression, checked, &input_map)?
            },
            UseCompression::No => {
                self.read_points_chunk::<<E::G2Affine as CurveAffine>::Uncompressed>(from, size, ElementType::G2_x, compression, checked, &input_map)?
            },

        };

        self.g2_alpha_x_powers = match compression {
            UseCompression::Yes => {
                self.read_points_chunk::<<E::G2Affine as CurveAffine>::Compressed>(from, size, ElementType::G2_alpha_x, compression, checked, &input_map)?
            },
            UseCompression::No => {
                self.read_points_chunk::<<E::G2Affine as CurveAffine>::Uncompressed>(from, size, ElementType::G2_alpha_x, compression, checked, &input_map)?
            },
        };

        self.g2_alpha = match compression {
            UseCompression::Yes => {
                let points = self.read_points_chunk::<<E::G2Affine as CurveAffine>::Compressed>(0, 1, ElementType::G2_alpha, compression, checked, &input_map)?;
                
                points[0]
            },
            UseCompression::No => {
                let points = self.read_points_chunk::<<E::G2Affine as CurveAffine>::Uncompressed>(0, 1, ElementType::G2_alpha, compression, checked, &input_map)?;

                points[0]
            },
        };

        Ok(())
    }

    // fn read_point<ENC: EncodedPoint>(

    // ) -> 

    fn read_points_chunk<ENC: EncodedPoint>(
        &mut self,
        from: usize,
        size: usize,
        element_type: ElementType,
        compression: UseCompression,
        checked: CheckForCorrectness,
        input_map: &Mmap,
    ) -> Result<Vec<ENC::Affine>, DeserializationError>
    {
        // Read the encoded elements
        let mut res = vec![ENC::empty(); size];

        for (i, encoded) in res.iter_mut().enumerate() {
            let index = from + i;
            assert!(index < P::D * 2);
            let position = Self::calculate_mmap_position(index, element_type, compression);
            let element_size = Self::get_size(element_type, compression);
            let memory_slice = input_map.get(position..position+element_size).expect("must read point data from file");
            memory_slice.clone().read_exact(encoded.as_mut())?;
        }

        // Allocate space for the deserialized elements
        let mut res_affine = vec![ENC::Affine::zero(); size];

        let mut chunk_size = res.len() / num_cpus::get();
        if chunk_size == 0 {
            chunk_size = 1;
        }

        // If any of our threads encounter a deserialization/IO error, catch
        // it with this.
        let decoding_error = Arc::new(Mutex::new(None));

        crossbeam::scope(|scope| {
            for (source, target) in res.chunks(chunk_size).zip(res_affine.chunks_mut(chunk_size)) {
                let decoding_error = decoding_error.clone();

                scope.spawn(move |_| {
                    for (source, target) in source.iter().zip(target.iter_mut()) {
                        match {
                            // If we're a participant, we don't need to check all of the
                            // elements in the accumulator, which saves a lot of time.
                            // The hash chain prevents this from being a problem: the
                            // transcript guarantees that the accumulator was properly
                            // formed.
                            match checked {
                                CheckForCorrectness::Yes => {
                                    // Points at infinity are never expected in the accumulator
                                    source.into_affine().map_err(|e| e.into()).and_then(|source| {
                                        if source.is_zero() {
                                            Err(DeserializationError::PointAtInfinity)
                                        } else {
                                            Ok(source)
                                        }
                                    })
                                },
                                CheckForCorrectness::No => source.into_affine_unchecked().map_err(|e| e.into())
                            }
                        }
                        {
                            Ok(source) => {
                                *target = source;
                            },
                            Err(e) => {
                                *decoding_error.lock().unwrap() = Some(e);
                            }
                        }
                    }
                });
            }
        }).expect("Must check correctness");

        match Arc::try_unwrap(decoding_error).unwrap().into_inner().unwrap() {
            Some(e) => {
                Err(e)
            },
            None => {
                Ok(res_affine)
            }
        }
    }
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    fn write_all(
        &mut self,
        chunk_start: usize,
        compression: UseCompression,
        element_type: ElementType,
        output_map: &mut MmapMut,
    ) -> io::Result<()>
    {
        match element_type {
            ElementType::G1_x => {
                for (i, c) in self.g1_x_powers.clone().iter().enumerate() {
                    let index = chunk_start + i;
                    self.write_point(index, c, compression, element_type, output_map)?;
                }
            },
            ElementType::G1_alpha_x => {
                for (i, c) in self.g1_alpha_x_powers.clone().iter().enumerate() {
                    let index = chunk_start + i;
                    self.write_point(index, c, compression, element_type, output_map)?;
                }
            },
            ElementType::G2_x => {
                for (i, c) in self.g2_x_powers.clone().iter().enumerate() {
                    let index = chunk_start + i;
                    self.write_point(index, c, compression, element_type, output_map)?;
                }
            },
            ElementType::G2_alpha_x => {
                for (i, c) in self.g2_alpha_x_powers.clone().iter().enumerate() {
                    let index = chunk_start + i;
                    self.write_point(index, c, compression, element_type, output_map)?;
                }
            },
            ElementType::G2_alpha => {
                let index = chunk_start;
                self.write_point(index, &self.g2_alpha.clone(), compression, element_type, output_map)?
            }
        };

        output_map.flush_async()?;

        Ok(())
    }

    fn write_point<C>(
        &mut self,
        index: usize,
        p: &C,
        compression: UseCompression,
        element_type: ElementType,
        output_map: &mut MmapMut,
    ) -> io::Result<()>
        where C: CurveAffine<Engine = E, Scalar = E::Fr>
    {
        assert!(index < P::D * 2);
        match compression {
            UseCompression::Yes => {
                let position = Self::calculate_mmap_position(index, element_type, compression);
                (&mut output_map[position..]).write(p.into_compressed().as_ref())?;
            },
            UseCompression::No => {
                let position = Self::calculate_mmap_position(index, element_type, compression);
                (&mut output_map[position..]).write(p.into_uncompressed().as_ref())?;
            },
        };

        Ok(())
    }

    /// Write the accumulator with some compression behavior.
    pub fn write_chunk(
        &mut self,
        chunk_start: usize,
        compression: UseCompression,
        output_map: &mut MmapMut
    ) -> io::Result<()>
    {
        self.write_all(chunk_start, compression, ElementType::G1_x, output_map)?;
        self.write_all(chunk_start, compression, ElementType::G1_alpha_x, output_map)?;
        self.write_all(chunk_start, compression, ElementType::G2_x, output_map)?;
        self.write_all(chunk_start, compression, ElementType::G2_alpha_x, output_map)?;
        self.write_all(chunk_start, compression, ElementType::G2_alpha, output_map)?;

        Ok(())
    }

}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    /// Transforms the accumulator with a private key.
    /// Due to large amount of data in a previous accumulator even in the compressed form
    /// this function can now work on compressed input. Output can be made in any form 
    /// WARNING: Contributor does not have to check that values from challenge file were serialized
    /// corrently, but we may want to enforce it if a ceremony coordinator does not recompress the previous
    /// contribution into the new challenge file 
    pub fn transform(
        input_map: &Mmap,
        output_map: &mut MmapMut,
        input_is_compressed: UseCompression,
        compress_the_output: UseCompression,
        check_input_for_correctness: CheckForCorrectness,
        key: &PrivateKey<E>
    ) -> io::Result<()>
    {

        /// Exponentiate a large number of points, with an optional coefficient to be applied to the
        /// exponent.
        fn batch_exp<EE: Engine, C: CurveAffine<Engine = EE, Scalar = EE::Fr> >(bases: &mut [C], exp: &[C::Scalar], coeff: Option<&C::Scalar>) {
            assert_eq!(bases.len(), exp.len());
            let mut projective = vec![C::Projective::zero(); bases.len()];
            let chunk_size = bases.len() / num_cpus::get();

            // Perform wNAF over multiple cores, placing results into `projective`.
            crossbeam::scope(|scope| {
                for ((bases, exp), projective) in bases.chunks_mut(chunk_size)
                                                       .zip(exp.chunks(chunk_size))
                                                       .zip(projective.chunks_mut(chunk_size))
                {
                    scope.spawn(move |_| {
                        let mut wnaf = Wnaf::new();

                        for ((base, exp), projective) in bases.iter_mut()
                                                              .zip(exp.iter())
                                                              .zip(projective.iter_mut())
                        {
                            let mut exp = *exp;
                            if let Some(coeff) = coeff {
                                exp.mul_assign(coeff);
                            }

                            *projective = wnaf.base(base.into_projective(), 1).scalar(exp.into_repr());
                        }
                    });
                }
            }).expect("Must contribute");

            // Perform batch normalization
            crossbeam::scope(|scope| {
                for projective in projective.chunks_mut(chunk_size)
                {
                    scope.spawn(move |_| {
                        C::Projective::batch_normalization(projective);
                    });
                }
            }).expect("Must batch normalize");

            // Turn it all back into affine points
            for (projective, affine) in projective.iter().zip(bases.iter_mut()) {
                *affine = projective.into_affine();
            }
        }

        let mut accumulator = Self::empty();

        use itertools::MinMaxResult::{MinMax};

        for chunk in &(0..P::D).into_iter().chunks(P::EMPIRICAL_BATCH_SIZE) {
            if let MinMax(start, end) = chunk.minmax() {
                let size = end - start + 1;
                println!("Processing powers from {} to {}", zero_index_to_power::<P>(start), zero_index_to_power::<P>(end));
                accumulator.read_chunk(start, size, input_is_compressed, check_input_for_correctness, &input_map).expect("must read a first chunk");
                // Construct the powers of tau
                let mut taupowers = vec![E::Fr::zero(); size];
                let chunk_size = size / num_cpus::get();

                // Construct exponents in parallel
                crossbeam::scope(|scope| {
                    for (i, taupowers) in taupowers.chunks_mut(chunk_size).enumerate() {
                        scope.spawn(move |_| {
                            let base_exp = (P::D - (i * chunk_size)) as u64;
                            let mut acc = key.x.pow(&[base_exp]).inverse().expect("inverse must exist for contribution");

                            for t in taupowers {
                                *t = acc;
                                acc.mul_assign(&key.x);
                            }
                        });
                    }
                }).expect("Must compute exponents");

                batch_exp::<E, _>(&mut accumulator.g1_x_powers, &taupowers[0..], None);
                batch_exp::<E, _>(&mut accumulator.g1_alpha_x_powers, &taupowers[0..], Some(&key.alpha));
                batch_exp::<E, _>(&mut accumulator.g2_x_powers, &taupowers[0..], None);
                batch_exp::<E, _>(&mut accumulator.g2_alpha_x_powers, &taupowers[0..], Some(&key.alpha));
                accumulator.g2_alpha = accumulator.g2_alpha.mul(key.alpha).into_affine();
                accumulator.write_chunk(start, compress_the_output, output_map)?;

                println!("Done processing {} powers", end);
            } else {
                panic!("Chunk does not have a min and max");
            }
        }

        for chunk in &(P::D..P::D*2).into_iter().chunks(P::EMPIRICAL_BATCH_SIZE) {
            if let MinMax(start, end) = chunk.minmax() {
                let size = end - start + 1;
                accumulator.read_chunk(start, size, input_is_compressed, check_input_for_correctness, &input_map).expect("must read a first chunk");
                println!("Processing powers from {} to {}", zero_index_to_power::<P>(start), zero_index_to_power::<P>(end));
                // Construct the powers of tau
                let mut taupowers = vec![E::Fr::zero(); size];
                let chunk_size = size / num_cpus::get();

                // Construct exponents in parallel
                crossbeam::scope(|scope| {
                    for (i, taupowers) in taupowers.chunks_mut(chunk_size).enumerate() {
                        scope.spawn(move |_| {
                            let base_exp = (1 + (i * chunk_size)) as u64;
                            let mut acc = key.x.pow(&[base_exp]);

                            for t in taupowers {
                                *t = acc;
                                acc.mul_assign(&key.x);
                            }
                        });
                    }
                }).expect("Must compute exponents");

                batch_exp::<E, _>(&mut accumulator.g1_x_powers, &taupowers[0..], None);
                batch_exp::<E, _>(&mut accumulator.g1_alpha_x_powers, &taupowers[0..], Some(&key.alpha));
                batch_exp::<E, _>(&mut accumulator.g2_x_powers, &taupowers[0..], None);
                batch_exp::<E, _>(&mut accumulator.g2_alpha_x_powers, &taupowers[0..], Some(&key.alpha));
                accumulator.g2_alpha = accumulator.g2_alpha.mul(key.alpha).into_affine();
                accumulator.write_chunk(start, compress_the_output, output_map)?;

                println!("Done processing {} powers", end);
            } else {
                panic!("Chunk does not have a min and max");
            }
        }

        Ok(())
    }
}

impl<E:Engine, P: CeremonyParameters> BachedAccumulator<E, P> {
    /// Generate initial empty accumulator
    pub fn generate_initial(
        output_map: &mut MmapMut,
        compress_the_output: UseCompression,
    ) -> io::Result<()>
    {
        use itertools::MinMaxResult::{MinMax};

        for chunk in &(0..2*P::D).into_iter().chunks(P::EMPIRICAL_BATCH_SIZE) {
            if let MinMax(start, end) = chunk.minmax() {
                let size = end - start + 1;
                let mut accumulator = Self {
                    g1_x_powers: vec![E::G1Affine::one(); size],
                    g1_alpha_x_powers: vec![E::G1Affine::one(); size],
                    g2_x_powers: vec![E::G2Affine::one(); size],
                    g2_alpha_x_powers: vec![E::G2Affine::one(); size],
                    g2_alpha: E::G2Affine::one(),
                    hash: blank_hash(),
                    marker: std::marker::PhantomData::<P>{}
                };

                accumulator.write_chunk(start, compress_the_output, output_map)?;
                println!("Done processing {} powers", end);
            } else {
                panic!("Chunk does not have a min and max");
            }
        }

        Ok(())
    }
}

// return an expected power for zero-indexed array
// index of 0 -> power of -d
// index of 1 -> power of -d + 1
// ...
// index of d-1 -> power of -1
// there is no power of 0
// index of d -> power of 1
// index of d + 1 -> power of 2
// index of 2*d - 1 -> power of +d
fn zero_index_to_power<P:CeremonyParameters>(index: usize) -> i64 {
    let d = P::D;
    let d_i64 = d as i64;
    assert!(index < d*2);
    if index < d {
        return (index as i64) - d_i64;
    } else {
        return (index as i64) - d_i64 + 1i64;
    }
}

fn power_to_zero_index<P:CeremonyParameters>(power: i64) -> usize {
    let d = P::D;
    let d_i64 = d as i64;
    assert!(power >= -d_i64);
    assert!(power <= d_i64);
    assert!(power != 0i64);

    if power < 0i64 {
        return (d_i64 + power) as usize;
    } else {
        return (d_i64 + power - 1i64) as usize;
    }
}

#[test]
fn test_index_to_power () {
    #[derive(Clone)]
    struct TestParameters {

    }

    impl CeremonyParameters for TestParameters {
        const D: usize = 16;

        const G1_UNCOMPRESSED_BYTE_SIZE: usize = 64;
        const G2_UNCOMPRESSED_BYTE_SIZE: usize = 128;
        const G1_COMPRESSED_BYTE_SIZE: usize = 32;
        const G2_COMPRESSED_BYTE_SIZE: usize = 64;
    }

    let d = TestParameters::D as i64;

    let index = 0; 
    // first element is g^(x^-d)
    let expected_power = -d;
    let calculated_power = zero_index_to_power::<TestParameters>(index);
    let recalculated_index = power_to_zero_index::<TestParameters>(calculated_power);
    assert_eq!(expected_power, calculated_power);
    assert_eq!(index, recalculated_index);

    let index = TestParameters::D - 1;
    let expected_power = -1i64;
    let calculated_power = zero_index_to_power::<TestParameters>(index);
    let recalculated_index = power_to_zero_index::<TestParameters>(calculated_power);
    assert_eq!(expected_power, calculated_power);
    assert_eq!(index, recalculated_index);

    let index = TestParameters::D;
    let expected_power = 1i64;
    let calculated_power = zero_index_to_power::<TestParameters>(index);
    let recalculated_index = power_to_zero_index::<TestParameters>(calculated_power);
    assert_eq!(expected_power, calculated_power);
    assert_eq!(index, recalculated_index);

    let index = TestParameters::D*2 - 1;
    let expected_power = d;
    let calculated_power = zero_index_to_power::<TestParameters>(index);
    let recalculated_index = power_to_zero_index::<TestParameters>(calculated_power);
    assert_eq!(expected_power, calculated_power);
    assert_eq!(index, recalculated_index);
}