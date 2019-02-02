extern crate pairing;
extern crate rand;
extern crate crossbeam;
extern crate num_cpus;
extern crate blake2;
extern crate generic_array;
extern crate typenum;
extern crate byteorder;
extern crate ff;

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

// following the original notation `g` is a generator of G1,
// `h` is a generator of G2
pub trait CeremonyParameters: Clone {
    // `d` is a max degree of the polynomial in the arguments
    const D: usize; 
    
    const G1_UNCOMPRESSED_BYTE_SIZE: usize;
    const G2_UNCOMPRESSED_BYTE_SIZE: usize;
    const G1_COMPRESSED_BYTE_SIZE: usize;
    const G2_COMPRESSED_BYTE_SIZE: usize;

    // G1 elements:
    // `for i in [-d, d], i != 0 => g^(x^i)`
    // `for i in [-d, d], i != 0 => g^(alpha*x^i)`
    const G1_NUM_ELEMENTS: usize = (2 * Self::D) + (2 * Self::D);

    // G2 elements:
    // `for i in [-d, d], i != 0 => h^(x^i)`
    // `for i in [-d, d], i != 0 => h^(alpha*x^i)`
    // `h^alpha`
    const G2_NUM_ELEMENTS: usize = (2 * Self::D) + (2 * Self::D) + 1;

    // size of the uncompressed accumulator, usually used as a challenge
    const ACCUMULATOR_BYTE_SIZE: usize = (Self::G1_NUM_ELEMENTS * Self::G1_UNCOMPRESSED_BYTE_SIZE)
                                            + (Self::G2_NUM_ELEMENTS * Self::G2_UNCOMPRESSED_BYTE_SIZE)
                                            + Self::HASH_SIZE; // blake2b hash of previous contribution

    const PUBLIC_KEY_SIZE: usize = 2 * Self::G2_UNCOMPRESSED_BYTE_SIZE + // x, alpha in g2
                                    4 * Self::G1_UNCOMPRESSED_BYTE_SIZE; // (s1, s1*x), (s2, s2*alpha) in g1

    // size of the contribution, it's in compressed form and used as response
    const CONTRIBUTION_BYTE_SIZE: usize = (Self::G1_NUM_ELEMENTS * Self::G1_COMPRESSED_BYTE_SIZE)
                                            + (Self::G2_NUM_ELEMENTS * Self::G2_COMPRESSED_BYTE_SIZE)
                                            + Self::HASH_SIZE // blake2b hash of previous contribution
                                            + Self::PUBLIC_KEY_SIZE; // public key

    // Blake2b hash size
    const HASH_SIZE: usize = 64;

    const EMPIRICAL_BATCH_SIZE: usize = 1 << 21;
}



/// Determines if point compression should be used.
#[derive(Copy, Clone, PartialEq)]
pub enum UseCompression {
    Yes,
    No
}

/// Determines if points should be checked for correctness during deserialization.
/// This is not necessary for participants, because a transcript verifier can
/// check this theirself.
#[derive(Copy, Clone, PartialEq)]
pub enum CheckForCorrectness {
    Yes,
    No
}


/// Errors that might occur during deserialization.
#[derive(Debug)]
pub enum DeserializationError {
    IoError(io::Error),
    DecodingError(GroupDecodingError),
    PointAtInfinity
}

impl fmt::Display for DeserializationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DeserializationError::IoError(ref e) => write!(f, "Disk IO error: {}", e),
            DeserializationError::DecodingError(ref e) => write!(f, "Decoding error: {}", e),
            DeserializationError::PointAtInfinity => write!(f, "Point at infinity found")
        }
    }
}

impl From<io::Error> for DeserializationError {
    fn from(err: io::Error) -> DeserializationError {
        DeserializationError::IoError(err)
    }
}

impl From<GroupDecodingError> for DeserializationError {
    fn from(err: GroupDecodingError) -> DeserializationError {
        DeserializationError::DecodingError(err)
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum ElementType {
    G1_x,
    G1_alpha_x,
    G2_x,
    G2_alpha_x,
    G2_alpha
}