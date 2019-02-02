extern crate alpha_line;
extern crate pairing;
extern crate memmap;

use alpha_line::small_bn256::{Bn256CeremonyParameters};
use alpha_line::batched_accumulator::{BachedAccumulator};
use alpha_line::parameters::{UseCompression, CeremonyParameters};
use alpha_line::utils::{blank_hash};
use alpha_line::utils::{pretty_print_hash};

use std::fs::OpenOptions;
use std::io::{Write};
use pairing::bn256::Bn256;
use memmap::*;

const COMPRESS_NEW_CHALLENGE: UseCompression = UseCompression::No;

fn main() {
println!("Will contribute to accumulator for up to {}th powers", Bn256CeremonyParameters::D);
    
    let file = OpenOptions::new()
                            .read(true)
                            .write(true)
                            .create_new(true)
                            .open("challenge").expect("unable to create `./challenge`");
            
    let expected_challenge_length = match COMPRESS_NEW_CHALLENGE {
        UseCompression::Yes => {
            Bn256CeremonyParameters::CONTRIBUTION_BYTE_SIZE - Bn256CeremonyParameters::PUBLIC_KEY_SIZE
        },
        UseCompression::No => {
            Bn256CeremonyParameters::ACCUMULATOR_BYTE_SIZE
        }
    };

    file.set_len(expected_challenge_length as u64).expect("unable to allocate large enough file");

    let mut writable_map = unsafe { MmapOptions::new().map_mut(&file).expect("unable to create a memory map") };

    // Write a blank BLAKE2b hash:
    let hash = blank_hash();
    (&mut writable_map[0..]).write(hash.as_slice()).expect("unable to write a default hash to mmap");
    writable_map.flush().expect("unable to write blank hash to `./challenge`");

    println!("Blank hash for an empty challenge:");

    pretty_print_hash(hash.as_slice());

    BachedAccumulator::<Bn256, Bn256CeremonyParameters>::generate_initial(&mut writable_map, COMPRESS_NEW_CHALLENGE).expect("generation of initial accumulator is successful");
    writable_map.flush().expect("unable to flush memmap to disk");

    // Get the hash of the contribution, so the user can compare later
    let output_readonly = writable_map.make_read_only().expect("must make a map readonly");
    let contribution_hash = BachedAccumulator::<Bn256, Bn256CeremonyParameters>::calculate_hash(&output_readonly);

    println!("Empty contribution is formed with a hash:");

    pretty_print_hash(contribution_hash.as_slice());

    println!("Wrote a fresh accumulator to `./challenge`");
}
