# Alpha line

It is named after the Lyman Alpha Lines in a spectrum.

## Original story

This is a [multi-party computation](https://en.wikipedia.org/wiki/Secure_multi-party_computation) (MPC) ceremony which constructs a structured reference string (SRS) for SONIC proof system. Based on the modifier powers of tau implementation. Can be run in memory constrained environment and does contribute the entropy by chinks using a limited amount of RAM.

## Extensions

SGX implementation is coming soon.

## WARNING

It's highly experimental implementation, that follows the original approach of "powers of tau", but was not battle-tested or analyzed for security.

## Recommendations from original ceremony

Participants of the ceremony sample some randomness, perform computation and then destroy the randomness. **Only one participant needs to do this successfully to ensure the final parameters are secure.** This is due to the simple fact that to construct a final variable `x` or `alpha` every participant contributes his chunk in a form `x[i+1] = x[i]*contrib` and does it in a power of the exponent, so discrete log makes it difficult to extract `x[i+1]` if you know `x[i]` if you know only `g^(x[i]) and g^(x[i+1])`. In order to see that this randomness is truly destroyed, participants may take various kinds of precautions:

* putting the machine in a Faraday cage
* destroying the machine afterward
* running the software on secure hardware
* not connecting the hardware to any networks
* using multiple machines and randomly picking the result of one of them to use
* using a different code than what we have provided
* using a secure operating system
* using an operating system that nobody would expect you to use (Rust can compile to Mac OS X and Windows)
* using an unusual Rust toolchain or [alternate rust compiler](https://github.com/thepowersgang/mrustc)
* lots of other ideas we can't think of
* run it a non-standard device like a mobile device or Raspberry Pi

It is entirely up to the participants. In general, participants should beware of side-channel attacks and assume that remnants of the randomness will be in RAM after the computation has finished.

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
