//! SplitMix64 pseudorandom number generator.
//!
//! Used to draw the Pollard's rho start and offset values. It is seeded from
//! the number being factored, so factoring a number does the same work on
//! every call, whatever was factored before.
//!
//! Algorithm from Steele, Lea and Flood, "Fast splittable pseudorandom number
//! generators", OOPSLA 2014 (<https://doi.org/10.1145/2714064.2660195>),
//! following Sebastiano Vigna's reference implementation
//! (<https://prng.di.unimi.it/splitmix64.c>).

/// SplitMix64 generator. Not suitable for cryptographic use.
pub(crate) struct SplitMix64(u64);

impl SplitMix64 {
    pub(crate) fn new(seed: u64) -> Self {
        Self(seed)
    }

    pub(crate) fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reference_values() {
        // outputs of the reference implementation
        let mut rng = SplitMix64::new(1_234_567);
        let expected = [
            6_457_827_717_110_365_317,
            3_203_168_211_198_807_973,
            9_817_491_932_198_370_423,
            4_593_380_528_125_082_431,
            16_408_922_859_458_223_821,
        ];
        for e in expected {
            assert_eq!(rng.next_u64(), e);
        }
        assert_eq!(SplitMix64::new(0).next_u64(), 0xe220_a839_7b1d_cdaf);
    }

    #[test]
    fn reproducible() {
        let draw = |seed| {
            let mut rng = SplitMix64::new(seed);
            (0..8).map(|_| rng.next_u64()).collect::<Vec<_>>()
        };
        let first = draw(42);
        assert_eq!(first, draw(42));
        assert_ne!(first, draw(43));
        assert_ne!(first[0], first[1]);
    }
}
