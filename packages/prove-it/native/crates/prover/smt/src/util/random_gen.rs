//! Ported from Z3 (src/util/util.h), MIT license, through `random-gen.ts`. random_gen: Z3's linear
//! congruential generator, which the model finder and the simplex settings seed.

#[derive(Clone, Debug)]
pub struct RandomGen {
    seed: u32,
}

impl RandomGen {
    pub fn new(seed: u32) -> RandomGen {
        RandomGen { seed }
    }

    /// A number in `0..=0x7fff`.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> u32 {
        self.seed = self.seed.wrapping_mul(214_013).wrapping_add(2_531_011);
        (self.seed >> 16) & 0x7fff
    }
}
