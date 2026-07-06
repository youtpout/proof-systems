//! The Poseidon sponge state machine, generic over the element type.
//!
//! This is the absorb/squeeze protocol (mode transitions, permute on
//! rate-full) shared by the out-of-circuit [`crate::poseidon::ArithmeticSponge`]
//! (element type = a field `F`) and snarky's in-circuit sponge (element type
//! = a circuit variable). The permutation and field addition are supplied as
//! closures so the same protocol serves both.

use crate::poseidon::SpongeState;

/// A sponge over elements of type `T`, holding the full state
/// (rate + capacity) and the absorb/squeeze mode.
pub struct SpongeMachine<T> {
    pub state: Vec<T>,
    pub rate: usize,
    pub mode: SpongeState,
}

impl<T: Clone> SpongeMachine<T> {
    /// Creates a sponge with the given initial state and rate.
    #[must_use]
    pub const fn new(state: Vec<T>, rate: usize) -> Self {
        Self {
            state,
            rate,
            mode: SpongeState::Absorbed(0),
        }
    }

    /// Absorbs `inputs`, adding each into the current rate slot and permuting
    /// when the rate is full. `add(a, b)` returns `a + b`; `permute(state)`
    /// applies the permutation in place.
    pub fn absorb(
        &mut self,
        inputs: &[T],
        add: impl Fn(&T, &T) -> T,
        mut permute: impl FnMut(&mut Vec<T>),
    ) {
        for x in inputs {
            match self.mode {
                SpongeState::Absorbed(n) => {
                    if n == self.rate {
                        permute(&mut self.state);
                        self.state[0] = add(&self.state[0], x);
                        self.mode = SpongeState::Absorbed(1);
                    } else {
                        self.state[n] = add(&self.state[n], x);
                        self.mode = SpongeState::Absorbed(n + 1);
                    }
                }
                SpongeState::Squeezed(_) => {
                    self.state[0] = add(&self.state[0], x);
                    self.mode = SpongeState::Absorbed(1);
                }
            }
        }
    }

    /// Squeezes one element, permuting when the rate is exhausted.
    pub fn squeeze(&mut self, mut permute: impl FnMut(&mut Vec<T>)) -> T {
        match self.mode {
            SpongeState::Squeezed(n) => {
                if n == self.rate {
                    permute(&mut self.state);
                    self.mode = SpongeState::Squeezed(1);
                    self.state[0].clone()
                } else {
                    self.mode = SpongeState::Squeezed(n + 1);
                    self.state[n].clone()
                }
            }
            SpongeState::Absorbed(_) => {
                permute(&mut self.state);
                self.mode = SpongeState::Squeezed(1);
                self.state[0].clone()
            }
        }
    }
}
