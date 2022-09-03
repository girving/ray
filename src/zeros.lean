-- Zeros and poles

import data.real.basic
import data.complex.basic
import tactic.linarith.frontend
import tactics
import simple
open tactic.interactive (nlinarith)
open complex (abs has_zero)
open nat (iterate)
open simple

-- The order of a zero at a point
def zero_order (f : ℂ → ℂ) (c : ℂ) (d : ℕ) := ∃ g : ℂ → ℂ, ∀ z, f z = (z - c)^d * g z
