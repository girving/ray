import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic

/-!
## `ℚ` machinery
-/

/-- The smallest `n` s.t. `|x| < 2^n` -/
@[irreducible] def Rat.log2 (x : ℚ) : ℤ :=
  -- Initial guess, which might be too low by one
  let n := x.num.natAbs
  let ln := n.log2
  let ld := x.den.log2
  let g : ℤ := ln - ld
  -- If `a / x.den < 2^g`, then `g` is good, otherwise we need `g + 1`
  let good := bif 0 ≤ g then decide (n < x.den <<< g.toNat) else n <<< (-g).toNat < x.den
  bif good then g else g+1
