module
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Complex.Exponential

/-!
## Shared defs, to minimise public imports
-/

open scoped Real

/-- A `Finset ℕ` with only large elements -/
@[expose] public def Late (N : Finset ℕ) (m : ℕ) :=
  ∀ n, n ∈ N → n ≥ m

/-- Lipschitz coefficient for `pow1p_small_general` -/
@[expose] public noncomputable def psg (r s : ℝ) : ℝ :=
  rexp (r * s / (1 - r)) / (1 - r)
