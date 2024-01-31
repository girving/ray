import Ray.Approx.Floating.Basic

/-!
## Floating point absolute value
-/

open Set
open scoped Real
namespace Floating

/-- Absolute value -/
@[irreducible, pp_dot] def abs (x : Floating) : Floating where
  n := ⟨x.n.abs⟩
  s := x.s
  zero_same := by
    intro h; apply x.zero_same
    simpa only [Int64.ext_iff, Int64.n_zero, Int64.abs_eq_zero_iff] using h
  nan_same := by
    intro h; apply x.nan_same
    simpa only [Int64.ext_iff, Int64.n_min, Int64.abs_eq_pow_iff] using h
  norm := by
    intro n0 nm s0
    simp only [Int64.abs_abs, Int64.ext_iff, Int64.n_zero, Int64.n_min,
      Int64.abs_eq_zero_iff, Ne.def, Int64.abs_eq_pow_iff] at n0 nm ⊢
    refine x.norm ?_ ?_ s0
    repeat simpa only [ne_eq, Int64.ext_iff, Int64.n_zero]

-- Definition lemmas
@[simp] lemma n_abs {x : Floating} : x.abs.n = ⟨x.n.abs⟩ := by rw [abs]
@[simp] lemma s_abs {x : Floating} : x.abs.s = x.s := by rw [abs]

/-- `abs` preserves `nan` -/
@[simp] lemma abs_nan : (nan : Floating).abs = nan := by native_decide

/-- `abs` is exact away from `nan` -/
@[simp] lemma val_abs {x : Floating} (n : x ≠ nan) : x.abs.val = |x.val| := by
  rw [val, val]
  simp only [abs_mul, abs_of_pos two_zpow_pos, n_abs, s_abs]
  refine congr_arg₂ _ ?_ rfl
  simp only [Int64.coe_of_nonneg (Int64.isNeg_abs (x.n_ne_min n)), Int64.toNat_abs,
    Int.coe_natAbs, Int.cast_abs, Complex.int_cast_abs]
