import Ray.Approx.Floating.Basic
import Ray.Approx.Floating.Order

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
      Int64.abs_eq_zero_iff, Ne, Int64.abs_eq_pow_iff] at n0 nm ⊢
    refine x.norm ?_ ?_ s0
    repeat simpa only [ne_eq, Int64.ext_iff, Int64.n_zero]

-- Definition lemmas
@[simp] lemma n_abs {x : Floating} : x.abs.n = ⟨x.n.abs⟩ := by rw [abs]
@[simp] lemma s_abs {x : Floating} : x.abs.s = x.s := by rw [abs]

/-- `abs` preserves `nan` -/
@[simp] lemma abs_nan : (nan : Floating).abs = nan := by native_decide

/-- `abs` preserves `nan` -/
@[simp] lemma abs_eq_nan {x : Floating} : x.abs = nan ↔ x = nan := by
  simp only [ext_iff, n_abs, n_nan, Int64.ext_iff, Int64.n_min, Int64.abs_eq_pow_iff, s_abs,
    s_nan, imp_self]

/-- `abs` is exact away from `nan` -/
@[simp] lemma val_abs {x : Floating} (n : x ≠ nan) : x.abs.val = |x.val| := by
  rw [val, val]
  simp only [abs_mul, abs_of_pos (two_zpow_pos (𝕜 := ℝ)), n_abs, s_abs]
  refine congr_arg₂ _ ?_ rfl
  simp only [Int64.coe_of_nonneg (Int64.isNeg_abs (x.n_ne_min n)), Int64.toNat_abs, Int.natCast_natAbs,
    Int.cast_abs]

/-- `abs` is nonnegative away from `nan` -/
@[simp] lemma abs_nonneg {x : Floating} (n : x ≠ nan) : 0 ≤ x.abs.val := by
  simp only [val_abs n, abs_nonneg]; apply _root_.abs_nonneg

/-- `abs` is the identity for nonnegatives (since `nan < 0`) -/
@[simp] lemma abs_of_nonneg {x : Floating} (x0 : 0 ≤ x.val) : x.abs = x := by
  have xn : x.n.isNeg = false := by simpa only [isNeg_iff, decide_eq_false_iff_not, not_lt]
  simp only [ext_iff, n_abs, s_abs, and_true, Int64.abs_eq_self' xn]

/-- `abs` is negates nonpositives (since `-nan = nan`) -/
@[simp] lemma abs_of_nonpos {x : Floating} (x0 : x.val ≤ 0) : x.abs = -x := by
  by_cases z : x = 0
  · simp only [z, val_zero, le_refl, abs_of_nonneg, neg_zero]
  have x0' := Ne.lt_of_le (val_ne_zero.mpr z) x0
  have xn : x.n.isNeg = true := by simpa only [isNeg_iff, decide_eq_true_eq]
  simp only [ext_iff, n_abs, Int64.abs_eq_neg' xn, Int64.neg_def, n_neg, s_abs, s_neg, and_self]

/-- `abs` is conservative -/
@[mono] lemma mem_approx_abs {a : ℝ} {x : Floating} (ax : a ∈ approx x) : |a| ∈ approx x.abs := by
  by_cases n : x = nan
  · simp only [n, abs_nan, approx_nan, mem_univ]
  · simp only [ne_eq, n, not_false_eq_true, approx_eq_singleton, mem_singleton_iff, abs_eq_nan,
      val_abs] at ax ⊢
    rw [ax]
