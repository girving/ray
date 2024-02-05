import Ray.Approx.Floating.Basic

/-!
## Floating point negation
-/

open Set
open scoped Real
namespace Floating

instance : Neg Floating where
  neg x := {
    n := -x.n
    s := x.s
    zero_same := by intro h; simp only [neg_eq_zero] at h; exact x.zero_same h
    nan_same := by intro h; simp only [Int64.neg_eq_min] at h; exact x.nan_same h
    norm := by
      intro z n d
      simp only [ne_eq, neg_eq_zero, Int64.neg_eq_min] at z n
      simp only [ne_eq, not_false_eq_true, Int64.abs_neg, z, n, x.norm, d] }

@[simp] lemma n_neg {x : Floating} : (-x).n = -x.n := rfl
@[simp] lemma s_neg {x : Floating} : (-x).s = x.s := rfl

/-- Negation propagates `nan` -/
@[simp] lemma neg_nan : (-nan : Floating) = nan := by
  simp only [ext_iff, n_neg, n_nan, Int64.neg_min, s_neg, s_nan, and_self]

/-- Negation preserves `nan` -/
@[simp] lemma neg_eq_nan_iff {x : Floating} : -x = nan ↔ x = nan := by
  simp only [ext_iff, n_neg, n_nan, Int64.neg_eq_min, s_neg, s_nan]

/-- `-0 = 0` -/
@[simp] lemma neg_zero : (-0 : Floating) = 0 := by
  simp only [ext_iff, n_neg, n_zero, s_neg, s_zero, and_self, _root_.neg_zero]

/-- Negation preserves `0` -/
@[simp] lemma neg_eq_zero_iff {x : Floating} : -x = 0 ↔ x = 0 := by
  simp only [ext_iff, n_neg, n_zero, neg_eq_zero, s_neg, s_zero]

/-- Negation flips `.val`, except at `nan` -/
@[simp] lemma val_neg {x : Floating} (n : x ≠ nan) : (-x).val = -x.val := by
  rw [val, val]
  simp only [n_neg, s_neg, ←neg_mul, Int64.coe_neg (x.n_ne_min n), Int.cast_neg]

/-- Negation negates `approx` -/
@[simp] lemma approx_neg {x : Floating} : approx (-x) = -approx x := by
  by_cases n : x = nan
  · simp only [n, neg_nan, approx_nan, neg_univ]
  · simp only [ne_eq, neg_eq_nan_iff, n, not_false_eq_true, approx_eq_singleton, val_neg,
      neg_singleton]

/-- `-` is conservative -/
instance : ApproxNeg Floating ℝ where
  approx_neg x := by simp only [approx_neg, subset_refl]

/-- `- -x = x` -/
instance : InvolutiveNeg Floating where
  neg_neg x := by simp only [ext_iff, n_neg, neg_neg, s_neg, and_self]
