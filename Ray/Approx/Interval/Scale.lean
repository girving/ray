import Ray.Approx.Floating.Scale
import Ray.Approx.Interval.Basic

open Pointwise

/-!
## Interval scaling by a power of two
-/

open Set
open scoped Real
namespace Interval

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB (x : Interval) (t : Int64) : Interval :=
  mix (x.lo.scaleB t) (x.hi.scaleB t) (by
    intro n0 n1
    simp only [ne_eq, n0, not_false_eq_true, Floating.val_scaleB, n1, gt_iff_lt, two_zpow_pos,
      mul_le_mul_right, le])

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB' (x : Interval) (t : Fixed 0) : Interval :=
  bif t == nan then nan else scaleB x t.n

/-- `scaleB` propagates `nan` -/
@[simp] lemma nan_scaleB {t : Int64} : (nan : Interval).scaleB t = nan := by
  rw [scaleB]; simp only [lo_nan, Floating.nan_scaleB, hi_nan, mix_self, coe_nan]

/-- `scaleB` propagates `nan` -/
lemma ne_nan_of_scaleB {x : Interval} {t : Int64} (n : x.scaleB t ≠ nan) : x ≠ nan := by
  contrapose n; simp only [ne_eq, not_not] at n
  simp only [n, nan_scaleB, ne_eq, not_true_eq_false, not_false_eq_true]

/-- `scaleB'` propagates `nan` -/
@[simp] lemma nan_scaleB' {t : Fixed 0} : (nan : Interval).scaleB' t = nan := by
  rw [scaleB']; simp only [nan_scaleB, Bool.cond_self]

/-- `scaleB'` propagates `nan` -/
@[simp] lemma scaleB'_nan {x : Interval} : x.scaleB' nan = nan := by
  rw [scaleB']; simp only [beq_self_eq_true, Fixed.nan_n, cond_true]

/-- `scaleB'` propagates `nan` -/
lemma ne_nan_of_scaleB' {x : Interval} {t : Fixed 0} (n : x.scaleB' t ≠ nan) :
    x ≠ nan ∧ t ≠ nan := by
  contrapose n; simp only [ne_eq, not_not, not_and_or] at n
  rcases n with n | n
  all_goals simp only [n, nan_scaleB', scaleB'_nan, ne_eq, not_true_eq_false, not_false_eq_true]

/-- `scaleB` is conservative -/
@[mono] lemma mem_approx_scaleB {x : Interval} {t : Int64} {x' : ℝ}
    (xm : x' ∈ approx x) : x' * 2^(t : ℤ) ∈ approx (x.scaleB t) := by
  rw [scaleB]
  simp only [approx, lo_eq_nan, mem_ite_univ_left, mem_Icc] at xm ⊢
  intro n
  simp only [lo_mix n, hi_mix n]
  simp only [mix_eq_nan, not_or] at n
  have xn := Floating.ne_nan_of_scaleB n.1
  simp only [ne_eq, lo_eq_nan] at xn
  simp only [xn, not_false_eq_true, forall_true_left] at xm
  simpa only [ne_eq, n.1, not_false_eq_true, Floating.val_scaleB, gt_iff_lt, two_zpow_pos,
    mul_le_mul_right, n.2]

/-- `scaleB'` is conservative -/
@[mono] lemma mem_approx_scaleB' {x : Interval} {t : Fixed 0} {x' t' : ℝ}
    (xm : x' ∈ approx x) (tm : t' ∈ approx t) : x' * 2^t' ∈ approx (x.scaleB' t) := by
  rw [scaleB']
  by_cases tn : t = nan
  · simp only [tn, beq_self_eq_true, Fixed.nan_n, cond_true, approx_nan, mem_univ]
  simp only [bif_eq_if, beq_iff_eq, ne_eq, neg_neg, tn, not_false_eq_true, Fixed.ne_nan_of_neg,
    ite_false]
  simp only [approx, ne_eq, neg_neg, tn, not_false_eq_true, Fixed.ne_nan_of_neg, ite_false,
    mem_singleton_iff] at tm
  rw [tm, Fixed.val, Int64.coe_zero, zpow_zero, mul_one, Real.rpow_intCast]
  exact mem_approx_scaleB xm

/-!
### Dividing by two
-/

@[irreducible] def div2 (x : Interval) : Interval :=
  mix (x.lo.div2) (x.hi.div2) (by
    intro n0 n1
    simp only [ne_eq, n0, not_false_eq_true, Floating.val_div2, n1]
    exact div_le_div_of_nonneg_right x.le (by norm_num))

@[mono] lemma mem_approx_div2 {x : Interval} {x' : ℝ} (xm : x' ∈ approx x) :
    x' / 2 ∈ approx (div2 x) := by
  rw [div2]
  simp only [approx, lo_eq_nan, mem_ite_univ_left, mem_Icc] at xm ⊢
  intro n
  simp only [lo_mix n, hi_mix n]
  simp only [mix_eq_nan, not_or] at n
  have xn := Floating.ne_nan_of_div2 n.1
  simp only [ne_eq, lo_eq_nan] at xn
  simp only [xn, not_false_eq_true, forall_true_left] at xm
  simpa only [ne_eq, n.1, not_false_eq_true, Floating.val_div2, n.2,
    div_le_div_right (by norm_num : (0 : ℝ) < 2)]
