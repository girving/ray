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
  mix (x.lo.scaleB t false) (x.hi.scaleB t true) (by
    intro n0 n1
    refine le_trans (Floating.scaleB_le n0) (le_trans ?_ (Floating.le_scaleB n1))
    exact mul_le_mul_of_nonneg_right x.le two_zpow_pos.le)

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB' (x : Interval) (t : Fixed 0) : Interval :=
  bif t == nan then nan else scaleB x t.n

/-- `scaleB` propagates `nan` -/
@[simp] lemma nan_scaleB {t : Int64} : (nan : Interval).scaleB t = nan := by
  rw [scaleB]; simp only [lo_nan, Floating.nan_scaleB, hi_nan, mix_self, coe_nan]

/-- `scaleB` propagates `nan` -/
@[simp] lemma ne_nan_of_scaleB {x : Interval} {t : Int64} (n : x.scaleB t ≠ nan) : x ≠ nan := by
  contrapose n; simp only [ne_eq, not_not] at n
  simp only [n, nan_scaleB, ne_eq, not_true_eq_false, not_false_eq_true]

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
  constructor
  · exact le_trans (Floating.scaleB_le n.1) (mul_le_mul_of_nonneg_right xm.1 two_zpow_pos.le)
  · exact le_trans (mul_le_mul_of_nonneg_right xm.2 two_zpow_pos.le) (Floating.le_scaleB n.2)

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
  rw [tm, Fixed.val, Int64.coe_zero, zpow_zero, mul_one, Real.rpow_int_cast]
  exact mem_approx_scaleB xm
