import Ray.Approx.Floating.Standardization

open Pointwise

/-!
## Floating point scaling by changing the exponent
-/

open Set
open scoped Real
namespace Floating

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB (x : Floating) (t : Int64) : Floating :=
  bif t.isNeg then
    let t := (-t).n
    bif x.s < t then nan else of_ns x.n (x.s - t)
  else
    bif .max - t.n < x.s then nan else of_ns x.n (x.s + t.n)

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB' (x : Floating) (t : Fixed 0) : Floating :=
  bif t == nan then nan else scaleB x t.n

/-- `scaleB` is conservative -/
@[mono] lemma mem_approx_scaleB {x : Floating} (t : Int64) {x' : ℝ}
    (xm : x' ∈ approx x) : x' * 2^(t : ℤ) ∈ approx (x.scaleB t) := by
  rw [scaleB]
  have t0 : 0 < (2 : ℝ) := by norm_num
  by_cases xn : x = nan
  · simp only [Bool.cond_decide, xn, s_nan, decide_True, n_nan, cond_true, of_ns_nan, ite_self,
      Bool.cond_self, approx_nan, rounds_univ, mem_univ]
  simp only [approx_eq_singleton xn, mem_singleton_iff] at xm
  simp only [bif_eq_if, decide_eq_true_eq, xm]
  clear x' xm
  by_cases tn : t.isNeg
  · simp only [tn, ite_true]
    by_cases xt : x.s < (-t).n
    · simp only [xt, ↓reduceIte, approx_nan, mem_univ]
    · simp only [xt, ite_false, approx_eq_singleton (of_ns_ne_nan_iff.mpr (x.n_ne_min xn)),
        val_of_ns (x.n_ne_min xn), mem_singleton_iff]
      simp only [not_lt] at xt
      rw [val]
      simp only [mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ← zpow_add₀,
        mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj, Int.cast_eq_zero,
        Int64.coe_eq_zero, UInt64.toInt, UInt64.coe_toNat_sub xt, Int64.toNat_neg tn]
      left
      ring
  · simp only [tn, ite_false]
    by_cases xt : .max - t.n < x.s
    · simp only [xt, ite_true, approx_nan, mem_univ]
    · simp only [xt, ite_false, approx_eq_singleton (of_ns_ne_nan_iff.mpr (x.n_ne_min xn)),
        val_of_ns (x.n_ne_min xn), mem_singleton_iff]
      simp only [not_lt] at xt
      simp only [Bool.not_eq_true] at tn
      rw [val, mul_assoc, ←zpow_add₀ t0.ne']
      simp only [mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, ne_eq, OfNat.ofNat_ne_one,
        not_false_eq_true, zpow_inj, Int.cast_eq_zero, Int64.coe_eq_zero, UInt64.toInt,
        UInt64.toNat_add_of_le xt, Nat.cast_add, Int64.coe_of_nonneg tn]
      left
      ring

/-- `scaleB _ _` is exact if not `nan` -/
lemma val_scaleB {x : Floating} {t : Int64} (n : x.scaleB t ≠ nan) :
    (x.scaleB t).val = x.val * 2^(t : ℤ) := by
  have h := mem_approx_scaleB t (val_mem_approx (x := x))
  simp only [approx, n, ↓reduceIte, mem_singleton_iff] at h
  exact h.symm

/-- `scaleB` propagates `nan` -/
@[simp] lemma nan_scaleB {t : Int64} : (nan : Floating).scaleB t = nan := by
  rw [scaleB]
  simp only [bif_eq_if, decide_true_eq_true, if_true]
  split_ifs
  all_goals simp only [n_nan, s_nan, of_ns_nan]

/-- `scaleB` propagates `nan` -/
@[simp] lemma ne_nan_of_scaleB {x : Floating} {t : Int64} (n : x.scaleB t ≠ nan) : x ≠ nan := by
  contrapose n; simp only [ne_eq, not_not] at n
  simp only [n, nan_scaleB, ne_eq, not_true_eq_false, not_false_eq_true]

/-!
### Dividing by two
-/

@[irreducible] def div2 (x : Floating) : Floating := x.scaleB (-1)

/-- `div2` is conservative -/
@[mono] lemma mem_approx_div2 {x : Floating} {x' : ℝ} (xm : x' ∈ approx x) :
    x' / 2 ∈ approx x.div2 := by
  have e : x' / 2 = x' * 2^(-1 : ℤ) := by
    simp only [div_eq_mul_inv, Int.reduceNeg, zpow_neg, zpow_one]
  rw [e, div2]
  exact mem_approx_scaleB _ xm

/-- `div2` is exact if not `nan` -/
lemma val_div2 {x : Floating} (n : x.div2 ≠ nan) : x.div2.val = x.val / 2 := by
  symm
  simpa only [approx, n, ↓reduceIte, mem_singleton_iff] using
    mem_approx_div2 (val_mem_approx (x := x))

/-- `div2` propagates `nan` -/
@[simp] lemma nan_div2 : (nan : Floating).div2 = nan := by
  rw [div2]; simp only [nan_scaleB]

/-- `div2` propagates `nan` -/
@[simp] lemma ne_nan_of_div2 {x : Floating} (n : x.div2 ≠ nan) : x ≠ nan := by
  rw [div2] at n; exact ne_nan_of_scaleB n
