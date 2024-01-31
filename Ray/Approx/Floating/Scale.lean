import Ray.Floating.Standardization

open Pointwise

/-!
## Floating point scaling by changing the exponent
-/

open Set
open scoped Real
namespace Floating

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB (x : Floating) (t : Int64) (up : Bool) : Floating :=
  bif t.isNeg then
    let t := (-t).n
    bif x.s < t then
      bif x = nan then nan else of_ns (x.n.shiftRightRound (t-x.s) up) 0
    else of_ns x.n (x.s - t)
  else
    bif .max - t.n < x.s then nan else of_ns x.n (x.s + t.n)

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def scaleB' (x : Floating) (t : Fixed 0) (up : Bool) : Floating :=
  bif t == nan then nan else scaleB x t.n up

/-- `scaleB` is conservative -/
@[mono] lemma mem_approx_scaleB {x : Floating} {t : Int64} {up : Bool} {x' : ℝ}
    (xm : x' ∈ approx x) : x' * 2^(t : ℤ) ∈ rounds (approx (x.scaleB t up)) !up := by
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
    · have yn : x.n.shiftRightRound ((-t).n-x.s) up ≠ .min :=
        Int64.shiftRightRound_ne_min (x.n_ne_min xn) _ _
      simp only [xt, xn, ite_false, ite_true, approx_eq_singleton (of_ns_ne_nan_iff.mpr yn),
        val_of_ns yn, Int64.coe_shiftRightRound, UInt64.toInt_zero, zero_sub, zpow_neg,
        mem_rounds_singleton, Bool.not_eq_true']
      rw [val]
      simp only [mul_comm _ _⁻¹, zpow_sub₀ t0.ne', div_eq_mul_inv, ← mul_assoc]
      simp only [mul_assoc, ← zpow_add₀ t0.ne', gt_iff_lt, inv_pos, two_zpow_pos, mul_le_mul_left]
      induction up
      · simp only [ite_true, ge_iff_le]
        refine le_trans Int.rdiv_le ?_
        simp only [Nat.cast_pow, Nat.cast_ofNat, UInt64.toInt, gt_iff_lt, zero_lt_two, pow_pos,
          div_le_iff, mul_assoc, zpow_mul_pow t0.ne', UInt64.coe_toNat_sub xt.le,
          Int64.toNat_neg tn]
        ring_nf
        simp only [zpow_zero, mul_one, le_refl]
      · simp only [ite_false, ge_iff_le]
        refine le_trans ?_ Int.le_rdiv
        simp only [Nat.cast_pow, Nat.cast_ofNat, UInt64.toInt, gt_iff_lt, zero_lt_two, pow_pos,
          le_div_iff, mul_assoc, zpow_mul_pow t0.ne', UInt64.coe_toNat_sub xt.le,
          Int64.toNat_neg tn]
        ring_nf
        simp only [zpow_zero, mul_one, le_refl]
    · apply subset_rounds
      simp only [xt, ite_false, approx_eq_singleton (of_ns_ne_nan_iff.mpr (x.n_ne_min xn)),
        val_of_ns (x.n_ne_min xn), mem_singleton_iff]
      simp only [not_lt] at xt
      rw [val]
      simp only [mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ← zpow_add₀,
        mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj, Int.cast_eq_zero,
        Int64.coe_eq_zero, UInt64.toInt, UInt64.coe_toNat_sub xt, Int64.toNat_neg tn]
      left
      ring
  · apply subset_rounds
    simp only [tn, ite_false]
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
