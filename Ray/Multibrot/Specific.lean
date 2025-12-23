module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.NumberField.Basic

/-!
## Bounds about `exp`, `log` at specific values or bounds
-/

open Real (exp log)
open Set
noncomputable section

-- We do big `norm_num` calculations in this file
set_option exponentiation.threshold 2000

/-- `exp a < b` in terms `norm_num` can handle `-/
public lemma exp_ofNat_lt {a : ℕ} {b : ℝ} (a0 : a ≠ 0 := by norm_num)
    (h0 : 2.7182818286 ^ a < b := by norm_num) : exp a < b := by
  rw [←Real.exp_one_pow a]
  exact _root_.trans (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg _) a0) h0

/-- `exp (-a) < b` in terms `norm_num` can handle `-/
public lemma exp_neg_ofNat_lt {a : ℕ} {b : ℝ} (a0 : a ≠ 0 := by norm_num)
    (b0 : 0 < b := by norm_num) (h0 : b⁻¹ < 2.7182818283 ^ a := by norm_num) : exp (-a) < b := by
  rw [Real.exp_neg, inv_lt_comm₀, ←Real.exp_one_pow a]
  · exact _root_.trans h0 (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) a0)
  · exact Real.exp_pos _
  · exact b0

/-- `b < exp a` in terms `norm_num` can handle `-/
public lemma lt_exp_ofNat {a : ℕ} {b : ℝ} (a0 : a ≠ 0 := by norm_num)
    (h0 : b < 2.7182818283 ^ a := by norm_num) : b < exp a := by
  rw [←Real.exp_one_pow a]
  exact _root_.trans h0 (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) a0)

/-- `c < exp (a/b)` in terms `norm_num` can handle `-/
public lemma lt_exp_div {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num) (b0 : b ≠ 0 := by norm_num)
    (c0 : 0 < c := by norm_num) (h0 : c ^ b < 2.7182818283 ^ a := by norm_num) :
    c < exp (a / b) := by
  have e : exp (a/b : ℝ) = exp 1 ^ (a / b : ℝ) := by rw [Real.exp_one_rpow]
  rw [e, div_eq_mul_inv, Real.rpow_mul (Real.exp_nonneg _), Real.lt_rpow_inv_iff_of_pos,
    Real.rpow_natCast, Real.rpow_natCast]
  · exact _root_.trans h0 (pow_lt_pow_left₀ Real.exp_one_gt_d9 (by norm_num) a0)
  · exact c0.le
  · apply Real.rpow_nonneg (Real.exp_nonneg _)
  · simp only [Nat.cast_pos, Nat.pos_iff_ne_zero]; exact b0

/-- `exp (a/b) < c` in terms `norm_num` can handle `-/
public lemma exp_div_lt {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num) (b0 : b ≠ 0 := by norm_num)
    (c0 : 0 < c := by norm_num) (h0 : 2.7182818286 ^ a < c ^ b := by norm_num) :
    exp (a / b) < c := by
  have e : exp (a/b : ℝ) = exp 1 ^ (a / b : ℝ) := by rw [Real.exp_one_rpow]
  rw [e, div_eq_mul_inv, Real.rpow_mul (Real.exp_nonneg _), Real.rpow_inv_lt_iff_of_pos,
    Real.rpow_natCast, Real.rpow_natCast]
  · exact _root_.trans (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_nonneg _) a0) h0
  · apply Real.rpow_nonneg (Real.exp_nonneg _)
  · exact c0.le
  · simp only [Nat.cast_pos, Nat.pos_iff_ne_zero]; exact b0

/-- `exp (-(a/b)) < c` in terms `norm_num` can handle `-/
public lemma exp_neg_div_lt {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num)
    (b0 : b ≠ 0 := by norm_num) (c0 : 0 < c := by norm_num)
    (h0 : c⁻¹ ^ b < 2.7182818283 ^ a := by norm_num) :
    exp (-(a / b : ℝ)) < c := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) c0]
  exact lt_exp_div a0 b0 (inv_pos.mpr c0) h0

/-- `c < exp (-(a/b))` in terms `norm_num` can handle `-/
public lemma lt_exp_neg_div {a b : ℕ} {c : ℝ} (a0 : a ≠ 0 := by norm_num)
    (b0 : b ≠ 0 := by norm_num) (c0 : 0 < c := by norm_num)
    (h0 : 2.7182818286 ^ a < c⁻¹ ^ b := by norm_num) :
    c < exp (-(a / b : ℝ)) := by
  rw [Real.exp_neg, lt_inv_comm₀ c0 (Real.exp_pos _)]
  exact exp_div_lt a0 b0 (inv_pos.mpr c0) h0

-- Specific values of `exp`
public lemma exp_two_thirds_lt : exp (2/3) < 1.95 := exp_div_lt
public lemma le_exp_9 : 1000 ≤ exp 9 := (lt_exp_ofNat).le

-- Specific values of `log`
public lemma lt_log_2 : 0.693 < log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  norm_num; exact exp_div_lt
public lemma lt_log_3 : 1.098 < log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  norm_num; exact exp_div_lt
public lemma log_3_lt : log 3 < 1.099 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  norm_num; exact lt_exp_div
public lemma lt_log_4 : 1.386 < log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  norm_num; exact exp_div_lt
public lemma log_4_lt : log 4 < 1.387 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  norm_num; exact lt_exp_div

/-- `-log (1 - 1/x) < 0.41` if `3 ≤ x` -/
public lemma neg_log_one_sub_lt {x : ℝ} (x3 : 3 ≤ x) : -log (1 - 1/x) < 0.41 := by
  have le : 2/3 ≤ 1 - 1 / x := by
    rw [le_tsub_iff_le_tsub (by norm_num), one_div, inv_le_comm₀ (by positivity)]
    · exact le_trans (by norm_num) x3
    · norm_num
    · rw [one_div, inv_le_one_iff₀]; right; exact le_trans (by norm_num) x3
  rw [neg_lt, Real.lt_log_iff_exp_lt (lt_of_lt_of_le (by norm_num) le)]
  refine lt_of_lt_of_le ?_ le
  norm_num; exact exp_neg_div_lt
