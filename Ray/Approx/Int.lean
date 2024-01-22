import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic

/-!
## `ℤ` facts
-/

/-- `abs` and `zpow` commute -/
lemma abs_zpow {x : ℝ} {n : ℤ} : |x ^ n| = |x| ^ n := by
  induction' n with n n
  · simp only [Int.ofNat_eq_coe, zpow_coe_nat, abs_pow]
  · simp only [zpow_negSucc, abs_inv, abs_pow]

/-- `Int` division, rounding up or down -/
def Int.rdiv (a : ℤ) (b : ℕ) (up : Bool) : ℤ :=
  bif up then -(-a / b) else a / b

/-- `rdiv` rounds down if desired -/
lemma Int.rdiv_le {a : ℤ} {b : ℕ} : (a.rdiv b false : ℝ) ≤ a / b := by
  simp only [rdiv, cond_false]
  by_cases b0 : b = 0
  · simp only [b0, Nat.cast_zero, Int.ediv_zero, cast_zero, div_zero, le_refl]
  · rw [le_div_iff]
    · have e : (b : ℝ) = (b : ℤ) := rfl
      rw [e, ←Int.cast_mul, Int.cast_le]
      exact Int.ediv_mul_le _ (Nat.cast_ne_zero.mpr b0)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)

/-- `rdiv` rounds up if desired -/
lemma Int.le_rdiv {a : ℤ} {b : ℕ} : (a / b : ℝ) ≤ a.rdiv b true := by
  simp only [rdiv, cond_true, cast_neg]
  by_cases b0 : b = 0
  · simp only [b0, Nat.cast_zero, div_zero, Int.ediv_zero, cast_zero, neg_zero, le_refl]
  · rw [le_neg, ←neg_div, ←Int.cast_neg]
    generalize -a = a
    rw [le_div_iff]
    · have e : (b : ℝ) = (b : ℤ) := rfl
      rw [e, ←Int.cast_mul, Int.cast_le]
      exact Int.ediv_mul_le _ (Nat.cast_ne_zero.mpr b0)
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)

/-- `Int.ediv (-small) big = -1` -/
lemma Int.ediv_eq_neg_one {a b : ℤ} (a0 : 0 < a) (ab : a ≤ b) : -a / b = -1 := by
  refine Eq.trans (Int.ediv_of_neg_of_pos (by omega) (by omega)) ?_
  simp only [neg_neg, neg_add_rev, add_right_eq_self, neg_eq_zero]
  exact Int.ediv_eq_zero_of_lt (by omega) (by omega)

/-- `a ^ n / a ^ k = a ^ (n - k)` if `k ≤ n` -/
lemma Int.ediv_pow_of_le {a : ℤ} {n k : ℕ} (a0 : a ≠ 0) (kn : k ≤ n) :
    a ^ n / a ^ k = a ^ (n - k) := by
  rw [←Int.cast_inj (α := ℝ), Int.cast_div]
  · simp only [cast_pow]
    rw [pow_sub₀ _ (Int.cast_ne_zero.mpr a0) kn, div_eq_mul_inv]
  · exact pow_dvd_pow _ kn
  · positivity

/-- `-a ^ n / a ^ k = -a ^ (n - k)` if `k ≤ n` -/
lemma Int.neg_ediv_pow_of_le {a : ℤ} {n k : ℕ} (a0 : a ≠ 0) (kn : k ≤ n) :
    -a ^ n / a ^ k = -a ^ (n - k) := by
  rw [Int.neg_ediv_of_dvd, Int.ediv_pow_of_le a0 kn]
  exact pow_dvd_pow _ kn

/-- `ℕ`'s `-ceilDiv` in terms of `Int.ediv` -/
lemma Int.cast_neg_ceilDiv_eq_ediv (a b : ℕ) : -((a ⌈/⌉ b : ℕ) : ℤ) = (-a) / b := by
  simp only [Nat.ceilDiv_eq_add_pred_div, ofNat_ediv]
  by_cases b0 : b = 0
  · simp only [b0, add_zero, Nat.cast_zero, Int.ediv_zero, neg_zero]
  have b0' : (b : ℤ) ≠ 0 := by omega
  have b1 : 1 ≤ b := by omega
  rw [←Nat.div_add_mod a b]
  generalize a / b = x
  generalize hy : a % b = y
  have yb : y < b := by rw [←hy]; exact Nat.mod_lt a b1
  rw [mul_comm b]
  by_cases y0 : y = 0
  · simp only [y0, add_zero, Nat.cast_mul, ←Int.neg_mul, Nat.add_sub_assoc b1,
      Int.mul_ediv_cancel _ b0', Nat.cast_add, Nat.cast_mul, neg_inj]
    rw [add_comm, Int.add_mul_ediv_right, add_left_eq_self]
    · apply Int.ediv_eq_zero_of_lt; omega; omega
    · omega
  · have y1 : 1 ≤ y := by omega
    have e : x * b + y + b - 1 = (x + 1) * b + (y - 1) := by
      rw [Nat.add_assoc, Nat.add_comm y b, ←Nat.add_assoc, ←add_one_mul, ←Nat.add_sub_assoc y1]
    simp only [e, Nat.cast_add, Nat.cast_mul, Nat.cast_one, neg_add_rev, ←neg_mul,
      add_comm ((↑x + 1) * ↑b), Int.add_mul_ediv_right _ _ b0']
    have yb0 : ((y - 1 : ℕ) : ℤ) / b = 0 := by
      rw [Int.ediv_eq_zero_of_lt (by omega)]
      omega
    have yb1 : -(y : ℤ) / b = -1 := by
      have e : -(y : ℤ) = ((b - y) + -1 * b) := by ring_nf
      rw [e, Int.add_mul_ediv_right _ _ b0', Int.ediv_eq_zero_of_lt (by omega) (by omega)]
      norm_num
    simp only [yb0, yb1]
    ring_nf

/-- `ℕ`'s `ceilDiv` in terms of `Int.ediv` -/
lemma Int.cast_ceilDiv_eq_neg_ediv (a b : ℕ) : ((a ⌈/⌉ b : ℕ) : ℤ) = -((-a) / b) := by
  rw [←Int.cast_neg_ceilDiv_eq_ediv, neg_neg]
