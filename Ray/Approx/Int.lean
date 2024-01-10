import Mathlib.Data.Real.Basic

/-!
## `ℤ` facts
-/

lemma abs_zpow {x : ℝ} {n : ℤ} : |x ^ n| = |x| ^ n := by
  induction' n with n n
  · simp only [Int.ofNat_eq_coe, zpow_coe_nat, abs_pow]
  · simp only [zpow_negSucc, abs_inv, abs_pow]
