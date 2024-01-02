import Mathlib.Data.Real.Basic

/-!
## `ℤ` facts
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

lemma abs_zpow {x : ℝ} {n : ℤ} : |x ^ n| = |x| ^ n := by
  induction' n with n n
  · simp only [Int.ofNat_eq_coe, zpow_coe_nat, abs_pow]
  · simp only [zpow_negSucc, abs_inv, abs_pow]
