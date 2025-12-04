import Mathlib.Analysis.RCLike.Basic

/-!
## Facts about `d ≥ 2`

This is a separate file so I can import them separate from dynamics machinery.
-/

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

lemma two_le_d (d : ℕ) [h : Fact (2 ≤ d)] : 2 ≤ d := h.elim
lemma d_pos (d : ℕ) [Fact (2 ≤ d)] : 0 < d := by linarith [two_le_d d]
lemma d_ne_zero (d : ℕ) [Fact (2 ≤ d)] : d ≠ 0 := (d_pos d).ne'
lemma d_gt_one (d : ℕ) [Fact (2 ≤ d)] : 1 < d := by linarith [two_le_d d]
lemma d_ge_one (d : ℕ) [Fact (2 ≤ d)] : 1 ≤ d := (d_gt_one _).le
lemma d_minus_one_pos (d : ℕ) [Fact (2 ≤ d)] : 0 < d - 1 := by have h := two_le_d d; omega
lemma one_le_d_minus_one (d : ℕ) [Fact (2 ≤ d)] : 1 ≤ d - 1 := by have h := two_le_d d; omega
lemma two_le_cast_d (d : ℕ) [Fact (2 ≤ d)] : (2 : ℝ) ≤ d :=
  le_trans (by norm_num) (Nat.cast_le.mpr (two_le_d d))

-- Teach `bound` about `d`
attribute [bound] two_le_d d_gt_one d_ge_one d_pos two_le_cast_d one_le_d_minus_one
attribute [aesop norm apply (rule_sets := [Bound])] d_ne_zero  -- TODO: Make `@[bound]` work here

/-- `2` works -/
instance : Fact (2 ≤ 2) := ⟨by norm_num⟩
