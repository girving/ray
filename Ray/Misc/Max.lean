import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Basic

/-!
## Lemmas about `max` and `partialSups`
-/

open Set (univ)
noncomputable section

/-- `max` is continuous, `ContinuousOn` comp version -/
theorem ContinuousOn.max {A : Type} [TopologicalSpace A] {f g : A → ℝ} {s : Set A}
    (fc : ContinuousOn f s) (gc : ContinuousOn g s) : ContinuousOn (fun x ↦ max (f x) (g x)) s :=
  continuous_max.comp_continuousOn (fc.prod gc)

/-- `max` is convex -/
theorem convexOn_max : ConvexOn ℝ univ (fun p : ℝ × ℝ ↦ max p.1 p.2) := by
  apply ConvexOn.sup; · use convex_univ; intros; simp
  · use convex_univ; intros; simp

/-- `↔` version of `partialSups_le` -/
theorem partialSups_le_iff (s : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    partialSups s n ≤ x ↔ ∀ k, k ≤ n → s k ≤ x := by
  refine' ⟨_, partialSups_le _ _ _⟩
  induction' n with n h
  · simp only [partialSups_zero, Nat.zero_eq, le_zero_iff, forall_eq, imp_self]
  · simp only [partialSups_succ, sup_le_iff, and_imp]
    intro px sx k kn
    by_cases kn' : k ≤ n; exact h px k kn'
    simp only [not_le] at kn'
    have e : k = n + 1 := by rw [Nat.succ_eq_add_one] at kn; linarith
    rw [e]; exact sx

/-- `partialSups` is continuous -/
theorem ContinuousOn.partialSups {A : Type} [TopologicalSpace A] {f : ℕ → A → ℝ} {s : Set A}
    (fc : ∀ n, ContinuousOn (f n) s) (n : ℕ) :
    ContinuousOn (fun x ↦ partialSups (fun k ↦ f k x) n) s := by
  induction' n with n h; simp [fc 0]; simp; exact ContinuousOn.max h (fc _)
