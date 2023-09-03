-- Versions of max

import analysis.convex.function
import data.real.basic
import topology.basic
import topology.continuous_on
import topology.metric_space.basic

open set (univ)
noncomputable theory

-- max is continuous, continuous_on comp version
lemma continuous_on.max {A : Type} [topological_space A] {f g : A → ℝ} {s : set A}
    (fc : continuous_on f s) (gc : continuous_on g s) : continuous_on (λ x, max (f x) (g x)) s :=
  continuous_max.comp_continuous_on (fc.prod gc)

-- max is convex
lemma convex_on_max : convex_on ℝ univ (λ p : ℝ × ℝ, max p.1 p.2) := begin
  apply convex_on.sup, {
    use convex_univ, intros, simp,
  }, {
    use convex_univ, intros, simp,
  },
end

-- iff version of partial_sups_le
lemma partial_sups_le_iff (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : partial_sups s n ≤ x ↔ ∀ k, k ≤ n → s k ≤ x := begin
  refine ⟨_, partial_sups_le _ _ _⟩,
  induction n with n h, {
    simp only [partial_sups_zero, le_zero_iff, forall_eq, imp_self],
  }, {
    simp only [partial_sups_succ, sup_le_iff, and_imp],
    intros px sx k kn,
    by_cases kn' : k ≤ n, exact h px k kn',
    simp only [not_le] at kn',
    have e : k = n+1, { rw nat.succ_eq_add_one at kn, linarith },
    rw e, exact sx,
  },
end

lemma continuous_on.partial_sups {A : Type} [topological_space A] {f : ℕ → A → ℝ} {s : set A}
    (fc : ∀ n, continuous_on (f n) s) (n : ℕ)
    : continuous_on (λ x, partial_sups (λ k, f k x) n) s := begin
  induction n with n h, simp [fc 0], simp, exact continuous_on.max h (fc _),
end