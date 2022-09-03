-- Versions of max

import analysis.convex.function
import data.real.basic
import topology.continuous_on
import topology.metric_space.basic

open set (univ)
noncomputable theory

-- max expression as a function on pairs
noncomputable def pair_max (p : ℝ × ℝ) := max p.fst p.snd 
lemma pair_max_eq (x y : ℝ) : pair_max (x,y) = max x y := rfl
lemma convex_on_pair_max : convex_on ℝ univ pair_max := begin
  have e : pair_max = (λ p, p.fst) ⊔ (λ p, p.snd), { funext p, simp [pair_max, sup_eq_max] },
  rw e, apply convex_on.sup, {
    use convex_univ, intros, simp,
  }, {
    use convex_univ, intros, simp,
  }
end

-- The max of the first n+1 elements of a sequence (n+1 to avoid empty sets).
-- I ran into annoying technicalities due to finset.max', so writing out range_max inductively
noncomputable def range_max (s : ℕ → ℝ) : ℕ → ℝ
| 0 := s 0
| (n+1) := max (range_max n) (s (n+1))

@[simp] lemma range_max_zero (s : ℕ → ℝ) : range_max s 0 = s 0 := rfl
@[simp] lemma range_max_succ (s : ℕ → ℝ) (n : ℕ) : range_max s n.succ = max (range_max s n) (s n.succ) := by simp [range_max]
lemma monotone.range_max {s : ℕ → ℝ} : monotone (range_max s) := begin
  intros a b ab,
  generalize hd : b - a = d,
  have hd' : b = a + d, { rw ←hd, rw add_comm, rw nat.sub_add_cancel ab },
  rw hd', clear hd hd' ab b,
  induction d with d h, simp,
  apply trans h,
  have e : a + d.succ = (a + d).succ := rfl,
  simp [e]
end
lemma le_range_max_self (s : ℕ → ℝ) (n : ℕ) : s n ≤ range_max s n := begin induction n with n, simp, simp end
lemma le_range_max (s : ℕ → ℝ) {a : ℕ} {n : ℕ} (an : a ≤ n) : s a ≤ range_max s n := begin
  transitivity range_max s a, apply le_range_max_self, apply monotone.range_max an,
end
lemma range_max_le_iff (s : ℕ → ℝ) (n : ℕ) (x : ℝ) : range_max s n ≤ x ↔ ∀ k, k ≤ n → s k ≤ x := begin
  induction n with n h, simp, simp, constructor, {
    intros b k kn, by_cases kn' : k ≤ n, exact h.mp b.1 k kn',
    simp at kn',
    have e : k = n+1, { rw nat.succ_eq_add_one at b kn, linarith },
    rw e, exact b.2,
  }, {
    intro b, use [h.mpr (λ _ kn, b _ (trans kn (nat.le_succ _))), b n.succ (by simp)],
  },
end

lemma continuous_on.range_max {A : Type} [topological_space A] {f : ℕ → A → ℝ} {s : set A}
    (fc : ∀ n, continuous_on (f n) s) (n : ℕ)
    : continuous_on (λ x, range_max (λ k, f k x) n) s := begin
  induction n with n h, simp [fc 0], simp [←pair_max_eq], exact continuous_max.comp_continuous_on (h.prod (fc _)),
end