-- Facts about the dual space unit ball in a normed_space

import topology.basic

import max
import max_log
import tactics
import topology

open complex (abs exp I log)
open filter (at_top)
open function (curry uncurry)
open metric (ball closed_ball sphere)
open set (range univ)
open topological_space (second_countable_topology)
open_locale real nnreal ennreal topological_space complex_conjugate
noncomputable theory

variables {G : Type} [normed_add_comm_group G]
variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [second_countable_topology E]

-- A nonconstructive function which extracts a dual vector exhibiting f x = ∥x∥
def dual_vector (x : E) : E →L[ℂ] ℂ := classical.some (exists_dual_vector'' ℂ x)
lemma dual_vector_norm (x : E) : ∥dual_vector x∥ ≤ 1 := (classical.some_spec (exists_dual_vector'' ℂ x)).1
lemma dual_vector_nnnorm (x : E) : ∥dual_vector x∥₊ ≤ 1 := dual_vector_norm _
@[simp] lemma dual_vector_apply (x : E) : dual_vector x x = ∥x∥ := (classical.some_spec (exists_dual_vector'' ℂ x)).2

lemma dual_vector_le (x y : E) : abs (dual_vector x y) ≤ ∥y∥ := begin
  rw ←complex.norm_eq_abs,
  calc ∥dual_vector x y∥ ≤ ∥dual_vector x∥ * ∥y∥ : (dual_vector x).le_op_norm y
  ... ≤ 1 * ∥y∥ : by bound [dual_vector_norm x]
  ... = ∥y∥ : by simp,
end

-- Dual vectors of a dense subset of E
def duals : ℕ → E →L[ℂ] ℂ := λ n, dual_vector (topological_space.dense_seq E n)

-- Lipschitz 0 functions are constant
lemma lipschitz_with.is_const {g : ℝ → ℝ} (g0 : lipschitz_with 0 g) : ∀ x y, g x = g y := begin
  intros x y, have h := g0 x y, simp at h, exact h,
end

lemma duals_bdd_above {g : ℝ → ℝ} (gm : monotone g) (x : E)
    : bdd_above (range (λ n, g ∥duals n x∥)) := begin
  rw bdd_above_def, use [g ∥x∥], simp, intro n, apply gm, apply dual_vector_le,
end

-- One-sided Lipschitz bounds on the reals
lemma lipschitz_with.le {f : G → ℝ} {k : ℝ≥0} (fk : lipschitz_with k f) (x y : G) : f x ≤ f y + k * dist x y := begin
  calc f x = f y + (f x - f y) : by ring_nf
  ... ≤ f y + |f x - f y| : by bound
  ... = f y + dist (f x) (f y) : by rw real.dist_eq
  ... ≤ f y + k * dist x y : by bound [fk.dist_le_mul x y],
end 

-- Norms are suprs over duals (version with an arbitrary monotone + Lipschitz function)
lemma norm_eq_duals_supr' {g : ℝ → ℝ} {k : nnreal} (gm : monotone g) (gk : lipschitz_with k g) (x : E)
    : g ∥x∥ = ⨆ n, g ∥duals n x∥ := begin
  by_cases k0 : k = 0, { rw k0 at gk, have g0 := gk.is_const 0, simp [←g0 _] },
  have kp : (k : ℝ) > 0, { simp at ⊢, exact ne.bot_lt k0, },
  apply le_antisymm, {
    apply le_of_forall_pos_le_add, intros e ep,
    rcases metric.dense_range_iff.mp (topological_space.dense_range_dense_seq E) x (e/2/k) (by bound) with ⟨n,nx⟩,
    generalize hy : topological_space.dense_seq E n = y, rw hy at nx,
    have hn : duals n = dual_vector y := by rw [←hy,duals],
    have h := le_csupr (duals_bdd_above gm x) n,
    generalize hs : (⨆ n, g ∥duals n x∥) = s,
    simp_rw [hs,hn] at h, clear hs hn hy, simp at h,
    have gk' : lipschitz_with k (λ x, g (abs (dual_vector y x))), {
      have k11 : (k : ℝ≥0) = k * 1 * 1 := by norm_num, rw k11,
      simp_rw ←complex.norm_eq_abs, apply (gk.comp lipschitz_with_one_norm).comp,
      exact (dual_vector y).lipschitz.weaken (dual_vector_nnnorm y),
    },
    calc g ∥x∥ ≤ g (∥y∥) + (k * 1) * dist x y : (gk.comp lipschitz_with_one_norm).le x y
    ... ≤ g (∥y∥) + (k * 1) * (e/2 / k) : by bound
    ... = g (∥y∥) + k / k * e/2 : by ring
    ... ≤ g (∥y∥) + 1 * e/2 : by bound
    ... = g (∥y∥) + e/2 : by simp
    ... = g (abs (dual_vector y y)) + e/2 : by simp
    ... ≤ g (abs (dual_vector y x)) + k * dist y x + e/2 : by bound [gk'.le]
    ... ≤ s + k * dist y x + e/2 : by bound
    ... = s + k * dist x y + e/2 : by rw dist_comm
    ... ≤ s + k * (e/2 / k) + e/2 : by bound
    ... = s + k / k * e/2 + e/2 : by ring_nf
    ... ≤ s + 1 * e/2 + e/2 : by bound
    ... = s + e : by ring_nf,
  }, {
    apply csupr_le, intro n, apply gm, simp, apply dual_vector_le,
  },
end

lemma norm_eq_duals_supr (x : E) : ∥x∥ = ⨆ n, ∥duals n x∥ := begin
  have h := norm_eq_duals_supr' (@monotone_id ℝ _) lipschitz_with.id x, simp at h ⊢, exact h,
end

lemma max_log_norm_eq_duals_supr (b : ℝ) (x : E)
    : max_log b ∥x∥ = ⨆ n, max_log b ∥duals n x∥ :=
  norm_eq_duals_supr' (monotone_max_log b) (lipschitz_with.max_log b) x
  
-- Rewrite a ℕ supr into a monotonic limit
lemma csupr.has_lim (s : ℕ → ℝ) (ba : bdd_above (range s))
    : filter.tendsto (λ n, range_max s n) at_top (𝓝 (⨆ n, s n)) := begin
  rw metric.tendsto_at_top, intros e ep,
  generalize hb : (⨆ n, s n) - e = b,
  have bs : b < (⨆ n, s n), { rw ←hb, exact sub_lt_self _ (by bound) },
  rcases exists_lt_of_lt_csupr bs with ⟨N,sN⟩, simp at sN,
  use N, intros n nN, rw real.dist_eq, rw abs_lt, constructor, {
    simp, simp [←hb] at sN,
    calc supr s = supr s - e + e : by ring
    ... < s N + e : by bound
    ... ≤ range_max s n + e : by bound [le_range_max s nN]
    ... = e + range_max s n : by ring,
  }, {
    simp,
    have rs : range_max s n ≤ supr s, {
      rw range_max_le_iff, intros a an,
      exact le_csupr ba a,
    },
    calc range_max s n - supr s ≤ supr s - supr s : by bound
    ... = 0 : by ring
    ... < e : ep,
  },
end

lemma duals_lim_tendsto_max_log_norm (b : ℝ) (x : E)
    : filter.tendsto (range_max (λ k, max_log b ∥duals k x∥)) at_top (𝓝 (max_log b ∥x∥)) := begin
  rw max_log_norm_eq_duals_supr, exact csupr.has_lim _ (duals_bdd_above (monotone_max_log _) _),
end

lemma max_log_norm_eq_duals_lim (b : ℝ) (x : E)
    : max_log b ∥x∥ = lim at_top (range_max (λ k, max_log b ∥duals k x∥)) := begin
  have a := duals_lim_tendsto_max_log_norm b x,
  exact tendsto_nhds_unique a (tendsto_nhds_lim ⟨_,a⟩),
end