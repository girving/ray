-- Infinite series of analytic functions

import analysis.analytic.basic
import data.complex.basic
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import topology.metric_space.basic
import topology.uniform_space.uniform_convergence
import topology.algebra.infinite_sum

import analytic
import bounds
import simple
import tactics
import uniform

open complex (abs)
open filter (at_top)
open metric (ball closed_ball sphere)
open_locale real nnreal ennreal topological_space

noncomputable theory

-- Summability restricted to sets
def summable_on (f : ℕ → ℂ → ℂ) (s : set ℂ) := ∀ z, z ∈ s → summable (λ n, f n z)
def has_sum_on (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : set ℂ) := ∀ z, z ∈ s → has_sum (λ n, f n z) (g z)
noncomputable def tsum_on (f : ℕ → ℂ → ℂ) := λ z, tsum (λ n, f n z)
def has_uniform_sum (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : set ℂ) :=
  tendsto_uniformly_on (λ (N : finset ℕ) z, N.sum (λ n, f n z)) g at_top s

-- Uniform vanishing means late sums are uniformly small
def uniform_vanishing (f : ℕ → ℂ → ℂ) (s : set ℂ) :=
  ∀ e : ℝ, e > 0 → ∃ n : ℕ, ∀ (N : finset ℕ) z, late N n → z ∈ s → N.sum (λ n, abs (f n z)) < e

lemma uniform_vanishing_to_summable {f : ℕ → ℂ → ℂ} {s : set ℂ} {z : ℂ}
    (zs : z ∈ s) (h : uniform_vanishing f s) : summable (λ n, f n z) := begin
  rw [summable_iff_cauchy_seq_finset, metric.cauchy_seq_iff],
  intros e ep,
  rcases h e ep with ⟨m,hm⟩,
  existsi finset.range m,
  intros A HA B HB,
  calc dist (A.sum (λ n, f n z)) (B.sum (λ n, f n z)) ≤ (A ∆ B).sum (λ n, abs (f n z)) : symm_diff_bound _ _ _
  ... < e : hm (A ∆ B) z (symm_diff_late HA HB) zs
end

lemma uniform_vanishing_to_uniform_cauchy_series {f : ℕ → ℂ → ℂ} {s : set ℂ}
    (h : uniform_vanishing f s) : uniform_cauchy_seq_on (λ (N : finset ℕ) z, N.sum (λ n, f n z)) at_top s := begin
  rw metric.uniform_cauchy_seq_on_iff,
  intros e ep,
  rcases h e ep with ⟨m,hm⟩,
  existsi finset.range m,
  intros A HA B HB z zs,
  calc dist (A.sum (λ n, f n z)) (B.sum (λ n, f n z)) ≤ (A ∆ B).sum (λ n, abs (f n z)) : symm_diff_bound _ _ _
  ... < e : hm (A ∆ B) z (symm_diff_late HA HB) zs
end

lemma uniform_vanishing_to_tendsto_uniformly_on {f : ℕ → ℂ → ℂ} {s : set ℂ}
    (h : uniform_vanishing f s) : has_uniform_sum f (tsum_on f) s := begin
  rw [has_uniform_sum, metric.tendsto_uniformly_on_iff],
  intros e ep,
  rcases h (e/4) (by bound) with ⟨m,hm⟩,
  rw filter.eventually_at_top,
  existsi finset.range m,
  intros N Nm z zs,
  rw tsum_on, simp,
  generalize G : tsum (λ n, f n z) = g,
  have S : summable (λ n, f n z) := uniform_vanishing_to_summable zs h,
  have GS : has_sum (λ n, f n z) g, { rw ←G, exact summable.has_sum S }, clear S,
  rw has_sum at GS,
  rw metric.tendsto_at_top at GS,
  rcases GS (e/4) (by bound) with ⟨M,HM⟩, clear GS G h,
  set A := N ∪ (M \ N),
  have AM : M ⊆ A := simple.subset_union_sdiff _ _,
  simp at HM,
  specialize HM A AM,
  rw dist_comm at HM,
  calc dist g (N.sum (λ n, f n z)) ≤ dist g (A.sum (λ n, f n z)) + dist (A.sum (λ n, f n z)) (N.sum (λ n, f n z)) : by bound
  ... ≤ e/4 + dist (A.sum (λ n, f n z)) (N.sum (λ n, f n z)) : by bound
  ... = e/4 + dist (N.sum (λ n, f n z) + (M \ N).sum (λ n, f n z)) (N.sum (λ n, f n z))
      : by rw finset.sum_union finset.disjoint_sdiff
  ... = e/4 + abs (N.sum (λ n, f n z) + (M \ N).sum (λ n, f n z) - N.sum (λ n, f n z)) : by rw complex.dist_eq
  ... = e/4 + abs ((M \ N).sum (λ n, f n z)) : by ring_nf
  ... ≤ e/4 + (M \ N).sum (λ n, abs (f n z)) : by bound [simple.finset_complex_abs_sum_le (M \ N) (λ n, f n z)]
  ... ≤ e/4 + e/4 : by bound [hm (M \ N) z (sdiff_late M Nm) zs]
  ... = e/2 : by ring
  ... < e : by bound
end

-- Geometric bounds with c ≤ 0 are degenerate
lemma c_nonpos.degenerate {f : ℕ → ℂ → ℂ} {s : set ℂ} {c a : ℝ}
    (c0 : c ≤ 0) (a0 : 0 ≤ a) (hf : ∀ n z, z ∈ s → abs (f n z) ≤ c * a^n)
    : ∀ n z, z ∈ s → f n z = 0 := begin
  intros n z zs, specialize hf n z zs,
  have ca : c * a^n ≤ 0 := mul_nonpos_iff.mpr (or.inr ⟨c0, by bound⟩),
  exact complex.abs_eq_zero.mp (le_antisymm (trans hf ca) (complex.abs_nonneg _))
end

-- Uniformly exponentially converging series converge uniformly.
theorem fast_series_converge_uniformly_on {f : ℕ → ℂ → ℂ} {s : set ℂ} {c a : ℝ}
    (a0 : 0 ≤ a) (a1 : a < 1) (hf : ∀ n z, z ∈ s → abs (f n z) ≤ c * a^n)
    : has_uniform_sum f (tsum_on f) s := begin
  by_cases c0 : c ≤ 0, {
    have fz := c_nonpos.degenerate c0 a0 hf, simp at fz,
    rw [has_uniform_sum, metric.tendsto_uniformly_on_iff],
    intros e ep, apply filter.eventually_of_forall, intros n z zs,
    rw tsum_on, simp,
    simp_rw fz _ z zs, simp,
    assumption
  }, {
    simp at c0,
    apply uniform_vanishing_to_tendsto_uniformly_on,
    -- ∀ e : ℝ, e > 0 → ∃ n : ℕ, ∀ (N : finset ℕ) z, late N n → z ∈ s → N.sum (λ n, abs (f n z)) < e
    intros e ep,
    set t := (1-↑a)/↑c*(e/2),
    have tp : t > 0 := by bound,
    rcases exists_pow_lt_of_lt_one tp a1 with ⟨n,nt⟩,
    existsi n,
    intros N z NL zs,
    have a1p : 1 - (a : ℝ) > 0 := by bound,
    calc N.sum (λ n, abs (f n z)) ≤ N.sum (λ n, c * a^n) : finset.sum_le_sum (λ n _, hf n z zs)
    ... = c * N.sum (λ n, a^n) : finset.mul_sum.symm
    ... ≤ c * (a^n * (1 - a)⁻¹) : by bound [late_geometric_bound _ (by bound) a1]
    ... = a^n * (c * (1 - a)⁻¹) : by ring
    ... ≤ t * (c * (1 - a)⁻¹) : by bound
    ... = (1 - a) / c * (e / 2) * (c * (1 - a)⁻¹) : rfl
    ... = (1 - a) * (1 - a)⁻¹ * (c / c) * (e / 2) : by ring
    ... = 1 * 1 * (e / 2) : by rw [field.mul_inv_cancel (ne_of_gt a1p), simple.div_self (ne_of_gt c0)]
    ... = e / 2 : by ring
    ... < e : by bound
  }
end

-- Exponentially converging series converge.
theorem fast_series_converge_at {f : ℕ → ℂ} {c a : ℝ}
    (a0 : 0 ≤ a) (a1 : a < 1) (hf : ∀ n, abs (f n) ≤ c * a^n) : summable f := begin
  set s : set ℂ := {0},
  set g : ℕ → ℂ → ℂ := λ n _, f n,
  have hg : ∀ n z, z ∈ s → abs (g n z) ≤ c * a^n := λ n z zs, hf n,
  have u := fast_series_converge_uniformly_on a0 a1 hg,
  simp at u,
  rw has_uniform_sum at u,
  rw tendsto_uniformly_on_singleton_iff_tendsto at u,
  apply has_sum.summable, assumption
end

-- Finite sums of analytic functions are analytic
lemma finite_sums_are_analytic {f : ℕ → ℂ → ℂ} {s : set ℂ}
    (h : ∀ n, analytic_on ℂ (f n) s) (N : finset ℕ) : analytic_on ℂ (λ z, N.sum (λ n, f n z)) s := begin
  induction N using finset.induction with a B aB hB, {
    simp, intros z zs, exact entire.zero z
  }, {
    intros z zs,
    simp_rw finset.sum_insert aB,
    apply analytic_at.add,
    exact h a z zs,
    exact hB z zs
  }
end

-- Analytic series that converge exponentially converge to analytic functions.
theorem fast_series_converge {f : ℕ → ℂ → ℂ} {s : set ℂ} {c a : ℝ}
    (o : is_open s) (a0 : 0 ≤ a) (a1 : a < 1)
    (h : ∀ n, analytic_on ℂ (f n) s) (hf : ∀ n z, z ∈ s → abs (f n z) ≤ c * a^n)
    : ∃ (g : ℂ → ℂ), analytic_on ℂ g s ∧ has_sum_on f g s := begin
  set g := tsum_on f,
  existsi g,
  have su : has_uniform_sum f g s := fast_series_converge_uniformly_on a0 a1 hf,
  constructor, {
    refine uniform_analytic_lim o _ su,
    exact finite_sums_are_analytic h
  }, {
    intros z zs,
    exact summable.has_sum (fast_series_converge_at a0 a1 (λ n, hf n z zs))
  }
end