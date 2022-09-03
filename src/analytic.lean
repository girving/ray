-- Basics about analytic functions (general field case)

import analysis.analytic.basic
import analysis.analytic.composition
import analysis.analytic.linear
import analysis.calculus.fderiv_analytic
import analysis.calculus.formal_multilinear_series
import analysis.complex.cauchy_integral
import data.complex.basic
import data.finset.basic
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import topology.basic

import bounds
import multilinear
import simple
import tactics
import topology

open complex (abs exp I log)
open filter (at_top)
open metric (ball closed_ball sphere is_open_ball)
open linear_order (min)
open_locale real nnreal ennreal topological_space
noncomputable theory

variables {𝕜 : Type} [nontrivially_normed_field 𝕜]
variables {E : Type} [normed_add_comm_group E] [normed_space 𝕜 E] [complete_space E]
variables {F : Type} [normed_add_comm_group F] [normed_space 𝕜 F] [complete_space F]

-- A function is entire iff it is analytic everywhere
def entire (𝕜 : Type) {E F : Type}
    [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F]
    (f : E → F) := ∀ z, analytic_at 𝕜 f z

-- Entire functions are analytic on all sets
lemma entire.analytic_on {f : E → F} {s : set E} (e : entire 𝕜 f) : analytic_on 𝕜 f s := λ x xs, e x

-- Infinite radius of convergence implies entire
lemma radius_inf_to_entire {f : E → F} (p : formal_multilinear_series 𝕜 E F) (z : E)
    : has_fpower_series_on_ball f p z ∞ → entire 𝕜 f := begin
  intros h w,
  refine has_fpower_series_on_ball.analytic_at_of_mem h _,
  rw emetric.mem_ball, exact edist_lt_top w z
end

-- Analytic functions have derivatives
lemma analytic_at.has_deriv_at {f : 𝕜 → E} {z : 𝕜}
    : analytic_at 𝕜 f z → has_deriv_at f (deriv f z) z := begin
  intro a,
  have dwa : differentiable_within_at 𝕜 f set.univ z := analytic_at.differentiable_within_at a,
  refine (dwa.differentiable_at _).has_deriv_at,
  exact is_open.mem_nhds is_open_univ (set.mem_univ z),
end

-- Zero is entire
theorem entire.zero : entire 𝕜 (λ _ : E, (0 : F)) := (0 : E →L[𝕜] F).analytic_at

-- id is entire
theorem entire.id : entire 𝕜 (λ x : E, x) := (continuous_linear_map.id 𝕜 E).analytic_at

-- Finite sums of analytic functions are analytic
theorem analytic_at.sum {f : ℕ → E → F} {c : E}
    (h : ∀ n, analytic_at 𝕜 (f n) c) (N : finset ℕ) : analytic_at 𝕜 (λ z, N.sum (λ n, f n z)) c := begin
  induction N using finset.induction with a B aB hB, {
    simp, exact entire.zero c
  }, {
    simp_rw finset.sum_insert aB,
    apply analytic_at.add,
    exact h a,
    exact hB
  },
end
theorem analytic.sum {f : ℕ → E → F} {s : set E}
    (h : ∀ n, analytic_on 𝕜 (f n) s) (N : finset ℕ) : analytic_on 𝕜 (λ z, N.sum (λ n, f n z)) s :=
  λ z zs, analytic_at.sum (λ n, h n z zs) N

-- Power series terms are analytic
theorem change_origin.analytic_at (p : formal_multilinear_series 𝕜 E F) (rp : p.radius > 0) (n : ℕ)
    : analytic_at 𝕜 (λ x, p.change_origin x n) 0 :=
  (formal_multilinear_series.has_fpower_series_on_ball_change_origin p n rp).analytic_at

-- analytic_on is monotonic in the set
lemma analytic_on.mono {f : E → F} {sa sb : set E} (fa : analytic_on 𝕜 f sb) (s : sa ⊆ sb)
    : analytic_on 𝕜 f sa := λ x xa, fa x (s xa)

-- Analytic at a point means analytic in a small ball
theorem analytic_at.ball {f : E → F} {z : E}
    : analytic_at 𝕜 f z → ∃ (r : ℝ), r > 0 ∧ analytic_on 𝕜 f (ball z r) := begin
  intro a,
  rcases a with ⟨p,r,h⟩,
  by_cases ri : r = ∞, {
    existsi (1 : ℝ),
    exact ⟨by norm_num, λ z zs, has_fpower_series_on_ball.analytic_on h z (by {rw ri, simp})⟩
  }, {
    existsi r.to_real,
    constructor, {
      exact ennreal.to_real_pos (ne_of_gt h.r_pos) ri
    }, {
      intros z zs,
      refine has_fpower_series_on_ball.analytic_on h z _,
      simp at zs ⊢,
      have rr := ennreal.of_real_to_real ri,
      rw [←rr, edist_lt_of_real], assumption
    }
  }
end

-- Analytic at a point means analytic in a small closed ball
theorem analytic_at.cball {f : E → F} {z : E}
    : analytic_at 𝕜 f z → ∃ (r : ℝ), r > 0 ∧ analytic_on 𝕜 f (closed_ball z r) := begin
  intro a,
  rcases analytic_at.ball a with ⟨r, rp, ao⟩,
  existsi r/2,
  constructor, {
    bound
  }, {
    intros z zs,
    refine ao z _,
    simp at ⊢ zs,
    exact lt_of_le_of_lt zs (by bound)
  }
end

-- analytic_on depends only on values on s (→ version)
lemma analytic_on.congr {f g : E → F} {s : set E}
    (fa : analytic_on 𝕜 f s) (o : is_open s) (fg : ∀ z, z ∈ s → f z = g z)
    : analytic_on 𝕜 g s := begin
  intros z zs,
  rcases metric.is_open_iff.mp o z zs with ⟨r0,r0p,r0s⟩,
  rcases fa z zs with ⟨p,r1,fp⟩,
  existsi p, existsi (min (ennreal.of_real r0) r1),
  refine { r_le := trans (min_le_right _ _) fp.r_le,
           r_pos := lt_min_iff.mpr ⟨ennreal.of_real_pos.mpr r0p,fp.r_pos⟩,
           has_sum := _ },
  intros w wr, simp at wr,
  specialize fg (z + w) _, {
    apply r0s,
    simp, exact wr.left
  }, {
    rw ←fg, refine fp.has_sum _,
    simp, exact wr.right
  },
end

-- analytic_on depends only on values on s (↔ version)
lemma analytic_on_congr {f g : E → F} {s : set E}
    (o : is_open s) (fg : ∀ z, z ∈ s → f z = g z)
    : analytic_on 𝕜 f s ↔ analytic_on 𝕜 g s :=
  ⟨λ fa, fa.congr o fg, λ ga, ga.congr o (λ z zs, (fg z zs).symm)⟩

-- analytic_at depends only on values near c (→ version)
lemma analytic_at.congr {f g : E → F} {x : E}
    (fa : analytic_at 𝕜 f x) (h : f =ᶠ[nhds x] g) : analytic_at 𝕜 g x := begin
  rcases metric.eventually_nhds_iff_ball.mp h with ⟨e,ep,es⟩,
  rcases fa.ball with ⟨r,rp,fr⟩,
  have fer : analytic_on 𝕜 f (ball x (min e r)) := fr.mono (metric.ball_subset_ball (by bound)),
  have es' : ∀ y, y ∈ ball x (min e r) → f y = g y :=
    λ y yer, es y (metric.ball_subset_ball (by bound) yer),
  exact fer.congr is_open_ball es' x (metric.mem_ball_self (by bound)),
end

-- analytic_at depends only on values near c (↔ version)
lemma analytic_at_congr {f g : E → F} {x : E} (h : f =ᶠ[nhds x] g) : analytic_at 𝕜 f x ↔ analytic_at 𝕜 g x :=
  ⟨λ fa, fa.congr h, λ ga, ga.congr h.symm⟩