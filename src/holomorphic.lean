-- Basics about complex analytic (holomorphic) functions

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

import analytic
import bounds
import multilinear
import simple
import tactics
import topology

open complex (abs exp I log)
open filter (at_top)
open metric (ball closed_ball sphere)
open linear_order (min)
open_locale real nnreal ennreal topological_space
noncomputable theory

variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
variables {F : Type} [normed_add_comm_group F] [normed_space ℂ F] [complete_space F]

-- A function is entire iff it's differentiable everywhere
lemma differentiable.entire {f : ℂ → E} : differentiable ℂ f ↔ entire ℂ f :=
  ⟨differentiable.analytic_at, λ e z, analytic_at.differentiable_at (e z)⟩

-- A function is analytic at z iff it's differentiable on a surrounding open set
lemma differentiable_iff_analytic {f : ℂ → E} {s : set ℂ}
    (o : is_open s) : differentiable_on ℂ f s ↔ analytic_on ℂ f s := begin
  constructor, {
    intros d z zs,
    have n : s ∈ nhds z := is_open.mem_nhds o zs,
    exact differentiable_on.analytic_at d n
  }, {
    exact analytic_on.differentiable_on
  }
end

-- Constants are entire
theorem entire.const (a : E) : entire ℂ (λ _ : ℂ, a) := differentiable.entire.mp (differentiable_const a)
  
-- z^n is entire
theorem entire.monomial (n : ℕ) : entire ℂ (λ z : ℂ, z^n) := begin
  rw ←differentiable.entire, apply differentiable.pow differentiable_id,
end

-- Products of analytic functions are analytic
theorem analytic.mul {f g : ℂ → ℂ} {s : set ℂ}
    (o : is_open s) (hf : analytic_on ℂ f s) (hg : analytic_on ℂ g s) : analytic_on ℂ (f * g) s := begin
  rw ←differentiable_iff_analytic o at hf hg ⊢,
  exact differentiable_on.mul hf hg,
  repeat { exact complete_of_proper },
end

-- Products of analytic functions are analytic, point version
theorem analytic_at.mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : analytic_at ℂ f z) (hg : analytic_at ℂ g z) : analytic_at ℂ (λ z, f z * g z) z := begin
  rcases hf.ball with ⟨fr,frp,fb⟩,
  rcases hg.ball with ⟨gr,grp,gb⟩,
  have o : is_open (ball z (min fr gr)) := metric.is_open_ball,
  exact analytic.mul o
    (fb.mono (metric.ball_subset_ball (by bound)))
    (gb.mono (metric.ball_subset_ball (by bound)))
    z (metric.mem_ball_self (by bound)),
end

-- Finite products of analytic functions are analytic
theorem prod_analytic {f : ℕ → ℂ → ℂ} {s : set ℂ}
    (o : is_open s) (h : ∀ n, analytic_on ℂ (f n) s) (N : finset ℕ)
    : analytic_on ℂ (λ z, N.prod (λ n, f n z)) s := begin
  induction N using finset.induction with a B aB hB, {
    simp, intros z zs, exact entire.const 1 z
  }, {
    simp_rw finset.prod_insert aB,
    exact analytic.mul o (h a) hB
  }
end

-- exp is entire
theorem entire.exp : entire ℂ exp := begin
  rw ←differentiable.entire, simp
end

-- log is analytic at positive re
theorem log_analytic_re_pos {f : ℂ → ℂ} {c : ℂ}
    : analytic_at ℂ f c → (f c).re > 0 → analytic_at ℂ (λ z, log (f z)) c := begin
  intros fa cp, refine analytic_at.comp _ fa,
  have la : analytic_on ℂ log (ball (f c) (f c).re), {
    rw ←differentiable_iff_analytic metric.is_open_ball,
    apply differentiable_on.clog differentiable_on_id,
    intros z zs, apply or.inl, simp [complex.dist_eq] at ⊢ zs,
    flip_ineq,
    calc z.re = (f c).re - ((f c).re - z.re) : by abel
    ... = (f c).re - (f c - z).re : by rw ←complex.sub_re
    ... ≥ (f c).re - abs (f c - z) : by bound [complex.re_le_abs]
    ... = (f c).re - abs (-(z - f c)) : by ring_nf
    ... = (f c).re - abs (z - f c) : by rw complex.abs_neg
    ... > 0 : by bound,
    apply_instance,
  },
  exact la _ (metric.mem_ball_self cp),
end

-- log is analytic near 1
theorem log_analytic_near_one {f : ℂ → ℂ} {s : set ℂ}
    : is_open s → analytic_on ℂ f s → (∀ z, z ∈ s → abs (f z - 1) < 1)
    → analytic_on ℂ (λ z, log (f z)) s := begin
  intros o fa n,
  rw ←differentiable_iff_analytic o,
  refine differentiable_on.clog _ _,
  rw differentiable_iff_analytic o, assumption, exact complete_of_proper,
  intros z zs,
  exact near_one_avoids_negative_reals (n z zs),
  exact complete_of_proper
end

-- The principle branch of sqrt
def sqrt (z : ℂ) : ℂ := exp (log z / 2)