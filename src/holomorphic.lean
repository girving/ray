-- Basics about complex analytic (holomorphic) functions

import analysis.analytic.basic
import analysis.analytic.composition
import analysis.analytic.isolated_zeros
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
import osgood
import tactics
import topology

open complex (abs exp I log)
open filter (at_top)
open metric (ball closed_ball sphere is_open_ball)
open linear_order (min)
open set (univ)
open_locale real nnreal ennreal topology
noncomputable theory

variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
variables {F : Type} [normed_add_comm_group F] [normed_space ℂ F] [complete_space F]

-- A function is entire iff it's differentiable everywhere
lemma differentiable.entire {f : ℂ → E} : differentiable ℂ f ↔ analytic_on ℂ f univ :=
  ⟨λ d z m, d.analytic_at z, λ a z, (a z (set.mem_univ _)).differentiable_at⟩

-- A function is analytic at z iff it's differentiable on a surrounding open set
lemma differentiable_iff_analytic {f : ℂ → E} {s : set ℂ}
    (o : is_open s) : differentiable_on ℂ f s ↔ analytic_on ℂ f s := begin
  constructor, {
    intros d z zs,
    have n : s ∈ nhds z := is_open.mem_nhds o zs,
    exact differentiable_on.analytic_at d n
  }, {
    exact analytic_on.differentiable_on,
  },
end

-- A function is analytic at z iff it's differentiable on a surrounding open set
lemma analytic_at_iff_eventually_differentiable_at {f : ℂ → E} {c : ℂ}
    : analytic_at ℂ f c ↔ ∀ᶠ z in 𝓝 c, differentiable_at ℂ f z := begin
  constructor, {
    intros fa, rcases fa.ball with ⟨r,rp,fa⟩,
    exact fa.differentiable_on.eventually_differentiable_at (metric.ball_mem_nhds _ rp),
  }, {
    intros d, rcases metric.eventually_nhds_iff.mp d with ⟨r,rp,d⟩,
    have dr : differentiable_on ℂ f (ball c r), {
      intros z zs, simp only [metric.mem_ball] at zs, exact (d zs).differentiable_within_at,
    },
    rw differentiable_iff_analytic is_open_ball at dr,
    exact dr _ (metric.mem_ball_self rp), apply_instance,
  },
end

-- f : ℂ × ℂ → E is differentiable iff it is analytic
lemma differentiable_iff_analytic2 {E : Type} {f : ℂ × ℂ → E} {s : set (ℂ × ℂ)}
    [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    (o : is_open s) : differentiable_on ℂ f s ↔ analytic_on ℂ f s := begin
  constructor, {
    intro d, apply osgood o d.continuous_on, {
      intros z0 z1 zs,
      rcases metric.is_open_iff.mp o (z0,z1) zs with ⟨r,rp,rs⟩,
      have d0 : differentiable_on ℂ (λ z0, f (z0,z1)) (ball z0 r), {
        apply differentiable_on.comp d,
        exact differentiable_on.prod differentiable_on_id (differentiable_on_const _),
        intros z0 z0s, apply rs, simp at ⊢ z0s, assumption
      },
      exact (differentiable_iff_analytic is_open_ball).mp d0 z0 (metric.mem_ball_self rp)
    }, {
      intros z0 z1 zs,
      rcases metric.is_open_iff.mp o (z0,z1) zs with ⟨r,rp,rs⟩,
      have d1 : differentiable_on ℂ (λ z1, f (z0,z1)) (ball z1 r), {
        apply differentiable_on.comp d,
        exact differentiable_on.prod (differentiable_on_const _) differentiable_on_id ,
        intros z1 z1s, apply rs, simp at ⊢ z1s, assumption
      },
      exact (differentiable_iff_analytic is_open_ball).mp d1 z1 (metric.mem_ball_self rp)
    }
  }, {
    exact λ a, a.differentiable_on,
  },
end

-- f : ℂ × ℂ → E is cont_diff_at iff it is analytic
lemma cont_diff_at_iff_analytic_at2 {E : Type} {f : ℂ × ℂ → E} {x : ℂ × ℂ}
    [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    {n : ℕ∞} (n1 : 1 ≤ n) : cont_diff_at ℂ n f x ↔ analytic_at ℂ f x := begin
  constructor, {
    intro d, rcases d.cont_diff_on n1 with ⟨u,un,um,d⟩,
    simp [set.insert_eq_self.mpr (set.mem_univ _), nhds_within_univ] at un um,
    rcases mem_nhds_iff.mp un with ⟨v,uv,vo,vx⟩,
    refine (differentiable_iff_analytic2 vo).mp _ _ vx,
    exact (d.mono uv).differentiable_on (by norm_num),
  }, {
    intro a, exact a.cont_diff_at.of_le le_top,
  },
end  

-- z^n is entire
theorem analytic_on.monomial (n : ℕ) : analytic_on ℂ (λ z : ℂ, z^n) univ := begin
  rw ←differentiable.entire, apply differentiable.pow differentiable_id,
end
theorem analytic_at.monomial (n : ℕ) {z : ℂ} : analytic_at ℂ (λ z : ℂ, z^n) z := analytic_on.monomial n z (set.mem_univ _)

-- * is analytic
lemma analytic_on_mul : analytic_on ℂ (λ p : ℂ × ℂ, p.1 * p.2) univ :=
  (differentiable_iff_analytic2 is_open_univ).mp (differentiable_on_fst.mul differentiable_on_snd)

-- f * g is analytic
theorem analytic_at.mul {f g : E → ℂ} {x : E} (fa : analytic_at ℂ f x) (ga : analytic_at ℂ g x)
    : analytic_at ℂ (λ x, f x * g x) x := begin
  have e : (λ x, f x * g x) = (λ p : ℂ × ℂ, p.1 * p.2) ∘ (λ x, (f x, g x)) := rfl,
  rw e, exact (analytic_on_mul _ (set.mem_univ _)).comp (fa.prod ga),
end
theorem analytic_on.mul {f g : E → ℂ} {s : set E} (fa : analytic_on ℂ f s) (ga : analytic_on ℂ g s)
    : analytic_on ℂ (λ x, f x * g x) s := λ x m, (fa x m).mul (ga x m)

-- ⁻¹ is analytic away from zero
lemma analytic_on_inv : analytic_on ℂ (λ z, z⁻¹) {z : ℂ | z ≠ 0} :=
  (differentiable_iff_analytic is_open_ne).mp differentiable_on_inv

-- (f x)⁻¹ is analytic away from f x = 0
lemma analytic_at.inv {f : E → ℂ} {x : E} (fa : analytic_at ℂ f x) (f0 : f x ≠ 0) : analytic_at ℂ (λ x, (f x)⁻¹) x := begin
  refine (analytic_on_inv _ _).comp fa, simp only [f0, ne.def, set.mem_set_of_eq, not_false_iff],
end
lemma analytic_on.inv {f : E → ℂ} {s : set E} (fa : analytic_on ℂ f s) (f0 : ∀ x, x ∈ s → f x ≠ 0)
    : analytic_on ℂ (λ x, (f x)⁻¹) s:= λ x m, (fa x m).inv (f0 x m) 

-- f x / g x is analytic away from g x = 0
theorem analytic_at.div {f g : E → ℂ} {x : E} (fa : analytic_at ℂ f x) (ga : analytic_at ℂ g x) (g0 : g x ≠ 0)
    : analytic_at ℂ (λ x, f x / g x) x := begin simp_rw div_eq_mul_inv, exact fa.mul (ga.inv g0) end
theorem analytic_on.div {f g : E → ℂ} {s : set E} (fa : analytic_on ℂ f s) (ga : analytic_on ℂ g s) (g0 : ∀ x, x ∈ s → g x ≠ 0)
    : analytic_on ℂ (λ x, f x / g x) s := λ x m, (fa x m).div (ga x m) (g0 x m)

-- (f x)^n is analytic
theorem analytic_at.pow {f : E → ℂ} {x : E} (fa : analytic_at ℂ f x) {n : ℕ} : analytic_at ℂ (λ x, (f x)^n) x := begin
  induction n with n h, simp only [pow_zero], exact analytic_at_const, simp_rw pow_succ, exact fa.mul h,
end

-- Finite products of analytic functions are analytic
theorem prod_analytic {f : ℕ → E → ℂ} {s : set E} (h : ∀ n, analytic_on ℂ (f n) s) (N : finset ℕ)
    : analytic_on ℂ (λ z, N.prod (λ n, f n z)) s := begin
  induction N using finset.induction with a B aB hB, {
    simp, intros z zs, exact analytic_at_const,
  }, {
    simp_rw finset.prod_insert aB, exact (h a).mul hB,
  },
end

-- exp is entire
theorem analytic_on.exp : analytic_on ℂ exp univ := begin rw ←differentiable.entire, simp end
theorem analytic_at.exp {z : ℂ} : analytic_at ℂ exp z := analytic_on.exp z (set.mem_univ _)

-- log is analytic away from negative reals
theorem analytic_at_log {c : ℂ} (a : c.re > 0 ∨ c.im ≠ 0) : analytic_at ℂ log c := begin
  rw analytic_at_iff_eventually_differentiable_at,
  cases a, {
    have ae : ∀ᶠ z : ℂ in 𝓝 c, z.re > 0 :=
      continuous_at.eventually_lt continuous_at_const complex.continuous_re.continuous_at a,
    refine ae.mp (filter.eventually_of_forall _), intros z zr, exact differentiable_at_id.clog (or.inl zr),
  }, {
    have ae : ∀ᶠ z : ℂ in 𝓝 c, z.im ≠ 0 := complex.continuous_im.continuous_at.eventually_ne a,
    refine ae.mp (filter.eventually_of_forall _), intros z zr, exact differentiable_at_id.clog (or.inr zr),
  },
end

-- log is analytic away from negative reals
theorem analytic_at.log {f : E → ℂ} {c : E} (fa : analytic_at ℂ f c) (a : (f c).re > 0 ∨ (f c).im ≠ 0)
    : analytic_at ℂ (λ z, log (f z)) c := (analytic_at_log a).comp fa

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

-- f z ^ g z is analytic if f z is not a nonpositive real
theorem analytic_at.cpow {f g : E → ℂ} {c : E} (fa : analytic_at ℂ f c) (ga : analytic_at ℂ g c)
    (a : (f c).re > 0 ∨ (f c).im ≠ 0) : analytic_at ℂ (λ z, f z ^ g z) c := begin
  have fc : f c ≠ 0, {
    contrapose a, simp only [not_not] at a,
    simp only [a, complex.zero_re, gt_iff_lt, lt_self_iff_false, complex.zero_im, ne.def, eq_self_iff_true,
      not_true, or_self, not_false_iff],
  },
  have e : (λ z, f z ^ g z) =ᶠ[𝓝 c] (λ z, exp (log (f z) * g z)), {
    refine (fa.continuous_at.eventually_ne fc).mp (filter.eventually_of_forall _),
    intros z fz, simp only [fz, complex.cpow_def, if_false],
  },
  rw analytic_at_congr e, exact analytic_at.exp.comp ((fa.log a).mul ga),
end
