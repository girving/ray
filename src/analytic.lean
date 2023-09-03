-- Basics about analytic functions (general field case)

import analysis.analytic.basic
import analysis.analytic.composition
import analysis.analytic.linear
import analysis.analytic.isolated_zeros
import analysis.calculus.fderiv_analytic
import analysis.calculus.formal_multilinear_series
import analysis.complex.cauchy_integral
import analysis.normed_space.operator_norm
import data.complex.basic
import data.finset.basic
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import data.stream.defs
import topology.basic

import bounds
import multilinear
import tactics
import topology

open complex (abs exp I log)
open filter (at_top eventually_of_forall)
open function (curry uncurry)
open metric (ball closed_ball sphere is_open_ball)
open linear_order (min)
open set (univ)
open_locale real nnreal ennreal topology
noncomputable theory

variables {𝕜 : Type} [nontrivially_normed_field 𝕜]
variables {E : Type} [normed_add_comm_group E] [normed_space 𝕜 E] [complete_space E]
variables {F : Type} [normed_add_comm_group F] [normed_space 𝕜 F] [complete_space F]
variables {H : Type} [normed_add_comm_group H] [normed_space 𝕜 H] [complete_space H]
variables {G : Type} [normed_add_comm_group G] [normed_space 𝕜 G] [complete_space G]

-- Infinite radius of convergence implies entire
lemma radius_inf_to_entire {f : E → F} (p : formal_multilinear_series 𝕜 E F) (z : E)
    : has_fpower_series_on_ball f p z ∞ → analytic_on 𝕜 f univ := begin
  intros h w wu,
  refine has_fpower_series_on_ball.analytic_at_of_mem h _,
  rw emetric.mem_ball, exact edist_lt_top w z,
end

-- Analytic functions have derivatives
lemma analytic_at.has_deriv_at {f : 𝕜 → E} {z : 𝕜}
    : analytic_at 𝕜 f z → has_deriv_at f (deriv f z) z := begin
  intro a,
  have dwa : differentiable_within_at 𝕜 f univ z := analytic_at.differentiable_within_at a,
  refine (dwa.differentiable_at _).has_deriv_at,
  exact is_open.mem_nhds is_open_univ (set.mem_univ z),
end

-- id is entire
theorem analytic_at_id {x : E} : analytic_at 𝕜 (λ x : E, x) x := (continuous_linear_map.id 𝕜 E).analytic_at x
theorem analytic_on_id {s : set E} : analytic_on 𝕜 (λ x : E, x) s := λ _ _, analytic_at_id

-- Finite sums of analytic functions are analytic
theorem analytic_at.sum {f : ℕ → E → F} {c : E}
    (h : ∀ n, analytic_at 𝕜 (f n) c) (N : finset ℕ) : analytic_at 𝕜 (λ z, N.sum (λ n, f n z)) c := begin
  induction N using finset.induction with a B aB hB, {
    simp only [finset.sum_empty], exact analytic_at_const,
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

-- Analytic at a point means analytic locally
theorem analytic_at.eventually {f : E → F} {z : E} (fa : analytic_at 𝕜 f z)
    : ∀ᶠ w in 𝓝 z, analytic_at 𝕜 f w :=
  (is_open_analytic_at 𝕜 f).eventually_mem fa

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

-- fst and snd are analytic
lemma analytic_at_fst {p : E × F} : analytic_at 𝕜 (λ p : E × F, p.fst) p := (continuous_linear_map.fst 𝕜 E F).analytic_at p
lemma analytic_at_snd {p : E × F} : analytic_at 𝕜 (λ p : E × F, p.snd) p := (continuous_linear_map.snd 𝕜 E F).analytic_at p
lemma analytic_on_fst {s : set (E × F)} : analytic_on 𝕜 (λ p : E × F, p.fst) s := λ p _, analytic_at_fst
lemma analytic_on_snd {s : set (E × F)} : analytic_on 𝕜 (λ p : E × F, p.snd) s := λ p _, analytic_at_snd

-- Products of analytic functions are analytic
lemma analytic_at.prod {f : E → F} {g : E → G} {x : E} (fa : analytic_at 𝕜 f x) (ga : analytic_at 𝕜 g x)
    : analytic_at 𝕜 (λ x, (f x, g x)) x := begin
  rcases fa with ⟨p,pr,fp⟩,
  rcases ga with ⟨q,qr,gq⟩,
  set pq : formal_multilinear_series 𝕜 E (F × G) := λ n, (p n).prod (q n),
  have pqr : min pr qr ≤ pq.radius, {
    apply ennreal.le_of_forall_nnreal_lt, intros r rr,
    rcases p.norm_mul_pow_le_of_lt_radius (lt_of_lt_of_le rr (trans (min_le_left pr qr) fp.r_le)) with ⟨pc,pcp,ph⟩,
    rcases q.norm_mul_pow_le_of_lt_radius (lt_of_lt_of_le rr (trans (min_le_right pr qr) gq.r_le)) with ⟨qc,qcp,qh⟩,
    apply pq.le_radius_of_bound (max pc qc), intro n,
    calc ‖pq n‖ * ↑r^n = (max ‖p n‖ ‖q n‖) * ↑r^n : by simp only [continuous_multilinear_map.op_norm_prod]
    ... = max (‖p n‖ * ↑r^n) (‖q n‖ * ↑r^n) : max_mul_of_nonneg _ _ (by bound)
    ... ≤ max pc qc : by bound [ph n, qh n, max_le_max],
  },
  use [pq, min pr qr],
  exact {
    r_le := pqr,
    r_pos := by bound [fp.r_pos, gq.r_pos],
    has_sum := begin
      intros y yr, apply has_sum.prod_mk,
      exact fp.has_sum (emetric.ball_subset_ball (by bound) yr),
      exact gq.has_sum (emetric.ball_subset_ball (by bound) yr),
    end,
  },
end

-- Products of analytic functions are analytic
theorem analytic_on.prod {f : E → F} {g : E → G} {s : set E} (fa : analytic_on 𝕜 f s) (ga : analytic_on 𝕜 g s)
    : analytic_on 𝕜 (λ z, (f z,g z)) s := λ _ m, (fa _ m).prod (ga _ m)

lemma analytic_on.comp {f : F → G} {g : E → F} {s : set F} {t : set E} (fa : analytic_on 𝕜 f s) (ga : analytic_on 𝕜 g t)
    (m : set.maps_to g t s) : analytic_on 𝕜 (λ x, f (g x)) t := λ x xs, (fa _ (m xs)).comp (ga _ xs)

-- analytic_at.comp for a curried function
lemma analytic_at.curry_comp {h : F → G → H} {f : E → F} {g : E → G} {x : E}
    (ha : analytic_at 𝕜 (uncurry h) (f x, g x)) (fa : analytic_at 𝕜 f x) (ga : analytic_at 𝕜 g x)
    : analytic_at 𝕜 (λ x, h (f x) (g x)) x := begin
  have e : (λ x, h (f x) (g x)) = uncurry h ∘ (λ x, (f x, g x)) := rfl,
  rw e, exact analytic_at.comp ha (fa.prod ga),
end

-- analytic_on.comp for a curried function
lemma analytic_on.curry_comp {h : F → G → H} {f : E → F} {g : E → G} {s : set (F × G)} {t : set E}
    (ha : analytic_on 𝕜 (uncurry h) s) (fa : analytic_on 𝕜 f t) (ga : analytic_on 𝕜 g t) (m : ∀ x, x ∈ t → (f x, g x) ∈ s)
    : analytic_on 𝕜 (λ x, h (f x) (g x)) t :=
  λ x xt, (ha _ (m _ xt)).curry_comp (fa _ xt) (ga _ xt)

-- Curried analytic functions are analytic in each component
lemma analytic_at.in1 {f : E → F → G} {x : E} {y : F} (fa : analytic_at 𝕜 (uncurry f) (x,y)) : analytic_at 𝕜 (λ x, f x y) x :=
  analytic_at.curry_comp fa analytic_at_id analytic_at_const
lemma analytic_at.in2 {f : E → F → G} {x : E} {y : F} (fa : analytic_at 𝕜 (uncurry f) (x,y)) : analytic_at 𝕜 (λ y, f x y) y :=
  analytic_at.curry_comp fa analytic_at_const analytic_at_id
lemma analytic_on.in1 {f : E → F → G} {s : set (E × F)} {y : F} (fa : analytic_on 𝕜 (uncurry f) s)
    : analytic_on 𝕜 (λ x, f x y) {x | (x,y) ∈ s} := λ x m, (fa (x,y) m).in1
lemma analytic_on.in2 {f : E → F → G} {x : E} {s : set (E × F)} (fa : analytic_on 𝕜 (uncurry f) s)
    : analytic_on 𝕜 (λ y, f x y) {y | (x,y) ∈ s} := λ y m, (fa (x,y) m).in2 

-- Analytic everywhere means continuous
lemma analytic_on.continuous {f : E → F} (fa : analytic_on 𝕜 f univ) : continuous f := begin
  rw continuous_iff_continuous_on_univ, exact fa.continuous_on,
end

-- Order of a zero at a point.
-- We define this in terms of the function alone so that expressions involving order can depend only on f.
def order_at (f : 𝕜 → E) (c : 𝕜) : ℕ :=
  @dite _ (analytic_at 𝕜 f c) (classical.dec _) (λ p, (classical.some p).order) (λ _, 0)

-- Order is unique, since power series are
lemma has_fpower_series_at.order_at_unique {f : 𝕜 → E} {p : formal_multilinear_series 𝕜 𝕜 E} {c : 𝕜}
    (fp : has_fpower_series_at f p c) : order_at f c = p.order := begin
  have fa : analytic_at 𝕜 f c := ⟨p,fp⟩,
  have pr := exists.intro p fp,
  simp only [order_at, fa, dif_pos],
  have s := classical.some_spec pr,
  generalize hq : classical.some pr = q,
  simp_rw hq at s,
  rw fp.eq_formal_multilinear_series s,
end

-- order_at is zero for nonzeros
lemma order_at_eq_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) : order_at f c = 0 := begin
  by_cases fp : analytic_at 𝕜 f c, {
    rcases fp with ⟨p,fp⟩, rw fp.order_at_unique, rw ←fp.coeff_zero 1 at f0,
    rw formal_multilinear_series.order_eq_zero_iff', right,
    contrapose f0, simp only [not_not] at f0,
    simp only [f0, continuous_multilinear_map.zero_apply, ne.def, eq_self_iff_true, not_true, not_false_iff],
  }, {
    simp [order_at, fp],
  },
end

-- order_at = 0 means either f = 0 or f c ≠ 0
lemma order_at_eq_zero_iff {f : 𝕜 → E} {c : 𝕜} (fa : analytic_at 𝕜 f c)
    : order_at f c = 0 ↔ f =ᶠ[𝓝 c] 0 ∨ f c ≠ 0 := begin
  rcases fa with ⟨p,fp⟩,
  simp only [fp.order_at_unique, ←fp.coeff_zero (λ _, 0), formal_multilinear_series.order_eq_zero_iff'],
  nth_rewrite 1 ←norm_ne_zero_iff, rw continuous_multilinear_map.fin0_apply_norm, rw norm_ne_zero_iff,
  apply or_congr_left, intro h, exact fp.locally_zero_iff.symm,
end

-- order_at = 1 → deriv ≠ 0
lemma deriv_ne_zero_of_order_at_eq_one {f : 𝕜 → E} {c : 𝕜} (o : order_at f c = 1) : deriv f c ≠ 0 := begin
  by_cases fa : analytic_at 𝕜 f c, {
    rcases fa with ⟨p,fp⟩,
    rw fp.order_at_unique at o,
    have o0 : p.order ≠ 0, { rw o, exact one_ne_zero },
    have p0 := formal_multilinear_series.apply_order_ne_zero' o0,
    rw o at p0,
    simpa only [fp.deriv, formal_multilinear_series.apply_eq_pow_smul_coeff, one_pow, one_smul,
      formal_multilinear_series.coeff_eq_zero, ne.def],
  }, {
    simp only [order_at, fa] at o, rw dif_neg at o, norm_num at o, exact not_false,
  },
end

-- The leading nonzero coefficient of f's power series
def leading_coeff (f : 𝕜 → E) (c : 𝕜) : E := function.swap dslope c^[order_at f c] f c

-- leading_coeff for nonzeros
lemma leading_coeff_of_ne_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) : leading_coeff f c = f c :=
  by simp only [leading_coeff, order_at_eq_zero f0, function.iterate_zero_apply]

-- f is approximated by its leading monomial
lemma analytic_at.leading_approx {f : 𝕜 → E} {c : 𝕜} (fa : analytic_at 𝕜 f c)
    : (λ z, f z - (z - c)^(order_at f c) • leading_coeff f c) =o[𝓝 c] (λ z, (z-c)^(order_at f c)) := begin
  rcases fa with ⟨p,fp⟩,
  generalize ha : leading_coeff f c = a,
  generalize hd : order_at f c = d,
  have ha' : (function.swap dslope c^[d] f c = a) := by rw [←ha, ←hd, leading_coeff],
  have e := fp.eq_pow_order_mul_iterate_dslope,
  simp_rw [←fp.order_at_unique, hd] at e,
  apply asymptotics.is_o.of_is_O_with, intros k kp,
  rw asymptotics.is_O_with_iff,
  apply e.mp,
  have dc : continuous_at (function.swap dslope c^[d] f) c :=
    (fp.has_fpower_series_iterate_dslope_fslope d).analytic_at.continuous_at,
  rcases metric.continuous_at_iff.mp dc k kp with ⟨r,rp,rh⟩,
  rw ha' at rh,
  generalize hg : function.swap dslope c^[d] f = g, rw hg at rh,
  rw metric.eventually_nhds_iff, use [r, rp], intros y yr fe, rw fe,
  specialize rh yr, rw dist_eq_norm at rh,
  calc ‖(y-c)^d • g y - (y-c)^d • a‖ = ‖(y-c)^d‖ * ‖(g y - a)‖ : by rw [←smul_sub, norm_smul]
  ... ≤ ‖(y-c)^d‖ * k : by bound
  ... = k * ‖(y-c) ^ d‖ : by rw mul_comm,
end

-- order > 0 means f has a zero
lemma analytic_at.zero_of_order_pos {f : 𝕜 → E} {c : 𝕜} (fa : analytic_at 𝕜 f c) (p : order_at f c > 0)
    : f c = 0 := begin
  have a := (asymptotics.is_O_with_iff.mp (fa.leading_approx.forall_is_O_with zero_lt_one)).self,
  simp only [(pow_eq_zero_iff p).mpr, sub_self, zero_smul, sub_zero, norm_zero, mul_zero, norm_le_zero_iff] at a,
  exact a,
end

-- The power series of (z - c) • f z
def formal_multilinear_series.unshift' (p : formal_multilinear_series 𝕜 𝕜 E) (c : E) : formal_multilinear_series 𝕜 𝕜 E :=
  ((continuous_linear_map.smul_rightL 𝕜 𝕜 E (continuous_linear_map.id 𝕜 𝕜)).comp_formal_multilinear_series p).unshift c
@[simp] def formal_multilinear_series.unshift_coeff_zero (p : formal_multilinear_series 𝕜 𝕜 E) (c : E)
    : (p.unshift' c).coeff 0 = c :=
  by simp only [formal_multilinear_series.coeff, formal_multilinear_series.unshift', formal_multilinear_series.unshift,
    continuous_multilinear_curry_fin0_symm_apply]
@[simp] def formal_multilinear_series.unshift_coeff_succ (p : formal_multilinear_series 𝕜 𝕜 E) (c : E) (n : ℕ)
    : (p.unshift' c).coeff (n+1) = p.coeff n := begin
  simp only [formal_multilinear_series.coeff, formal_multilinear_series.unshift', formal_multilinear_series.unshift,
    continuous_linear_map.comp_formal_multilinear_series_apply, linear_isometry_equiv.norm_map],
  simp [continuous_linear_map.smul_rightL, finset.univ, fintype.elems, fin.init],
end

-- The power series of (z - c)^n • f z
def formal_multilinear_series.unshift_iter (p : formal_multilinear_series 𝕜 𝕜 E) (n : ℕ) :=
  (λ p, formal_multilinear_series.unshift' p (0 : E))^[n] p
def formal_multilinear_series.unshift_iter_coeff (p : formal_multilinear_series 𝕜 𝕜 E) (n : ℕ) (i : ℕ) :
    (p.unshift_iter n).coeff i = if i < n then 0 else p.coeff (i - n) := begin
  revert i, induction n with n h, {
    simp only [formal_multilinear_series.unshift_iter, function.iterate_zero, id.def, not_lt_zero', tsub_zero, if_false,
      eq_self_iff_true, forall_const],
  }, {
    simp_rw formal_multilinear_series.unshift_iter at h,
    simp only [formal_multilinear_series.unshift_iter, function.iterate_succ', function.comp],
    generalize hq : (λ (p : formal_multilinear_series 𝕜 𝕜 E), p.unshift' 0)^[n] p = q, rw hq at h, clear hq,
    intro i, induction i with i hi, {
      simp only [formal_multilinear_series.unshift_coeff_zero, nat.succ_pos', if_true],
    }, {
      simp only [nat.succ_lt_succ_iff, h i, formal_multilinear_series.unshift_coeff_succ, nat.succ_sub_succ_eq_sub],
    },
  },
end

-- unshift' respects norm and radius norm
def formal_multilinear_series.unshift_norm' (p : formal_multilinear_series 𝕜 𝕜 E) (c : E) (n : ℕ)
    : ‖p.unshift' c (n+1)‖ = ‖p n‖ :=
  by simp only [formal_multilinear_series.norm_apply_eq_norm_coef, formal_multilinear_series.unshift_coeff_succ]
def formal_multilinear_series.unshift_radius' (p : formal_multilinear_series 𝕜 𝕜 E) {c : E} : (p.unshift' c).radius = p.radius := begin
  simp_rw formal_multilinear_series.radius,
  apply le_antisymm, {
    refine supr₂_le _, intros r k, refine supr_le _, intro h, refine trans _ (le_supr₂ r (k*↑r⁻¹)),
    have h := λ n, mul_le_mul_of_nonneg_right (h (n+1)) (nnreal.coe_nonneg r⁻¹),
    by_cases r0 : r = 0, { simp only [r0, ennreal.coe_zero, ennreal.supr_zero_eq_zero, le_zero_iff] },
    simp only [pow_succ', ←mul_assoc _ _ ↑r, mul_assoc _ ↑r _, mul_inv_cancel (nnreal.coe_ne_zero.mpr r0),
      nonneg.coe_inv, mul_one, p.unshift_norm'] at h,
    exact le_supr _ h,
  }, {
    refine supr₂_le _, intros r k, refine supr_le _, intro h, refine trans _ (le_supr₂ r (max ‖c‖ (k*↑r))),
    have h' : ∀ n, ‖p.unshift' c n‖ * ↑r^n ≤ (max ‖c‖ (k*↑r)), {
      intro n, induction n with n i,
      simp only [formal_multilinear_series.unshift_coeff_zero, formal_multilinear_series.norm_apply_eq_norm_coef, pow_zero,
        mul_one, le_max_iff, le_refl, true_or],
      simp only [formal_multilinear_series.norm_apply_eq_norm_coef] at h,
      simp only [formal_multilinear_series.unshift_coeff_succ, pow_succ', ←mul_assoc,
        formal_multilinear_series.norm_apply_eq_norm_coef, le_max_iff],
      right, exact mul_le_mul_of_nonneg_right (h n) (nnreal.coe_nonneg _),
    },
    exact le_supr _ h',
  },
end

-- The power series of (z - c) • f z is the unshifted power series
lemma has_fpower_series_on_ball.unshift {f : 𝕜 → E} {p : formal_multilinear_series 𝕜 𝕜 E} {c : 𝕜} {r : ennreal}
    (fp : has_fpower_series_on_ball f p c r) : has_fpower_series_on_ball (λ z, (z - c) • f z) (p.unshift' 0) c r := {
  r_le := trans fp.r_le (ge_of_eq p.unshift_radius'),
  r_pos := fp.r_pos,
  has_sum := begin
    intros y yr, simp only [formal_multilinear_series.apply_eq_pow_smul_coeff, add_sub_cancel'],
    generalize hs : (λ n, y^n • (p.unshift' 0).coeff n) = s,
    have s0 : y • f (c + y) = y • f (c + y) + (finset.range 1).sum s :=
      by simp only [←hs, p.unshift_coeff_zero, finset.range_one, finset.sum_singleton, smul_zero, add_zero],
    rw [s0, ←has_sum_nat_add_iff, ←hs],
    simp only [p.unshift_coeff_succ, pow_succ, ←smul_smul], apply has_sum.const_smul,
    have h := fp.has_sum yr, simp only [formal_multilinear_series.apply_eq_pow_smul_coeff] at h, exact h,
  end,
}
lemma has_fpower_series_at.unshift {f : 𝕜 → E} {p : formal_multilinear_series 𝕜 𝕜 E} {c : 𝕜}
    (fp : has_fpower_series_at f p c) : has_fpower_series_at (λ z, (z - c) • f z) (p.unshift' 0) c := begin
  rcases fp with ⟨r,fa⟩, use [r, fa.unshift],
end
lemma has_fpower_series_at.unshift_iter {f : 𝕜 → E} {p : formal_multilinear_series 𝕜 𝕜 E} {c : 𝕜} {n : ℕ}
    (fp : has_fpower_series_at f p c) : has_fpower_series_at (λ z, (z - c)^n • f z) (p.unshift_iter n) c := begin
  induction n with n h, {
    simp only [nat.nat_zero_eq_zero, pow_zero, one_smul], exact fp,
  }, {
    simp only [pow_succ, ←smul_smul, formal_multilinear_series.unshift_iter, function.iterate_succ', function.comp],
    exact h.unshift,
  },
end

-- Power series terms are zero iff their coeffs are zero
lemma formal_multilinear_series.zero_iff_coeff_zero (p : formal_multilinear_series 𝕜 𝕜 E) {n : ℕ}
    : p n = 0 ↔ p.coeff n = 0 := begin
  constructor, {
    intro h, rw [formal_multilinear_series.coeff, h], simp only [continuous_multilinear_map.zero_apply],
  }, {
    intro h, rw [←p.mk_pi_field_coeff_eq n, h], simp only [continuous_multilinear_map.mk_pi_field_zero],
  },
end
lemma formal_multilinear_series.ne_zero_iff_coeff_ne_zero (p : formal_multilinear_series 𝕜 𝕜 E) {n : ℕ}
    : p n ≠ 0 ↔ p.coeff n ≠ 0 := begin
  constructor, {
    intro h, contrapose h, simp only [not_not] at ⊢ h, exact p.zero_iff_coeff_zero.mpr h,
  }, {
    intro h, contrapose h, simp only [not_not] at ⊢ h, exact p.zero_iff_coeff_zero.mp h,
  },
end

-- Power series coefficients of (z - n)^n • f z are what you expect
lemma analytic_at.monomial_mul_order_at {f : 𝕜 → E} {c : 𝕜} (fa : analytic_at 𝕜 f c) (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ)
    : order_at (λ z, (z - c)^n • f z) c = n + order_at f c := begin
  rcases fa with ⟨p,fp⟩,
  have pnz : p ≠ 0, {
    contrapose fnz, simp at fnz, simpa only [has_fpower_series_at.locally_zero_iff fp, filter.not_frequently, not_not],
  },
  have pe : ∃ i, p i ≠ 0, { rw function.ne_iff at pnz, exact pnz },
  have pne : ∃ i, (p.unshift_iter n) i ≠ 0, {
    rcases pe with ⟨i,pi⟩, use n+i,
    simp only [formal_multilinear_series.ne_zero_iff_coeff_ne_zero] at ⊢ pi,
    simpa only [p.unshift_iter_coeff, add_lt_iff_neg_left, add_tsub_cancel_left],
  },
  have fq : has_fpower_series_at (λ z, (z - c)^n • f z) (p.unshift_iter n) c := fp.unshift_iter,
  rw [fp.order_at_unique, fq.order_at_unique],
  rw @formal_multilinear_series.order_eq_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (classical.dec_pred _) pe,
  rw @formal_multilinear_series.order_eq_find _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (classical.dec_pred _) pne,
  rw nat.find_eq_iff, constructor, {
    have s := @nat.find_spec _ (classical.dec_pred _) pe,
    simp only [p.zero_iff_coeff_zero, ne.def] at s,
    simp only [p.unshift_iter_coeff, formal_multilinear_series.zero_iff_coeff_zero, s, ne.def, add_lt_iff_neg_left, not_lt_zero',
      add_tsub_cancel_left, if_false, not_false_iff],
  }, {
    intros m mp, simp [formal_multilinear_series.zero_iff_coeff_zero, p.unshift_iter_coeff], intro mn,
    generalize ha : m - n = a, have hm : m = n + a := by rw [←ha, add_comm, nat.sub_add_cancel mn],
    simp only [hm, add_lt_add_iff_left, nat.lt_find_iff, not_not] at mp,
    specialize mp a (le_refl _), rwa ←formal_multilinear_series.zero_iff_coeff_zero,
  },
end
lemma analytic_at.monomial_mul_leading_coeff {f : 𝕜 → E} {c : 𝕜} (fa : analytic_at 𝕜 f c) (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ)
    : leading_coeff (λ z, (z - c)^n • f z) c = leading_coeff f c := begin
  simp [leading_coeff, fa.monomial_mul_order_at fnz n], generalize ha : order_at f c = a,
  induction n with n h, simp only [zero_add, pow_zero, one_smul],
  simp [pow_succ, ←smul_smul, nat.succ_add],
  generalize hg : (λ z, (z - c)^n • f z) = g,
  have hg' : ∀ z, (z - c)^n • f z = g z, { rw ←hg, simp only [eq_self_iff_true, forall_const] },
  simp_rw hg' at ⊢ h,
  have e : function.swap dslope c (λ z, (z - c) • g z) = g, {
    simp only [function.swap, (@dslope_sub_smul) _ _ _ _ _ (classical.dec_eq _),
      function.update_eq_self_iff, sub_self],
    rw deriv_smul, simp only [sub_self, zero_smul, deriv_sub, differentiable_at_id', differentiable_at_const, deriv_id'',
      deriv_const', sub_zero, one_smul, zero_add],
    exact differentiable_at_id.sub (differentiable_at_const _),
    rw ←hg, exact ((differentiable_at_id.sub (differentiable_at_const _)).pow _).smul fa.differentiable_at,
  },
  rw [e, h],
end

-- analytic_at version of analytic_on.cont_diff_on
lemma analytic_at.cont_diff_at {f : E → F} {c : E} (fa : analytic_at 𝕜 f c) : cont_diff_at 𝕜 ⊤ f c := begin
  rcases fa.ball with ⟨r,rp,fa⟩,
  have m : c ∈ ball c r := metric.mem_ball_self rp, 
  exact (fa.cont_diff_on _ m).cont_diff_at (is_open_ball.mem_nhds m),
end

-- fderiv and deriv are analytic_at
lemma analytic_at.fderiv {f : E → F} {c : E} (fa : analytic_at 𝕜 f c) : analytic_at 𝕜 (fderiv 𝕜 f) c := begin
  rcases fa.ball with ⟨r,rp,fa⟩, exact fa.fderiv _ (metric.mem_ball_self rp),
end
lemma analytic_at.deriv {f : 𝕜 → 𝕜} {c : 𝕜} (fa : analytic_at 𝕜 f c) [complete_space 𝕜]
    : analytic_at 𝕜 (λ x, deriv f x) c := begin
  simp only [←fderiv_deriv],
  have a1 : ∀ g, analytic_at 𝕜 (λ g : 𝕜 →L[𝕜] 𝕜, continuous_linear_map.apply 𝕜 𝕜 1 g) g :=
    λ g, continuous_linear_map.analytic_at _ _,
  refine (a1 _).comp fa.fderiv,
end

-- deriv in the second variable is analytic
lemma analytic_at.deriv2 [complete_space 𝕜] {f : E → 𝕜 → 𝕜} {c : E × 𝕜} (fa : analytic_at 𝕜 (uncurry f) c)
    : analytic_at 𝕜 (λ x : E × 𝕜, deriv (f x.1) x.2) c := begin
  set p : (E × 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜 := continuous_linear_map.apply 𝕜 𝕜 (0,1),
  have e : ∀ᶠ x : E × 𝕜 in 𝓝 c, deriv (f x.1) x.2 = p (fderiv 𝕜 (uncurry f) x), {
    refine fa.eventually.mp (eventually_of_forall _),
    rintros ⟨x,y⟩ fa, simp only [←fderiv_deriv],
    have e : f x = uncurry f ∘ (λ y, (x,y)) := rfl, 
    rw e, rw fderiv.comp,
    have pd : fderiv 𝕜 (λ y : 𝕜, (x, y)) y = continuous_linear_map.inr 𝕜 E 𝕜, {
      apply has_fderiv_at.fderiv, apply has_fderiv_at_prod_mk_right,
    },
    simp only [pd, continuous_linear_map.comp_apply, continuous_linear_map.inr_apply,
      continuous_linear_map.apply_apply],
    exact fa.differentiable_at, exact (differentiable_at_const _).prod differentiable_at_id,
  },
  rw analytic_at_congr e,
  exact (p.analytic_at _).comp fa.fderiv,
end

-- Scaling does the expected thing to power series
lemma has_fpower_series_at.const_smul {f : 𝕜 → E} {c a : 𝕜} {p : formal_multilinear_series 𝕜 𝕜 E}
    (fp : has_fpower_series_at f p c) : has_fpower_series_at (λ z, a • f z) (λ n, a • p n) c := begin
  rw has_fpower_series_at_iff at fp ⊢, refine fp.mp (eventually_of_forall (λ z h, _)),
  simp only [formal_multilinear_series.coeff, continuous_multilinear_map.smul_apply, smul_comm _ a],
  exact h.const_smul a,
end

-- Nonzero scaling does not change analyticitiy
lemma analytic_at_iff_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0)
    : analytic_at 𝕜 (λ z, a • f z) c ↔ analytic_at 𝕜 f c := begin
  constructor, {
    rintros ⟨p,fp⟩,
    have e : f = (λ z, a⁻¹ • (a • f z)), {
      funext, simp only [←smul_assoc, smul_eq_mul, inv_mul_cancel a0, one_smul],
    },
    rw e, exact ⟨_, fp.const_smul⟩,
  }, {
    rintros ⟨p,fp⟩, exact ⟨_, fp.const_smul⟩,
  },
end

-- Nonzero scaling does not change order_at
lemma order_at_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) : order_at (λ z, a • f z) c = order_at f c := begin
  by_cases fa : analytic_at 𝕜 f c, {
    rcases fa with ⟨p,fp⟩,
    have e : ∀ n, a • p n ≠ 0 ↔ p n ≠ 0 := λ n, by simp only [a0, ne.def, smul_eq_zero, false_or],
    simp only [fp.order_at_unique, fp.const_smul.order_at_unique, formal_multilinear_series.order, e],
  }, {
    have ga := fa, rw ←analytic_at_iff_const_smul a0 at ga,
    simp only [order_at, fa, ga], rw [dif_neg, dif_neg],
    exact not_false, exact not_false, apply_instance,
  },
end

-- The leading coefficient of zero is zero
lemma leading_coeff.zero {c : 𝕜} : leading_coeff (λ z : 𝕜, (0 : E)) c = 0 := begin
  simp only [leading_coeff],
  generalize hn : order_at (λ z : 𝕜, (0 : E)) c = n, clear hn,
  induction n with n h, simp only [function.iterate_zero_apply],
  simp only [function.iterate_succ_apply], convert h,
  simp only [function.swap, dslope, deriv_const],
  funext, simp only [slope_fun_def, vsub_eq_sub, sub_zero, smul_zero, function.update_apply],
  by_cases ac : a = c, simp only [ac, if_pos], simp only [ac], rw [if_neg], exact not_false,
end

-- deriv scales linearly without assuming differentiability
lemma deriv_const_smul' {f : 𝕜 → E} {c : 𝕜} (a : 𝕜) : deriv (λ x, a • f x) c = a • deriv f c := begin
  by_cases a0 : a = 0, simp only [a0, zero_smul, deriv_const],
  by_cases d : differentiable_at 𝕜 f c, exact deriv_const_smul _ d,
  have ad : ¬differentiable_at 𝕜 (λ x, a • f x) c, {
    contrapose d, simp only [not_not] at d ⊢,
    have e : f = (λ z, a⁻¹ • (a • f z)), {
      funext, simp only [←smul_assoc, smul_eq_mul, inv_mul_cancel a0, one_smul],
    },
    rw e, exact d.const_smul _,
  },
  simp only [deriv_zero_of_not_differentiable_at d, deriv_zero_of_not_differentiable_at ad, smul_zero],
end

-- leading_coeff has linear scaling
lemma leading_coeff_const_smul {f : 𝕜 → E} {c a : 𝕜} : leading_coeff (λ z, a • f z) c = a • leading_coeff f c := begin
  by_cases a0 : a = 0, simp only [a0, zero_smul, leading_coeff.zero],
  simp only [leading_coeff, order_at_const_smul a0],
  generalize hn : order_at f c = n, clear hn,
  have e : (function.swap dslope c^[n] (λ z : 𝕜, a • f z)) = a • (function.swap dslope c^[n] f), {
    induction n with n h, funext, simp only [function.iterate_zero_apply, pi.smul_apply],
    generalize hg : function.swap dslope c^[n] f = g,
    simp only [function.iterate_succ_apply', h, hg],
    funext x, simp only [function.swap],
    by_cases cx : x = c,
    simp only [cx, dslope_same, pi.smul_apply, pi.smul_def, deriv_const_smul'],
    simp only [dslope_of_ne _ cx, pi.smul_apply, slope, vsub_eq_sub, ←smul_sub, smul_comm _ a],
  },
  simp only [e, pi.smul_apply],
end

-- leading_coeff is nonzero for nonzero order
lemma leading_coeff_ne_zero {f : 𝕜 → E} {c : 𝕜} (fa : analytic_at 𝕜 f c) (o0 : order_at f c ≠ 0)
    : leading_coeff f c ≠ 0 := begin
  rcases fa with ⟨p,fp⟩,
  simp only [fp.order_at_unique, leading_coeff] at o0 ⊢,
  exact fp.iterate_dslope_fslope_ne_zero (formal_multilinear_series.ne_zero_of_order_ne_zero o0),
end