-- Convergent sequences of analytic functions

import analysis.analytic.basic
import analysis.calculus.fderiv_analytic
import analysis.complex.cauchy_integral
import analysis.complex.re_im_topology
import data.complex.basic
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import measure_theory.integral.interval_integral
import order.bounded_order
import order.filter.at_top_bot
import topology.metric_space.basic
import topology.uniform_space.uniform_convergence

import analytic
import bounds
import simple
import tactics
import topology

open complex (abs I)
open filter (at_top)
open measure_theory.measure_space (volume)
open metric (ball closed_ball sphere)
open_locale real nnreal topological_space

noncomputable theory

def power_series := formal_multilinear_series ℂ ℂ ℂ

lemma cauchy_on_cball_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : analytic_on ℂ f (closed_ball z r))
    : has_fpower_series_on_ball f (cauchy_power_series f z r) z r := begin
  have hd : differentiable_on ℂ f (closed_ball z r), {
    intros x H, exact analytic_at.differentiable_within_at (h x H)
  },
  set p : power_series := cauchy_power_series f z r,
  exact differentiable_on.has_fpower_series_on_ball hd rp
end

lemma analytic_on_cball_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (rp : r > 0) (h : analytic_on ℂ f (closed_ball z r))
    : ∃ p : power_series, has_fpower_series_on_ball f p z r :=
  ⟨cauchy_power_series f z r, cauchy_on_cball_radius rp h⟩

lemma analytic_on_small_cball {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (h : analytic_on ℂ f (ball z r))
    (s : ℝ≥0) (sr : s < r) : analytic_on ℂ f (closed_ball z s) := begin
  intros x hx,
  rw closed_ball at hx, simp at hx,
  have hb : x ∈ ball z r, {
    rw ball, simp,
    calc nndist x z ≤ s : hx
    ... < r : sr
  },
  exact h x hb
end

lemma analytic_on_ball_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (rp : r > 0) (h : analytic_on ℂ f (ball z r))
    : ∃ p : power_series, has_fpower_series_on_ball f p z r := begin
  have h0 := analytic_on_small_cball h (r/2) (nnreal.half_lt_self $ ne_of_gt rp),
  rcases analytic_on_cball_radius (nnreal.half_pos rp) h0 with ⟨p, ph⟩,
  set R := formal_multilinear_series.radius p,
  refine ⟨p, { r_le := _, r_pos := ennreal.coe_pos.mpr rp, has_sum := _ }⟩, {
    apply ennreal.le_of_forall_pos_nnreal_lt,
    intros t tp tr,
    have ht := analytic_on_small_cball h t (ennreal.coe_lt_coe.elim_left tr),
    rcases analytic_on_cball_radius tp ht with ⟨p',hp'⟩,
    have pp : p = p' := has_fpower_series_at.eq_formal_multilinear_series ⟨↑(r/2),ph⟩ ⟨t,hp'⟩,
    rw ←pp at hp',
    refine hp'.r_le
  }, {
    intros y yr,
    rw [emetric.ball, set.mem_set_of] at yr,
    rcases exists_between yr with ⟨t,t0,t1⟩,
    have ht := analytic_on_small_cball h t.to_nnreal (simple.nnreal_ennreal_coe_lt t1),
    rcases analytic_on_cball_radius _ ht with ⟨p',hp'⟩,
    have pp : p = p' := has_fpower_series_at.eq_formal_multilinear_series ⟨↑(r/2),ph⟩ ⟨t.to_nnreal,hp'⟩,
    rw ←pp at hp',
    refine hp'.has_sum _,
    rw [emetric.ball, set.mem_set_of],
    calc edist y 0 < t : t0
    ... = ↑(t.to_nnreal) : (ennreal.coe_to_nnreal $ ne_top_of_lt t1).symm,
    exact simple.to_nnreal_pos t0 t1
  }
end

lemma cauchy_bound {f : ℂ → ℂ} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} {w : ℂ} {n : ℕ}
  (rp : r > 0) (h : ∀ w ∈ closed_ball c r, abs (f w) ≤ d)
  : abs (cauchy_power_series f c r n (λ _, w)) ≤ abs w ^ n * r⁻¹ ^ n * d :=
begin
  set wr := abs w ^ n * r⁻¹ ^ n * d, 
  rw [cauchy_power_series_apply f c r n w],
  rw [smul_eq_mul, complex.abs_mul],
  generalize hg : (λ z, (w / (z - c)) ^ n • (z - c)⁻¹ • f z) = g,
  have gs : ∀ z ∈ sphere c r, ∥g z∥ ≤ wr * r⁻¹, {
    intro, simp, intro, rw ←hg, simp, rw H,
    have zb : z ∈ closed_ball c r, simp, rw [←nnreal.coe_le_coe, coe_nndist, complex.dist_eq], linarith,
    have zs := h z zb,
    calc abs w ^ n / ↑r ^ n * (r⁻¹ * abs (f z)) = abs w ^ n * r⁻¹ ^ n * (r⁻¹ * abs (f z))
      : by rw simple.div_pow_inv (abs w ^ n) ↑r n
    ... ≤ abs w ^ n * r⁻¹ ^ n * (r⁻¹ * d) : by bound
    ... = abs w ^ n * r⁻¹ ^ n * d * r⁻¹ : by ring
    ... = wr * r⁻¹ : rfl
  },
  have cn := circle_integral.norm_integral_le_of_norm_le_const (nnreal.coe_nonneg r) gs,
  rw complex.norm_eq_abs at cn,
  simp at hg cn ⊢,
  have p3 : |π| = π := abs_eq_self.elim_right (by linarith [real.pi_gt_three]),
  calc |π|⁻¹ * 2⁻¹ * abs (circle_integral g c ↑r) ≤ |π|⁻¹ * 2⁻¹ * (2*π*r * (wr * r⁻¹)) : by bound
  ... = (π * |π|⁻¹) * (r * r⁻¹) * wr : by ring
  ... = (π * π⁻¹) * (r * r⁻¹) * wr : by rw p3
  ... = 1 * (r * r⁻¹) * wr : by rw mul_inv_cancel real.pi_ne_zero
  ... = 1 * 1 * wr : by rw mul_inv_cancel (nnreal.coe_ne_zero.elim_right $ ne_of_gt rp)
  ... = wr : by ring
end

lemma circle_integral_sub {f g : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (fi : circle_integrable f c r) (gi : circle_integrable g c r)
    : circle_integral f c r - circle_integral g c r = circle_integral (f - g) c r := begin
  rw circle_integral, generalize hf : (λ θ : ℝ, deriv (circle_map c r) θ • f (circle_map c r θ)) = fc,
  rw circle_integral, generalize hg : (λ θ : ℝ, deriv (circle_map c r) θ • g (circle_map c r θ)) = gc,
  rw circle_integral, generalize hfg : (λ θ : ℝ, deriv (circle_map c r) θ • (f-g) (circle_map c r θ)) = fgc,
  have hs : fc - gc = fgc, {
    rw [←hf, ←hg, ←hfg], apply funext, simp, intro, rw mul_sub_left_distrib,
  },
  rw ←hs, clear hfg hs fgc, symmetry,
  have fci := circle_integrable.out fi, rw hf at fci,
  have gci := circle_integrable.out gi, rw hg at gci,
  exact interval_integral.integral_sub fci gci
end

lemma circle_map_nz {c : ℂ} {r : ℝ≥0} {θ : ℝ} (rp : r > 0) : circle_map c r θ - c ≠ 0 := begin
  simp, intro h, rw h at rp, simp at rp, exact rp
end

lemma cauchy_is_circle_integrable {f : ℂ → ℂ} {c : ℂ} {r : ℝ≥0}
    (n : ℕ) (w : ℂ) (rp : r > 0) (h : continuous_on f (closed_ball c r))
    : circle_integrable (λ z, w^n / (z - c)^n * ((z - c)⁻¹ * f z)) c r := begin
  refine continuous_on.interval_integrable _,
  refine continuous_on.mul _ _,
  refine continuous_on.mul continuous_on_const _,
  apply continuous.continuous_on,
  refine continuous.inv₀ (by continuity) (λ x, pow_ne_zero n (circle_map_nz rp)),
  refine continuous_on.mul _ _,
  apply continuous.continuous_on,
  refine continuous.inv₀ (by continuity) (λ x, circle_map_nz rp),
  refine continuous_on.comp h (continuous.continuous_on (by continuity)) _,
  intros θ hθ, exact circle_map_mem_closed_ball c (nnreal.coe_nonneg r) θ,
end

lemma cauchy_sub {f g : ℂ → ℂ} {c : ℂ} {r : ℝ≥0}
    (n : ℕ) (w : ℂ) (rp : r > 0) (cf : continuous_on f (closed_ball c r)) (cg : continuous_on g (closed_ball c r))
    : cauchy_power_series f c r n (λ _, w) - cauchy_power_series g c r n (λ _, w)
      = cauchy_power_series (f - g) c r n (λ _, w) :=
begin
  rw [cauchy_power_series_apply f c r n w], 
  rw [cauchy_power_series_apply g c r n w], 
  rw [cauchy_power_series_apply (f-g) c r n w],
  set s : ℂ := (2 * π * I)⁻¹,
  simp,
  have hfg : (λ z, w^n / (z - c)^n * ((z - c)⁻¹ * (f - g) z))
           = (λ z, w^n / (z - c)^n * ((z - c)⁻¹ * f z))
           - (λ z, w^n / (z - c)^n * ((z - c)⁻¹ * g z)), {
    apply funext, simp, intro, ring,
  },
  have fi := cauchy_is_circle_integrable n w rp cf,
  have gi := cauchy_is_circle_integrable n w rp cg,
  have cia := circle_integral_sub fi gi,
  rw [←mul_sub_left_distrib, cia],
  clear cia fi gi hfg cf cg rp,
  have flip : (λ z, w^n/(z-c)^n * ((z-c)⁻¹ * f z)) - (λ z, w^n/(z-c)^n * ((z-c)⁻¹ * g z))
            = (λ z, w^n/(z-c)^n * ((z-c)⁻¹ * f z) - w^n/(z-c)^n * ((z-c)⁻¹ * g z)) := rfl,
  rw flip, clear flip, ring_nf
end

lemma cauchy_dist {f g : ℂ → ℂ} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0}
  (n : ℕ) (w : ℂ) (rp : r > 0) (cf : continuous_on f (closed_ball c r)) (cg : continuous_on g (closed_ball c r))
  (h : ∀ z, z ∈ closed_ball c r → abs (f z - g z) ≤ d)
  : dist (cauchy_power_series f c r n (λ _, w)) (cauchy_power_series g c r n (λ _, w)) ≤ abs w ^ n * r⁻¹ ^ n * d :=
begin
  rw [complex.dist_eq, cauchy_sub n w rp cf cg],
  refine cauchy_bound rp _, intros z zr, simp at h zr, refine h z zr
end

-- Uniform limits of analytic functions are analytic.
theorem uniform_analytic_lim {I : Type} [lattice I] [nonempty I] {f : I → ℂ → ℂ} {g : ℂ → ℂ} {s : set ℂ}
    (o : is_open s) (h : ∀ n, analytic_on ℂ (f n) s) (u : tendsto_uniformly_on f g at_top s)
    : analytic_on ℂ g s := begin
  intros c hc,
  rcases open_has_cball o c hc with ⟨r, rp, cb⟩,
  have hb : ∀ n, analytic_on ℂ (f n) (closed_ball c r) := λ n, (h n).mono cb,
  set pr := λ n, cauchy_power_series (f n) c r,
  have hpf : ∀ n, has_fpower_series_on_ball (f n) (pr n) c r, {
    intro,
    have cs := cauchy_on_cball_radius rp (hb n),
    have pn : pr n = cauchy_power_series (f n) c r := rfl,
    rw ←pn at cs, exact cs
  },
  have cfs : ∀ n, continuous_on (f n) s := λ n, analytic_on.continuous_on (h n),
  have cf : ∀ n, continuous_on (f n) (closed_ball c r) := λ n, continuous_on.mono (cfs n) cb,
  have cg : continuous_on g (closed_ball c r)
    := continuous_on.mono (tendsto_uniformly_on.continuous_on u (filter.eventually_of_forall cfs)) cb,
  clear h hb hc o cfs,
  set p := cauchy_power_series g c r,
  exact has_fpower_series_on_ball.analytic_at {
    r_le := le_radius_cauchy_power_series g c r,
    r_pos := ennreal.coe_pos.mpr rp,
    has_sum := _
  },
  intros y yb,
  have yr := yb, simp at yr,
  set a := abs y / r,
  have a0 : a ≥ 0 := by bound,
  have a1 : a < 1 := (div_lt_one (nnreal.coe_pos.mpr rp)).mpr yr,
  have a1p : 1 - a > 0 := by bound,
  rw [has_sum, metric.tendsto_at_top],
  intros e ep,
  generalize d4 : (1-a)*(e/4) = d,
  have dp : d > 0, { rw ←d4, bound },
  rcases filter.eventually_at_top.mp (metric.tendsto_uniformly_on_iff.mp u d dp) with ⟨n,hn'⟩,
  set hn := hn' n, simp at hn, clear hn' u,
  have dfg : dist (f n (c + y)) (g (c + y)) ≤ d, {
    apply le_of_lt, rw dist_comm,
    refine hn (c + y) _,
    apply cb,
    simp, exact le_of_lt yr
  },
  set hs := (hpf n).has_sum yb, rw [has_sum, metric.tendsto_at_top] at hs,
  rcases hs d dp with ⟨N,NM⟩, clear hs,
  existsi N, intros M NlM,
  have dpf := le_of_lt (NM M NlM), clear NM NlM N yb,
  have dppr : dist (M.sum (λ (k : ℕ), p k (λ _, y))) (M.sum (λ (k : ℕ), pr n k (λ _, y))) ≤ e/4, {
    transitivity M.sum (λ (k : ℕ), dist (p k (λ _, y)) (pr n k (λ _, y))),
    apply dist_sum_sum_le M (λ (k : ℕ), p k (λ _, y)) (λ (k : ℕ), pr n k (λ _, y)),
    transitivity M.sum (λ k, a^k * d), {
      apply finset.sum_le_sum, intros k hk,
      have hak : a^k = abs y^k * r⁻¹^k, {
        calc (abs y / r)^k = (abs y * r⁻¹)^k : by ring
        ... = abs y^k * r⁻¹^k : mul_pow _ _ _
      },
      rw hak,
      generalize hd' : d.to_nnreal = d',
      have dd : (d' : ℝ) = d, { rw ←hd', exact real.coe_to_nnreal d (le_of_lt dp) },
      have hcb : ∀ z, z ∈ closed_ball c r → abs (g z - f n z) ≤ d', {
        intros z zb, exact trans (le_of_lt (hn z (cb zb))) (le_of_eq dd.symm)
      },
      exact trans (cauchy_dist k y rp cg (cf n) hcb) (mul_le_mul_of_nonneg_left (le_of_eq dd) (by bound))
    }, {
      have pgb : M.sum (λ k, a^k) ≤ (1-a)⁻¹ := partial_geometric_bound M a0 a1,
      calc M.sum (λ k, a^k * d) = M.sum (λ k, a^k) * d : by rw ←finset.sum_mul
      ... ≤ (1-a)⁻¹ * d : by bound
      ... = (1-a)⁻¹ * ((1-a) * (e/4)) : by rw ←d4
      ... = (1-a) * (1-a)⁻¹ * (e/4) : by ring
      ... = 1 * (e/4) : by rw mul_inv_cancel (ne_of_gt a1p)
      ... = e/4 : by ring
    }
  },
  generalize hMp : M.sum (λ k : ℕ, p k (λ _, y)) = Mp, rw hMp at dppr,
  generalize hMpr : M.sum (λ k, pr n k (λ _, y)) = Mpr, rw hMpr at dpf dppr,
  calc dist Mp (g (c + y)) ≤ dist Mp (f n (c + y)) + dist (f n (c + y)) (g (c + y)) : dist_triangle _ _ _
  ... ≤ dist Mp Mpr + dist Mpr (f n (c + y)) + d : by bound
  ... ≤ e/4 + d + d : by bound
  ... = e/4 + 2*(1-a)*(e/4) : by { rw ←d4, ring }
  ... ≤ e/4 + 2*(1-0)*(e/4) : by bound
  ... = (3/4)*e : by ring
  ... < 1*e : mul_lt_mul_of_pos_right (by norm_num) ep
  ... = e : by simp
end