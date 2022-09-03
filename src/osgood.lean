-- Osgood's lemma for two variables: continuous, separately analytic functions are jointly analytic
--   https://en.wikipedia.org/wiki/Osgood's_lemma
-- We prove it for two variables only, as that's all we need.

import analysis.analytic.basic
import analysis.calculus.fderiv_analytic
import analysis.complex.cauchy_integral
import analysis.inner_product_space.euclidean_dist
import analysis.normed.group.basic
import analysis.normed_space.multilinear
import data.complex.basic
import data.finset.basic
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import data.set.function
import measure_theory.measure.measure_space_def
import topology.algebra.module.multilinear
import topology.basic

import analytic
import bounds
import holomorphic
import multilinear
import simple
import tactics
import topology

open complex (abs exp I log)
open filter (at_top)
open function (curry uncurry)
open linear_order (min)
open metric (ball closed_ball sphere bounded is_open_ball)
open prod (swap)
open_locale real nnreal ennreal topological_space
noncomputable theory

section osgood

variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
variable {f : ℂ × ℂ → E}
variable {s : set (ℂ × ℂ)}
variables {c0 c1 w0 w1 : ℂ}
variables {r b : ℝ}

-- Osgood's lemma follows from the multidimensional Cauchy integral formula
--   f c = (2πi)^(-d) (prod_k ∫_(C k) d(z k)) (prod_k (z k - c k)^⁻¹) f z
-- By induction, we can assume Osgood's lemma holds for d-1 = e.  Then we're left
-- with an integral over only the last dimension:
--   f c = (2πi)⁻¹ ∫_C dz (z - c e)⁻¹ ∑_n ...
-- Meh, that's not as nice as I was hoping, as we need Osgood to hold uniformly.
-- What I really want is a way to express the whole multilinear map cleanly.  The
-- nth multidimensional coefficient (with n : fin d → ℕ) looks like
--   p n = (2πi)^(-d) (prod_k ∫_(C k) d(z k)) (prod_k (z k - c k)^(-1 - n k)) f z
-- Actually, that's not too bad.  Let's do it without induction.

-- Quick refresher on why the Cauchy power series works.  Assume c = 0.  Then:
--   f_n = (2πi)⁻¹ ∫_C dz z^(-1-n) * f z
--   f w = (2πi)⁻¹ ∫_C dz (z - w)⁻¹ * f z
--       = (2πi)⁻¹ ∫_C dz (z - z * (w/z))⁻¹ * f z
--       = (2πi)⁻¹ ∫_C dz (1 - w/z)⁻¹ * z⁻¹ * f z
--       = (2πi)⁻¹ ∫_C dz Σ_n (w/z)^n * z⁻¹ * f z
--       = Σ_n w^n (2πi)⁻¹ ∫_C dz  z⁻¹^n * z⁻¹ * f z

-- A measureable, separately analytic function of 2 complex variables near c.
-- We assume f is differentiable in an open neighborhood of the closed_ball for simplicity.

structure sep (f : ℂ × ℂ → E) (c0 c1 : ℂ) (r b : ℝ) (s : set (ℂ × ℂ)) : Prop :=
  (rp : r > 0)
  (so : is_open s) 
  (rs : closed_ball (c0,c1) r ⊆ s)
  (fc : continuous_on f s)
  (fa0 : ∀ {c0 c1}, (c0,c1) ∈ s → analytic_at ℂ (λ z0, f (z0,c1)) c0)
  (fa1 : ∀ {c0 c1}, (c0,c1) ∈ s → analytic_at ℂ (λ z1, f (c0,z1)) c1)
  (bp : b ≥ 0)
  (fb : ∀ {z0 z1}, z0 ∈ sphere c0 r → z1 ∈ sphere c1 r → ∥f (z0,z1)∥ ≤ b)

lemma spheres_subset_closed_ball {c0 c1 : ℂ} {r : ℝ} : sphere c0 r ×ˢ sphere c1 r ⊆ closed_ball (c0,c1) r := begin
  rw [←closed_ball_prod_same, set.subset_def], intro z, simp, rw [complex.dist_eq, complex.dist_eq],
  intros a b, exact ⟨le_of_eq a, le_of_eq b⟩
end

lemma sep.rs' (h : sep f c0 c1 r b s) : sphere c0 r ×ˢ sphere c1 r ⊆ s := trans spheres_subset_closed_ball h.rs

lemma mem_open_closed {z c : ℂ} {r : ℝ} : z ∈ ball c r → z ∈ closed_ball c r := by { simp, exact le_of_lt }
lemma mem_sphere_closed {z c : ℂ} {r : ℝ} : z ∈ sphere c r → z ∈ closed_ball c r := by { simp, exact le_of_eq }

-- Spheres don't contain their center
lemma center_not_in_sphere {c z : ℂ} {r : ℝ} (rp : r > 0) (zs : z ∈ sphere c r) : z - c ≠ 0 := begin
  simp at zs, rw ←complex.abs_ne_zero, rw zs, exact ne_of_gt rp
end

-- f is continuous in z0
lemma sep.fc0 (h : sep f c0 c1 r b s) (w1m : w1 ∈ ball c1 r)
    : continuous_on (λ z0, f (z0,w1)) (closed_ball c0 r) := begin
  refine continuous_on.comp h.fc _ _,
  exact continuous_on.prod continuous_on_id continuous_on_const,
  intros z0 z0m, apply h.rs,
  rw ←closed_ball_prod_same, exact set.mem_prod.mpr ⟨z0m, mem_open_closed w1m⟩
end

-- f is continuous in z1
lemma sep.fc1 (h : sep f c0 c1 r b s) (w0m : w0 ∈ closed_ball c0 r)
    : continuous_on (λ z1, f (w0,z1)) (closed_ball c1 r) := begin
  refine continuous_on.comp h.fc _ _,
  exact continuous_on.prod continuous_on_const continuous_on_id,
  intros z1 z1m, apply h.rs,
  rw ←closed_ball_prod_same, exact set.mem_prod.mpr ⟨w0m, z1m⟩
end

-- f is differentiable in z0
lemma sep.fd0 (h : sep f c0 c1 r b s) (w0m : w0 ∈ closed_ball c0 r) (w1m : w1 ∈ closed_ball c1 r)
    : differentiable_at ℂ (λ z0, f (z0,w1)) w0 := begin
  have m : (w0,w1) ∈ s, { apply h.rs, rw ←closed_ball_prod_same, exact set.mem_prod.mpr ⟨w0m,w1m⟩ },
  exact analytic_at.differentiable_at (h.fa0 m)
end

-- f is differentiable in z1
lemma sep.fd1 (h : sep f c0 c1 r b s) (w0m : w0 ∈ closed_ball c0 r) (w1m : w1 ∈ closed_ball c1 r)
    : differentiable_at ℂ (λ z1, f (w0,z1)) w1 := begin
  have m : (w0,w1) ∈ s, { apply h.rs, rw ←closed_ball_prod_same, exact set.mem_prod.mpr ⟨w0m,w1m⟩ },
  exact analytic_at.differentiable_at (h.fa1 m)
end

-- Simplied 1D Cauchy integral formula, assuming differentiability everywhere in the interior
lemma cauchy1 {r : ℝ} {c w : ℂ} {f : ℂ → E}
    (wm : w ∈ ball c r) (fc : continuous_on f (closed_ball c r)) (fd : ∀ z, z ∈ ball c r → differentiable_at ℂ f z)
    : (2*π*I : ℂ)⁻¹ • ∮ z in C(c, r), (z - w)⁻¹ • f z = f w := begin
  refine complex.two_pi_I_inv_smul_circle_integral_sub_inv_smul_of_differentiable_on_off_countable
      set.countable_empty wm fc _,
  intros z zm, apply fd z _, simp at ⊢ zm, assumption
end

-- The 2D Cauchy integral formula
lemma cauchy2 (h : sep f c0 c1 r b s) (w0m : w0 ∈ ball c0 r) (w1m : w1 ∈ ball c1 r)
    : (2*π*I : ℂ)⁻¹ • ∮ z0 in C(c0, r), (z0 - w0)⁻¹ • 
      ((2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0,z1)) = f (w0,w1) := begin
  have h1 := λ z0 (z0m : z0 ∈ closed_ball c0 r), cauchy1 w1m (h.fc1 z0m) (λ z1 z1m, h.fd1 z0m (mem_open_closed z1m)),
  simp_rw smul_eq_mul at h1,
  have ic1 : continuous_on (λ z0, (2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0,z1)) (closed_ball c0 r) :=
    (h.fc0 w1m).congr h1,
  have id1 : differentiable_on ℂ (λ z0, (2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0,z1)) (ball c0 r), {
    rw differentiable_on_congr (λ z zs, h1 z (mem_open_closed zs)),
    intros z0 z0m, apply differentiable_at.differentiable_within_at,
    exact h.fd0 (mem_open_closed z0m) (mem_open_closed w1m),
  },
  have h01 := cauchy1 w0m ic1 (λ z0 z0m, differentiable_on.differentiable_at id1 (is_open.mem_nhds is_open_ball z0m)),
  simp_rw smul_eq_mul at h01,
  exact trans h01 (h1 w0 (mem_open_closed w0m))
end

-- One 2D coefficient of the 2D Cauchy series
def series2_coeff (h : sep f c0 c1 r b s) (n0 n1 : ℕ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ z0 in C(c0, r), (z0 - c0)⁻¹^n0 • (z0 - c0)⁻¹ • 
  ((2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹^n1 • (z1 - c1)⁻¹ • f (z0,z1))

-- series2_coeff summed over n0
def series2_coeff_n0_sum (h : sep f c0 c1 r b s) (n1 : ℕ) (w0 : ℂ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ (z0 : ℂ) in C(c0, r), (z0 - (c0+w0))⁻¹ •
  ((2*π*I : ℂ)⁻¹ • ∮ (z1 : ℂ) in C(c1, r), (z1 - c1)⁻¹^n1 • (z1 - c1)⁻¹ • f (z0,z1))

-- The 1D Cauchy series converges as expected (rephrasing of has_sum_cauchy_power_series_integral)
lemma cauchy1_has_sum {f : ℂ → E} {c w : ℂ} {r : ℝ}
    (rp : r > 0) (fc : continuous_on f (sphere c r)) (wm : w ∈ ball (0 : ℂ) r)
    : has_sum (λ n : ℕ, w^n • (2*π*I : ℂ)⁻¹ • ∮ z in C(c, r), (z - c)⁻¹^n • (z - c)⁻¹ • f z)
              ((2*π*I : ℂ)⁻¹ • ∮ z in C(c, r), (z - (c + w))⁻¹ • f z) := begin
  simp at wm,
  have ci : circle_integrable f c r := continuous_on.circle_integrable (by bound) fc,
  have h := has_sum_cauchy_power_series_integral ci wm,
  simp_rw cauchy_power_series_apply at h,
  generalize hs : (2*π*I : ℂ)⁻¹  = s, simp_rw hs at h,
  generalize hg : s • ∮ (z : ℂ) in C(c, r), (z - (c + w))⁻¹ • f z = g, rw hg at h,
  simp_rw [div_eq_mul_inv, mul_pow, ←smul_smul, circle_integral.integral_smul, smul_comm s _] at h,
  assumption
end

-- Circle integrals are continuous if the function varies continuously
lemma continuous_on.circle_integral {f : ℂ → ℂ → E} {s : set ℂ}
    (rp : r > 0) (cs : is_compact s) (fc : continuous_on (uncurry f) (s ×ˢ sphere c1 r))
    : continuous_on (λ z0, ∮ z1 in C(c1, r), f z0 z1) s := begin
  rcases fc.bounded_norm (is_compact.prod cs (is_compact_sphere _ _)) with ⟨b,_,bh⟩,
  intros z1 z1s,
  have fb : ∀ᶠ (x : ℂ) in 𝓝[s] z1, ∀ᵐ (t : ℝ), t ∈ set.interval_oc 0 (2 * π) →
      ∥deriv (circle_map c1 r) t • (λ (z1 : ℂ), f x z1) (circle_map c1 r t)∥ ≤ r * b, {
    apply eventually_nhds_within_of_forall, intros x xs, 
    apply measure_theory.ae_of_all _, intros t ti, simp, rw [norm_smul, complex.norm_eq_abs], simp,
    have bx := bh (x, circle_map c1 r t) (set.mk_mem_prod xs (circle_map_mem_sphere c1 (by bound) t)),
    calc |r| * ∥f x (circle_map c1 r t)∥ ≤ |r| * b : by bound
    ... = r * b : by rw abs_of_pos rp
  },
  refine interval_integral.continuous_within_at_of_dominated_interval _ fb (by simp) _, {
    apply eventually_nhds_within_of_forall, intros x xs,
    apply continuous_on.ae_strongly_measurable,
    apply continuous_on.smul, simp,
    exact continuous_on.mul (continuous.continuous_on (continuous_circle_map _ _)) continuous_on_const,
    have comp : (λ t, f x (circle_map c1 r t)) = (uncurry f) ∘ (λ t, (x, circle_map c1 r t)), { apply funext, intro t, simp },
    simp, rw comp, apply continuous_on.comp fc,
    exact continuous_on.prod continuous_on_const (continuous.continuous_on (continuous_circle_map _ _)),
    intros t ti, simp, exact ⟨xs, by bound⟩,
    exact measurable_set_interval_oc
  }, {
    apply measure_theory.ae_of_all _, intros t ti, simp,
    apply continuous_on.smul continuous_on_const,
    have comp : (λ x, f x (circle_map c1 r t)) = (uncurry f) ∘ (λ x, (x, circle_map c1 r t)), { apply funext, intro t, simp },
    rw comp, apply continuous_on.comp fc (continuous_on.prod continuous_on_id continuous_on_const),
    intros x xs, simp, exact ⟨xs, by bound⟩,
    exact z1s, exact uniform_space.to_topological_space, exact has_bounded_smul.has_continuous_smul
  }
end

-- Inverses are continuous on the sphere
lemma continuous_on.inv_sphere {c : ℂ} {r : ℝ} (rp : r > 0) : continuous_on (λ z, (z - c)⁻¹) (sphere c r) :=
  continuous_on.inv₀ (continuous_on.sub continuous_on_id continuous_on_const) (λ z zs, center_not_in_sphere rp zs)

-- Shifted inverses are continuous on the sphere
lemma continuous_on.inv_sphere_ball {c w : ℂ} {r : ℝ} (rp : r > 0) (wr : w ∈ ball (0 : ℂ) r)
    : continuous_on (λ z, (z - (c + w))⁻¹) (sphere c r) := begin
  refine continuous_on.inv₀ (continuous_on.sub continuous_on_id continuous_on_const) (λ z zs, _),
  rw ←complex.abs_ne_zero, simp at zs wr,
  apply ne_of_gt, flip_ineq,
  calc abs (z - (c + w)) = abs (z - c + (-w)) : by ring_nf
  ... ≥ abs (z - c) - abs (-w) : simple.abs_sub_ge _ _
  ... = r - abs (-w) : by rw zs
  ... = r - abs w : by simp
  ... > r - r : sub_lt_sub_left wr _
  ... = 0 : by ring
end

-- Cauchy series terms are continuous in the function
lemma continuous_on.cauchy1 {n1 : ℕ}
    (rp : r > 0) (fc : continuous_on f (sphere c0 r ×ˢ sphere c1 r))
    : continuous_on (λ z0, ∮ z1 in C(c1, r), (z1 - c1)⁻¹^n1 • (z1 - c1)⁻¹ • f (z0,z1)) (sphere c0 r) := begin
  apply continuous_on.circle_integral rp (is_compact_sphere _ _),
  apply continuous_on.smul, apply continuous_on.pow, apply continuous_on.inv₀,
  apply continuous.continuous_on, exact continuous.sub (continuous.snd continuous_id) continuous_const,
  intros x xp, exact center_not_in_sphere rp (set.mem_prod.mp xp).right,
  apply continuous_on.smul, apply continuous_on.inv₀,
  apply continuous.continuous_on, exact continuous.sub (continuous.snd continuous_id) continuous_const,
  intros x xp, exact center_not_in_sphere rp (set.mem_prod.mp xp).right,
  simp, exact fc
end

-- Summing over n0 in the 2D series does the right thing
lemma cauchy2_has_sum_n0 (h : sep f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (w1m : w1 ∈ ball (0 : ℂ) r) (n1 : ℕ)
    : has_sum (λ n0 : ℕ, w0^n0 • series2_coeff h n0 n1) (series2_coeff_n0_sum h n1 w0) := begin
  have cc1 : continuous_on (λ z0, (2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹^n1 • (z1 - c1)⁻¹ • f (z0,z1)) (sphere c0 r), {
    exact continuous_on.smul continuous_on_const (continuous_on.cauchy1 h.rp (continuous_on.mono h.fc h.rs'))
  },
  exact cauchy1_has_sum h.rp cc1 w0m
end

-- Seminormed norm = normed norm
lemma seminorm_eq_norm (x : E)
    : @norm E normed_add_comm_group.to_has_norm x = @norm E seminormed_add_comm_group.to_has_norm x := by simp

-- Sums commute with circle_integral under reasonable hypotheses
lemma sum_integral_commute {f : ℕ → ℂ → E} {g : ℂ → E} {c : ℂ} {r : ℝ}
    (b : ℕ → ℝ) (rp : r > 0) (fc : ∀ n, continuous_on (f n) (sphere c r))
    (fb : ∀ n z, z ∈ sphere c r → ∥f n z∥ ≤ b n) (bs : summable b)
    (h : ∀ z, z ∈ sphere c r → has_sum (λ n, f n z) (g z))
    : has_sum (λ n, ∮ z in C(c, r), f n z) (∮ z in C(c, r), g z) := begin
  rw circle_integral, simp_rw circle_integral, simp,
  apply interval_integral.has_sum_integral_of_dominated_convergence (λ n _, r * b n), {
    intro n, apply continuous_on.ae_strongly_measurable, apply continuous_on.smul,
    apply continuous_on.mul (continuous.continuous_on (continuous_circle_map _ _)) continuous_on_const,
    apply continuous_on.comp (fc n) (continuous.continuous_on (continuous_circle_map _ _)),
    intros t ti, exact circle_map_mem_sphere _ (by bound) _,
    exact measurable_set_interval_oc
  }, {
    intro n, apply measure_theory.ae_of_all, intros t ti, rw [norm_smul, complex.norm_eq_abs], simp, rw abs_of_pos rp,
    refine mul_le_mul_of_nonneg_left _ (le_of_lt rp),
    rwa ←seminorm_eq_norm (f n (circle_map c r t)),
    exact fb n (circle_map c r t) (circle_map_mem_sphere _ (by bound) _)
  }, {
    apply measure_theory.ae_of_all, intros t ti,
    exact summable.mul_left _ bs
  }, {
    simp
  }, {
    apply measure_theory.ae_of_all, intros t ti,
    apply has_sum.const_smul,
    exact h (circle_map c r t) (circle_map_mem_sphere _ (by bound) _)
  }
end

-- The simple bound on circle_interval
lemma bounded_circle_integral {f : ℂ → E} {c : ℂ} {r b : ℝ}
    (rp : r > 0) (fc : continuous_on f (sphere c r)) (fb : ∀ z, z ∈ sphere c r → ∥f z∥ ≤ b)
    : ∥∮ z in C(c,r), f z∥ ≤ 2 * π * r * b := begin
  rw circle_integral, simp,
  have nonneg_2π := le_of_lt real.two_pi_pos,
  have ib : ∥∫ t in 0..2*π, (circle_map 0 r t * I) • f (circle_map c r t)∥
          ≤ ∫ t in 0..2*π, ∥(circle_map 0 r t * I) • f (circle_map c r t)∥
          := interval_integral.norm_integral_le_integral_norm nonneg_2π,
  refine trans ib _, clear ib,
  simp_rw [norm_smul, complex.norm_eq_abs], simp,
  have mo : ∀ t, t ∈ set.Icc 0 (2*π) → ∥f (circle_map c r t)∥ ≤ b :=
    λ t ti, fb (circle_map c r t) (circle_map_mem_sphere c (by bound) t),
  have i0 : interval_integrable (λ t, ∥f (circle_map c r t)∥) real.measure_space.volume 0 (2*π), {
    apply continuous_on.interval_integrable,
    have ca : continuous_on norm set.univ := continuous.continuous_on continuous_norm,
    refine continuous_on.comp ca _ (set.maps_to_univ _ _),
    apply continuous_on.comp fc,
    exact continuous.continuous_on (continuous_circle_map _ _),
    intros t ti, exact circle_map_mem_sphere _ (by bound) _
  },
  have i1 : interval_integrable (λ _, b) real.measure_space.volume 0 (2*π) := interval_integrable_const,
  have im := interval_integral.integral_mono_on nonneg_2π i0 i1 mo,
  simp at im,
  calc |r| * ∫ t in 0..2*π, ∥f (circle_map c r t)∥ ≤ |r| * (2*π*b) : by bound
  ... = r * (2*π*b) : by rw abs_of_pos rp
  ... = 2*π*r*b : by ring
end

-- The 1D Cauchy integral without the constant has the expected bound
lemma cauchy1_bound {f : ℂ → E} {b r : ℝ} {c : ℂ}
    (rp : r > 0) (bp : b ≥ 0) (fc : continuous_on f (sphere c r)) (bh : ∀ z, z ∈ sphere c r → ∥f z∥ ≤ b) (n : ℕ)
    : ∥∮ z in C(c, r), (z - c)⁻¹^n • (z - c)⁻¹ • f z∥ ≤ 2 * π * b * r⁻¹^n := begin
  have sb : ∀ z, z ∈ sphere c r → ∥(z - c)⁻¹^n • (z - c)⁻¹ • f z∥ ≤ r⁻¹^n * r⁻¹ * b, {
    intros z zs, have fb := bh z zs,
    rw [norm_smul, norm_smul, complex.norm_eq_abs, complex.norm_eq_abs], simp at ⊢ zs, rw zs, ring_nf, bound
  },
  have isb := bounded_circle_integral rp _ sb, swap, {
    apply continuous_on.smul, apply continuous_on.pow, exact continuous_on.inv_sphere rp,
    apply continuous_on.smul, exact continuous_on.inv_sphere rp, assumption
  },
  calc ∥∮ z in C(c, r), (z - c)⁻¹^n • (z - c)⁻¹ • f z∥ ≤ 2 * π * r * (r⁻¹ ^ n * r⁻¹ * b) : isb
  ... = 2 * π * b * r⁻¹^n * (r * r⁻¹) : by ring 
  ... = 2 * π * b * r⁻¹^n : by { rw field.mul_inv_cancel (ne_of_gt rp), simp }
end

-- The 1D Cauchy integral with the constant has the expected bound
lemma cauchy1_bound' {f : ℂ → E} {b r : ℝ} {c : ℂ}
    (rp : r > 0) (bp : b ≥ 0) (fc : continuous_on f (sphere c r)) (bh : ∀ z, z ∈ sphere c r → ∥f z∥ ≤ b) (n : ℕ)
    : ∥(2*π*I : ℂ)⁻¹ • ∮ z in C(c, r), (z - c)⁻¹^n • (z - c)⁻¹ • f z∥ ≤ b * r⁻¹^n := begin
  have a : abs ((2*π*I : ℂ)⁻¹) = (2*π)⁻¹, { simp, exact le_of_lt real.pi_pos },
  rw [norm_smul, complex.norm_eq_abs, a],
  calc (2*π)⁻¹ * ∥∮ z in C(c, r), (z - c)⁻¹^n • (z - c)⁻¹ • f z∥
      ≤ (2*π)⁻¹ * (2*π * b * r⁻¹^n) : by bound [cauchy1_bound rp bp fc bh n, rp, real.pi_pos]
  ... = (2*π)⁻¹ * (2*π) * b * r⁻¹^n : by ring
  ... = b * r⁻¹^n : by field_simp [ne_of_gt real.pi_pos]
end

-- Corollary of cauchy1_bound used in cauchy2_has_sum_n1n0
lemma cauchy2_has_sum_n1n0_bound (h : sep f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (w1m : w1 ∈ ball (0 : ℂ) r)
    (n : ℕ) {z0 : ℂ} (z0s : z0 ∈ sphere c0 r)
    : ∥w1^n • (2*π*I : ℂ)⁻¹ • (z0 - (c0 + w0))⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹^n • (z1 - c1)⁻¹ • f (z0,z1)∥
      ≤ (r - abs w0)⁻¹ * b * (abs w1 / r) ^ n := begin
  have isb := cauchy1_bound h.rp h.bp (continuous_on.mono (h.fc1 (mem_sphere_closed z0s)) metric.sphere_subset_closed_ball)
    (λ z1 z1s, h.fb z0s z1s) n,
  simp at z0s w0m w1m,
  have zcw : abs (z0 - (c0 + w0)) ≥ r - abs w0, {
    calc abs (z0 - (c0 + w0)) = abs (z0 - c0 + (-w0)) : by ring_nf
    ... ≥ abs (z0 - c0) - abs (-w0) : by bound
    ... = r - abs w0 : by { rw z0s, simp }
  },
  have zcw' : (abs (z0 - (c0 + w0)))⁻¹ ≤ (r - abs w0)⁻¹ := by bound,
  have pp := real.pi_pos,
  have a : (abs (2*π*I : ℂ))⁻¹ = (2*π)⁻¹, { simp, bound },
  rw [norm_smul, norm_smul, norm_smul, complex.norm_eq_abs, complex.norm_eq_abs, complex.norm_eq_abs,
      complex.abs_pow, complex.abs_inv, complex.abs_inv, a],
  calc abs w1^n * ((2*π)⁻¹ * ((abs (z0 - (c0 + w0)))⁻¹ * ∥∮ z1 in C(c1, r), (z1 - c1)⁻¹^n • (z1 - c1)⁻¹ • f (z0,z1)∥))
      ≤ abs w1^n * ((2*π)⁻¹ * ((abs (z0 - (c0 + w0)))⁻¹ * (2*π*b*r⁻¹^n))) : by bound
  ... ≤ abs w1^n * ((2*π)⁻¹ * ((r - abs w0)⁻¹ * (2*π*b*r⁻¹^n))) : by bound [h.bp, h.rp]
  ... = (2*π) * (2*π)⁻¹ * (r - abs w0)⁻¹ * b * (abs w1^n * r⁻¹^n) : by ring
  ... = (r - abs w0)⁻¹ * b * (abs w1 / r)^n
      : by rw [mul_inv_cancel (ne_of_lt real.two_pi_pos).symm, ←mul_pow, ←div_eq_mul_inv _ r, one_mul]
end

-- The outer n1 sum in the 2D series does the right thing
lemma cauchy2_has_sum_n1n0 (h : sep f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (w1m : w1 ∈ ball (0 : ℂ) r)
    : has_sum (λ n1, w1^n1 • series2_coeff_n0_sum h n1 w0) (f (c0 + w0, c1 + w1)) := begin
  have cw0m : c0 + w0 ∈ ball c0 r, { simp at ⊢ w0m, assumption },
  have cw1m : c1 + w1 ∈ ball c1 r, { simp at ⊢ w1m, assumption },
  simp_rw series2_coeff_n0_sum,
  rw ←cauchy2 h cw0m cw1m,
  generalize hs : (2 * ↑π * I)⁻¹ = s,
  simp_rw smul_comm _ s _,
  apply has_sum.const_smul,
  simp_rw ←circle_integral.integral_smul (w1^_) _ _ _,
  apply sum_integral_commute (λ n, (r - abs w0)⁻¹ * b * (abs w1 / r)^n) h.rp, {
    intro n,
    apply continuous_on.smul continuous_on_const,
    apply continuous_on.smul continuous_on_const,
    apply continuous_on.smul,
    exact continuous_on.inv_sphere_ball h.rp w0m,
    apply continuous_on.cauchy1 h.rp,
    apply continuous_on.mono h.fc h.rs',
    exact uniform_space.to_topological_space,
    exact has_bounded_smul.has_continuous_smul,
    exact uniform_space.to_topological_space,
    exact has_bounded_smul.has_continuous_smul
  }, {
    rw ←hs, exact λ n z0 z0s, cauchy2_has_sum_n1n0_bound h w0m w1m n z0s
  }, {
    apply summable.mul_left,
    apply summable_geometric_of_abs_lt_1,
    rw [abs_div, abs_of_pos h.rp], simp at ⊢ w1m, exact (div_lt_one h.rp).mpr w1m
  }, {
    intros z0 z0s,
    simp_rw smul_comm s _, simp_rw smul_comm (w1^_) _, apply has_sum.const_smul,
    have fcs : continuous_on (λ z1, f (z0,z1)) (sphere c1 r) :=
      continuous_on.mono (h.fc1 (metric.sphere_subset_closed_ball z0s)) metric.sphere_subset_closed_ball,
    have hs1 := cauchy1_has_sum h.rp fcs w1m,
    simp_rw [hs, smul_comm _ s] at hs1,
    assumption
  }
end

-- 2D Cauchy series terms are geometrically bounded
lemma series2_coeff_bound (h : sep f c0 c1 r b s) (n0 n1 : ℕ) : ∥series2_coeff h n0 n1∥ ≤ b * r⁻¹^(n0 + n1) := begin
  have inner_c : continuous_on (λ z0, (2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹^n1 • (z1 - c1)⁻¹ • f (z0,z1)) (sphere c0 r) :=
    continuous_on.smul continuous_on_const (continuous_on.cauchy1 h.rp (continuous_on.mono h.fc h.rs')),
  have inner_b := λ z0 z0s,
    cauchy1_bound' h.rp h.bp (continuous_on.mono (h.fc1 (mem_sphere_closed z0s)) metric.sphere_subset_closed_ball)
      (λ z1, h.fb z0s) n1,
  have outer := cauchy1_bound' h.rp (by bound [h.bp, h.rp]) inner_c inner_b n0,
  have e : b * r⁻¹^n1 * r⁻¹^n0 = b * r⁻¹^(n0 + n1) := by rw [mul_assoc, ←pow_add, add_comm n0 _],
  rw series2_coeff, rw e at outer, exact outer
end

-- The 2D Cauchy series
def series2 (h : sep f c0 c1 r b s) : formal_multilinear_series ℂ (ℂ × ℂ) E :=
  λ n, (finset.range (n+1)).sum (λ n0, term_cmmap ℂ n n0 (series2_coeff h n0 (n - n0)))

-- series2 is (roughly) geometrically bounded
lemma series2_norm (h : sep f c0 c1 r b s) (n : ℕ) : ∥series2 h n∥ ≤ (n+1) * b * r⁻¹^n := begin
  rw series2, simp,
  have tb : ∀ n0, n0 ∈ finset.range (n+1) → ∥term_cmmap ℂ n n0 (series2_coeff h n0 (n-n0))∥ ≤ b * r⁻¹^n, {
    intros n0 n0n, simp at n0n,
    apply trans (term_cmmap_norm ℂ n n0 (series2_coeff h n0 (n-n0))),
    have sb := series2_coeff_bound h n0 (n-n0),
    rw [←nat.add_sub_assoc (nat.le_of_lt_succ n0n) n0, nat.add_sub_cancel_left] at sb,
    assumption
  },
  transitivity (finset.range (n+1)).sum (λ n0, ∥term_cmmap ℂ n n0 (series2_coeff h n0 (n-n0))∥), bound [norm_sum_le],
  transitivity (finset.range (n+1)).sum (λ _, b * r⁻¹^n), bound [finset.sum_le_sum, norm_smul_le], clear tb,
  rw finset.sum_const, simp, ring_nf
end

-- series2 converges within radius r
lemma cauchy2_radius (h : sep f c0 c1 r b s) : ennreal.of_real r ≤ (series2 h).radius := begin
  apply ennreal.le_of_forall_nnreal_lt,
  intros t tr,
  rw ←ennreal.to_real_lt_to_real (@ennreal.coe_ne_top t) (@ennreal.of_real_ne_top r) at tr,
  rw [ennreal.coe_to_real, ennreal.to_real_of_real (le_of_lt h.rp)] at tr,
  apply formal_multilinear_series.le_radius_of_summable_nnnorm,
  simp_rw [←norm_to_nnreal, ←nnreal.summable_coe], simp,
  have lo : ∀ n : ℕ, 0 ≤ ∥series2 h n∥ * ↑t^n, { intro, bound },
  have hi : ∀ n : ℕ, ∥series2 h n∥ * ↑t^n ≤ (n+1) * b * (t/r)^n, {
    intro n,
    transitivity (↑n+1) * b * r⁻¹^n * ↑t^n, { bound [series2_norm h n] },
    rw [mul_assoc ((↑n+1) * b) _ _, ←mul_pow, inv_mul_eq_div]
  },
  refine summable_of_nonneg_of_le lo hi _,
  simp_rw [mul_comm _ b, mul_assoc b _ _], apply summable.mul_left b,
  have trn : ∥↑t / r∥ < 1, { simp, rw [abs_of_pos h.rp, div_lt_one h.rp], assumption },
  simp_rw [right_distrib _ _ _, one_mul], 
  exact summable.add (has_sum_coe_mul_geometric_of_norm_lt_1 trn).summable (has_sum_geometric_of_norm_lt_1 trn).summable
end

-- The 2D series converges to f
lemma cauchy2_has_sum_2d (h : sep f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (w1m : w1 ∈ ball (0 : ℂ) r)
    : has_sum (λ n : ℕ × ℕ, w0^n.snd • w1^n.fst • series2_coeff h n.snd n.fst) (f (c0 + w0, c1 + w1)) := begin
  generalize ha : f (c0 + w0, c1 + w1) = a,
  generalize hf : (λ n : ℕ × ℕ, w0^n.snd • w1^n.fst • series2_coeff h n.snd n.fst) = f,
  generalize hg : (λ n1 : ℕ, w1^n1 • series2_coeff_n0_sum h n1 w0) = g,
  generalize ha' : ∑' n, f n = a',
  have gs : has_sum g a, { rw [←hg, ←ha], exact cauchy2_has_sum_n1n0 h w0m w1m },
  have fs : ∀ n1 : ℕ, has_sum (λ n0, f ⟨n1, n0⟩) (g n1), {
    intro n1, rw [←hf, ←hg], simp, simp_rw smul_comm (w0^_) _, apply has_sum.const_smul, exact cauchy2_has_sum_n0 h w0m w1m n1
  },
  have fb : ∀ n : ℕ × ℕ, ∥f n∥ ≤ b * (abs w0 / r)^n.snd * (abs w1 / r)^n.fst, {
    intro n, rw ←hf, simp,
    rw [norm_smul, norm_smul, mul_assoc], rw [complex.norm_eq_abs, complex.norm_eq_abs, ←mul_assoc], simp,
    transitivity abs w0^n.snd * abs w1^n.fst * (b * r⁻¹ ^ (n.snd + n.fst)), bound [series2_coeff_bound h n.snd n.fst],
    rw [pow_add, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow], ring_nf
  },
  have sf : summable f, {
    simp at w0m w1m,
    refine summable_of_norm_bounded _ _ fb,
    simp_rw mul_assoc, apply summable.mul_left, simp_rw mul_comm ((abs w0/r)^_) _,
    apply summable.mul_of_nonneg,
    exact summable_geometric_of_lt_1 (by bound [h.rp]) ((div_lt_one h.rp).mpr w1m),
    exact summable_geometric_of_lt_1 (by bound [h.rp]) ((div_lt_one h.rp).mpr w0m),
    intro n, bound [h.rp],
    intro n, bound [h.rp]
  },
  have fs' : has_sum f a', { rw ←ha', exact sf.has_sum },
  have gs' := has_sum.prod_fiberwise fs' fs, simp at gs',
  rw has_sum.unique gs gs',
  assumption
end

-- 2D sum to 1D+antidiagonal sum
lemma has_sum.antidiagonal_of_2d {f : ℕ × ℕ → E} {a : E} (h : has_sum f a)
    : has_sum (λ n, (finset.range (n+1)).sum (λ n1, f (n1,n-n1))) a := begin
  generalize hg : (λ n, (finset.range (n+1)).sum (λ n1, f (n1,n-n1))) = g,
  rw ←finset.nat.sigma_antidiagonal_equiv_prod.has_sum_iff at h,
  have fg : ∀ n, has_sum (λ d : finset.nat.antidiagonal n, (f ∘ finset.nat.sigma_antidiagonal_equiv_prod) ⟨n, d⟩) (g n), {
    intro n, simp,
    have fs := has_sum_fintype (λ d : ↥(finset.nat.antidiagonal n), f ↑d), -- simp at fs,
    have e : finset.univ.sum (λ d : ↥(finset.nat.antidiagonal n), f ↑d) = g n, {
      rw [finset.sum_coe_sort, finset.nat.sum_antidiagonal_eq_sum_range_succ_mk, ←hg],
    },
    rwa ←e
  },
  exact has_sum.sigma h fg
end

-- finset.sums depend only on function values within the set
lemma finset.sum_eq_of_eq_on {A B : Type} [decidable_eq A] [add_comm_monoid B] {s : finset A} {f g : A → B}
    (h : ∀ a, a ∈ s → f a = g a) : s.sum f = s.sum g := begin
  induction s using finset.induction with n t nt ht, simp,
  rw [finset.sum_insert nt, finset.sum_insert nt],
  rw [h n (finset.mem_insert_self n t), ht (λ a ta, h a (finset.mem_insert_of_mem ta))]
end

-- series2 converges to f
lemma cauchy2_has_sum (h : sep f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (w1m : w1 ∈ ball (0 : ℂ) r)
    : has_sum (λ n, series2 h n (λ _ : fin n, (w0,w1))) (f (c0 + w0, c1 + w1)) := begin
  have sum := (cauchy2_has_sum_2d h w0m w1m).antidiagonal_of_2d, simp at sum,
  generalize ha : f (c0 + w0, c1 + w1) = a, rw ha at sum, clear ha,
  have e : (λ n, (finset.range (n+1)).sum (λ n1, w0^(n-n1) • w1^n1 • series2_coeff h (n-n1) n1))
         = (λ n, series2 h n (λ _ : fin n, (w0, w1))), {
    clear sum, apply funext, intro n,
    rw series2, simp, simp_rw term_cmmap_apply,
    nth_rewrite 0 ←finset.sum_range_reflect, simp,
    apply finset.sum_eq_of_eq_on,
    intros n0 n0n', simp at n0n',
    have n0n := nat.le_of_lt_succ n0n',
    rw [nat.sub_sub_self n0n, min_eq_left n0n]
  },
  rwa ←e
end

-- Osgood's lemma on a cball: f is jointly analytic
lemma osgood_h (h : sep f c0 c1 r b s) : has_fpower_series_on_ball f (series2 h) (c0,c1) (ennreal.of_real r) := {
  r_le := cauchy2_radius h,
  r_pos := begin simp, exact h.rp end,
  has_sum := begin
    simp, intros w0 w1 wr, rw prod.norm_def at wr, simp at wr,
    have w0m : w0 ∈ ball (0 : ℂ) r, { simp, exact wr.left },
    have w1m : w1 ∈ ball (0 : ℂ) r, { simp, exact wr.right },
    exact cauchy2_has_sum h w0m w1m
  end
}

end osgood

-- Osgood's lemma: if f is separately analytic on an open set, it is jointly analytic on that set
theorem osgood {E : Type} {f : ℂ × ℂ → E} {s : set (ℂ × ℂ)} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    (o : is_open s) (fc : continuous_on f s)
    (fa0 : ∀ z0 z1 : ℂ, (z0,z1) ∈ s → analytic_at ℂ (λ z0, f (z0,z1)) z0)
    (fa1 : ∀ z0 z1 : ℂ, (z0,z1) ∈ s → analytic_at ℂ (λ z1, f (z0,z1)) z1)
    : analytic_on ℂ f s := begin
  intros c cs,
  rcases metric.is_open_iff.mp o c cs with ⟨r,rp,rs⟩,
  have rs : closed_ball c (r/2) ⊆ s := trans (metric.closed_ball_subset_ball (by bound)) rs,
  rcases (continuous_on.mono fc rs).bounded_norm (is_compact_closed_ball _ _) with ⟨b,bp,bh⟩,
  have h : sep f c.fst c.snd (r/2) b s := {
    rp := by bound, so := o, rs := rs, fc := fc, fa0 := fa0, fa1 := fa1, bp := bp,
    fb := λ z0 z1 z0m z1m, bh (z0,z1) (spheres_subset_closed_ball (set.mk_mem_prod z0m z1m)),
  },
  have a := (osgood_h h).analytic_at,
  simp at a, assumption
end

-- f : ℂ × ℂ → ℂ is differentiable iff it is analytic
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
  }
end