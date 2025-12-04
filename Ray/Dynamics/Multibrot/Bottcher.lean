import Mathlib.Analysis.Complex.RealDeriv
import Ray.Dynamics.Multibrot.Postcritical
import Ray.Dynamics.Multibrot.RealBounds

/-!
## Effective bounds on the Multibrot `bottcher` function

We derive effective bounds and estimates for the Böttcher coordinates of the Multibrot sets.  These
are used in `Isomorphism.lean` and `Connected.lean` to prove our main theoretical results.

We mainly need that our diagonal Böttcher `bottcher d c` is analytic with derivative 1 at `∞`,
by showing that the analytically continued map is given by the infinite product for large `c`.
This does not follow immediately from our dynamical work, which covers only finite `c : ℂ`.  I'm
uneasy that I've missed some basic conceptual arguments that would get to the analyticity result
more directly, though the effective calculations we did along the way are also useful for numerics.

Our main results are:

1. If `16 < abs c ≤ abs z`, `s.bottcher = bottcherNear`, and thus the infinite produce holds.
2. If `16 < abs c ≤ abs z`, `abs (s.bottcher c z - z⁻¹) ≤ 16 * (abs z)⁻¹^2`
3. `bottcher d` is monic at `∞` (has derivative 1 there)
-/

open Complex
open Function (uncurry)
open Filter (Tendsto)
open Metric (closedBall mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint Real RiemannSphere Topology
noncomputable section

variable {c z : ℂ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `z⁻¹` is in the `superNearC` region for large `c,z` -/
theorem inv_mem_t (c3 : 3 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖) : z⁻¹ ∈ superNearT d c := by
  simp only [mem_setOf, norm_inv, superNearT, one_div]
  refine ⟨by bound, ?_⟩
  calc ‖c‖ * ‖z‖⁻¹ ^ d
    _ ≤ ‖c‖ * ‖z‖⁻¹ ^ 2 := by bound
    _ ≤ ‖c‖ * ‖c‖⁻¹ ^ 2 := by bound
    _ = ‖c‖⁻¹ := by grind
    _ < 3⁻¹ := by bound
    _ < 2 / 5 := by norm_num

/-- `s.bottcher = bottcherNear` for large `c,z`.
    This means that `s.bottcher` is given by the infinite product formula from `BottcherNear.lean`
    for large `c,z`. -/
theorem bottcher_eq_bottcherNear_z (c4 : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    (superF d).bottcher c z = bottcherNear (fl (f d) ∞ c) d z⁻¹ := by
  have c0 : 0 < ‖c‖ := by linarith
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le c0 cz
  set s := superF d
  set t := closedBall (0 : ℂ) (‖c‖)⁻¹
  suffices e : EqOn (fun z : ℂ ↦ s.bottcher c (z : 𝕊)⁻¹) (bottcherNear (fl (f d) ∞ c) d) t by
    have z0' : z ≠ 0 := norm_ne_zero_iff.mp z0.ne'
    convert @e z⁻¹ _; rw [inv_coe (inv_ne_zero z0'), inv_inv]
    simp only [mem_closedBall, Complex.dist_eq, sub_zero, norm_inv, inv_le_inv₀ z0 c0, cz, t]
  have a0 : ContMDiffOnNhd I I (fun z : ℂ ↦ s.bottcher c (z : 𝕊)⁻¹) t := by
    intro z m
    refine (s.bottcher_mAnalyticOn _ ?_).along_snd.comp _ (mAnalytic_inv.comp mAnalytic_coe _)
    simp only [mem_closedBall, Complex.dist_eq, sub_zero, t] at m
    by_cases z0 : z = 0; simp only [z0, coe_zero, inv_zero']; exact s.post_a c
    rw [inv_coe z0]; refine postcritical_large (by linarith) ?_
    rwa [norm_inv, le_inv_comm₀ c0]; exact norm_pos_iff.mpr z0
  have a1 : ContMDiffOnNhd I I (bottcherNear (fl (f d) ∞ c) d) t := by
    intro z m; apply AnalyticAt.mAnalyticAt
    apply bottcherNear_analytic_z (superNearF d c)
    simp only [mem_closedBall, Complex.dist_eq, sub_zero, t] at m ⊢
    by_cases z0 : z = 0
    · simp [z0, superNearT, zero_pow (d_ne_zero d)]
    rw [← inv_inv z]
    apply inv_mem_t (by linarith)
    rwa [norm_inv, le_inv_comm₀ c0 (norm_pos_iff.mpr z0)]
  refine (a0.eq_of_locally_eq a1 (convex_closedBall _ _).isPreconnected ?_).self_of_nhdsSet
  use 0, mem_closedBall_self (by bound)
  have e : ∀ᶠ z in 𝓝 0, bottcherNear (fl (f d) ∞ c) d z = s.bottcherNear c (z : 𝕊)⁻¹ := by
    simp only [Super.bottcherNear, extChartAt_inf_apply, inv_inv, toComplex_coe,
      RiemannSphere.inv_inf, toComplex_zero, sub_zero, Super.fl, Filter.eventually_true]
  refine Filter.EventuallyEq.trans ?_ (Filter.EventuallyEq.symm e)
  have i : Tendsto (fun z : ℂ ↦ (z : 𝕊)⁻¹) (𝓝 0) (𝓝 ∞) := by
    have h : ContinuousAt (fun z : ℂ ↦ (z : 𝕊)⁻¹) 0 :=
      (RiemannSphere.continuous_inv.comp continuous_coe).continuousAt
    simp only [ContinuousAt, coe_zero, inv_zero'] at h; exact h
  exact i.eventually (s.bottcher_eq_bottcherNear c)

/-- `bottcher' = bottcherNear` for large `c` -/
theorem bottcher_eq_bottcherNear (c4 : 4 ≤ ‖c‖) :
    bottcher' d c = bottcherNear (fl (f d) ∞ c) d c⁻¹ :=
  bottcher_eq_bottcherNear_z c4 (le_refl _)

/-- Rule out the negative real axis via smallness -/
lemma arg_ne_pi_of_small (z1 : ‖z‖ ≤ 1) : arg (1 + z) ≠ π := by
  refine (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt ?_ (half_lt_self Real.pi_pos))).ne
  rw [Complex.abs_arg_le_pi_div_two_iff, Complex.add_re, Complex.one_re]
  calc 1 + z.re
    _ ≥ 1 + -|z.re| := by bound
    _ = 1 - |z.re| := by ring
    _ ≥ 1 - ‖z‖ := by bound
    _ ≥ 0 := by linarith

/-- Terms in the `bottcherNear` product are close to 1 -/
theorem term_approx (d : ℕ) [Fact (2 ≤ d)] (c3 : 3 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ 2 * 2⁻¹ ^ n * ‖z‖⁻¹ := by
  set s := superF d
  simp only [term]
  have wc := iterates_converge (superNearF d c) n (inv_mem_t (by bound) cz)
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w at wc
  replace wc : ‖w‖ ≤ ‖z‖⁻¹ := by rw [norm_inv] at wc; exact le_trans wc (by bound)
  have cw : ‖c * w ^ d‖ ≤ ‖z‖⁻¹ := by
    simp only [norm_mul, norm_pow]
    calc ‖c‖ * ‖w‖ ^ d
      _ ≤ ‖z‖ * ‖z‖⁻¹ ^ d := by bound
      _ ≤ ‖z‖ * ‖z‖⁻¹ ^ 2 := by bound
      _ = ‖z‖⁻¹ := by rw [pow_two]; field_simp
  have cw2 : ‖c * w ^ d‖ ≤ 2⁻¹ := by
    have i3 : ‖z‖⁻¹ ≤ 3⁻¹ := by bound
    linarith
  simp only [gl_f, gl]
  rw [Complex.inv_cpow _ _ (arg_ne_pi_of_small (by linarith)), ← Complex.cpow_neg]
  have dn : ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by simp; bound
  have d1 : ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖ ≤ 1 := le_trans dn (by bound)
  refine le_trans (pow_small ?_ d1) ?_
  · simp only [add_sub_cancel_left, one_div, cw2]
  · rw [add_sub_cancel_left]
    calc 4 * ‖c * w ^ d‖ * ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖
      _ ≤ 4 * ‖z‖⁻¹ * 2⁻¹ ^ (n + 1) := by bound
      _ ≤ 2 * 2⁻¹ ^ n * ‖z‖⁻¹ := by
        simp only [pow_succ, ← mul_assoc, mul_comm _ (2⁻¹ : ℝ)]
        ring_nf
        rfl

/-- Tight version of `term_approx`, with the bound depending on `‖c‖, ‖z‖` -/
lemma term_approx_tight_cz (d : ℕ) [Fact (2 ≤ d)] (c3 : 3 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤
      (1 - ‖c‖ * ((fb d ‖c‖)^[n] ‖z‖⁻¹) ^ d) ^ (-1 / d ^ (n + 1) : ℝ) - 1 := by
  set s := superF d
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w
  simp only [term, gl_f, gl, hw]
  simp only [fl_f] at hw
  have ci3 : ‖c‖⁻¹ ≤ 3⁻¹ := by bound
  have zc : ‖z‖⁻¹ ≤ ‖c‖⁻¹ := by bound
  have le := hw ▸ f_le_fb d c z c3.le cz n
  obtain ⟨y0,y3⟩ := fb_nonneg_le d ‖c‖ ‖z‖ c3.le cz n
  generalize hy : (fb d ‖c‖)^[n] ‖z‖⁻¹ = y at le y0 y3
  rw [Complex.inv_cpow, ← Complex.cpow_neg, neg_div', Nat.cast_pow]
  · generalize hp : (-1 / d ^ (n + 1) : ℝ) = p
    have hp' : (-1 / d ^ (n + 1) : ℂ) = p := by simp [← hp]
    simp only [hp']
    have p0 : p ≤ 0 := by bound
    refine le_trans (Complex.norm_one_add_cpow_sub_one_le_rpow_sub_one ?_ p0) ?_
    · simp
      bound
    · simp only [Complex.norm_mul, norm_pow, tsub_le_iff_right, sub_add_cancel]
      exact Real.rpow_le_rpow_of_nonpos (by bound) (by bound) p0
  · apply arg_ne_pi_of_small
    simp
    bound

/-- Tight version of `term_approx`, with the bound depending only on a `c, z` lower bound `b` -/
lemma term_approx_tight (d : ℕ) [Fact (2 ≤ d)] (b : ℝ) (b3 : 3 < b) (bc : b ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖)
    (n : ℕ) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤
      (1 - b * ((fb d b)^[n] b⁻¹) ^ d) ^ (-1 / d ^ (n + 1) : ℝ) - 1 := by
  refine le_trans (term_approx_tight_cz d (by linarith) cz n) (sub_le_sub_right ?_ _)
  refine Real.rpow_le_rpow_of_nonpos (by bound) (sub_le_sub_left ?_ _) (by bound)
  grw [fb_mono_z d ‖c‖ ‖z‖ (by linarith) cz n]
  all_goals bound

/-- Constant version of `term_approx_tight`, based on computable bounds -/
lemma term_approx_const {d n : ℕ} [Fact (2 ≤ d)] {b t : ℝ}
    (bc : b ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) (b3 : 3 < b := by norm_num) (t0 : 0 < t := by norm_num)
    (crunch : (t + 1) ^ (-2 ^ (n + 1) : ℤ) ≤ 1 - b * (fb 2 b)^[n] b⁻¹ ^ 2 := by norm_num [fb]) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ t := by
  refine le_trans (term_approx_tight d b b3 bc cz n) ?_
  rw [sub_le_iff_le_add, ← Real.rpow_inv_le_iff_of_neg (by linarith) (by bound) (by bound), inv_div,
    div_neg, div_one]
  refine le_trans ?_ (le_trans crunch (by bound))
  rw [← Real.rpow_intCast, Int.cast_neg, Int.cast_pow, Int.cast_two]
  bound

-- Weak `term` bounds for `4 ≤ ‖c‖ ≤ ‖z‖`
lemma term_approx_4_0 (d : ℕ) [Fact (2 ≤ d)] (bc : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.1548 := term_approx_const bc cz
lemma term_approx_4_1 (d : ℕ) [Fact (2 ≤ d)] (bc : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 1 z⁻¹ - 1‖ ≤ 0.0071 := term_approx_const bc cz
lemma term_approx_4_2 (d : ℕ) [Fact (2 ≤ d)] (bc : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 2 z⁻¹ - 1‖ ≤ 0.00003 := term_approx_const bc cz
lemma term_approx_4_3 (d : ℕ) [Fact (2 ≤ d)] (bc : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 3 z⁻¹ - 1‖ ≤ 0.00001 := term_approx_const bc cz

-- Weak `term` bounds for `5 ≤ ‖c‖ ≤ ‖z‖`
lemma term_approx_5_0 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.1181 := term_approx_const bc cz
lemma term_approx_5_1 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 1 z⁻¹ - 1‖ ≤ 0.0032 := term_approx_const bc cz
lemma term_approx_5_2 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 2 z⁻¹ - 1‖ ≤ 0.00001 := term_approx_const bc cz
lemma term_approx_5_3 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 3 z⁻¹ - 1‖ ≤ 0.00001 := term_approx_const bc cz

/-- Monomial version of `term_approx_tight`, based on computable bounds -/
lemma term_approx_pow {d n : ℕ} [Fact (2 ≤ d)] {b t zp : ℝ} {c z : ℂ} (bc : b ≤ ‖c‖)
    (cz : ‖c‖ ≤ ‖z‖) (t0 : 0 < t := by norm_num) (b3 : 3 < b := by norm_num)
    (crunch : ((t / b ^ (2 ^ (n + 1) - 1) + 1) ^ 2 ^ (n + 1))⁻¹ ≤ 1 - b * (fb 2 b)^[n] b⁻¹ ^ 2 := by
      norm_num [fb, factor])
    (zpn : zp = ‖z‖⁻¹ ^ (2 ^ (n + 1) - 1) := by simp) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ t * zp := by
  simp only [zpn]
  refine le_trans (term_approx_tight_cz d (by linarith) cz n) ?_
  refine le_trans (term_mono_d d b3.le bc cz n) ?_
  refine le_trans (Real.one_sub_rpow_neg_sub_one_le_linear (y := b * (fb 2 b)^[n] b⁻¹ ^ 2)
    (by bound) ?_ (by bound) (by bound)) ?_
  · apply fb_mono_cz_strong 2 b3.le bc cz
  · refine le_trans (mul_le_mul_of_nonneg_left (fb_le_factor 2 b3.le bc cz n) (by bound)) ?_
    simp only [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (by bound)
    rw [← le_div_iff₀ (by bound), div_le_iff₀ (by bound), sub_le_iff_le_add]
    have e : (2 : ℝ) ^ (n + 1) = (2 ^ (n + 1) : ℕ) := by simp
    rw [neg_div, one_div, neg_inv, Real.rpow_inv_le_iff_of_neg (by bound) (by bound) (by bound),
      Real.rpow_neg (by bound), e, Real.rpow_natCast]
    rw [factor_eq_div (by positivity)]
    simp only [inv_pow, div_eq_mul_inv, inv_inv, mul_pow, mul_inv, ← pow_mul, ← pow_succ]
    generalize hu : (fb 2 b)^[n] b⁻¹ ^ 2 = u at crunch
    have b0 : 0 < b := by bound
    have u0 : 0 < u := by bound
    simp only [← mul_assoc, mul_comm _ u]
    simp only [← mul_assoc, mul_comm _ u⁻¹, inv_mul_cancel₀ u0.ne', one_mul]
    rw [pow_sub₀ _ b0.ne' (by bound), pow_one, div_eq_mul_inv, mul_inv, inv_inv, ← mul_assoc,
      mul_comm _ u] at crunch
    exact crunch

-- Strong `term` bounds for `4 ≤ ‖c‖ ≤ ‖z‖`
def term_bounds_4 (z : ℂ) : Fin 6 → ℝ :=
  ![0.619 * ‖z‖⁻¹, 0.453 * ‖z‖⁻¹ ^ 3, 0.419 * ‖z‖⁻¹ ^ 7, 0.700 * ‖z‖⁻¹ ^ 15, 3.91 * ‖z‖⁻¹ ^ 31,
    245 * ‖z‖⁻¹ ^ 63]
lemma term_approx_pow_4 (d : ℕ) [Fact (2 ≤ d)] (bc : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) (n : Fin 6) :
    ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ term_bounds_4 z n := by
  fin_cases n <;> exact term_approx_pow bc cz

-- Strong `term` bounds for `5 ≤ ‖c‖ ≤ ‖z‖`
lemma term_approx_pow_5_0 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 0 z⁻¹ - 1‖ ≤ 0.591 * ‖z‖⁻¹ := term_approx_pow bc cz
lemma term_approx_pow_5_1 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 1 z⁻¹ - 1‖ ≤ 0.394 * ‖z‖⁻¹ ^ 3 := term_approx_pow bc cz
lemma term_approx_pow_5_2 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 2 z⁻¹ - 1‖ ≤ 0.313 * ‖z‖⁻¹ ^ 7 := term_approx_pow bc cz
lemma term_approx_pow_5_3 (d : ℕ) [Fact (2 ≤ d)] (bc : 5 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖term (fl (f d) ∞ c) d 3 z⁻¹ - 1‖ ≤ 0.392 * ‖z‖⁻¹ ^ 15 := term_approx_pow bc cz

/-- `s.bottcher c z = z⁻¹ + O(z⁻¹ ^ 2)` -/
theorem bottcher_approx_z (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c4 : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖(superF d).bottcher c z - z⁻¹‖ ≤ 0.943 * ‖z‖⁻¹ ^ 2 := by
  set s := superF d
  have z4 : ‖z‖⁻¹ ≤ 4⁻¹ := by bound
  simp only [bottcher_eq_bottcherNear_z c4 cz, bottcherNear, norm_mul, ← mul_sub_one,
    pow_two, ← mul_assoc, norm_inv, mul_comm ‖z‖⁻¹]
  refine mul_le_mul_of_nonneg_right ?_ (by bound)
  obtain ⟨p, h⟩ := term_prod_exists (superNearF d c) _ (inv_mem_t (by linarith) cz)
  rw [h.tprod_eq]
  refine le_trans (h.norm_sub_one_le (term_approx_pow_4 d c4 cz) (c := 2 * ‖z‖⁻¹) (a := 2⁻¹) ?_ ?_
    (by norm_num) (by norm_num) (by norm_num) ?_) ?_
  · exact fun _ _ ↦ le_trans (term_approx d (by linarith) cz _) (le_of_eq (by ring))
  · intro k
    fin_cases k <;> simp only [term_bounds_4] <;> bound
  · ring_nf
    linarith
  · simp only [term_bounds_4, Finset.prod_fin_eq_prod_range, Finset.prod_range_succ,
      Finset.range_one, Finset.prod_singleton, Nat.ofNat_pos, ↓reduceDIte, Fin.zero_eta, Fin.isValue,
      Matrix.cons_val_zero, Nat.one_lt_ofNat, Fin.mk_one, Matrix.cons_val_one, Nat.reduceLT,
      Fin.reduceFinMk, Matrix.cons_val, Nat.lt_add_one, tsub_le_iff_right]
    have z0 : 0 < ‖z‖⁻¹ := by bound
    generalize ‖z‖⁻¹ = x at z0 z4
    clear z cz h
    have pow : ∀ k : Fin 122, x ^ (k + 1 : ℕ) ≤ 4⁻¹ ^ (k : ℕ) * x := by
      intro k; simp only [pow_succ]; bound
    simp only [inv_pow, Fin.forall_iff_castSucc, Fin.reduceLast, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
      Nat.reduceAdd, Fin.coe_castSucc, pow_one, Fin.val_eq_zero, zero_add, pow_zero, inv_one,
      one_mul, le_refl, implies_true, and_true] at pow
    ring_nf
    linarith

/-- `bottcher' d c = c⁻¹ + O(c⁻¹^2)` -/
theorem bottcher_approx (d : ℕ) [Fact (2 ≤ d)] (c4 : 4 ≤ ‖c‖) :
    ‖bottcher' d c - c⁻¹‖ ≤ 0.943 * ‖c‖⁻¹ ^ 2 :=
  bottcher_approx_z d c4 (le_refl _)

/-- `bottcher` near `∞` as an analytic `ℂ → ℂ` function -/
def bottcher_inv (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ :=
  fun z ↦ bottcher d (↑z)⁻¹

lemma bottcher_inv_def : bottcher_inv d = fun z : ℂ ↦ bottcher d (↑z)⁻¹ := rfl

@[simp] lemma bottcher_inv_zero : bottcher_inv d 0 = 0 := by
  simp only [bottcher_inv, coe_zero, inv_zero', bottcher_inf]

/-- bottcher is monic at `∞` (has derivative 1) -/
theorem bottcher_hasDerivAt_one : HasDerivAt (bottcher_inv d) 1 0 := by
  rw [HasDerivAt, HasDerivAtFilter, bottcher_inv_def, bottcher, hasFDerivAtFilter_iff_isLittleO,
    coe_zero, inv_zero', fill_inf]
  simp only [sub_zero, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, mul_one]
  rw [Asymptotics.isLittleO_iff]
  intro k k0; rw [Metric.eventually_nhds_iff]
  refine ⟨min 16⁻¹ (k / 16), by bound, ?_⟩; intro z le
  simp only [dist_eq_norm, sub_zero, lt_min_iff] at le
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', fill_inf, sub_zero, norm_zero,
      MulZeroClass.mul_zero, le_refl]
  simp only [inv_coe z0, fill_coe]
  have b := bottcher_approx d (c := z⁻¹) ?_
  · simp only [inv_inv] at b; apply le_trans b
    simp only [norm_inv, inv_inv, pow_two, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc 0.943 * ‖z‖
      _ ≤ 16 * (k / 16) := by linarith [le.2]
      _ = k := by ring
  · rw [norm_inv, le_inv_comm₀ (by norm_num) (norm_pos_iff.mpr z0)]
    linarith

/-- bottcher is nonsingular at `∞` -/
theorem bottcher_mfderiv_inf_ne_zero : mfderiv I I (bottcher d) ∞ ≠ 0 := by
  simp only [mfderiv, (bottcherMAnalytic d _ multibrotExt_inf).mdifferentiableAt le_top, if_pos,
    writtenInExtChartAt, bottcher_inf, extChartAt_inf, extChartAt_eq_refl, Function.comp_def,
    PartialEquiv.refl_coe, id, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
    RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, PartialEquiv.coe_trans_symm,
    PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm,
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  rw [← bottcher_inv_def, bottcher_hasDerivAt_one.hasFDerivAt.fderiv]
  rw [Ne, ContinuousLinearMap.ext_iff, not_forall]; use 1
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    Algebra.id.smul_eq_mul, mul_one]
  convert one_ne_zero; exact NeZero.one
