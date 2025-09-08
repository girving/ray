import Ray.Dynamics.Multibrot.Postcritical

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
open Filter (Tendsto)
open Metric (closedBall mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `s.bottcher = bottcherNear` for large `c,z`.
    This means that `s.bottcher` is given by the infinite product formula from `BottcherNear.lean`
    for large `c,z`. -/
theorem bottcher_eq_bottcherNear_z {c z : ℂ} (c16 : 16 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    (superF d).bottcher c z = bottcherNear (fl (f d) ∞ c) d z⁻¹ := by
  have c0 : 0 < ‖c‖ := lt_trans (by norm_num) c16
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
    simp only [mem_setOf, mem_closedBall, Complex.dist_eq, sub_zero, t] at m ⊢
    refine lt_of_le_of_lt m ?_
    refine inv_strictAnti₀ (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) ?_
    exact max_lt c16 (half_lt_self (lt_trans (by norm_num) c16))
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
theorem bottcher_eq_bottcherNear {c : ℂ} (c16 : 16 < ‖c‖) :
    bottcher' d c = bottcherNear (fl (f d) ∞ c) d c⁻¹ :=
  bottcher_eq_bottcherNear_z c16 (le_refl _)

/-- `z⁻¹` is in the `superNearC` region for large `c,z` -/
theorem inv_mem_t {c z : ℂ} (c16 : 16 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    z⁻¹ ∈ {z : ℂ | ‖z‖ < (max 16 (‖c‖ / 2))⁻¹} := by
  simp only [mem_setOf, norm_inv]
  refine inv_strictAnti₀ (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) ?_
  exact lt_of_lt_of_le (max_lt c16 (half_lt_self (lt_trans (by norm_num) c16))) cz

/-- Terms in the `bottcherNear` product are close to 1 -/
theorem term_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c16 : 16 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖)
    (n : ℕ) : ‖term (fl (f d) ∞ c) d n z⁻¹ - 1‖ ≤ 2 * (1 / 2 : ℝ) ^ n * ‖z‖⁻¹ := by
  set s := superF d
  have z0 : ‖z‖ ≠ 0 := (lt_of_lt_of_le (lt_trans (by norm_num) c16) cz).ne'
  have i8 : ‖z‖⁻¹ ≤ 1 / 8 := by
    rw [one_div]; apply inv_anti₀; norm_num
    exact le_trans (by norm_num) (le_trans c16.le cz)
  have i1 : ‖z‖⁻¹ ≤ 1 := le_trans i8 (by norm_num)
  simp only [term]
  have wc := iterates_converge (superNearF d c) n (inv_mem_t c16 cz)
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w; rw [hw] at wc
  replace wc : ‖w‖ ≤ ‖z‖⁻¹ := by
    rw [norm_inv] at wc
    exact le_trans wc (mul_le_of_le_one_left (inv_nonneg.mpr (norm_nonneg _)) (by bound))
  have cw : ‖c * w ^ d‖ ≤ ‖z‖⁻¹ := by
    simp only [norm_mul, norm_pow]
    calc ‖c‖ * ‖w‖ ^ d
      _ ≤ ‖z‖ * ‖z‖⁻¹ ^ d := by bound
      _ ≤ ‖z‖ * ‖z‖⁻¹ ^ 2 := by bound
      _ = ‖z‖⁻¹ := by rw [pow_two]; field_simp [z0]
  have cw2 : ‖c * w ^ d‖ ≤ 1 / 2 := le_trans cw (le_trans i8 (by norm_num))
  simp only [gl_f, gl]; rw [Complex.inv_cpow, ← Complex.cpow_neg]; swap
  · refine (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt ?_ (half_lt_self Real.pi_pos))).ne
    rw [Complex.abs_arg_le_pi_div_two_iff, Complex.add_re, Complex.one_re]
    calc 1 + (c * w ^ d).re
      _ ≥ 1 + -|(c * w ^ d).re| := by bound
      _ = 1 - |(c * w ^ d).re| := by ring
      _ ≥ 1 - ‖c * w ^ d‖ := by bound
      _ ≥ 1 - 1 / 2 := by linarith
      _ ≥ 0 := by norm_num
  · have dn : ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖ ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      simp only [Nat.cast_pow, one_div, norm_neg, norm_inv, norm_pow, Complex.norm_natCast, inv_pow]
      bound
    have d1 : ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖ ≤ 1 := le_trans dn (by bound)
    refine le_trans (pow_small ?_ d1) ?_
    · rw [add_sub_cancel_left]; exact cw2
    · rw [add_sub_cancel_left]
      calc 4 * ‖c * w ^ d‖ * ‖-(1 / ((d ^ (n + 1) : ℕ) : ℂ))‖
        _ ≤ 4 * ‖z‖⁻¹ * (1/2 : ℝ) ^ (n + 1) := by bound
        _ ≤ 2 * (1/2 : ℝ) ^ n * ‖z‖⁻¹ := by
          simp only [pow_succ, ←mul_assoc, mul_comm _ (1/2:ℝ)]
          ring_nf
          rfl

/-- `s.bottcher c z = z⁻¹ + O(z⁻¹^2)` -/
theorem bottcher_approx_z (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c16 : 16 < ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ‖(superF d).bottcher c z - z⁻¹‖ ≤ (16:ℝ) * ‖z‖⁻¹ ^ 2 := by
  set s := superF d
  have i8 : ‖z‖⁻¹ ≤ 1 / 8 := by
    rw [one_div]; apply inv_anti₀; norm_num
    exact le_trans (by norm_num) (le_trans c16.le cz)
  simp only [bottcher_eq_bottcherNear_z c16 cz, bottcherNear, norm_mul, ← mul_sub_one, pow_two,
    ← mul_assoc, norm_inv, mul_comm ‖z‖⁻¹]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
  rcases term_prod_exists (superNearF d c) _ (inv_mem_t c16 cz) with ⟨p, h⟩
  rw [h.tprod_eq]; simp only [HasProd] at h
  apply le_of_tendsto' (Filter.Tendsto.comp continuous_norm.continuousAt (h.sub_const 1))
  clear h; intro A; simp only [Function.comp_def]
  rw [(by norm_num : (16 : ℝ) = 4 * 4), mul_assoc]
  refine dist_prod_one_le_abs_sum ?_ (by linarith)
  refine le_trans (Finset.sum_le_sum fun n _ ↦ term_approx d (by linarith) cz n) ?_
  simp only [mul_comm _ _⁻¹, ← mul_assoc, ← Finset.mul_sum]
  calc ‖z‖⁻¹ * 2 * A.sum (fun n ↦ (1/2:ℝ)^n)
    _ ≤ ‖z‖⁻¹ * 2 * (1 - 1 / 2)⁻¹ := by gcongr; apply partial_geometric_bound; repeat norm_num
    _ = ‖z‖⁻¹ * 4 := by ring

/-- `bottcher' d c = c⁻¹ + O(c⁻¹^2)` -/
theorem bottcher_approx (d : ℕ) [Fact (2 ≤ d)] {c : ℂ} (c16 : 16 < ‖c‖) :
    ‖bottcher' d c - c⁻¹‖ ≤ 16 * ‖c‖⁻¹ ^ 2 :=
  bottcher_approx_z d c16 (le_refl _)

/-- bottcher is monic at `∞` (has derivative 1) -/
theorem bottcher_hasDerivAt_one : HasDerivAt (fun z : ℂ ↦ bottcher d (↑z)⁻¹) 1 0 := by
  rw [HasDerivAt, HasDerivAtFilter, bottcher, hasFDerivAtFilter_iff_isLittleO, coe_zero, inv_zero',
    fill_inf]
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
  have b : ‖bottcher' d z⁻¹ - z⁻¹⁻¹‖ ≤ (16:ℝ) * ‖z⁻¹‖⁻¹ ^ 2 := bottcher_approx d ?_
  · simp only [inv_inv] at b; apply le_trans b
    simp only [norm_inv, inv_inv, pow_two, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc 16 * ‖z‖
      _ ≤ 16 * (k / 16) := by linarith [le.2]
      _ = k := by ring
  · rw [norm_inv, lt_inv_comm₀ (by norm_num) (norm_pos_iff.mpr z0)]; exact le.1

/-- bottcher is nonsingular at `∞` -/
theorem bottcher_mfderiv_inf_ne_zero : mfderiv I I (bottcher d) ∞ ≠ 0 := by
  simp only [mfderiv, (bottcherMAnalytic d _ multibrotExt_inf).mdifferentiableAt le_top, if_pos,
    writtenInExtChartAt, bottcher_inf, extChartAt_inf, extChartAt_eq_refl, Function.comp_def,
    PartialEquiv.refl_coe, id, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
    RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, PartialEquiv.coe_trans_symm,
    PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm,
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  rw [bottcher_hasDerivAt_one.hasFDerivAt.fderiv]
  rw [Ne, ContinuousLinearMap.ext_iff, not_forall]; use 1
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    Algebra.id.smul_eq_mul, mul_one]
  convert one_ne_zero; exact NeZero.one
