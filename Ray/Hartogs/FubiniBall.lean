import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Ray.Misc.Measure
import Ray.Misc.Prod

/-!
## Fubini's theorem for integration over the complex closed disk

We rewrite integration over the closed disk in polar coordinates, so that we can relate
disk integrals to `intervalIntegral`s of `circleIntegral`s.

We extend the result for annuli as well, since we use that for the Koebe quarter theorem.
-/

open Complex (abs arg exp I)
open LinearMap (toMatrix_apply)
open MeasureTheory
open Metric (ball closedBall sphere)
open Real (cos sin)
open Set
open scoped Real
noncomputable section

section realCircleMap

/-- `circleMap` as a map from `ℝ² → ℝ²` -/
def realCircleMap (c : ℂ) (x : ℝ × ℝ) : ℝ × ℝ :=
  ⟨c.re + x.1 * cos x.2, c.im + x.1 * sin x.2⟩

lemma realCircleMap_eq_circleMap (c : ℂ) (x : ℝ × ℝ) :
    realCircleMap c x = Complex.equivRealProd (circleMap c x.1 x.2) := by
  simp only [realCircleMap, circleMap, Complex.equivRealProd_apply, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_im,
    zero_mul, sub_zero, Complex.add_im, Complex.mul_im, add_zero]

/-- Abbreviation for the `fst` continuous linear map -/
abbrev d1 := ContinuousLinearMap.fst ℝ ℝ ℝ
/-- Abbreviation for the `snd` continuous linear map -/
abbrev d2 := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The derivative of `realCircleMap` -/
def rcmDeriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (0 + (x.1 • -sin x.2 • d2 + cos x.2 • d1)).prod (0 + (x.1 • cos x.2 • d2 + sin x.2 • d1))

lemma realCircleMap.fderiv {c : ℂ} {x : ℝ × ℝ} :
    HasFDerivAt (fun x ↦ realCircleMap c x) (rcmDeriv x) x := by
  simp_rw [realCircleMap]
  apply_rules [hasFDerivAt_const, hasFDerivAt_fst, hasFDerivAt_snd, HasFDerivAt.cos,
    HasFDerivAt.sin, HasFDerivAt.add, HasFDerivAt.mul, HasFDerivAt.prod]

/-- The Jacobian matrix of `realCircleMap` -/
def rcmMatrix (x : ℝ × ℝ) :=
  LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) (rcmDeriv x)
lemma rcm00 (x : ℝ × ℝ) : rcmMatrix x 0 0 = cos x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]
lemma rcm01 (x : ℝ × ℝ) : rcmMatrix x 0 1 = -x.1 * sin x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]
lemma rcm10 (x : ℝ × ℝ) : rcmMatrix x 1 0 = sin x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]
lemma rcm11 (x : ℝ × ℝ) : rcmMatrix x 1 1 = x.1 * cos x.2 := by
  simp [rcmMatrix, rcmDeriv, toMatrix_apply, d1, d2]

/-- The Jacobian determinant of `realCircleMap` -/
lemma rcmDeriv.det (x : ℝ × ℝ) : (rcmDeriv x).det = x.1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), ←rcmMatrix]
  rw [Matrix.det_fin_two, rcm00, rcm01, rcm10, rcm11]; ring_nf
  calc cos x.2 ^ 2 * x.1 + x.1 * sin x.2 ^ 2
    _ = x.1 * (cos x.2 ^ 2 + sin x.2 ^ 2) := by ring
    _ = x.1 := by simp only [Real.cos_sq_add_sin_sq, mul_one]

end realCircleMap

/-- Spheres are empty iff the radius is negative -/
@[simp]
theorem Metric.sphere_eq_empty {S : Type} [RCLike S] {c : S} {r : ℝ} : sphere c r = ∅ ↔ r < 0 := by
  constructor
  · intro rp; contrapose rp; simp at rp
    refine Nonempty.ne_empty ⟨c + r, ?_⟩
    simpa only [mem_sphere_iff_norm, add_sub_cancel_left, RCLike.norm_ofReal, abs_eq_self]
  · intro n; contrapose n
    rw [← not_nonempty_iff_eq_empty] at n
    simpa only [not_lt, NormedSpace.sphere_nonempty, not_le] using n

attribute [bound] Int.ceil_lt_add_one

/-- `range (circleMap c r _) = sphere c r` even when restricted to `Ioc 0 (2π)` -/
theorem circleMap_Ioc {c z : ℂ} {r : ℝ} (zs : z ∈ sphere c r) :
    ∃ t, t ∈ Ioc 0 (2 * π) ∧ z = circleMap c r t := by
  by_cases rp : r < 0
  · simp only [Metric.sphere_eq_empty.mpr rp, mem_empty_iff_false] at zs
  simp only [not_lt] at rp
  rw [←abs_of_nonneg rp, ← range_circleMap, mem_range] at zs
  rcases zs with ⟨t, ht⟩
  generalize ha : 2 * π = a
  have ap : a > 0 := by rw [←ha]; bound
  generalize hs : t + a - a * ⌈t / a⌉ = s
  use s; constructor
  · simp only [mem_Ioc, sub_pos, tsub_le_iff_right, ← hs]
    constructor
    · calc a * ⌈t / a⌉
        _ < a * (t / a + 1) := by bound
        _ = a / a * t + a := by ring
        _ = t + a := by field_simp [ap.ne']
    · calc a + a * ⌈t / a⌉
        _ ≥ a + a * (t / a) := by bound
        _ = a / a * t + a := by ring
        _ = t + a := by field_simp [ap.ne']
  · simp only [←ht, circleMap, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
      Complex.ofReal_intCast, add_right_inj, mul_eq_mul_left_iff, Complex.ofReal_eq_zero, ← hs]
    rw [mul_sub_right_distrib, right_distrib, Complex.exp_sub, Complex.exp_add]
    rw [mul_comm _ (⌈_⌉:ℂ), mul_assoc, Complex.exp_int_mul, ← ha]
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I, mul_one,
      one_zpow, div_one, true_or]

section FubiniHelper

/-- The square that we'll map onto the ball -/
def square (r0 r1 : ℝ) : Set (ℝ × ℝ) :=
  Ioc r0 r1 ×ˢ Ioc 0 (2 * π)

theorem square.rp {r0 r1 : ℝ} {x : ℝ × ℝ} (r0p : 0 ≤ r0) : x ∈ square r0 r1 → 0 < x.1 := by
  simp only [square, gt_iff_lt, not_lt, ge_iff_le, zero_lt_two, mul_pos_iff_of_pos_left,
    mem_prod, mem_Ioc, and_imp]
  intro h _ _ _; linarith

theorem Measurable.square {r0 r1 : ℝ} : MeasurableSet (square r0 r1) := by
  apply_rules [MeasurableSet.prod, measurableSet_Ioc]

def annulus_oc (c : ℂ) (r0 r1 : ℝ) : Set ℂ := closedBall c r1 \ closedBall c r0
def annulus_cc (c : ℂ) (r0 r1 : ℝ) : Set ℂ := closedBall c r1 \ ball c r0

lemma annulus_oc_subset_annulus_cc {c : ℂ} {r0 r1 : ℝ} :
    annulus_oc c r0 r1 ⊆ annulus_cc c r0 r1 :=
  diff_subset_diff (subset_refl _) Metric.ball_subset_closedBall

theorem square_eq {c : ℂ} {r0 r1 : ℝ} (r0p : 0 ≤ r0) :
    Complex.measurableEquivRealProd.symm ⁻¹' (annulus_oc c r0 r1) =
      realCircleMap c '' square r0 r1 := by
  rw [← MeasurableEquiv.image_eq_preimage]
  have e : realCircleMap c =
      fun x : ℝ × ℝ ↦ Complex.measurableEquivRealProd (circleMap c x.1 x.2) := by
    funext
    simp only [realCircleMap_eq_circleMap, Complex.measurableEquivRealProd,
      Complex.equivRealProd_apply, Homeomorph.toMeasurableEquiv_coe,
      ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_apply]
  have i : (fun x : ℝ × ℝ ↦ circleMap c x.1 x.2) '' square r0 r1 = annulus_oc c r0 r1 := by
    ext z
    rw [mem_image]
    constructor
    · intro gp; rcases gp with ⟨⟨s, t⟩, ss, tz⟩
      simp only at tz
      simp only [square, prod_mk_mem_set_prod_eq, mem_Ioc] at ss
      rw [← tz]
      have s0 : 0 < s := by linarith
      simp only [circleMap, add_comm c, annulus_oc, mem_diff, Metric.mem_closedBall,
        dist_add_self_left, norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal,
        Complex.abs_exp_ofReal_mul_I, mul_one, not_le, abs_of_pos s0, ss.1, true_and]
    · intro zr
      simp only [mem_diff, Metric.mem_closedBall, mem_singleton_iff, annulus_oc,
        not_le] at zr
      rw [dist_comm] at zr
      have zz : z ∈ sphere c (dist c z) := by
        simp only [Complex.dist_eq, mem_sphere_iff_norm, Complex.norm_eq_abs, Complex.abs.map_sub]
      rcases circleMap_Ioc zz with ⟨t, ts, tz⟩
      use (dist c z, t)
      simpa only [square, gt_iff_lt, not_lt, ge_iff_le, zero_lt_two, mul_pos_iff_of_pos_left,
        mem_prod, mem_Ioc, dist_pos, ne_eq, not_false_eq_true, zr, and_self, true_and,
        tz.symm, and_true] using ts
  have im := image_comp Complex.measurableEquivRealProd (fun x : ℝ × ℝ ↦ circleMap c x.1 x.2)
    (square r0 r1)
  simp only [Function.comp] at im
  simp only [e, im, i]

/-- `exp (t * I) = cos t + sin t * I` -/
theorem exp_of_im (t : ℝ) : exp (t * I) = cos t + sin t * I := by
  simp [Complex.ext_iff, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem Complex.cos_eq_cos (t : ℝ) : Complex.cos t = ↑(Real.cos t) := by simp

theorem Complex.sin_eq_sin (t : ℝ) : Complex.sin t = ↑(Real.sin t) := by simp

/-- The argument of `exp (t * I)` -/
theorem arg_exp_of_im (t : ℝ) : ∃ n : ℤ, arg (exp (t * I)) = t - 2 * π * n := by
  generalize hn : ⌈t / (2 * π) - 1 / 2⌉ = n; exists n
  have en : exp (2 * π * n * I) = 1 := by
    rw [mul_comm _ (n:ℂ), mul_assoc, Complex.exp_int_mul]
    simp only [Complex.exp_two_pi_mul_I, one_zpow]
  have e : exp (t * I) = exp (↑(t - 2 * π * n) * I) := by
    simp [mul_sub_right_distrib, Complex.exp_sub, en]
  have ts : t - 2 * π * n ∈ Ioc (-π) π := by
    simp only [mem_Ioc, neg_lt_sub_iff_lt_add, tsub_le_iff_right]
    constructor
    · have h : ↑n < t * (2 * π)⁻¹ - 1 / 2 + 1 := by rw [← hn]; exact Int.ceil_lt_add_one _
      calc 2 * π * ↑n
        _ < 2 * π * (t * (2 * π)⁻¹ - 1 / 2 + 1) := by bound
        _ = π + 2 * π * (2 * π)⁻¹ * t := by ring
        _ = π + t := by field_simp [Real.two_pi_pos.ne']
    · have h : ↑n ≥ t * (2 * π)⁻¹ - 1 / 2 := by rw [← hn]; exact Int.le_ceil _
      calc π + 2 * π * ↑n
        _ ≥ π + 2 * π * (t * (2 * π)⁻¹ - 1 / 2) := by bound
        _ = 2 * π * (2 * π)⁻¹ * t := by ring
        _ = t := by field_simp [Real.two_pi_pos.ne']
  rw [e, exp_of_im, ← Complex.cos_eq_cos, ← Complex.sin_eq_sin, Complex.arg_cos_add_sin_mul_I ts]

/-- `realCircleMap` is injective on the square -/
theorem rcm_inj {c : ℂ} {r0 r1 : ℝ} (r0p : 0 ≤ r0) : InjOn (realCircleMap c) (square r0 r1) := by
  intro x xs y ys e; simp [square] at xs ys
  simp_rw [realCircleMap_eq_circleMap, Equiv.apply_eq_iff_eq] at e
  simp_rw [circleMap] at e; simp at e
  have re : abs (↑x.1 * exp (x.2 * I)) = abs (↑y.1 * exp (y.2 * I)) := by rw [e]
  have x0 : 0 < x.1 := by linarith
  have y0 : 0 < y.1 := by linarith
  simp only [map_mul, Complex.abs_ofReal, abs_of_pos x0, Complex.abs_exp_ofReal_mul_I, mul_one,
    abs_of_pos y0] at re
  have ae : arg (↑x.1 * exp (x.2 * I)) = arg (↑y.1 * exp (y.2 * I)) := by rw [e]
  simp [Complex.arg_real_mul _ x0, Complex.arg_real_mul _ y0] at ae
  rcases arg_exp_of_im x.2 with ⟨nx, hx⟩
  rcases arg_exp_of_im y.2 with ⟨ny, h⟩
  rw [← ae, hx] at h; clear e ae hx
  have n0 : 2 * π * (nx - ny) < 2 * π * 1 := by linarith
  have n1 : 2 * π * -1 < 2 * π * (nx - ny) := by linarith
  have hn : (nx : ℝ) - ny = ↑(nx - ny) := by simp only [Int.cast_sub]
  have hn1 : (-1 : ℝ) = ↑(-1 : ℤ) := by norm_num
  have h1 : (1 : ℝ) = ↑(1 : ℤ) := by norm_num
  rw [mul_lt_mul_left Real.two_pi_pos, hn] at n0 n1
  rw [hn1] at n1; rw [h1] at n0; rw [Int.cast_lt] at n0 n1
  have n : nx = ny := by linarith
  rw [n] at h
  have i : x.2 = y.2 := by linarith
  have g : (x.1, x.2) = (y.1, y.2) := by rw [re, i]
  simp only [Prod.mk.eta] at g; exact g

end FubiniHelper

/-- Inverse lemma for fubini_ball -/
theorem measurable_symm_equiv_inverse {z : ℂ} :
    Complex.measurableEquivRealProd.symm (Complex.equivRealProd z) = z := by
  simp only [Complex.equivRealProd_apply]
  rw [Complex.measurableEquivRealProd, Homeomorph.toMeasurableEquiv_symm_coe]
  simp only [ContinuousLinearEquiv.symm_toHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph]
  apply Complex.ext; · simp only [Complex.equivRealProdCLM_symm_apply_re]
  · simp only [Complex.equivRealProdCLM_symm_apply_im]

/-- `circleMap` is continuous on `ℝ × ℝ` -/
theorem continuous_circleMap_full {c : ℂ} : Continuous fun x : ℝ × ℝ ↦ circleMap c x.1 x.2 := by
  continuity

/-- If `x.toReal = y` is positive, then `x = ofReal y` -/
theorem invert_toReal {x : ENNReal} {y : ℝ} (yp : y > 0) : x.toReal = y → x = ENNReal.ofReal y := by
  intro h; rw [← h]; refine (ENNReal.ofReal_toReal ?_).symm
  contrapose yp; simp only [ne_eq, not_not] at yp; simp only [yp, ENNReal.top_toReal] at h
  simp only [← h, lt_self_iff_false, not_false_eq_true]

/-- Integration over a complex annulus using polar coordinates -/
theorem fubini_annulus {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {r0 r1 : ℝ} (fc : ContinuousOn f (annulus_cc c r0 r1)) (r0p : 0 ≤ r0) :
    ∫ z in annulus_oc c r0 r1, f z =
      ∫ s in Ioc r0 r1, s • ∫ t in Ioc 0 (2 * π), f (circleMap c s t) := by
  have im := MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod
  rw [←MeasurePreserving.setIntegral_preimage_emb im
    Complex.measurableEquivRealProd.symm.measurableEmbedding f _]
  clear im
  rw [square_eq r0p]
  have dc : ∀ x, x ∈ square r0 r1 →
      HasFDerivWithinAt (realCircleMap c) (rcmDeriv x) (square r0 r1) x :=
    fun _ _ ↦ realCircleMap.fderiv.hasFDerivWithinAt
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume Measurable.square dc (rcm_inj r0p)]
  clear dc
  simp_rw [rcmDeriv.det]
  simp_rw [realCircleMap_eq_circleMap]
  simp_rw [measurable_symm_equiv_inverse]
  have e : ∀ x : ℝ × ℝ, x ∈ square r0 r1 → |x.1| • f (circleMap c x.1 x.2) =
      x.1 • f (circleMap c x.1 x.2) := by
    intro x xs; rw [abs_of_pos (square.rp r0p xs)]
  rw [MeasureTheory.setIntegral_congr Measurable.square e]; clear e
  rw [square, Measure.volume_eq_prod, MeasureTheory.setIntegral_prod]
  simp [integral_smul]
  have fi : IntegrableOn (fun x : ℝ × ℝ ↦ x.1 • f (circleMap c x.1 x.2))
      (Icc r0 r1 ×ˢ Icc 0 (2 * π)) := by
    apply ContinuousOn.integrableOn_compact
    · exact IsCompact.prod isCompact_Icc isCompact_Icc
    · apply ContinuousOn.smul continuous_fst.continuousOn
      apply fc.comp continuous_circleMap_full.continuousOn
      intro x xs
      simp only [Icc_prod_Icc, mem_Icc, Prod.le_def] at xs
      have x0 : 0 ≤ x.1 := by linarith
      simp only [circleMap, annulus_cc, mem_diff, Metric.mem_closedBall, dist_self_add_left,
        norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonneg x0,
        Complex.abs_exp_ofReal_mul_I, mul_one, xs.2.1, Metric.mem_ball, not_lt, xs.1.1, and_self]
  exact fi.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Integration over a complex ball using polar coordinates -/
theorem fubini_ball {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℂ → E} {c : ℂ} {r : ℝ} (fc : ContinuousOn f (closedBall c r)) :
    ∫ z in closedBall c r, f z =
      ∫ s in Ioc 0 r, s • ∫ t in Ioc 0 (2 * π), f (circleMap c s t) := by
  have center : closedBall c r =ᵐ[volume] (closedBall c r \ {c} : Set ℂ) := ae_minus_point
  rw [MeasureTheory.setIntegral_congr_set_ae center]; clear center
  rw [←Metric.closedBall_zero, ←annulus_oc]
  apply fubini_annulus
  · simpa only [annulus_cc, Metric.ball_zero, diff_empty]
  · rfl

/-- The volume of the complex closed ball is `π r^2` -/
theorem Complex.volume_closedBall' {c : ℂ} {r : ℝ} (rp : r ≥ 0) :
    (volume (closedBall c r)).toReal = π * r ^ 2 := by
  have c : ContinuousOn (fun _ : ℂ ↦ (1 : ℝ)) (closedBall c r) := continuousOn_const
  have f := fubini_ball c; clear c
  simp only [ENNReal.toReal_ofReal Real.two_pi_pos.le, ←
    intervalIntegral.integral_of_le rp, integral_const, Measure.restrict_apply, MeasurableSet.univ,
    univ_inter, Algebra.id.smul_eq_mul, mul_one, Real.volume_Ioc, tsub_zero,
    intervalIntegral.integral_mul_const, integral_id, zero_pow, Ne,
    Nat.one_ne_zero, not_false_iff] at f
  ring_nf at f ⊢; exact f

/-- `closedBall` with positive radius has positive, nonzero volume -/
theorem NiceVolume.closedBall (c : ℂ) {r : ℝ} (rp : r > 0) : NiceVolume (closedBall c r) :=
  { measurable := measurableSet_closedBall
    finite := by
      simp only [Complex.volume_closedBall]
      apply ENNReal.mul_lt_top
      · simp only [ne_eq, ENNReal.pow_eq_top_iff, ENNReal.ofReal_ne_top, OfNat.ofNat_ne_zero,
          not_false_eq_true, and_true]
      · simp only [ne_eq, ENNReal.coe_ne_top, not_false_eq_true]
    pos := by
      simp only [Complex.volume_closedBall, gt_iff_lt, CanonicallyOrderedCommSemiring.mul_pos,
        ENNReal.coe_pos, NNReal.pi_pos, and_true]
      apply ENNReal.pow_pos
      bound }

/-- `closedBall` with positive radius has positive volume near each point -/
theorem LocalVolume.closedBall {c : ℂ} {r : ℝ} (rp : r > 0) : LocalVolumeSet (closedBall c r) := by
  apply LocalVolume.closure_interior
  · intro x r rp
    simp only [Complex.volume_ball, gt_iff_lt, CanonicallyOrderedCommSemiring.mul_pos,
      ENNReal.coe_pos, NNReal.pi_pos, and_true]
    apply ENNReal.pow_pos
    bound
  · have rz := rp.ne'
    simp only [interior_closedBall c rz, closure_ball c rz, subset_refl]
