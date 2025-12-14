module
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Ray.Koebe.Snap
public import Ray.Koebe.Wind
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Ray.Misc.Bound
import Ray.Misc.Measure

/-!
## The area of a star-shaped region

If `f : Circle → ℂˣ` winds and is additionally differentiable, we can compute the area inside it
via a circle integral.
-/

open Complex (exp I reCLM imCLM equivRealProdCLM)
open LinearMap (toMatrix_apply)
open Module (Basis.finTwoProd)
open Set
open MeasureTheory (volume)
open scoped Real Topology ComplexConjugate
noncomputable section

variable {f : Circle → ℂˣ}

/-- `f` winds monotonically around the origin, and is differentiable -/
public structure WindDiff (f : Circle → ℂˣ) : Prop where
  fc : Continuous f
  inj : (fun x ↦ snap (f x)).Injective
  diff : Differentiable ℝ (fun t ↦ (f (.exp t)).val)

namespace WindDiff

public lemma wind (i : WindDiff f) : Wind f := ⟨i.fc, i.inj⟩

-- Abbreviations for `f`-related functions
@[expose] public def fe (_ : WindDiff f) (t : ℝ) : ℂ := (f (.exp t)).val
@[expose] public def dfe (i : WindDiff f) (t : ℝ) : ℂ := deriv i.fe t
@[expose] public def fdfe (i : WindDiff f) (t : ℝ) : ℝ →L[ℝ] ℂ := fderiv ℝ i.fe t

@[simp] lemma deriv_fe (i : WindDiff f) {t : ℝ} : deriv i.fe t = i.dfe t := rfl
lemma hasDerivAt_fe (i : WindDiff f) {t : ℝ} : HasDerivAt i.fe (i.dfe t) t :=
  i.diff.differentiableAt.hasDerivAt
lemma hasFDerivAt_fe (i : WindDiff f) {t : ℝ} : HasFDerivAt i.fe (i.fdfe t) t :=
  i.diff.differentiableAt.hasFDerivAt
@[simp] lemma fdfe_one (i : WindDiff f) {t : ℝ} : i.fdfe t 1 = i.dfe t := by
  unfold dfe; unfold fdfe; unfold fe; simp only [fderiv_eq_smul_deriv, one_smul]

-- Abbreviation for `fst` and `snd` as continuous linear maps
private abbrev d1 := ContinuousLinearMap.fst ℝ ℝ ℝ
private abbrev d2 := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- The square we will map onto the disk -/
private def square : Set (ℝ × ℝ) := Ioc 0 1 ×ˢ Ioc (-π) π

/-- Our map from the square to the disk -/
def gs (i : WindDiff f) (x : ℝ × ℝ) : ℝ × ℝ :=
  (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) (x.1 • i.fe x.2)

/-- The derivative of `i.gs` -/
def dgs (i : WindDiff f) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).comp (x.1 • (i.fdfe x.2).comp d2 + d1.smulRight (i.fe x.2))

lemma fderiv (i : WindDiff f) {x : ℝ × ℝ} :
    HasFDerivAt i.gs (i.dgs x) x := by
  apply (ContinuousLinearMap.hasFDerivAt _).comp
  exact hasFDerivAt_fst.smul (𝕜' := ℝ) (i.hasFDerivAt_fe.comp _ hasFDerivAt_snd)

/-- The Jacobian matrix of `i.gs` -/
def gsm (i : WindDiff f) (x : ℝ × ℝ) :=
  LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) (i.dgs x)
macro "gsm" : tactic => `(tactic| simp [WindDiff.gsm, WindDiff.dgs, toMatrix_apply])
lemma gsm00 (i : WindDiff f) (x : ℝ × ℝ) : i.gsm x 0 0 = (i.fe x.2).re := by gsm
lemma gsm01 (i : WindDiff f) (x : ℝ × ℝ) : i.gsm x 0 1 = x.1 * (i.dfe x.2).re := by gsm
lemma gsm10 (i : WindDiff f) (x : ℝ × ℝ) : i.gsm x 1 0 = (i.fe x.2).im := by gsm
lemma gsm11 (i : WindDiff f) (x : ℝ × ℝ) : i.gsm x 1 1 = x.1 * (i.dfe x.2).im := by gsm

/-- The Jacobian determinant of `i.dgs` -/
lemma dgs_det (i : WindDiff f) (x : ℝ × ℝ) :
    (i.dgs x).det = x.1 * inner ℝ (i.fe x.2 * I) (i.dfe x.2) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Basis.finTwoProd ℝ), ← WindDiff.gsm]
  simp [Matrix.det_fin_two, gsm00, gsm01, gsm10, gsm11]
  ring

/-- Factor `i.gs` through `i.wind.g` -/
lemma gs_eq (i : WindDiff f) (x : ℝ × ℝ) (x0 : 0 < x.1) :
    i.gs x = Complex.measurableEquivRealProd (i.wind.g (x.1 • (Circle.exp x.2).val)) := by
  simp only [gs, Complex.real_smul, ContinuousLinearEquiv.coe_coe, Complex.equivRealProdCLM_apply,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.mul_im,
    add_zero, Circle.coe_exp, Wind.g_apply, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.measurableEquivRealProd_apply, abs_of_pos x0,
    snap_mul_of_pos x0, snap_exp_mul_I, WindDiff.fe]

/-- `i.gs` is injective on `square` -/
lemma injOn_gs (i : WindDiff f) : InjOn i.gs square := by
  apply InjOn.comp
  · apply Function.Injective.injOn
    simp only [ContinuousLinearEquiv.coe_coe]
    apply ContinuousLinearEquiv.injective
  · set p : ℝ × ℝ → ℂ := fun x ↦ x.1 * (Circle.exp x.2).val
    have pe : ∀ x, x ∈ square → i.wind.g (p x) = x.1 • i.fe x.2 := by
      intro x m
      simp only [square, mem_prod, mem_Ioc] at m
      simp [p, i.wind.g_apply, snap_mul_of_pos m.1.1, WindDiff.fe, abs_of_pos m.1.1]
    refine InjOn.congr ?_ pe
    refine (i.wind.g.injective.injOn (s := univ)).comp ?_ (mapsTo_univ _ _)
    intro x xm y ym e
    have ae : ∀ {x}, x ∈ square → (exp (x.2 * I)).arg = x.2 := by
      intro x m
      simp only [Complex.arg_exp_mul_I, two_mul, toIocMod_eq_self, neg_add_cancel_left, m.2]
    simpa only [Circle.coe_exp, Complex.ext_norm_arg_iff, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, xm.1.1, abs_of_pos, Complex.norm_exp_ofReal_mul_I, mul_one, ym.1.1, p,
      Complex.arg_real_mul, ae, xm, ym, ← Prod.ext_iff] using e
  · apply mapsTo_univ

lemma disk_eq (i : WindDiff f) :
    i.wind.disk = Complex.measurableEquivRealProd.symm '' ({0} ∪ i.gs '' square) := by
  ext w
  constructor
  · intro m
    by_cases w0 : w = 0
    · exact ⟨0, by simp [w0, true_or, Complex.ext_iff]⟩
    · set z := i.wind.g.symm w
      have n : ⟨‖z‖, z.arg⟩ ∈ square := by
        obtain ⟨u,um,h⟩ := m
        simp only [Metric.mem_closedBall, dist_zero_right] at um
        contrapose w0
        simp only [square, ← h, Homeomorph.symm_apply_apply, mem_prod, mem_Ioc, norm_pos_iff, ne_eq,
          um, and_true, Complex.neg_pi_lt_arg, Complex.arg_le_pi, and_self, z, not_not] at w0 ⊢
        simp only [w0, Wind.g_zero]
      refine ⟨i.gs ⟨‖z‖, z.arg⟩, ?_, ?_⟩
      · simp only [mem_union]
        exact .inr (mem_image_of_mem i.gs n)
      · rw [i.gs_eq]
        · simp [z]
        · simpa using n.1.1
  · simp only [mem_image, mem_union, mem_singleton_iff]
    rintro ⟨y,(y0 | ⟨x,m,xy⟩),yw⟩
    · simp [← yw, y0]
      apply i.wind.zero_mem_disk
    · rw [i.gs_eq _ m.1.1] at xy
      simp [← yw, ← xy, Wind.disk, m.1.2, abs_of_pos m.1.1]

-- Measurability lemmas
lemma measurableSet_square : MeasurableSet square := by simp only [square]; measurability
lemma measurableSet_gs_square (i : WindDiff f) : MeasurableSet (i.gs '' square) :=
  MeasureTheory.measurable_image_of_fderivWithin measurableSet_square
    (fun _ _ ↦ i.fderiv.hasFDerivWithinAt) i.injOn_gs

/-- The area of `i.disk` as a circle integral -/
public theorem volume_eq (i : WindDiff f) :
    volume.real i.wind.disk = 2⁻¹ * ∫ t in (-π)..π, |inner ℝ (i.fe t * I) (i.dfe t)| := by
  simp only [i.disk_eq, image_union, MeasureTheory.Measure.real, image_singleton,
    measure_union_eq_right, MeasureTheory.NoAtoms.measure_singleton]
  rw [MeasurableEquiv.image_symm, Complex.volume_preserving_equiv_real_prod.measure_preimage
    i.measurableSet_gs_square.nullMeasurableSet]
  have ie : ∫ z in i.gs '' square, (1 : ℝ) = volume.real (i.gs '' square) • 1 :=
    MeasureTheory.setIntegral_const _
  simp only [smul_eq_mul, mul_one, MeasureTheory.Measure.real] at ie
  simp only [← ie, MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul _
    measurableSet_square (fun _ _ ↦ i.fderiv.hasFDerivWithinAt) i.injOn_gs, i.dgs_det, smul_eq_mul,
    mul_one, abs_mul]
  refine Eq.trans (MeasureTheory.setIntegral_prod_mul (s := Ioc 0 1) (t := Ioc (-π) π)
    (f := fun x ↦ |x|) (g := fun x ↦ |inner ℝ (i.fe x * I) (i.dfe x)|)) ?_
  refine congr_arg₂ _ ?_ ?_
  · rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (g := fun x ↦ x)]
    · simp [← intervalIntegral.integral_of_le zero_le_one]
    · intro x m; simp [m.1.le]
  · rw [intervalIntegral.integral_of_le (by bound)]
