import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.RingTheory.Norm.Transitivity

/-!
## Complex facts
-/

open Classical
open Metric (sphere)
open Complex (arg log I imCLM slitPlane)
open ContinuousLinearMap (lsmul)
open Set
open scoped ContDiff Real
noncomputable section

variable {X : Type} [TopologicalSpace X]

lemma Complex.arg_lt_zero_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 := by
  rw [← not_iff_not, not_lt, not_lt]
  exact arg_nonneg_iff

/-- A clean version of `(z / w).im` -/
lemma div_im_eq_inner (z w : ℂ) : (z / w).im = inner ℝ z (w * I) / w.normSq := by
  simp [Complex.div_im, Complex.inner]
  ring

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

/-!
### Derivatives mixing `ℝ` and `ℂ`
-/

/-- `Complex.ofReal` is real analytic -/
lemma Complex.analyticAt_ofReal {x : ℝ} : AnalyticAt ℝ Complex.ofReal x := by
  have e : Complex.ofReal = fun x ↦ Complex.ofRealCLM x := by simp
  rw [e]
  exact Complex.ofRealCLM.analyticAt x

/-- `Complex.ofReal` is real analytic -/
lemma AnalyticAt.ofReal {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (a : AnalyticAt ℝ f x) : AnalyticAt ℝ (fun x ↦ (f x : ℂ)) x :=
  Complex.analyticAt_ofReal.comp a

/-- `Complex.ofReal` is real analytic -/
lemma Complex.contDiffAt_ofReal {x : ℝ} : ContDiffAt ℝ ω Complex.ofReal x :=
  Complex.analyticAt_ofReal.contDiffAt

/-- `Complex.ofReal` is real analytic -/
lemma Complex.contDiff_ofReal : ContDiff ℝ ω Complex.ofReal := by
  rw [contDiff_iff_contDiffAt]
  intro x
  apply Complex.contDiffAt_ofReal

/-- Complex `norm` is real analytic -/
lemma Complex.analyticAt_norm {z : ℂ} (z0 : z ≠ 0) : AnalyticAt ℝ (fun z : ℂ ↦ ‖z‖) z :=
  (contDiffAt_norm (𝕜 := ℝ) z0).analyticAt

/-- Complex `norm` is real analytic -/
lemma AnalyticAt.norm {𝕜 E : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedSpace 𝕜 ℂ] [NormedSpace ℝ E] {f : E → ℂ} {x : E} (a : AnalyticAt 𝕜 f x) (f0 : f x ≠ 0) :
    AnalyticAt ℝ (fun x ↦ ‖f x‖) x :=
  (Complex.analyticAt_norm f0).comp a.restrictScalars

/-- A complex derivative, treated as `ℂ →L[ℝ] → ℂ` -/
lemma Complex.real_hasFDerivAt {f : ℂ → ℂ} {z : ℂ} {f' : ℂ} (h : HasDerivAt f f' z) :
    HasFDerivAt f (lsmul ℝ ℂ f') z := by
  convert h.hasFDerivAt.restrictScalars ℝ
  ext
  exact mul_comm _ _

/-- The derivative of `.im` -/
lemma hasFDerivAt_im {z : ℂ} : HasFDerivAt Complex.im imCLM z := by
  have e : Complex.im = (fun z ↦ imCLM z) := by ext z; simp only [Complex.imCLM_apply]
  rw [e]; apply ContinuousLinearMap.hasFDerivAt

/-- The derivative of `arg`, via `log` -/
lemma hasFDerivAt_arg {z : ℂ} (m : z ∈ slitPlane) :
    HasFDerivAt arg (imCLM ∘L lsmul ℝ ℂ z⁻¹) z := by
  have e : arg = (fun z ↦ (log z).im) := by ext z; rw [Complex.log_im]
  rw [e]
  exact HasFDerivAt.comp _ hasFDerivAt_im (Complex.real_hasFDerivAt (Complex.hasDerivAt_log m))

/-- The derivative of `arg` along a curve -/
lemma HasDerivAt.arg {p : ℝ → ℂ} {p' : ℂ} {t : ℝ} (h : HasDerivAt p p' t) (m : p t ∈ slitPlane) :
    HasDerivAt (fun t ↦ arg (p t)) ((p t)⁻¹ * p').im t := by
  convert ((hasFDerivAt_arg m).comp t h.hasFDerivAt).hasDerivAt
  simp only [ContinuousLinearMap.comp, Complex.imCLM_coe, ContinuousLinearMap.coe_mk',
    LinearMap.coe_comp, Complex.imLm_coe, Function.comp_apply]
  apply congr_arg
  apply congr_arg
  convert ContinuousLinearMap.smulRight_apply.symm
  simp only [ContinuousLinearMap.one_apply, one_smul]

/-!
### Determinants of complex derivatives
-/

lemma Complex.algebra_norm (z : ℂ) : Algebra.norm ℝ (z : ℂ) = ‖z‖ ^ 2 := by
  sorry

/-- If `f` is complex differentiable at a point, it's `fderiv` determinant is clean -/
lemma Complex.fderiv_det {f : ℂ → ℂ} {z : ℂ} (df : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z).det = ‖deriv f z‖ ^ 2 := by
  have d1 := df.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have d2 := (df.restrictScalars ℝ).hasFDerivAt
  rw [d2.unique d1]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, Complex.algebra_norm,
    LinearMap.det_restrictScalars, LinearMap.det_ring, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
