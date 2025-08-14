import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
## Snap a complex number to `Circle`
-/

open Complex (arg I)
open Set
open scoped Real Topology ComplexConjugate
noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- `z / abs z : Circle` -/
def snap (z : ℂ) : Circle :=
  if n : z = 0 then 1 else ⟨z / ‖z‖, by simp [n, Submonoid.unitSphere, div_self]⟩

lemma coe_snap {z : ℂ} (z0 : z ≠ 0) : (snap z).val = z / ‖z‖ := by
  simp only [snap, z0, ↓reduceDIte, div_eq_mul_inv]

@[simp] lemma norm_snap {z : ℂ} : ‖(snap z).val‖ = 1 := by
  simp only [snap, norm_eq_of_mem_sphere]

@[simp] lemma arg_snap {z : ℂ} (z0 : z ≠ 0) : arg (snap z) = arg z := by
  simp only [snap, z0, ↓reduceDIte, div_eq_mul_inv]
  have e0 : arg ((‖z‖ : ℂ))⁻¹ = 0 := by
    simp only [← Complex.ofReal_inv]
    apply Complex.arg_ofReal_of_nonneg
    bound
  rw [Complex.arg_mul z0]
  · simp only [add_eq_left, e0]
  · simpa only [ne_eq, inv_eq_zero, Complex.ofReal_eq_zero, norm_eq_zero]
  · simp only [e0, add_zero, Complex.arg_mem_Ioc]

lemma snap_eq_snap_iff {z w : ℂ} (z0 : z ≠ 0) (w0 : w ≠ 0) : snap z = snap w ↔ arg z = arg w := by
  simp only [Circle.ext_iff, Complex.ext_norm_arg_iff, norm_snap, arg_snap z0, arg_snap w0,
    true_and]

@[simp] lemma snap_mul {z w : ℂ} (z0 : z ≠ 0) (w0 : w ≠ 0) : snap (z * w) = snap z * snap w := by
  simp only [snap, mul_eq_zero, z0, w0, or_self, ↓reduceDIte, Complex.norm_mul, Complex.ofReal_mul,
    div_eq_mul_inv, mul_inv_rev, Circle.ext_iff, Circle.coe_mul]
  ring

@[simp] lemma snap_zero : snap 0 = 1 := by
  simp only [snap, ↓reduceDIte]

@[simp] lemma snap_of_pos {t : ℝ} (t0 : 0 < t) : snap (t : ℂ) = 1 := by
  simp only [snap, Complex.ofReal_eq_zero, t0.ne', ↓reduceDIte, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos t0, ne_eq, not_false_eq_true, div_self, Circle.ext_iff, OneMemClass.coe_one]

@[simp] lemma snap_mul_of_pos {t : ℝ} (t0 : 0 < t) {z : ℂ} : snap (t * z) = snap z := by
  simp only [snap, mul_eq_zero, Complex.ofReal_eq_zero, t0.ne', false_or, Complex.norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos t0, Complex.ofReal_mul, div_mul_eq_div_div,
    ne_eq, not_false_eq_true, mul_div_cancel_left₀]

@[simp] lemma snap_circle (z : Circle) : snap z.val = z := by
  simp only [snap, Circle.coe_ne_zero, ↓reduceDIte, norm_eq_of_mem_sphere, Complex.ofReal_one,
    div_one, Subtype.coe_eta]

@[simp] lemma norm_mul_snap {z : ℂ} (z0 : z ≠ 0) : ‖z‖ * (snap z).val = z := by
  have n : (‖z‖ : ℂ) ≠ 0 := by simpa
  simp only [snap, z0, ↓reduceDIte, mul_div_cancel₀ _ n]

/-- Alternative definition using `Set.codRestrict` -/
lemma snap_eq_restrict :
    snap = codRestrict (fun z : ℂ ↦ if z = 0 then 1 else z / ‖z‖) (Submonoid.unitSphere ℂ)
      (by intro z; simp only; split_ifs with h; all_goals simp [h]) := by
  ext z
  by_cases z0 : z = 0
  all_goals simp [z0, coe_snap]

lemma continuousAt_snap {z : ℂ} (z0 : z ≠ 0) : ContinuousAt snap z := by
  rw [snap_eq_restrict, continuousAt_codRestrict_iff]
  have e : ∀ᶠ w : ℂ in 𝓝 z, (if w = 0 then 1 else w / ‖w‖) = w / ‖w‖ := by
    filter_upwards [eventually_ne_nhds z0]
    aesop
  refine ContinuousAt.congr_of_eventuallyEq ?_ e
  exact continuousAt_id.div (Complex.continuous_ofReal.comp continuous_norm).continuousAt
    (by simpa only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero])

@[fun_prop] lemma ContinuousAt.snap_units {f : X → ℂˣ} {x : X} (fc : ContinuousAt f x) :
    ContinuousAt (fun x ↦ snap (f x)) x := by
  refine (continuousAt_snap ?_).comp ?_
  · apply Units.ne_zero
  · exact Units.continuous_val.continuousAt.comp fc

@[fun_prop] lemma Continuous.snap_units {f : X → ℂˣ} (fc : Continuous f) :
    Continuous (fun x ↦ snap (f x)) := by
  rw [continuous_iff_continuousAt]
  fun_prop

lemma snap_unit (z : ℂˣ) : snap z = ⟨z / ‖z.val‖, by simp [Submonoid.unitSphere]⟩ := by
  simp only [snap, Units.ne_zero, ↓reduceDIte]

@[simp] lemma snap_exp_mul_I {t : ℝ} : snap (Complex.exp (t * I)) = Circle.exp t := by
  simp [Circle.ext_iff, coe_snap]
