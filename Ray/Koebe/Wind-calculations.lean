import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Exponential
import Ray.Analytic.Holomorphic
import Ray.Koebe.Snap
import Ray.Misc.Bound
import Ray.Misc.Circle
import Ray.Misc.Cis
import Ray.Misc.Connected
import Ray.Misc.Real
import Ray.Hartogs.FubiniBall

/-!
## Curves that wind monotonically bound a star-shaped region

If `f : AddCircle (2*π) → ℂ` is close to `t ↦ r * exp (t * I)` and winds monotonically around the
origin, then it bounds a star-shaped region.  This lets us compute the area of the region by
integrating along the curve.

Ah, since we don't want to deal in manifold derivatives, let's actually assume the curve is
holomorphic in a neighbhorhood of `circle`.

DO NOT SUBMIT: Move lemmas and utilities out of this file.
-/

open Complex (arg exp I)
open Metric (ball closedBall isOpen_ball sphere)
open Bornology Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped Real Topology ComplexConjugate
noncomputable section

/-!
### Star-shaped regions
-/

variable {f : Circle → ℂˣ}
variable {x : Circle}

/-- `f z ≈ z`, and `f` winds monotonically around the origin -/
structure Wind (f : Circle → ℂˣ) : Prop where
  fc : Continuous f
  close : ∀ x, ‖(f x).val - x‖ < 1/100
  inj : (fun x ↦ snap (f x)).Injective

attribute [bound] Wind.close
@[bound] lemma Wind.close_le (i : Wind f) : ‖(f x).val - x‖ ≤ 1/100 := (i.close x).le

lemma coe_snap_f : (snap (f x)).val = f x / ‖(f x).val‖ := by
  simp only [coe_snap (Units.ne_zero _)]

lemma Wind.isHomeomorph (i : Wind f) : IsHomeomorph (fun z ↦ snap (f z)) :=
  Circle.isHomeomorph_of_injective i.fc.snap_units i.inj

/-- `z ↦ snap (f z)` as a homeomorphism -/
def Wind.h (i : Wind f) : Homeomorph Circle Circle := i.isHomeomorph.homeomorph

@[simp] lemma Wind.h_apply (i : Wind f) (z : Circle) : i.h z = snap (f z) := rfl

lemma Wind.f_h_symm (i : Wind f) (z : Circle) :
    f (i.h.symm z) = ‖(f (i.h.symm z)).val‖ • z.val := by
  have h := i.h.apply_symm_apply z
  simp only [Wind.h_apply, Circle.ext_iff, Complex.real_smul, snap_unit] at h ⊢
  rwa [mul_comm, ← div_eq_iff]
  simp

@[simp] lemma Wind.h_symm_f (i : Wind f) (z : Circle) : i.h.symm (snap (f z)) = z :=
  i.h.symm_apply_apply z

/- DO NOT SUBMIT: We'll add these back once I figure out the cleanest route to injectivity above
--mono : ∀ z : ℂ, ‖z‖ = 1 → 0 < (z * (f z)⁻¹ * deriv f z).re
/-- `t ↦ snap (f (cis t))` is injective for close values, via monotonicity of `arg`.
    We use closeness to avoid `arg` wraparound issues. -/
lemma Wind.inj_near (i : Wind f r) {a b : ℝ} (ab : a < b) (ba : b ≤ a + 1/2) :
    snap (f (cis a)) ≠ snap (f (cis b)) := by
  generalize hc : f (cis a) = c
  rw [← hc]
  have c0 : c ≠ 0 := by simpa only [←hc] using i.f_cis_ne_zero
  have cf0 : ∀ {t}, c⁻¹ * f (cis t) ≠ 0 := by
    intro t; simpa only [ne_eq, mul_eq_zero, inv_eq_zero, c0, false_or] using i.f_cis_ne_zero
  generalize hg : (fun t : ℝ ↦ arg (c⁻¹ * f (cis (a + t)))) = g
  suffices h : g 0 ≠ g (b-a) by
    simpa only [ne_eq, ← hg, add_zero, add_sub_cancel, ← snap_eq_snap_iff cf0 cf0,
      snap_mul,
      mul_eq_mul_left_iff, inv_eq_zero, c0, or_false] using h
  apply ne_of_lt
  suffices h : StrictMonoOn g (Icc 0 (b - a)) by
    apply h
    · simp only [mem_Icc, le_refl, sub_nonneg, true_and]; bound
    · simp only [mem_Icc, sub_nonneg, le_refl, and_true]; bound
    · bound
  have dg : ∀ t, t ∈ Icc 0 (b-a) → HasDerivAt g
      ((c⁻¹ * f (cis (a + t)))⁻¹ * (c⁻¹ * (deriv f (cis (a + t)) *
        ((1:ℝ) • (cis (a + t) * I))))).im t := by
    intro t m; rw [← hg]
    apply HasDerivAt.arg
    · apply HasDerivAt.const_mul
      apply HasDerivAt.comp
      · apply DifferentiableAt.hasDerivAt
        exact (i.fa _ cis_mem_sphere).differentiableAt
      · exact hasDerivAt_cis.scomp t ((hasDerivAt_id _).const_add _)
    · simp only [Complex.mem_slitPlane_iff]
      left
      apply re_mul_inv_pos_of_close
      simp only [←hc]
      have cc : ‖cis (a + t) - cis a‖ ≤ 1/2 := by
        have h := lipschitzWith_cis.dist_le_mul (a + t) a
        simp only [Complex.dist_eq, NNReal.coe_one, dist_self_add_left, Real.norm_eq_abs,
          abs_of_nonneg m.1, one_mul] at h
        linarith [m.2]
      calc ‖f (cis (a + t)) - f (cis a)‖
        _ = ‖f (cis (a + t)) - r * cis (a + t) + (r * cis (a + t) - r * cis a) -
              (f (cis a) - r * cis a)‖ := by abel_nf
        _ ≤ ‖f (cis (a + t)) - r * cis (a + t) + (r * cis (a + t) - r * cis a)‖ +
             ‖f (cis a) - r * cis a‖ := by bound
        _ ≤ ‖f (cis (a + t)) - r * cis (a + t)‖ + ‖r * cis (a + t) - r * cis a‖ +
             ‖f (cis a) - r * cis a‖ := by bound
        _ ≤ r/100 + ‖r * cis (a + t) - r * cis a‖ + r/100 := by
              bound [i.close (cis (a + t)) norm_cis, i.close (cis a) norm_cis]
        _ ≤ r/100 + r * ‖cis (a + t) - cis a‖ + r/100 := by
              rw [← mul_sub, norm_mul, norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg i.r0.le]
        _ ≤ r/100 + r * (1/2) + r/100 := by bound
        _ < r - r/100 := by linarith [i.r0]
        _ ≤ ‖r * cis a‖ - r/100 := by
              simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg i.r0.le, mul_one, le_refl,
                norm_cis]
        _ ≤ ‖r * cis a‖ - ‖f (cis a) - r * cis a‖ := by bound [i.close (cis a) norm_cis]
        _ ≤ ‖r * cis a + (f (cis a) - r * cis a)‖ := by bound
        _ = ‖f (cis a)‖ := by ring_nf
  simp only [one_smul, mul_inv, inv_inv, ← mul_assoc, mul_comm _ c⁻¹, inv_mul_cancel₀ c0,
    one_mul, Complex.mul_I_im] at dg
  simp only [← mul_assoc, mul_comm _ (cis _)] at dg
  apply strictMonoOn_of_deriv_pos
  · apply convex_Icc
  · intro t m; exact (dg t m).continuousAt.continuousWithinAt
  · intro t m; simp only [(dg t (interior_subset m)).deriv, i.mono _ norm_cis]

/-- `t ↦ snap (f (cis t))` is injective for close values (symmetric version)` -/
lemma Wind.inj_near' (i : Wind f r) {a b : ℝ} (ne : a ≠ b) (ab : |b - a| ≤ 1/2) :
    snap (f (cis a)) ≠ snap (f (cis b)) := by
  by_cases h : a < b
  · rw [abs_of_nonneg (by bound)] at ab
    exact i.inj_near h (by linarith)
  · symm
    simp only [not_lt] at h
    rw [abs_of_nonpos (by bound)] at ab
    exact i.inj_near (ne.symm.lt_of_le h) (by linarith)
-/

/- DO NOT SUBMIT: Will we use this?
/-- `snap (f z)` is close to `z` -/
lemma Wind.snap_close (i : Wind f) : ‖snap (f x) - x.val‖ ≤ 1/40 := by
  have a0 : 0 < ‖f x‖ := i.norm_f_pos
  have aa0 : 0 < ‖(‖f x‖ : ℂ)‖ := by simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm, a0]
  rw [← mul_le_mul_iff_of_pos_right aa0, ← norm_mul, sub_mul, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), i.coe_snap,
    div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr a0.ne'), mul_comm x.val]
  calc ‖f x - ‖f x‖ * x‖
    _ = ‖f x - x - (‖f x‖ - 1) * x‖ := by ring_nf
    _ ≤ ‖f x - x‖ + ‖(‖f x‖ - 1) * x.val‖ := by bound
    _ ≤ 1/100 + ‖(‖f x‖ - 1) * x.val‖ := by bound
    _ = 1/100 + |‖f x‖ - ‖x.val‖| := by
        simp only [norm_mul, Complex.norm_real, mul_one, Circle.norm_coe,
          ← Complex.ofReal_sub, Real.norm_eq_abs, ← Complex.ofReal_one]
    _ ≤ 1/100 + ‖f x - x‖ := by bound [abs_norm_sub_norm_le (f x) x]
    _ ≤ 1/100 + 1/100 := by bound
    _ ≤ 1/40 * (1 - 1/100) := by norm_num
    _ ≤ 1/40 * (‖x.val‖ - 1/100) := by norm_num [Circle.norm_coe]
    _ ≤ 1/40 * (‖x.val‖ - ‖f x - x‖) := by bound
    _ ≤ 1/40 * ‖x + (f x - x)‖ := by bound
    _ = 1/40 * ‖f x‖ := by ring_nf
-/

/- DO NOT SUBMIT: Figure out the way to use this
/-- `z ↦ snap (f z)` is injective -/
lemma Wind.inj (i : Wind f r) : InjOn (fun z ↦ snap (f z)) (sphere 0 1) := by
  -- We're either close enough to apply `i.inj_near` or far enough that `i.close` works.
  intro x xm y ym e
  contrapose e
  simp only [mem_sphere_iff_norm, sub_zero] at xm ym ⊢
  by_cases xy : ‖y - x‖ ≤ 1/10
  · obtain ⟨a,_,xa⟩ := cis_exists_le xm
    have rm : ‖y / x‖ = 1 := by
      simp only [norm_div, ym, xm, ne_eq, one_ne_zero, not_false_eq_true, div_self]
    obtain ⟨t,tm,rt⟩ := cis_exists_le rm
    have x0 : x ≠ 0 := by simp only [← norm_ne_zero_iff, xm, ne_eq, one_ne_zero, not_false_eq_true]
    have yb : y = cis (a + t) := by simpa only [cis_add, ← xa, mul_comm x, ← div_eq_iff x0]
    rw [xa, yb]
    apply i.inj_near'
    · contrapose e
      simp only [ne_eq, left_eq_add, not_not] at e
      simp only [e, cis_zero, div_eq_iff x0, one_mul] at rt
      simp only [rt, not_true_eq_false, not_false_eq_true]
    · simp only [add_sub_cancel_left]
      refine le_trans (abs_le_mul_norm_cis tm) ?_
      rw [← div_le_div_iff_of_pos_right (c := ‖x‖) (by positivity), ← norm_div, sub_div,
        div_self (norm_ne_zero_iff.mp (by positivity)), rt, xm, div_one] at xy
      refine le_trans (mul_le_mul_of_nonneg_left xy (by bound)) ?_
      linarith [Real.pi_le_four]
  · simp only [not_le] at xy
    rw [← dist_eq_zero, Complex.dist_eq]
    apply ne_of_gt
    calc ‖snap (f x) - snap (f y)‖
      _ = ‖-(y - x) + (snap (f x) - x - (snap (f y) - y))‖ := by ring_nf
      _ ≥ ‖-(y - x)‖ - ‖snap (f x) - x - (snap (f y) - y)‖ := by bound
      _ ≥ ‖-(y - x)‖ - (‖snap (f x) - x‖ + ‖snap (f y) - y‖) := by bound
      _ ≥ ‖-(y - x)‖ - (1/40 + 1/40) := by bound [i.snap_close xm, i.snap_close ym]
      _ = ‖y - x‖ - 1/20 := by norm_num; apply norm_sub_rev
      _ ≥ 1/10 - 1/20 := by bound
      _ > 0 := by norm_num
-/
