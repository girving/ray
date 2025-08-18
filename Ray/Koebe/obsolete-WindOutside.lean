import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Exponential
import Ray.Analytic.Holomorphic
import Ray.Koebe.Snap
import Ray.Misc.Annuli
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
variable {z w : ℂ}
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

/-!
### Minimum and maximum values of `‖f z‖` on the circle
-/

/-- `‖f z‖` is lower bounded on `‖z‖ = 1` -/
lemma Wind.exists_min (i : Wind f) : ∃ x, IsMinOn (fun z ↦ ‖(f z).val‖) univ x := by
  have e := (isCompact_univ (X := Circle)).exists_isMinOn (f := fun z ↦ ‖(f z).val‖) (by simp) ?_
  · simpa only [mem_univ, true_and] using e
  · exact (Units.continuous_val.comp i.fc).norm.continuousOn

/-- `‖f z‖` is upper bounded on `‖z‖ = 1` -/
lemma Wind.exists_max (i : Wind f) : ∃ x, IsMaxOn (fun z ↦ ‖(f z).val‖) univ x := by
  have e := (isCompact_univ (X := Circle)).exists_isMaxOn (f := fun z ↦ ‖(f z).val‖) (by simp) ?_
  · simpa only [mem_univ, true_and] using e
  · exact (Units.continuous_val.comp i.fc).norm.continuousOn

/-- The minimum of `‖f z‖` on `‖z‖ = 1` -/
def Wind.min (i : Wind f) : ℝ := ‖(f (Classical.choose i.exists_min)).val‖

/-- The maximum of `‖f z‖` on `‖z‖ = 1` -/
def Wind.max (i : Wind f) : ℝ := ‖(f (Classical.choose i.exists_max)).val‖

@[bound] lemma Wind.min_pos (i : Wind f) : 0 < i.min := by simp [min]
@[bound] lemma Wind.max_pos (i : Wind f) : 0 < i.max := by simp [max]
@[bound] lemma Wind.min_nonneg (i : Wind f) : 0 ≤ i.min := i.min_pos.le
@[bound] lemma Wind.max_nonneg (i : Wind f) : 0 ≤ i.max := i.max_pos.le

@[bound] lemma Wind.min_le (i : Wind f) : i.min ≤ ‖(f x).val‖ :=
  Classical.choose_spec i.exists_min trivial

@[bound] lemma Wind.le_max (i : Wind f) : ‖(f x).val‖ ≤ i.max :=
  Classical.choose_spec i.exists_max trivial

/-!
### Star-shaped parameterisation of the plane, extrapolating out from `f`
-/

/-- Forward map extending `f` to the plane -/
def Wind.fe (_ : Wind f) (z : ℂ) : ℂ := ‖z‖ • f (snap z)

/-- Inverse map -/
def Wind.fi (i : Wind f) (w : ℂ) : ℂ :=
  let z := i.h.symm (snap w)
  ‖w‖ / ‖(f z).val‖ * z

@[simp] lemma Wind.fe_zero (i : Wind f) : i.fe 0 = 0 := by simp [Wind.fe]
@[simp] lemma Wind.fi_zero (i : Wind f) : i.fi 0 = 0 := by simp [Wind.fi]

/-- `fi ∘ fe = id` -/
lemma Wind.left_inv (i : Wind f) : Function.LeftInverse i.fi i.fe := by
  intro z
  by_cases z0 : z = 0
  · simp only [z0, fe_zero, fi_zero]
  · simp [Wind.fe, Wind.fi, z0]

/-- `fe ∘ fi = id` -/
lemma Wind.right_inv (i : Wind f) : Function.RightInverse i.fi i.fe := by
  intro w
  by_cases w0 : w = 0
  · simp only [w0, fe_zero, fi_zero]
  · simp only [fe, fi, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, norm_eq_of_mem_sphere, mul_one, Complex.real_smul, Complex.ofReal_div]
    rw [← Complex.ofReal_div, snap_mul, snap_of_pos, one_mul, i.f_h_symm]
    all_goals simp [Complex.real_smul, Complex.norm_real, ne_eq, w0, not_false_eq_true, mul_one,
      Complex.ofReal_div]
    nth_rw 2 [i.f_h_symm]
    rw [Complex.real_smul, ← mul_assoc, div_mul_cancel₀ _ (by simp)]
    exact norm_mul_snap w0

lemma Wind.continuous_fe (i : Wind f) : Continuous i.fe := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases z0 : z = 0
  · refine Metric.continuousAt_iff.mpr fun ε ε0 ↦ ⟨ε / i.max, by bound, fun w wz ↦ ?_⟩
    simp only [z0, dist_zero_right, fe, Complex.real_smul, norm_zero, snap_zero, zero_smul,
      Complex.norm_mul, Complex.norm_real, norm_norm, lt_div_iff₀ i.max_pos] at wz ⊢
    exact lt_of_le_of_lt (by bound) wz
  · apply ContinuousAt.smul
    · exact continuous_norm.continuousAt
    · exact Units.continuous_val.continuousAt.comp (i.fc.continuousAt.comp (continuousAt_snap z0))

lemma Wind.continuous_fi (i : Wind f) : Continuous i.fi := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases w0 : w = 0
  · refine Metric.continuousAt_iff.mpr fun ε ε0 ↦ ⟨ε * i.min, by bound, fun z zw ↦ ?_⟩
    simp only [w0, dist_zero_right, ← div_lt_iff₀ i.min_pos, fi, norm_zero, Complex.ofReal_zero,
      snap_zero, zero_div, zero_mul, Complex.norm_mul, Complex.norm_div, Complex.norm_real,
      norm_norm, norm_eq_of_mem_sphere, mul_one] at zw ⊢
    exact lt_of_le_of_lt (by bound) zw
  · apply ContinuousAt.mul (ContinuousAt.div ?_ ?_ ?_) ?_
    · fun_prop
    · refine Complex.continuous_ofReal.continuousAt.comp ?_
      refine (Units.continuous_val.comp (i.fc.comp i.h.continuous_symm)).norm.continuousAt.comp ?_
      exact continuousAt_snap (by simpa using w0)
    · simp
    · apply continuousAt_subtype_val.comp
      exact i.h.continuous_symm.continuousAt.comp (continuousAt_snap (by simpa using w0))

/-- Star-shaped parameterisation of the plane, extrapolating out from `f` -/
def Wind.g (i : Wind f) : Homeomorph ℂ ℂ where
  toFun := i.fe
  invFun := i.fi
  left_inv := i.left_inv
  right_inv := i.right_inv
  continuous_toFun := i.continuous_fe
  continuous_invFun := i.continuous_fi

lemma Wind.g_apply (i : Wind f) : i.g z = ‖z‖ • f (snap z) := rfl
lemma Wind.g_symm_apply (i : Wind f) : i.g.symm w =
    let z := i.h.symm (snap w)
    ‖w‖ / ‖(f z).val‖ * z.val := rfl
@[simp] lemma Wind.g_zero (i : Wind f) : i.g 0 = 0 := by simp [i.g_apply]
@[simp] lemma Wind.g_symm_zero (i : Wind f) : i.g.symm 0 = 0 := by simp [i.g_symm_apply]

/-!
### Regions inside the wind
-/

def Wind.disk (i : Wind f) : Set ℂ := i.g '' closedBall 0 1
def Wind.inner (i : Wind f) : Set ℂ := i.g '' ball 0 1

lemma Wind.isCompact_disk (i : Wind f) : IsCompact i.disk :=
  (isCompact_closedBall _ _).image_of_continuousOn i.g.continuous.continuousOn

lemma Wind.isOpen_inner (i : Wind f) : IsOpen i.inner := by
  simp only [inner, Homeomorph.isOpen_image, isOpen_ball]

@[simp] lemma Wind.zero_mem_inner (i : Wind f) : 0 ∈ i.inner := by use 0; simp

lemma Wind.frontier_disk (i : Wind f) : frontier i.disk = i.g '' sphere 0 1 := by
  simp only [Wind.disk, ← Homeomorph.image_frontier]
  rw [frontier_closedBall _ (by norm_num)]

/-!
### Star-shaped parameterization of the complement of an analytic image

DO NOT SUBMIT: Update for above refactor

Let `f` be analytic for `1 ≤ ‖z‖`, with `Wind f r`.  Let `R = f '' {z | 1 < ‖z‖}`.  We want
to parameterize `Rᶜ` as `(t,r) ↦ r * cis t` for `r ∈ Icc 0 1`.  The above machinery shows that
this parameterization injects into `Rᶜ`, so we just need to show that it covers `Rᶜ`.

DO NOT SUBMIT: The paragraph below is unclear. Rewrite once I've finished the proof.

`Rᶜ` is closed, so consider a minimum radius point `w ∉ R`.  `w` is arbitrarily close to `R`, so
as long as the nearby `f`-arguments don't escape to infinity we're done.  If we also know that
`f` winds for larger values of `r`, we're done, so let's assume that.
-/

/-- `f z ≈ z` outside radius `r`, `f` is injective, and `f` winds monotonically around the origin -/
structure WindOutside (f : ℂ → ℂ) (r : ℝ) : Prop where
  r0 : 0 < r
  fa : AnalyticOnNhd ℂ f (norm_Ici r)
  inj : InjOn f (norm_Ici r)
  close : ∀ z : ℂ, r ≤ ‖z‖ → ‖f z - z‖ < ‖z‖ / 100
  mono : ∀ z : ℂ, r ≤ ‖z‖ → 0 < (z * (f z)⁻¹ * deriv f z).re

-- Teach `bound` that `0 < r`
attribute [bound_forward] WindOutside.r0

/-- `f z` has large `abs` -/
lemma WindOutside.le_norm (i : WindOutside f r) {z : ℂ} (m : r ≤ ‖z‖) :
    99 / 100 * ‖z‖ ≤ ‖f z‖ := by
  calc ‖f z‖
    _ = ‖z + (f z - z)‖ := by ring_nf
    _ ≥ ‖z‖ - ‖f z - z‖ := by bound
    _ ≥ ‖z‖ - ‖z‖ / 100 := by bound [i.close _ m]
    _ = 99 / 100 * ‖z‖ := by ring

-- DO NOT SUBMIT: Move to Analytic.lean
lemma analyticAt_real_smul {s : ℝ} {z : ℂ} : AnalyticAt ℂ (fun z ↦ s • z) z := by
  simp only [Complex.real_smul]; exact analyticAt_const.mul analyticAt_id

-- DO NOT SUBMIT: Upstream
theorem hasDerivAt_const_mul {𝕜 : Type*} [NontriviallyNormedField 𝕜] (c : 𝕜) {x : 𝕜} :
    HasDerivAt (fun x : 𝕜 => c * x) c x := by
  simp only [mul_comm c]; apply hasDerivAt_mul_const

/-- If we wind for `r ≤ ‖z‖`, we wind for any `s ≥ r` -/
lemma WindOutside.wind (i : WindOutside f r) {s : ℝ} (rs : r ≤ s) : Wind (fun z ↦ f (s • z)) s := by
  have s0 : 0 < s := by bound
  exact {
    r0 := by bound
    fa := by
      intro z m
      refine (i.fa _ ?_).comp analyticAt_real_smul
      simp only [mem_sphere_iff_norm, sub_zero] at m
      simpa only [Complex.real_smul, norm_Ici, mem_setOf_eq, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos s0, m, mul_one]
    close := by
      intro z m
      simp only [Complex.real_smul]
      refine lt_of_lt_of_le (i.close _ ?_) ?_
      · simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s0, m, mul_one]
      · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s0, m, mul_one,
          le_refl]
    mono := by
      intro z m
      have ez : z = s⁻¹ • s • z := by simp only [smul_smul, inv_mul_cancel₀ s0.ne', one_smul]
      have ed : deriv (fun z ↦ f (s • z)) z = s • deriv f (s • z) := by
        apply HasDerivAt.deriv
        simp only [Complex.real_smul, mul_comm _ (deriv _ _)]
        refine (i.fa (s * z) ?_).differentiableAt.hasDerivAt.comp z (hasDerivAt_const_mul _)
        simpa only [norm_Ici, mem_setOf_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos s0, m, mul_one]
      nth_rw 1 [ez, ed]
      simp only [Complex.real_smul, ←mul_assoc, mul_comm _ (s : ℂ), Complex.ofReal_inv,
        mul_inv_cancel_right₀ (Complex.ofReal_ne_zero.mpr s0.ne')]
      apply i.mono
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s0, m, mul_one] }

-- What if we instead prove
--   `f '' abs_Ioi r = i.diskᶜ`
-- via
--   `f '' abs_Ioi r ⊆ i.diskᶜ`  (1)
--   `i.diskᶜ ⊆ f '' abs_Ioi r`  (2)
-- These are both open sets, and `f '' abs_Ioi r` is connected.  Can we show (1) via
-- `IsPreconnected.relative_clopen`.  We'd need
--    `(f '' abs_Ioi r ∩ i.diskᶜ).Nonempty`  -- `i.disk` is compact, `f '' abs_Ioi r` is unbounded
--    `f '' abs_Ioi r ∩ i.diskᶜ ⊆ interior i.diskᶜ`  -- `i.diskᶜ` is open
--    `f '' abs_Ioi r ∩ closure i.diskᶜ ⊆ i.diskᶜ`  -- The boundary of `i.diskᶜ` is the boundary
--      of `i.disk`, which is `f '' sphere 0 r`, so intersection is impossible by injectivity
-- What about (2)?  Let's also try `IsPreconnected.relative_clopen`.  We only need
--    `i.diskᶜ ∩ closure (f '' abs_Ioi r) ⊆ f '' abs_Ioi r`  -- This would follow if
--       `closure (f '' abs_Ioi r) = f '' abs_Ici r`, again by injectivity.
--       `ContinuousOn.image_closure` shows that `f '' abs_Ici r ⊆ closure (f '' abs_Ioi r)`.  The
--       other direction follows if `f '' abs_Ici r` is closed, which holds because `f z ≈ z` for
--       large `z`.

lemma WindOutside.isClosed_image (i : WindOutside f r) : IsClosed (f '' norm_Ici r) := by
  rw [isClosed_iff_frequently]
  intro w h
  generalize ht : max (2 * r) (2 * ‖w‖) = t
  have t0 : 0 < t := by rw [← ht]; bound
  have b : ∀ᶠ z in 𝓝 w, z ∈ f '' norm_Ici r → z ∈ f '' norm_Icc r t := by
    have n : ∀ᶠ z in 𝓝 w, ‖z‖ < 2 / 3 * t := by
      apply continuous_norm.continuousAt.eventually_lt continuousAt_const
      rw [←ht]
      by_cases w0 : w = 0
      · simp only [w0, norm_zero, mul_zero]; rw [max_eq_left (by bound)]; bound
      · replace w0 : 0 < ‖w‖ := norm_pos_iff.mpr w0
        linarith [le_max_right (2 * r) (2 * ‖w‖)]
    filter_upwards [n]
    simp only [norm_Ici, mem_image, mem_setOf_eq, norm_Icc, mem_preimage, mem_Icc,
      forall_exists_index, and_imp]
    intro fz fzt z rz zfz
    simp only [← zfz] at fzt ⊢
    refine ⟨z, ⟨rz, ?_⟩, rfl⟩
    contrapose fzt
    simp only [not_le, not_lt] at fzt ⊢
    refine le_trans ?_ (i.le_norm rz)
    linarith
  replace h := h.mp b
  rw [← mem_closure_iff_frequently, IsClosed.closure_eq] at h
  · exact image_mono norm_Icc_subset_norm_Ici h
  · apply IsCompact.isClosed
    apply isCompact_norm_Icc.image_of_continuousOn
    exact i.fa.continuousOn.mono norm_Icc_subset_norm_Ici

lemma WindOutside.not_isBounded_image (i : WindOutside f r) : ¬IsBounded (f '' norm_Ioi r) := by
  by_contra h
  rw [← NormedSpace.isVonNBounded_iff ℂ, NormedSpace.image_isVonNBounded_iff] at h
  rcases h with ⟨s, h⟩
  generalize ht : max (2 * r) (2 * s) = t
  have t0 : 0 < t := by rw [← ht]; bound
  have st : 2 * s ≤ t := by rw [← ht]; bound
  generalize hw : (t : ℂ) = w
  have aw : ‖w‖ = t := by rw [← hw]; simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos t0]
  have rw : r < ‖w‖ := by rw [aw, ← ht]; bound
  specialize @h w (by simp only [norm_Ioi, mem_setOf_eq, rw])
  contrapose h
  simp only [not_le]
  refine lt_of_lt_of_le ?_ (i.le_norm rw.le)
  rw [aw]; linarith

lemma WindOutside.isOpen_image (i : WindOutside f r) : IsOpen (f '' norm_Ioi r) := by
  have fa : AnalyticOnNhd ℂ f (norm_Ioi r) := i.fa.mono norm_Ioi_subset_norm_Ici
  have pc : IsPreconnected (norm_Ioi r) := isPreconnected_norm_Ioi
  rcases fa.is_constant_or_isOpen pc with ⟨w,h⟩ | h
  · have b : IsBounded (f '' norm_Ioi r) := by
      rw [← NormedSpace.isVonNBounded_iff ℂ, NormedSpace.image_isVonNBounded_iff]
      use ‖w‖
      intro z m
      simp only [h _ m, le_refl]
    exfalso
    exact i.not_isBounded_image b
  · exact h _ (le_refl _) isOpen_norm_Ioi

/-- `f '' norm_Ioi r` is unbounded and `disk i` is bounded, so `left ∩ rightᶜ` is nonempty -/
lemma WindOutside.nonempty_inter (i : WindOutside f r) : (f '' norm_Ioi r ∩ i.diskᶜ).Nonempty := by
  apply nonempty_of_not_subset
  have b := i.not_isBounded_image
  contrapose b; simp only [not_not] at b ⊢
  exact i.isCompact_disk.isBounded.subset b

/-- `i.discᶜ` is preconnected -/
lemma WindOutside.isPreconnected_compl_disk (i : WindOutside f r) : IsPreconnected i.diskᶜ := by
  apply IsConnected.isPreconnected
  apply IsPathConnected.isConnected
  sorry
  --· exact i.isCompact_disk.isClosed
  --· exact isPathConnected_sphere

/-- If we wind outside `r`, the complement of the image is star-shaped -/
lemma WindOutside.image_eq_compl_disk (i : WindOutside f r) : f '' norm_Ioi r = i.diskᶜ := by
  apply subset_antisymm
  · rw [← i.isCompact_disk.isClosed.isOpen_compl.interior_eq]
    apply IsPreconnected.relative_clopen
    · exact isPreconnected_norm_Ioi.image _ (i.fa.continuousOn.mono norm_Ioi_subset_norm_Ici)
    · exact i.nonempty_inter
    · rw [i.isCompact_disk.isClosed.isOpen_compl.interior_eq]
      apply inter_subset_right
    · intro z ⟨m0,m1⟩
      by_cases m2 : z ∈ interior i.diskᶜ
      · exact interior_subset m2
      · have m3 : z ∈ frontier i.diskᶜ := ⟨m1,m2⟩
        rw [frontier_compl] at m3
        replace m3 := i.frontier_disk_subset m3
        rcases m0 with ⟨w0,⟨w0r,w0z⟩⟩
        rcases m3 with ⟨w1,⟨w1r,w1z⟩⟩
        simp only [norm_Ioi, mem_setOf_eq, mem_sphere_iff_norm, sub_zero] at w0r w1r
        have w01 := (i.inj.eq_iff ?_ ?_).mp (w0z.trans w1z.symm)
        · simp only [w01] at w0r; linarith
        · simp only [norm_Ici, mem_setOf_eq]; bound
        · simp only [norm_Ici, mem_setOf_eq, w1r, le_refl]
  · rw [← i.isOpen_image.interior_eq]
    apply IsPreconnected.relative_clopen
    · exact i.isPreconnected_compl_disk
    · exact inter_comm _ _ ▸ i.nonempty_inter
    · intro z ⟨_,m⟩
      rwa [i.isOpen_image.interior_eq]
    · rw [closure_eq_self_union_frontier, inter_union_distrib_left]
      apply union_subset inter_subset_right


/-- If we wind outside `r`, the complement of the image is star-shaped -/
lemma WindOutside.compl_image_eq (i : WindOutside f r) : (f '' norm_Ioi r)ᶜ = i.disk := by
  stop
  ext w
  constructor
  · sorry
  · intro ⟨t,⟨t0,t1⟩,z,m,e⟩
    simp only [Complex.real_smul] at e
    simp only [← e, abs_Ioi, mem_compl_iff, mem_image, mem_setOf_eq, not_exists, not_and]
    -- We have a collision `f w = t * f z` for `r < abs w`, `t ∈ Icc 0 1`.  Let `u` be the
    -- set of such `w`.  We will show that `abs '' u` is clopen w.r.t. `Ici (abs z)`: we can't
    -- hit `t = 1` by injectivity so we're open by the open mapping theorem, and we're relatively
    -- closed by construction.  But then for sufficiently large radius we get a contradiction.

    /-
    generalize hu : abs_Ici r ∩ f ⁻¹' i.disk = u
    have uc : IsClosed u := by
      rw [← hu]
      apply ContinuousOn.preimage_isClosed_of_isClosed
      · exact i.fa.continuousOn
      · exact isClosed_abs_Ici
      · exact i.isCompact_disk.isClosed
    -/
