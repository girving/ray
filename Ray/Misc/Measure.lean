import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Prod
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Ray.Misc.Topology
import Ray.Tactic.Bound

/-!
## Miscellaneous measure theory lemmas
-/

open Filter (liminf limsup atTop Tendsto)
open Function (curry uncurry)
open MeasureTheory
open Metric (ball closedBall sphere)
open Set (Ioc Icc)
open scoped Real ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [SecondCountableTopology E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {X : Type} [MeasureSpace X] [MetricSpace X] [BorelSpace X]
variable {Y : Type} [MeasureSpace Y] [MetricSpace Y] [BorelSpace Y]
variable {A : Type} [TopologicalSpace A]

/-- If a set has measure 0, any subset does too -/
theorem null_subset {s t : Set ℝ} (h : s ⊆ t) : volume t = 0 → volume s = 0 := by
  simp_rw [← le_zero_iff]; exact le_trans (measure_mono h)

/-- Two functions are `ae =` on a set if the expected ae statement holds -/
theorem ae_eq_on_def {Y : Type} {f g : X → Y} {s : Set X} (m : MeasurableSet s) :
    f =ᵐ[volume.restrict s] g ↔ ∀ᵐ x, x ∈ s → f x = g x := by
  rw [Filter.EventuallyEq, ae_restrict_iff' m]

/-- Removing a null set isn't significant measure-wise -/
theorem ae_minus_null {s t : Set X} (tz : volume t = 0) : s =ᵐ[volume] s \ t := by
  simp only [Filter.EventuallyEq._eq_1, Pi.sdiff_apply, eq_iff_iff]
  have e : ∀ x, x ∉ t → (x ∈ s ↔ x ∈ s \ t) := by
    intro x h; simp only [Set.mem_diff, h, not_false_iff, and_true_iff]
  simp_rw [Set.mem_def] at e
  refine Filter.Eventually.mono ?_ e
  rw [ae_iff]; simpa [Set.setOf_set]

/-- Removing a point isn't significant measure-wise (if there are no atoms) -/
theorem ae_minus_point [NoAtoms (volume : Measure X)] {s : Set X} {x : X} :
    s =ᵐ[volume] (s \ {x} : Set X) :=
  ae_minus_null (measure_singleton x)

/-- `ℝ × ℝ` has additive Haar measure.
    Lean fails to infer this, so I'm caching it for easy access. -/
instance ProdRealReal.isAddHaarMeasure_volume : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure :=
  MeasureTheory.Measure.prod.instIsAddHaarMeasure _ _

/-- `ℂ` has additive Haar measure -/
instance Complex.isAddHaarMeasure_volume : (volume : Measure ℂ).IsAddHaarMeasure := by
  have v : (volume : Measure ℂ) = volume.map Complex.equivRealProdAddHom.symm := by
    have e : (⇑Complex.measurableEquivRealProd.symm : ℝ × ℝ → ℂ) =
        ⇑Complex.equivRealProdAddHom.symm := by
      funext x
      simp only [Complex.ext_iff, Complex.measurableEquivRealProd,
        Homeomorph.toMeasurableEquiv_symm_coe, ContinuousLinearEquiv.symm_toHomeomorph,
        ContinuousLinearEquiv.coe_toHomeomorph, Complex.equivRealProdCLM_symm_apply_re,
        Complex.equivRealProdAddHom_symm_apply_re, eq_self_iff_true,
        Complex.equivRealProdCLM_symm_apply_im, Complex.equivRealProdAddHom_symm_apply_im,
        and_self_iff]
    rw [←e]; clear e
    exact (MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).map_eq.symm
  rw [v]
  have e : (⇑Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) =
      ⇑Complex.equivRealProdAddHom.symm.toAddMonoidHom := by
    funext x
    simp only [Complex.ext_iff, AddEquiv.coe_toAddMonoidHom, Complex.equivRealProdCLM_symm_apply_re,
      Complex.equivRealProdAddHom_symm_apply_re, eq_self_iff_true,
      Complex.equivRealProdCLM_symm_apply_im, Complex.equivRealProdAddHom_symm_apply_im,
      and_self_iff]
  apply Measure.isAddHaarMeasure_map (volume : Measure (ℝ × ℝ))
    Complex.equivRealProdAddHom.symm.toAddMonoidHom
  · rw [←e]; apply ContinuousLinearEquiv.continuous
  · apply AddEquiv.surjective
  · rw [←e]; exact Complex.equivRealProdCLM.symm.toHomeomorph.toCocompactMap.cocompact_tendsto'

/-- `ℂ` has no atoms -/
instance Complex.noAtoms_volume : NoAtoms (volume : Measure ℂ) where
  measure_singleton := by
    intro z
    rw [←(MeasurePreserving.symm _ Complex.volume_preserving_equiv_real_prod).measure_preimage]
    · rw [←MeasurableEquiv.image_eq_preimage, Set.image_singleton,
        MeasureTheory.NoAtoms.measure_singleton]
    · apply MeasurableSet.singleton

/-- The property that a set has finite, positive measure.
    This means that multiplication and division by the measure are invertible operations. -/
structure NiceVolume (s : Set X) : Prop where
  measurable : MeasurableSet s
  finite : volume s < ∞
  pos : volume s > 0

-- Useful lemmas about NiceVolume
theorem NiceVolume.ne_zero {s : Set X} (sn : NiceVolume s) : volume s ≠ 0 := sn.pos.ne'
theorem NiceVolume.ne_top {s : Set X} (sn : NiceVolume s) : volume s ≠ ⊤ := sn.finite.ne
theorem NiceVolume.real_pos {s : Set X} (sn : NiceVolume s) : 0 < (volume s).toReal :=
  ENNReal.toReal_pos_iff.mpr ⟨sn.pos, sn.finite⟩
theorem NiceVolume.real_nonneg {s : Set X} (sn : NiceVolume s) : (volume s).toReal ≠ 0 :=
  sn.real_pos.ne'

/-- Constants are integrable on NiceVolume sets -/
theorem NiceVolume.integrableOn_const {s : Set X} (sn : NiceVolume s) (c : ℝ) :
    IntegrableOn (fun _ : X ↦ c) s :=
  integrableOn_const.mpr (Or.inr sn.finite)

/-- Uniform limits of continuous functions and integrals commute -/
theorem TendstoUniformlyOn.integral_tendsto {f : ℕ → X → E} {g : X → E} {s : Set X}
    [IsLocallyFiniteMeasure (volume : Measure X)] (u : TendstoUniformlyOn f g atTop s)
    (fc : ∀ n, ContinuousOn (f n) s) (sc : IsCompact s) :
    Tendsto (fun n ↦ ∫ x in s, f n x) atTop (nhds (∫ x in s, g x)) := by
  rcases u.uniformCauchySeqOn.bounded fc sc with ⟨b, _, bh⟩
  apply tendsto_integral_of_dominated_convergence (F := f) (f := g) (fun _ ↦ b)
  · intro n; exact (fc n).aestronglyMeasurable sc.measurableSet
  · exact continuousOn_const.integrableOn_compact sc
  · intro n; specialize bh n; rw [ae_restrict_iff' sc.measurableSet]
    exact ae_of_all _ bh
  · rw [ae_restrict_iff' sc.measurableSet]; apply ae_of_all; intro x xs; exact u.tendsto_at xs

/-- An abbreviation for Ioc 0 (2*π) -/
def itau := Ioc 0 (2 * π)

-- Lemmas about Itau
theorem itau_volume : volume itau = ENNReal.ofReal (2 * π) := by
  simp only [itau, Real.volume_Ioc, sub_zero]
theorem itau_real_volume : (volume itau).toReal = 2 * π := by
  simp only [itau_volume, ENNReal.toReal_ofReal Real.two_pi_pos.le]
theorem NiceVolume.itau : NiceVolume itau :=
  { measurable := by simp only [_root_.itau, gt_iff_lt, zero_lt_two, mul_pos_iff_of_pos_left, not_lt,
      ge_iff_le, measurableSet_Ioc]
    finite := by simp only [itau_volume, ENNReal.ofReal_lt_top]
    pos := by simp only [itau_volume, gt_iff_lt, ENNReal.ofReal_pos, zero_lt_two,
      mul_pos_iff_of_pos_left, Real.pi_pos] }
theorem measurableSet_itau : MeasurableSet itau := by
  simp only [itau, measurableSet_Ioc]
theorem tau_mem_itau : 2*π ∈ itau := by
  simp only [itau, Set.mem_Ioc, gt_iff_lt, zero_lt_two, mul_pos_iff_of_pos_left, Real.pi_pos,
    le_refl, and_self]

/-- Continuous functions are integrable on spheres -/
theorem ContinuousOn.integrableOn_sphere {f : ℂ → E} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (closedBall c r)) (rp : 0 < r) :
    IntegrableOn (fun t ↦ f (circleMap c r t)) itau := by
  apply Continuous.integrableOn_Ioc; apply fc.comp_continuous (continuous_circleMap _ _)
  intro t; simp only [Metric.mem_closedBall, Complex.dist_eq, circleMap_sub_center,
    abs_circleMap_zero, abs_of_pos rp, le_refl]

/-- Continuous functions are integrable on `closedBall` -/
theorem ContinuousOn.integrableOn_closedBall {f : ℂ → E} {c : ℂ} {r : ℝ}
    (fc : ContinuousOn f (closedBall c r)) : IntegrableOn f (closedBall c r) :=
  fc.integrableOn_compact (isCompact_closedBall _ _)

/-- Averages add -/
theorem Average.add {f g : X → E} {s : Set X} (fi : IntegrableOn f s) (gi : IntegrableOn g s) :
    ⨍ z in s, f z + g z = (⨍ z in s, f z) + ⨍ z in s, g z := by
  simp_rw [average_eq, integral_add fi gi, smul_add]

/-- Averages subtract -/
theorem Average.sub {f g : X → E} {s : Set X} (fi : IntegrableOn f s) (gi : IntegrableOn g s) :
    ⨍ z in s, f z - g z = (⨍ z in s, f z) - ⨍ z in s, g z := by
  simp_rw [average_eq, integral_sub fi gi, smul_sub]

/-- Averages commute with linear maps -/
theorem average_linear_comm {f : X → E} {s : Set X} (fi : IntegrableOn f s) (g : E →L[ℝ] F) :
    ⨍ x in s, g (f x) = g (⨍ x in s, f x) := by
  simp only [average_eq, Complex.smul_re, MeasurableSet.univ, Measure.restrict_apply,
    Set.univ_inter, SMulHomClass.map_smul]
  by_cases v0 : (volume s).toReal = 0; simp [v0]
  rw [(Ne.isUnit v0).inv.smul_left_cancel]
  exact ContinuousLinearMap.integral_comp_comm _ fi

/-- Averages on a set depend only on ae values within the set -/
theorem average_congr_on {f g : X → E} {s : Set X} (sn : NiceVolume s)
    (h : ∀ᵐ x, x ∈ s → f x = g x) : ⨍ x in s, f x = ⨍ x in s, g x := by
  rw [← ae_eq_on_def sn.measurable] at h; exact average_congr h

/-- Means are at most the values of the function -/
theorem mean_bound {f : X → ℝ} {s : Set X} {b : ℝ} (sn : NiceVolume s) (fi : IntegrableOn f s)
    (fb : ∀ z, z ∈ s → f z ≤ b) : ⨍ x in s, f x ≤ b := by
  rw [average_eq, smul_eq_mul]
  have bi := sn.integrableOn_const b
  have ib := set_integral_mono_on fi bi sn.measurable fb
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, ge_iff_le] at ib ⊢
  trans (volume s).toReal⁻¹ * ((volume s).toReal * b)
  · gcongr; apply le_trans ib
    simp only [integral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
      smul_eq_mul, le_refl]
  · rw [←mul_assoc _ _ b, inv_mul_cancel sn.real_nonneg, one_mul]

/-- Sets where each point is near positive volume -/
def LocalVolumeSet (s : Set X) :=
  ∀ x r, x ∈ s → 0 < r → 0 < volume (s ∩ ball x r)

/-- Sets in the closure of their interior have local volume -/
theorem LocalVolume.closure_interior (s : Set X) (bp : ∀ (x : X) (r), r > 0 → volume (ball x r) > 0)
    (ci : s ⊆ closure (interior s)) : LocalVolumeSet s := by
  intro x r xs rp
  have xci := ci xs
  rcases Metric.mem_closure_iff.mp xci r rp with ⟨y, ys, xy⟩
  rcases Metric.isOpen_iff.mp isOpen_interior y ys with ⟨e, ep, ye⟩
  set t := min e (r - dist x y)
  have es : ball y t ⊆ s ∩ ball x r := by
    simp only [Set.subset_inter_iff]; constructor
    exact _root_.trans (Metric.ball_subset_ball (by bound)) (_root_.trans ye interior_subset)
    apply Metric.ball_subset_ball'
    trans r - dist x y + dist y x; bound; simp [dist_comm]
  exact lt_of_lt_of_le (bp y t (by bound)) (measure_mono es)

/-- Ioc has local volume -/
theorem LocalVolume.Ioc {a b : ℝ} : LocalVolumeSet (Set.Ioc a b) := by
  apply LocalVolume.closure_interior
  · intro x r rp
    simp only [Real.volume_ball, gt_iff_lt, ENNReal.ofReal_pos, mul_pos_iff_of_pos_left,
      zero_lt_bit0, zero_lt_one]
    bound
  · by_cases ab : a = b; · simp only [ab, Set.Ioc_self, Set.empty_subset]
    simp only [interior_Ioc, closure_Ioo ab, Set.Ioc_subset_Icc_self]

/-- itau has local volume -/
theorem LocalVolume.itau : LocalVolumeSet itau := LocalVolume.Ioc

/-- If an interval mean is above b, and each value is below b, then each value is exactly b -/
theorem mean_squeeze {f : X → ℝ} {s : Set X} {b : ℝ} (sn : NiceVolume s) (lv : LocalVolumeSet s)
    (fc : ContinuousOn f s) (fi : IntegrableOn f s) (lo : b ≤ ⨍ x in s, f x)
    (hi : ∀ x, x ∈ s → f x ≤ b) : ∀ x, x ∈ s → f x = b := by
  contrapose lo; rw [average_eq]
  simp only [Algebra.id.smul_eq_mul, not_le]
  simp only [not_forall] at lo
  rcases lo with ⟨x, xs, fx'⟩
  have fx := lt_of_le_of_ne (hi x xs) fx'; clear fx'
  rcases Metric.continuousOn_iff.mp fc x xs ((b - f x) / 2) (by linarith) with ⟨e, ep, he⟩
  have vtp' := lv x e xs ep
  generalize ht : s ∩ ball x e = t; rw [ht] at vtp'
  have ts : t ⊆ s := by rw [← ht]; exact Set.inter_subset_left _ _
  have tf : volume t < ⊤ := lt_of_le_of_lt (measure_mono ts) sn.finite
  have tm : MeasurableSet t := by
    rw [← ht]; exact MeasurableSet.inter sn.measurable measurableSet_ball
  have sc : s \ t ∪ t = s := Set.diff_union_of_subset ts
  nth_rw 2 [← sc]
  rw [integral_union]
  simp only [MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, gt_iff_lt]
  · set m := (b + f x) / 2
    set vs := (volume s).toReal
    set vt := (volume t).toReal
    have vsp : vs > 0 := sn.real_pos
    have vtp : vt > 0 := ENNReal.toReal_pos (vtp'.ne') (lt_top_iff_ne_top.mp tf)
    rw [inv_mul_lt_iff' vsp]
    have mb : m < b := by
      calc (b + f x) / 2
        _ < (b + b) / 2 := (div_lt_div_right (by norm_num)).mpr (by bound)
        _ = b := by ring
    have i0 : ∫ x in s \ t, f x ≤ (vs - vt) * b := by
      set b' := fun _ ↦ b
      have df : volume (s \ t) < ⊤ := lt_of_le_of_lt (measure_mono (Set.diff_subset _ _)) sn.finite
      have dm : MeasurableSet (s \ t) := MeasurableSet.diff sn.measurable tm
      have fb := @set_integral_mono_on _ _ volume f b' (s \ t)
        (fi.mono (Set.diff_subset _ _) (le_refl _)) (integrableOn_const.mpr (Or.inr df)) dm ?_
      simp [measure_diff ts tm (lt_top_iff_ne_top.mp tf),
        ENNReal.toReal_sub_of_le (measure_mono ts) (lt_top_iff_ne_top.mp sn.finite)] at fb
      exact fb
      intro y yd; simp at yd; exact hi y yd.left
    have i1 : ∫ x in t, f x ≤ vt * m := by
      set m' := fun _ ↦ m
      have fm := @set_integral_mono_on _ _ volume f m' t (fi.mono ts (le_refl _))
        (integrableOn_const.mpr (Or.inr tf)) tm ?_
      simp at fm; exact fm
      intro y yt
      rw [← ht] at yt; simp at ht yt
      specialize he y yt.left yt.right
      simp [Real.dist_eq] at he
      calc
        f y = f x + (f y - f x) := by ring
        _ ≤ f x + |f y - f x| := by bound
        _ ≤ f x + (b - f x) / 2 := by bound
        _ = (b + f x) / 2 := by ring
    calc
      (∫ x : X in s \ t, f x) + ∫ x : X in t, f x ≤ (vs - vt) * b + vt * m := by bound
      _ = vs * b - vt * (b - m) := by ring
      _ < vs * b - 0 := (sub_lt_sub_left (by bound) _)
      _ = b * vs := by ring
  · rw [disjoint_comm]; exact Set.disjoint_sdiff_right
  · exact tm
  · exact fi.mono (Set.diff_subset _ _) (le_refl _)
  · exact fi.mono ts (le_refl _)

theorem ContinuousOn.intervalIntegral {f : X → ℝ → E} {s : Set X} {a b : ℝ}
    (fc : ContinuousOn (uncurry f) (s ×ˢ Icc a b)) (sc : IsCompact s) (ab : a ≤ b) :
    ContinuousOn (fun x ↦ ∫ t in a..b, f x t) s := by
  rcases ((sc.prod isCompact_Icc).bddAbove_image fc.norm).exists_ge 0 with ⟨c, _, fb⟩
  simp only [Set.ball_image_iff] at fb
  simp only [Set.forall_prod_set, uncurry] at fb
  have e : ∀ x t, f x t = (uncurry f) (x, t) := by
    simp only [Function.uncurry_apply_pair, eq_self_iff_true, forall_const, imp_true_iff]
  intro x xs
  apply intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ ↦ c)
  · apply eventually_nhdsWithin_of_forall; intro y ys
    refine' ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    rw [Set.uIoc_of_le ab]; simp_rw [e]; apply fc.comp
    · apply Continuous.continuousOn; exact Continuous.Prod.mk y
    · intro t ts; exact Set.mk_mem_prod ys (Set.Ioc_subset_Icc_self ts)
  · apply eventually_nhdsWithin_of_forall; intro y ys; rw [Set.uIoc_of_le ab]
    apply ae_of_all; intro t ts; apply fb _ ys _ (Set.Ioc_subset_Icc_self ts)
  · exact intervalIntegrable_const
  · apply ae_of_all; intro t ts; simp_rw [e]; apply fc.comp
    · apply Continuous.continuousOn; exact Continuous.Prod.mk_left t
    · rw [Set.uIoc_of_le ab] at ts
      intro y ys; exact Set.mk_mem_prod ys (Set.Ioc_subset_Icc_self ts)
    · assumption

/-- `liminf` preserves ae measurability, general filter version -/
theorem aEMeasurable_liminf' {I I' : Type} {u : Filter I} {f : I → X → ENNReal} {μ : Measure X}
    {p : I' → Prop} {s : I' → Set I} (fm : ∀ n, AEMeasurable (f n) μ) (uc : u.HasCountableBasis p s)
    (sc : ∀ i, (s i).Countable) : AEMeasurable (fun x ↦ u.liminf fun n ↦ f n x) μ := by
  simp_rw [uc.toHasBasis.liminf_eq_iSup_iInf]
  refine' aemeasurable_biSup _ uc.countable _
  intro i _; exact aemeasurable_biInf _ (sc i) (fun n _ ↦ fm n)

/-- `liminf` preserves ae measurability, `ℕ` version -/
theorem aEMeasurable_liminf {f : ℕ → X → ENNReal} {μ : Measure X} (fm : ∀ n, AEMeasurable (f n) μ) :
    AEMeasurable (fun x ↦ atTop.liminf fun n ↦ f n x) μ :=
  aEMeasurable_liminf' fm Filter.atTop_countable_basis fun _ ↦ Set.to_countable _

theorem set_lintegral_mono_aEMeasurable {s : Set X} {f g : X → ENNReal}
    (sm : MeasurableSet s) (fg : ∀ x, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ≤ ∫⁻ x in s, g x := by
  apply lintegral_mono_ae; rw [ae_restrict_iff' sm]; exact ae_of_all _ fg
