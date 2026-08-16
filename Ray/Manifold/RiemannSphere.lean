module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Ray.Manifold.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Tactic.Cases
import Ray.Analytic.Analytic
import Ray.Manifold.Analytic
import Ray.Manifold.OneDimension
import Ray.Misc.Cobounded

/-!
## The Riemann sphere

We give `OnePoint ℂ` the natural analytic manifold structure with two charts,
namely `coe` and `inv ∘ coe`, giving the Riemann sphere `𝕊`.
-/

open Bornology (cobounded)
open Classical
open Complex
open Filter (Tendsto atTop)
open Function (curry uncurry)
open OneDimension
open Set
open scoped Topology OnePoint
noncomputable section

variable {α : Type}

/-- A left inverse to `coe : ℂ → 𝕊`.
    We put this outside the `RiemannSphere` namespace so that `z.toComplex` works. -/
public def OnePoint.toComplex (z : OnePoint ℂ) : ℂ := z.rec 0 id

namespace RiemannSphere

/-- The Riemann sphere, as a complex manifold -/
scoped notation "𝕊" => OnePoint ℂ

-- Basic instances for 𝕊
public instance : Zero 𝕊 := ⟨((0 : ℂ) : 𝕊)⟩
public instance : Inhabited 𝕊 := ⟨0⟩
@[simp] public theorem coe_zero : ((0 : ℂ) : 𝕊) = (0 : 𝕊) := rfl
@[simp] public theorem coe_eq_coe {z w : ℂ} : (z : 𝕊) = w ↔ z = w := OnePoint.coe_eq_coe
@[simp] public theorem coe_eq_zero (z : ℂ) : (z : 𝕊) = (0 : 𝕊) ↔ z = 0 := by
  simp only [← coe_zero, coe_eq_coe]

/-- `coe : ℂ → 𝕊` is injective -/
public theorem injective_coe : Function.Injective (fun z : ℂ ↦ (z : 𝕊)) := OnePoint.coe_injective

/-- `coe : ℂ → 𝕊` is continuous -/
public theorem continuous_coe : Continuous (fun z : ℂ ↦ (z : 𝕊)) := OnePoint.continuous_coe

-- Recursion lemmas
@[simp] public theorem rec_coe {C : 𝕊 → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : 𝕊)} (z : ℂ) :
    (z : 𝕊).rec i f = f z := rfl
@[simp] public theorem rec_inf {C : 𝕊 → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : 𝕊)} :
    (∞ : 𝕊).rec i f = i := rfl
theorem map_rec {A B : Sort*} (g : A → B) {f : ℂ → A} {i : A} {z : 𝕊} :
    g (z.rec i f) = (z.rec (g i) (g ∘ f)) := by
  induction z using OnePoint.rec
  · simp only [rec_inf]
  · simp only [rec_coe, Function.comp]

-- ∞ is not 0 or finite
@[simp] public theorem inf_ne_coe {z : ℂ} : (∞ : 𝕊) ≠ ↑z := by
  simp only [Ne, OnePoint.infty_ne_coe, not_false_iff]
@[simp] public theorem inf_ne_zero : (∞ : 𝕊) ≠ (0 : 𝕊) := by
  have e : (0 : 𝕊) = ((0 : ℂ) : 𝕊) := rfl; rw [e]; exact inf_ne_coe
@[simp] public theorem zero_ne_inf : (0 : 𝕊) ≠ (∞ : 𝕊) := inf_ne_zero.symm
@[simp] public theorem coe_ne_inf {z : ℂ} : (z : 𝕊) ≠ ∞ := inf_ne_coe.symm
@[simp] public theorem coe_eq_inf_iff {z : ℂ} : (z : 𝕊) = ∞ ↔ False := ⟨coe_ne_inf, False.elim⟩

-- Conversion to ℂ, sending ∞ to 0
@[simp] public theorem toComplex_coe {z : ℂ} : (z : 𝕊).toComplex = z := by rfl
@[simp] public theorem toComplex_inf : (∞ : 𝕊).toComplex = 0 := by rfl
public theorem coe_toComplex {z : 𝕊} (h : z ≠ ∞) : ↑z.toComplex = z := by
  induction z using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at h
  · simp only [toComplex_coe]
@[simp] public lemma  toComplex_zero : (0 : 𝕊).toComplex = 0 := by rw [← coe_zero, toComplex_coe]
@[simp] public lemma toComplex_eq_zero {z : 𝕊} : z.toComplex = 0 ↔ z = 0 ∨ z = ∞ := by
  induction z using OnePoint.rec
  · simp only [toComplex_inf, or_true]
  · simp only [toComplex_coe, coe_eq_zero, OnePoint.coe_ne_infty, or_false]
public theorem continuousAt_toComplex {z : ℂ} : ContinuousAt OnePoint.toComplex z := by
  simp only [OnePoint.continuousAt_coe]; exact continuousAt_id
public theorem continuousOn_toComplex : ContinuousOn OnePoint.toComplex ({∞}ᶜ) := by
  intro z m; induction z using OnePoint.rec
  · simp only [mem_compl_iff, mem_singleton_iff, not_true] at m
  · exact continuousAt_toComplex.continuousWithinAt

/-- `toComplex` is injective away from `∞` -/
public lemma toComplex_inj {z w : 𝕊} (zi : z ≠ (∞ : 𝕊)) (wi : w ≠ (∞ : 𝕊)) :
    z.toComplex = w.toComplex ↔ z = w := by
  induction' z using OnePoint.rec
  all_goals induction' w using OnePoint.rec
  all_goals simp_all

/-- Inversion in `𝕊`, interchanging `0` and `∞` -/
public def inv (z : 𝕊) : 𝕊 := if z = 0 then ∞ else ↑z.toComplex⁻¹
public instance : Inv 𝕊 := ⟨RiemannSphere.inv⟩
theorem inv_def (z : 𝕊) : z⁻¹ = RiemannSphere.inv z := by rfl
public instance : InvolutiveInv 𝕊 where
  inv := Inv.inv
  inv_inv := by
    simp_rw [inv_def, inv]; apply OnePoint.rec
    · simp only [inf_ne_zero, toComplex_inf, inv_zero, coe_zero, ite_false, toComplex_zero,
        ite_true]
    · intro z; by_cases z0 : z = 0
      · simp only [z0, coe_zero, toComplex_zero, inv_zero, ite_true, inf_ne_zero, toComplex_inf,
          ite_false]
      · simp only [coe_eq_zero, z0, toComplex_coe, ite_false, inv_eq_zero, inv_inv]
@[simp] public lemma inv_zero' : (0 : 𝕊)⁻¹ = ∞ := by simp only [inv_def, inv, if_true]
@[simp] public lemma inv_inf : ((∞ : 𝕊)⁻¹ : 𝕊) = 0 := by simp [inv_def, inv, inf_ne_zero]

public theorem inv_coe {z : ℂ} (z0 : z ≠ 0) : (z : 𝕊)⁻¹ = ↑(z : ℂ)⁻¹ := by
  simp only [inv_def, inv, z0, toComplex_coe, if_false, coe_eq_zero]
@[simp] public lemma inv_eq_inf {z : 𝕊} : z⁻¹ = ∞ ↔ z = 0 := by
  induction z using OnePoint.rec
  · simp only [inv_inf]; exact ⟨Eq.symm, Eq.symm⟩
  · simp only [inv_def, inv, not_not, imp_false, ite_eq_left_iff, OnePoint.coe_ne_infty]
@[simp] public lemma inv_eq_zero {z : 𝕊} : z⁻¹ = 0 ↔ z = ∞ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf]
  · simp only [inv_def, inv, toComplex_coe]
    by_cases z0 : (z : 𝕊) = 0; simp only [if_pos, z0, inf_ne_zero, inf_ne_zero.symm]
    simp only [if_neg z0, coe_ne_inf, iff_false]; rw [coe_eq_zero, _root_.inv_eq_zero]
    simpa only [coe_eq_zero] using z0
public theorem toComplex_inv {z : 𝕊} : z⁻¹.toComplex = z.toComplex⁻¹ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, toComplex_zero, toComplex_inf, inv_zero]
  · by_cases z0 : z = 0
    · simp only [z0, coe_zero, inv_zero', toComplex_inf, toComplex_zero, inv_zero]
    · simp only [z0, inv_coe, Ne, not_false_iff, toComplex_coe]

/-- `coe` tends to `∞` `cobounded` -/
public theorem coe_tendsto_inf : Tendsto (fun z : ℂ ↦ (z : 𝕊)) (cobounded ℂ) (𝓝 ∞) := by
  rw [Filter.tendsto_iff_comap, OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact]
  exact Metric.cobounded_le_cocompact

/-- `coe` tends to `∞` `cobounded`, but without touching `∞` -/
public theorem coe_tendsto_inf' : Tendsto (fun z : ℂ ↦ (z : 𝕊)) (cobounded _) (𝓝[{∞}ᶜ] ∞) := by
  have e : {(∞ : 𝕊)}ᶜ = range (fun z : ℂ ↦ (z : 𝕊)) := by
    ext z; induction' z using OnePoint.rec with z
    · simp only [mem_compl_iff, mem_singleton_iff, not_true, mem_range, OnePoint.coe_ne_infty,
        exists_false]
    · simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true,
        mem_range, coe_eq_coe, exists_eq]
  simp only [e, tendsto_nhdsWithin_range, coe_tendsto_inf]

@[simp] public lemma map_some_cobounded : Filter.map OnePoint.some (cobounded ℂ) = 𝓝[{∞}ᶜ] ∞ := by
  rw [@OnePoint.nhdsNE_infty_eq, Metric.cobounded_eq_cocompact, Filter.coclosedCompact_eq_cocompact]

/-- Inversion is continuous -/
public theorem continuous_inv : Continuous fun z : 𝕊 ↦ z⁻¹ := by
  rw [← continuousOn_univ]; intro z _; apply ContinuousAt.continuousWithinAt
  induction' z using OnePoint.rec with z
  · simp only [OnePoint.continuousAt_infty', Function.comp_def, Filter.coclosedCompact_eq_cocompact,
      inv_inf, ← Metric.cobounded_eq_cocompact]
    have e : ∀ᶠ z : ℂ in cobounded ℂ, ↑z⁻¹ = (↑z : 𝕊)⁻¹ := by
      refine (eventually_cobounded 0).mp (.of_forall fun z z0 ↦ ?_)
      simp only [norm_pos_iff] at z0; rw [inv_coe z0]
    apply Filter.Tendsto.congr' e
    exact Filter.Tendsto.comp continuous_coe.continuousAt inv_tendsto_cobounded'
  · simp only [OnePoint.continuousAt_coe, Function.comp_def, inv_def, inv, coe_eq_zero,
      toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, ContinuousAt, OnePoint.nhds_infty_eq, if_true,
        Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      simp only [← nhdsNE_sup_pure, Filter.tendsto_sup]
      constructor
      · refine Filter.Tendsto.mono_right ?_ le_sup_left
        apply tendsto_nhdsWithin_congr (f := fun z : ℂ ↦ (↑z⁻¹ : 𝕊))
        · intro z m
          rw [mem_compl_singleton_iff] at m
          simp only [m, ite_false]
        · simp only [map_some_cobounded]
          apply coe_tendsto_inf'.comp
          rw [← @tendsto_cobounded_iff_tendsto_nhds_zero ℂ ℂ _ _ fun z : ℂ ↦ z]
          exact Filter.tendsto_id
      · refine Filter.Tendsto.mono_right ?_ le_sup_right
        simp only [Filter.pure_zero, Filter.tendsto_pure, ite_eq_left_iff, Filter.eventually_zero,
          not_true, IsEmpty.forall_iff]
    · have e : ∀ᶠ w : ℂ in 𝓝 z, (if w = 0 then ∞ else ↑w⁻¹ : 𝕊) = ↑w⁻¹ := by
        refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
        simp only [Ne, id_eq] at w0; simp only [w0, if_false]
      simp only [continuousAt_congr e]
      exact continuous_coe.continuousAt.comp (tendsto_inv₀ z0)
instance : ContinuousInv 𝕊 := ⟨continuous_inv⟩

/-- Inversion as an equivalence -/
public def invEquiv : 𝕊 ≃ 𝕊 where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

/-- Inversion as a homeomorphism -/
public def invHomeomorph : 𝕊 ≃ₜ 𝕊 where
  toEquiv := invEquiv
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv
@[simp] public lemma invEquiv_apply (z : 𝕊) : invEquiv z = z⁻¹ := by
  simp only [invEquiv, Equiv.coe_fn_mk]
@[simp] public lemma invEquiv_symm : invEquiv.symm = invEquiv := by
  simp only [Equiv.ext_iff, invEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, forall_const]
@[simp] public lemma invHomeomorph_apply (z : 𝕊) : invHomeomorph z = z⁻¹ := by
  simp only [invHomeomorph]
  exact invEquiv_apply z
@[simp] public lemma invHomeomorph_symm : invHomeomorph.symm = invHomeomorph := Homeomorph.ext (by
  intro x
  show invEquiv.symm x = invEquiv x
  rw [invEquiv_symm])

/-- `coe : ℂ → 𝕊` as an equivalence -/
public def coePartialEquiv : PartialEquiv ℂ 𝕊 where
  toFun := fun x : ℂ ↦ x
  invFun := OnePoint.toComplex
  source := univ
  target := {∞}ᶜ
  map_source' z _ := by
    simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_iff]
  map_target' z _ := mem_univ _
  left_inv' z _ := toComplex_coe
  right_inv' z m := coe_toComplex m

/-- `coe : ℂ → 𝕊` as a partial homeomorphism.  This is the first chart of `𝕊`. -/
public def coeOpenPartialHomeomorph : OpenPartialHomeomorph ℂ 𝕊 where
  toPartialEquiv := coePartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  continuousOn_toFun := continuous_coe.continuousOn
  continuousOn_invFun := continuousOn_toComplex

/-- `inv ∘ coe : ℂ → 𝕊` as a partial homeomorphism.  This is the second chart of `𝕊`. -/
public def invCoeOpenPartialHomeomorph : OpenPartialHomeomorph ℂ 𝕊 :=
  coeOpenPartialHomeomorph.trans invHomeomorph.toOpenPartialHomeomorph

@[simp] lemma coePartialEquiv_target : coePartialEquiv.target = {∞}ᶜ := rfl
@[simp] lemma coeOpenPartialHomeomorph_target : coeOpenPartialHomeomorph.target = {∞}ᶜ := by
  simp only [coeOpenPartialHomeomorph, coePartialEquiv_target]
@[simp] lemma invCoeOpenPartialHomeomorph_target : invCoeOpenPartialHomeomorph.target = {0}ᶜ := by
  ext z; simp only [invCoeOpenPartialHomeomorph, OpenPartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    invHomeomorph_symm, coeOpenPartialHomeomorph_target, preimage_compl, univ_inter, mem_compl_iff,
    mem_preimage, invHomeomorph_apply, mem_singleton_iff, inv_eq_inf]
@[simp] public lemma coePartialEquiv_apply (z : ℂ) : coePartialEquiv z = ↑z := by rfl
@[simp] public lemma coePartialEquiv_symm_apply (z : 𝕊) : coePartialEquiv.symm z = z.toComplex := by
  rfl
@[simp] public lemma invCoeOpenPartialHomeomorph_apply (z : ℂ) :
    invCoeOpenPartialHomeomorph z = (z : 𝕊)⁻¹ := by rfl
@[simp] public lemma invCoeOpenPartialHomeomorph_symm_apply (z : 𝕊) :
    invCoeOpenPartialHomeomorph.symm z = (z⁻¹).toComplex := by rfl

/-- Chart structure for `𝕊` -/
public instance : ChartedSpace ℂ 𝕊 where
  atlas := {e | e = coeOpenPartialHomeomorph.symm ∨ e = invCoeOpenPartialHomeomorph.symm}
  chartAt z := z.rec invCoeOpenPartialHomeomorph.symm (fun _ ↦ coeOpenPartialHomeomorph.symm)
  mem_chart_source := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        invCoeOpenPartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, inf_ne_zero,
        not_false_eq_true]
    · simp only [rec_coe, OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        coeOpenPartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty,
        not_false_eq_true]
  chart_mem_atlas := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, mem_ofPred_eq, or_true]
    · simp only [rec_coe, mem_ofPred_eq, true_or]

/-- There are just two charts on `𝕊` -/
theorem two_charts {e : OpenPartialHomeomorph 𝕊 ℂ} (m : e ∈ atlas ℂ 𝕊) :
    e = coeOpenPartialHomeomorph.symm ∨ e = invCoeOpenPartialHomeomorph.symm := m

-- Chart simplification lemmas
@[simp] public lemma chartAt_coe {z : ℂ} : chartAt ℂ (z : 𝕊) = coeOpenPartialHomeomorph.symm := rfl
@[simp] public lemma chartAt_inf : @chartAt ℂ _ 𝕊 _ _ ∞ = invCoeOpenPartialHomeomorph.symm := rfl
public theorem extChartAt_coe {z : ℂ} : extChartAt I (z : 𝕊) = coePartialEquiv.symm := by
  simp only [coeOpenPartialHomeomorph, extChartAt, OpenPartialHomeomorph.extend, chartAt_coe,
    OpenPartialHomeomorph.symm_toPartialEquiv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
theorem extChartAt_zero : extChartAt I (0 : 𝕊) = coePartialEquiv.symm := by
  simp only [← coe_zero, extChartAt_coe]
public theorem extChartAt_inf :
    extChartAt I (∞ : 𝕊) = invEquiv.toPartialEquiv.trans coePartialEquiv.symm := by
  apply PartialEquiv.ext
  · intro z
    simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      OpenPartialHomeomorph.extend, chartAt_inf, OpenPartialHomeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.coe_trans_symm,
      OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm,
      invEquiv_symm, PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply, Function.comp_apply]
    show coePartialEquiv.symm (invEquiv.symm z) = coePartialEquiv.symm (invEquiv z)
    rw [invEquiv_symm]
  · intro z
    simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      invEquiv, OpenPartialHomeomorph.extend, chartAt_inf,
      OpenPartialHomeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.trans_toPartialEquiv,
      modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialEquiv.symm_symm,
      PartialEquiv.coe_trans, OpenPartialHomeomorph.coe_toPartialEquiv,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
      PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply, Equiv.coe_fn_symm_mk]
  · simp only [extChartAt, invCoeOpenPartialHomeomorph, coeOpenPartialHomeomorph, invHomeomorph,
      OpenPartialHomeomorph.extend, chartAt_inf, OpenPartialHomeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.symm_source, PartialEquiv.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm,
      invEquiv_symm, PartialEquiv.trans_source, Equiv.toPartialEquiv_source,
      Equiv.toPartialEquiv_apply]
    show univ ∩ ⇑invEquiv.symm ⁻¹' coePartialEquiv.target
      = univ ∩ ⇑invEquiv ⁻¹' coePartialEquiv.target
    rw [invEquiv_symm]
public theorem extChartAt_inf_apply {x : 𝕊} : extChartAt I ∞ x = x⁻¹.toComplex := by
  simp only [extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
    Equiv.toPartialEquiv_apply, invEquiv_apply]

/-- `𝕊`'s charts have analytic groupoid structure -/
instance : HasGroupoid 𝕊 (contDiffGroupoid ⊤ I) where
  compatible := by
    have e0 : ((fun z : ℂ ↦ (z : 𝕊)) ⁻¹' {0})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, coe_eq_zero]
    have e1 : ((fun z : ℂ ↦ (z : 𝕊)⁻¹) ⁻¹' {∞})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, inv_eq_inf, coe_eq_zero]
    have a : AnalyticOnNhd ℂ (fun z : ℂ ↦ OnePoint.toComplex (z : 𝕊)⁻¹) {0}ᶜ := by
      apply AnalyticOnNhd.congr (f := fun z ↦ z⁻¹)
      · exact isOpen_compl_singleton
      · apply analyticOnNhd_inv
      · intro z z0; simp only [mem_compl_iff, mem_singleton_iff] at z0
        simp only [inv_coe z0, toComplex_coe]
    intro f g fa ga
    simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid, mfld_simps]
    refine ⟨AnalyticOnNhd.contDiffOn ?_ ?_, AnalyticOnNhd.contDiffOn ?_ ?_⟩
    all_goals cases' two_charts fa with fh fh
    all_goals cases' two_charts ga with gh gh
    all_goals try simp [fh, gh, coeOpenPartialHomeomorph, invCoeOpenPartialHomeomorph,
      coePartialEquiv, coeOpenPartialHomeomorph, invHomeomorph, invEquiv, Function.comp_def,
      analyticOnNhd_id, e0, e1, a, uniqueDiffOn_univ]
    all_goals try exact isOpen_compl_singleton.uniqueDiffOn
    all_goals apply IsOpen.uniqueDiffOn
    all_goals convert isOpen_univ
    all_goals aesop

/-- `𝕊` is an analytic manifold -/
public instance : IsManifold I ⊤ 𝕊 where

/-- Composing with `coe` turns convergence `cobounded` into convergence to `𝓝 ∞` -/
public theorem tendsto_inf_iff_tendsto_cobounded {X : Type} {f : Filter X} {g : X → ℂ} :
    Tendsto (fun x ↦ (g x : 𝕊)) f (𝓝 ∞) ↔ Tendsto (fun x ↦ g x) f (cobounded ℂ) := by
  constructor
  · intro t; simp only [Filter.tendsto_iff_comap] at t ⊢
    rw [←Function.comp_def, ←Filter.comap_comap, OnePoint.comap_coe_nhds_infty,
      Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at t
    exact t
  · exact fun h ↦ coe_tendsto_inf.comp h

variable {X : Type} [TopologicalSpace X]
variable {Y : Type} [TopologicalSpace Y]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

/-- `coe : ℂ → 𝕊` is an open map -/
public theorem isOpenMap_coe : IsOpenMap (fun z : ℂ ↦ (z : 𝕊)) := by
  intro s o
  have e : (fun z : ℂ ↦ (z : 𝕊)) '' s = {∞}ᶜ ∩ OnePoint.toComplex ⁻¹' s := by
    apply Set.ext; intro z
    simp only [mem_image, mem_inter_iff, mem_compl_singleton_iff, mem_preimage]
    constructor
    intro ⟨x, m, e⟩; simp only [← e, toComplex_coe, m, and_true]; exact inf_ne_coe.symm
    intro ⟨n, m⟩; use z.toComplex, m, coe_toComplex n
  rw [e]; exact continuousOn_toComplex.isOpen_inter_preimage isOpen_compl_singleton o

public theorem prod_nhds_eq {x : X} {z : ℂ} :
    𝓝 (x, (z : 𝕊)) = Filter.map (fun p : X × ℂ ↦ (p.1, ↑p.2)) (𝓝 (x, z)) := by
  refine le_antisymm ?_
    (continuousAt_fst.prodMk (continuous_coe.continuousAt.comp continuousAt_snd))
  apply IsOpenMap.nhds_le; exact IsOpenMap.id.prodMap isOpenMap_coe

theorem mem_inf_of_mem_cobounded {s : Set ℂ} (f : s ∈ cobounded ℂ) :
    (fun z : ℂ ↦ (z : 𝕊)) '' s ∪ {∞} ∈ 𝓝 (∞ : 𝕊) := by
  simp only [OnePoint.nhds_infty_eq, Filter.mem_sup, Filter.coclosedCompact_eq_cocompact, ←
    Metric.cobounded_eq_cocompact, Filter.mem_map]
  exact ⟨Filter.mem_of_superset f fun _ m ↦ Or.inl (mem_image_of_mem _ m), Or.inr rfl⟩

theorem prod_mem_inf_of_mem_cobounded {s : Set (X × ℂ)} {x : X} (f : s ∈ 𝓝 x ×ˢ cobounded ℂ) :
    (fun p : X × ℂ ↦ (p.1, (p.2 : 𝕊))) '' s ∪ univ ×ˢ {∞} ∈ 𝓝 (x, (∞ : 𝕊)) := by
  rcases Filter.mem_prod_iff.mp f with ⟨t, tx, u, ui, sub⟩
  rw [nhds_prod_eq]
  refine Filter.mem_prod_iff.mpr ⟨t, tx, (fun z : ℂ ↦ (z : 𝕊)) '' u ∪ {∞},
    mem_inf_of_mem_cobounded ui, ?_⟩
  intro ⟨y, z⟩ ⟨yt, m⟩
  simp only [mem_prod_eq, mem_image, mem_union, mem_singleton_iff, mem_univ, true_and,
    Prod.ext_iff] at yt m ⊢
  induction' z using OnePoint.rec with z
  · simp only [or_true]
  · simp only [coe_eq_inf_iff, or_false, coe_eq_coe] at m ⊢
    rcases m with ⟨w, wu, wz⟩; refine ⟨⟨y, z⟩, sub (mk_mem_prod yt ?_), rfl, rfl⟩; rw [← wz]
    exact wu

/-- `coe : ℂ → 𝕊` is analytic -/
public theorem mAnalytic_coe : ContMDiff I I ⊤ (fun z : ℂ ↦ (z : 𝕊)) := by
  rw [mAnalytic_iff_of_boundaryless]; use continuous_coe; intro z
  simp only [extChartAt_coe, extChartAt_eq_refl, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, id_eq]
  rw [← PartialEquiv.invFun_as_coe]
  simp only [coePartialEquiv]
  apply analyticAt_id

/-- `OnePoint.toComplex : 𝕊 → ℂ` is analytic except at `∞` -/
public theorem mAnalyticAt_toComplex {z : ℂ} :
    ContMDiffAt I I ⊤ (OnePoint.toComplex : 𝕊 → ℂ) z := by
  rw [mAnalyticAt_iff_of_boundaryless]
  use continuousAt_toComplex
  simp only [toComplex_coe, extChartAt_coe, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.symm_symm, coePartialEquiv_symm_apply]
  apply analyticAt_id

/-- `OnePoint.toComplex : 𝕊 → ℂ` is analytic except at `∞` -/
public theorem mAnalyticAt_toComplex' {z : 𝕊} (ne : z ≠ ∞) :
    ContMDiffAt I I ⊤ (OnePoint.toComplex : 𝕊 → ℂ) z := by
  induction z using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at ne
  · apply mAnalyticAt_toComplex

/-- Inversion is analytic -/
public theorem mAnalytic_inv : ContMDiff I I ⊤ (fun z : 𝕊 ↦ z⁻¹) := by
  rw [mAnalytic_iff_of_boundaryless]
  use continuous_inv
  intro z
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, extChartAt_inf, ← coe_zero, extChartAt_coe, Function.comp_def,
      PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
      coePartialEquiv_symm_apply, toComplex_coe, PartialEquiv.coe_trans_symm,
      PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm,
      inv_inv]
    apply analyticAt_id
  · simp only [extChartAt_coe, PartialEquiv.symm_symm, Function.comp_def, coePartialEquiv_apply,
      coePartialEquiv_symm_apply, toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, coe_zero, extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
        invEquiv_apply, Equiv.toPartialEquiv_apply, inv_zero', inv_inv, toComplex_coe]
      apply analyticAt_id
    · simp only [inv_coe z0, extChartAt_coe, coePartialEquiv_symm_apply]
      refine (analyticAt_id.inv z0).congr ?_
      refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
      rw [id] at w0
      simp only [Pi.inv_apply, id, inv_coe w0, toComplex_coe]

/-- Given `f : ℂ → X`, fill in the value at `∞` to get `𝕊 → X` -/
public def fill {X : Type} (f : ℂ → X) (y : X) : 𝕊 → X := fun z ↦ z.rec y f

/-- Lift `f : ℂ → ℂ` to `𝕊 → 𝕊` by filling in a value at `∞` -/
public def lift (f : ℂ → ℂ) (y : 𝕊) : 𝕊 → 𝕊 := fun z ↦ z.rec y (fun z ↦ f z)

/-- Lift `f : X → ℂ → ℂ` to `X → 𝕊 → 𝕊` by filling in a value at `∞` -/
public def lift' (f : X → ℂ → ℂ) (y : 𝕊) : X → 𝕊 → 𝕊 := fun x z ↦ z.rec y (fun z ↦ f x z)

section Fill

variable {f : ℂ → ℂ}
variable {g : α → ℂ → ℂ}
variable {y : 𝕊} {x : α} {z : ℂ}

-- Values of `fill` and `lift` at `coe` and `∞`
@[simp] public lemma fill_coe {f : ℂ → α} {y : α} : fill f y z = f z := by rfl
@[simp] public lemma fill_inf {f : ℂ → α} {y : α} : fill f y ∞ = y := by rfl
@[simp] public lemma lift_coe : lift f y z = ↑(f z) := by rfl
@[simp] public lemma lift_coe' : lift' g y x z = ↑(g x z) := by rfl
@[simp] public lemma lift_inf : lift f y ∞ = y := by rfl
@[simp] public lemma lift_inf' : lift' g y x ∞ = y := by rfl

public lemma toComplex_lift' {w : 𝕊} (ne : w ≠ ∞) :
    (lift' g y x w).toComplex = g x w.toComplex := by
  induction w using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at ne
  · simp only [lift', rec_coe, toComplex_coe]

end Fill

variable {f : ℂ → ℂ}
variable {g : X → ℂ → ℂ}
variable {y : 𝕊} {x : X} {z : ℂ}

/-- `lift` in terms of `fill` -/
public theorem lift_eq_fill : lift f y = fill (fun z ↦ (f z : 𝕊)) y := by rfl

/-- `fill` is continuous at finite values -/
public theorem continuousAt_fill_coe {f : ℂ → X} {y : X} (fc : ContinuousAt f z) :
    ContinuousAt (fill f y) z := by
  simp only [OnePoint.continuousAt_coe, Function.comp_def, fill_coe, fc]

/-- `fill` is continuous at `∞` -/
public theorem continuousAt_fill_inf {f : ℂ → X} {y : X} (fi : Tendsto f (cobounded ℂ) (𝓝 y)) :
    ContinuousAt (fill f y) ∞ := by
  simp only [OnePoint.continuousAt_infty', Filter.coclosedCompact_eq_cocompact, ←
    Metric.cobounded_eq_cocompact, Function.comp_def, fill_coe, fill_inf, fi]

/-- `fill` is continuous -/
public theorem continuous_fill {f : ℂ → X} {y : X} (fc : Continuous f)
    (fi : Tendsto f (cobounded ℂ) (𝓝 y)) : Continuous (fill f y) := by
  rw [continuous_iff_continuousAt]; intro z; induction z using OnePoint.rec
  · exact continuousAt_fill_inf fi
  · exact continuousAt_fill_coe fc.continuousAt

/-- `fill` is analytic at finite values -/
public theorem mAnalyticAt_fill_coe [IsManifold I ⊤ T] {f : ℂ → T} {y : T}
    (fa : ContMDiffAt I I ⊤ f z) : ContMDiffAt I I ⊤ (fill f y) z := by
  have e : (fun x : 𝕊 ↦ f x.toComplex) =ᶠ[𝓝 ↑z] fill f y := by
    simp only [OnePoint.nhds_coe_eq, Filter.EventuallyEq, Filter.eventually_map, toComplex_coe,
      fill_coe, Filter.eventually_true]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ e.symm
  refine fa.comp_of_eq mAnalyticAt_toComplex ?_
  simp only [toComplex_coe]

/-- `fill` is analytic at `∞` -/
public theorem mAnalyticAt_fill_inf [IsManifold I ⊤ T] {f : ℂ → T} {y : T}
    (fa : ∀ᶠ z in cobounded ℂ, ContMDiffAt I I ⊤ f z) (fi : Tendsto f (cobounded ℂ) (𝓝 y)) :
    ContMDiffAt I I ⊤ (fill f y) ∞ := by
  rw [mAnalyticAt_iff_of_boundaryless]
  use continuousAt_fill_inf fi
  simp only [Function.comp_def, extChartAt, OpenPartialHomeomorph.extend, fill, rec_inf,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, chartAt_inf,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_symm,
    OpenPartialHomeomorph.toFun_eq_coe, invCoeOpenPartialHomeomorph_apply,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, invCoeOpenPartialHomeomorph_symm_apply, inv_inf,
    toComplex_zero]
  have e : (fun z : ℂ ↦ chartAt ℂ y (OnePoint.rec y f (↑z)⁻¹)) = fun z : ℂ ↦
      extChartAt I y (if z = 0 then y else f z⁻¹) := by
    funext z; by_cases z0 : z = 0
    · simp only [z0, coe_zero, inv_zero', rec_inf, extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
        OpenPartialHomeomorph.toFun_eq_coe, if_true]
    · simp only [inv_coe z0, rec_coe, extChartAt, OpenPartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, z0, ite_false,
        OpenPartialHomeomorph.toFun_eq_coe]
  rw [e]; clear e
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · apply (inv_tendsto_cobounded.eventually fa).mp
    apply (inv_tendsto_cobounded.eventually (fi.eventually
      ((isOpen_extChartAt_source y).eventually_mem (mem_extChartAt_source (I := I) y)))).mp
    apply eventually_nhdsWithin_of_forall; intro z z0 m fa
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at z0
    have e : (fun z ↦ extChartAt I y (if z = 0 then y else f z⁻¹)) =ᶠ[𝓝 z]
        fun z ↦ extChartAt I y (f z⁻¹) := by
      refine (continuousAt_id.eventually_ne z0).mp (.of_forall fun w w0 ↦ ?_)
      simp only [Ne, id_eq] at w0; simp only [w0, if_false]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ e
    apply AnalyticAt.differentiableAt; apply ContMDiffAt.analyticAt I I
    refine (contMDiffAt_extChartAt' (extChartAt_source I y ▸ m)).comp _ ?_
    exact fa.comp _ (contMDiffAt_id.inv₀ z0)
  · refine (continuousAt_extChartAt' ?_).comp ?_
    · simp only [if_pos, mem_extChartAt_source]
    · simp only [← continuousWithinAt_compl_self, ContinuousWithinAt]
      apply tendsto_nhdsWithin_congr (f := fun z ↦ f z⁻¹)
      intro z z0; simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at z0
      simp only [z0, if_false]
      exact Filter.Tendsto.comp fi inv_tendsto_cobounded

/-- `fill` is analytic -/
theorem mAnalytic_fill [IsManifold I ⊤ T] {f : ℂ → T} {y : T} (fa : ContMDiff I I ⊤ f)
    (fi : Tendsto f (cobounded ℂ) (𝓝 y)) : ContMDiff I I ⊤ (fill f y) := by
  intro z; induction z using OnePoint.rec
  · exact mAnalyticAt_fill_inf (.of_forall fa) fi
  · exact mAnalyticAt_fill_coe (fa _)

/-- `lift'` is continuous at finite values -/
theorem continuousAt_lift_coe' (gc : ContinuousAt (uncurry g) (x, z)) :
    ContinuousAt (uncurry (lift' g y)) (x, ↑z) := by
  simp only [lift', ContinuousAt, uncurry, rec_coe, OnePoint.nhds_coe_eq, prod_nhds_eq,
    Filter.tendsto_map'_iff, Function.comp_def]
  exact Filter.Tendsto.comp Filter.tendsto_map gc

/-- `lift'` is continuous at `∞` -/
theorem continuousAt_lift_inf' (gi : Tendsto (uncurry g) (𝓝 x ×ˢ cobounded ℂ) (cobounded ℂ)) :
    ContinuousAt (uncurry (lift' g ∞)) (x, ∞) := by
  simp only [ContinuousAt, Filter.Tendsto, Filter.le_def, Filter.mem_map]; intro s m
  simp only [OnePoint.nhds_infty_eq, Filter.coclosedCompact_eq_cocompact, Filter.mem_sup,
    Filter.mem_map, Filter.mem_pure, ← Metric.cobounded_eq_cocompact, lift', rec_inf, uncurry] at m
  simp only [Tendsto] at gi; specialize gi m.1
  simp only [Filter.mem_map, preimage_preimage] at gi
  have e : uncurry (lift' g ∞) ⁻¹' s =
      (fun x : X × ℂ ↦ (x.1, (x.2 : 𝕊))) ''
        ((fun x : X × ℂ ↦ (g x.1 x.2 : 𝕊)) ⁻¹' s) ∪ univ ×ˢ {∞} := by
    apply Set.ext; intro ⟨x, z⟩; induction z using OnePoint.rec
    · simp only [mem_preimage, mem_image, mem_union, mem_prod_eq, mem_univ, true_and,
      mem_singleton_iff, or_true, uncurry, lift', rec_inf, m.2]
    · simp only [uncurry, lift', mem_preimage, rec_coe, prod_singleton, image_univ, mem_union,
        mem_image, Prod.ext_iff, coe_eq_coe, Prod.exists, exists_eq_right_right, exists_eq_right,
        mem_range, OnePoint.infty_ne_coe, and_false, exists_false, or_false]
  rw [e]; exact prod_mem_inf_of_mem_cobounded gi

/-- `lift'` is continuous -/
theorem continuous_lift' (gc : Continuous (uncurry g))
    (gi : ∀ x, Tendsto (uncurry g) (𝓝 x ×ˢ cobounded ℂ) (cobounded ℂ)) :
    Continuous (uncurry (lift' g ∞)) := by
  rw [← continuousOn_univ]; intro ⟨x, z⟩ _; apply ContinuousAt.continuousWithinAt
  induction z using OnePoint.rec
  · exact continuousAt_lift_inf' (gi x)
  · exact continuousAt_lift_coe' gc.continuousAt

/-- `lift` is continuous at finite values -/
theorem continuousAt_lift_coe (fc : ContinuousAt f z) : ContinuousAt (lift f y) z :=
  haveI gc : ContinuousAt (uncurry fun _ : Unit ↦ f) ((), z) := by
    refine ContinuousAt.comp fc ?_; exact continuousAt_snd
  (continuousAt_lift_coe' gc).comp (ContinuousAt.prodMk continuousAt_const continuousAt_id)

/-- `lift` is continuous at `∞` -/
theorem continuousAt_lift_inf (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) :
    ContinuousAt (lift f ∞) ∞ :=
  haveI gi : Tendsto (uncurry fun _ : Unit ↦ f) (𝓝 () ×ˢ cobounded ℂ) (cobounded ℂ) :=
    fi.comp Filter.tendsto_snd
  (continuousAt_lift_inf' gi).comp (ContinuousAt.prodMk continuousAt_const continuousAt_id)

/-- `lift` is continuous -/
theorem continuous_lift (fc : Continuous f) (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) :
    Continuous (lift f ∞) := by
  rw [continuous_iff_continuousAt]; intro z; induction z using OnePoint.rec
  · exact continuousAt_lift_inf fi
  · exact continuousAt_lift_coe fc.continuousAt

/-- `lift` is analytic at finite values -/
theorem mAnalyticAt_lift_coe (fa : AnalyticAt ℂ f z) : ContMDiffAt I I ⊤ (lift f y) z := by
  rw [lift_eq_fill]
  exact mAnalyticAt_fill_coe ((mAnalytic_coe _).comp _ (fa.mAnalyticAt I I))

/-- `lift` is analytic at `∞` -/
theorem mAnalyticAt_lift_inf (fa : ∀ᶠ z in cobounded ℂ, AnalyticAt ℂ f z)
    (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) : ContMDiffAt I I ⊤ (lift f ∞) ∞ := by
  rw [lift_eq_fill]; apply mAnalyticAt_fill_inf
  exact fa.mp (.of_forall fun z fa ↦ (mAnalytic_coe _).comp _ (fa.mAnalyticAt I I))
  exact coe_tendsto_inf.comp fi

/-- `lift` is analytic -/
public theorem mAnalytic_lift (fa : AnalyticOnNhd ℂ f univ)
    (fi : Tendsto f (cobounded ℂ) (cobounded ℂ)) : ContMDiff I I ⊤ (lift f ∞) := by
  intro z; induction z using OnePoint.rec
  · exact mAnalyticAt_lift_inf (.of_forall fun z ↦ fa z (mem_univ _)) fi
  · exact mAnalyticAt_lift_coe (fa _ (mem_univ _))

/-- `lift'` is analytic (the parameterized version) -/
public theorem mAnalytic_lift' {f : ℂ → ℂ → ℂ} (fa : AnalyticOnNhd ℂ (uncurry f) univ)
    (fi : ∀ x, Tendsto (uncurry f) (𝓝 x ×ˢ cobounded ℂ) (cobounded ℂ)) :
    ContMDiff II I ⊤ (uncurry (lift' f ∞)) := by
  apply osgoodManifold (continuous_lift' fa.continuous fi)
  · intro x z
    induction z using OnePoint.rec
    · simp only [uncurry, lift_inf']; exact contMDiffAt_const
    · exact (mAnalytic_coe _).comp _ ((fa _ (mem_univ ⟨_,_⟩)).along_fst.mAnalyticAt _ _)
  · intro x z
    exact mAnalytic_lift (fun _ _ ↦ (fa _ (mem_univ ⟨_,_⟩)).along_snd)
      ((fi x).comp (tendsto_const_nhds.prodMk Filter.tendsto_id)) z

/-- `𝕊` is path connected -/
public instance : PathConnectedSpace 𝕊 := by
  constructor; use ∞
  have i1 : Joined ∞ ((1 : ℂ) : 𝕊) := by
    generalize hp : (fun t : unitInterval ↦ (((t : ℝ) : ℂ) : 𝕊)⁻¹) = p
    have pc : Continuous p := by
      rw [← hp]
      exact continuous_inv.comp (continuous_coe.comp (Complex.continuous_ofReal.comp
        continuous_subtype_val))
    use ⟨p, pc⟩
    simp only [← hp]; rw [Icc.coe_zero, Complex.ofReal_zero, coe_zero, inv_zero']
    simp only [← hp]; rw [Icc.coe_one, Complex.ofReal_one, inv_coe one_ne_zero, inv_one]
  have cc : ∀ x y : ℂ, Joined (x : 𝕊) (y : 𝕊) := by
    intro x y
    have p := PathConnectedSpace.somePath x y
    use p.map continuous_coe
    repeat simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.coe_coe, Path.source, Path.target]
  replace ic : ∀ x : ℂ, Joined ∞ (x : 𝕊) := fun x ↦ i1.trans (cc _ _)
  intro x y; induction x using OnePoint.rec
  · induction y using OnePoint.rec
    · exact Joined.refl _
    · apply ic
  · induction y using OnePoint.rec
    · exact (ic _).symm
    · apply cc
