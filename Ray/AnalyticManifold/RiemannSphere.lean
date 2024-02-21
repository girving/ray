import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint
import Ray.Analytic.Analytic
import Ray.AnalyticManifold.AnalyticManifold
import Ray.AnalyticManifold.OneDimension
import Ray.Misc.AtInf

/-!
## The Riemann sphere

We give `OnePoint ℂ` the natural analytic manifold structure with two charts,
namely `coe` and `inv ∘ coe`, giving the Riemann sphere `𝕊`.
-/

open Classical
open Complex (abs)
open Filter (eventually_of_forall Tendsto atTop)
open Function (curry uncurry)
open Set
open scoped Topology OnePoint
noncomputable section

/-- A left inverse to `coe : ℂ → 𝕊`.
    We put this outside the `RiemannSphere` namespace so that `z.toComplex` works. -/
def OnePoint.toComplex (z : OnePoint ℂ) : ℂ := z.rec 0 id

namespace RiemannSphere

/-- The Riemann sphere, as a complex manifold -/
scoped notation "𝕊" => OnePoint ℂ

-- Basic instances for 𝕊
instance : Zero 𝕊 := ⟨((0 : ℂ) : 𝕊)⟩
instance : Inhabited 𝕊 := ⟨0⟩
@[simp] theorem coe_zero : ((0 : ℂ) : 𝕊) = (0 : 𝕊) := rfl
@[simp] theorem coe_eq_coe {z w : ℂ} : (z : 𝕊) = w ↔ z = w := OnePoint.coe_eq_coe
@[simp] theorem coe_eq_zero (z : ℂ) : (z : 𝕊) = (0 : 𝕊) ↔ z = 0 := by
  simp only [← coe_zero, coe_eq_coe]

/-- `coe : ℂ → 𝕊` is injective -/
theorem injective_coe : Function.Injective (fun z : ℂ ↦ (z : 𝕊)) := OnePoint.coe_injective

/-- `coe : ℂ → 𝕊` is continuous -/
theorem continuous_coe : Continuous (fun z : ℂ ↦ (z : 𝕊)) := OnePoint.continuous_coe

-- Recursion lemmas
@[simp] theorem rec_coe {C : 𝕊 → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : 𝕊)} (z : ℂ) :
    (z : 𝕊).rec i f = f z := rfl
@[simp] theorem rec_inf {C : 𝕊 → Sort*} {i : C ∞} {f : ∀ z : ℂ, C (z : 𝕊)} :
    (∞ : 𝕊).rec i f = i := rfl
theorem map_rec {A B : Sort*} (g : A → B) {f : ℂ → A} {i : A} {z : 𝕊} :
    g (z.rec i f) = (z.rec (g i) (g ∘ f)) := by
  induction z using OnePoint.rec
  · simp only [rec_inf]
  · simp only [rec_coe, Function.comp]

-- ∞ is not 0 or finite
theorem inf_ne_coe {z : ℂ} : (∞ : 𝕊) ≠ ↑z := by
  simp only [Ne.def, OnePoint.infty_ne_coe, not_false_iff]
theorem inf_ne_zero : (∞ : 𝕊) ≠ (0 : 𝕊) := by
  have e : (0 : 𝕊) = ((0 : ℂ) : 𝕊) := rfl; rw [e]; exact inf_ne_coe
theorem coe_ne_inf {z : ℂ} : (z : 𝕊) ≠ ∞ := inf_ne_coe.symm
theorem coe_eq_inf_iff {z : ℂ} : (z : 𝕊) = ∞ ↔ False := ⟨coe_ne_inf, False.elim⟩

-- Conversion to ℂ, sending ∞ to 0
@[simp] theorem toComplex_coe {z : ℂ} : (z : 𝕊).toComplex = z := rfl
@[simp] theorem toComplex_inf : (∞ : 𝕊).toComplex = 0 := rfl
theorem coe_toComplex {z : 𝕊} (h : z ≠ ∞) : ↑z.toComplex = z := by
  induction z using OnePoint.rec
  · simp only [ne_eq, not_true_eq_false] at h
  · simp only [toComplex_coe]
@[simp] theorem toComplex_zero : (0 : 𝕊).toComplex = 0 := by rw [← coe_zero, toComplex_coe]
theorem continuousAt_toComplex {z : ℂ} : ContinuousAt OnePoint.toComplex z := by
  simp only [OnePoint.continuousAt_coe, Function.comp, toComplex_coe]; exact continuousAt_id
theorem continuousOn_toComplex : ContinuousOn OnePoint.toComplex ({∞}ᶜ) := by
  intro z m; induction z using OnePoint.rec
  · simp only [mem_compl_iff, mem_singleton_iff, not_true] at m
  · exact continuousAt_toComplex.continuousWithinAt

/-- Inversion in `𝕊`, interchanging `0` and `∞` -/
def inv (z : 𝕊) : 𝕊 := if z = 0 then ∞ else ↑z.toComplex⁻¹
instance : Inv 𝕊 := ⟨RiemannSphere.inv⟩
theorem inv_def (z : 𝕊) : z⁻¹ = RiemannSphere.inv z := rfl
instance : InvolutiveInv 𝕊 where
  inv := Inv.inv
  inv_inv := by
    simp_rw [inv_def, inv]; apply OnePoint.rec
    · simp only [inf_ne_zero, toComplex_inf, inv_zero, coe_zero, ite_false, toComplex_zero,
        ite_true]
    · intro z; by_cases z0 : z = 0
      · simp only [z0, coe_zero, toComplex_zero, inv_zero, ite_true, inf_ne_zero, toComplex_inf,
          ite_false]
      · simp only [coe_eq_zero, z0, toComplex_coe, ite_false, inv_eq_zero, inv_inv]
@[simp] theorem inv_zero' : (0 : 𝕊)⁻¹ = ∞ := by simp only [inv_def, inv, eq_self_iff_true, if_true]
@[simp] theorem inv_inf : ((∞ : 𝕊)⁻¹ : 𝕊) = 0 := by simp [inv_def, inv, inf_ne_zero]

theorem inv_coe {z : ℂ} (z0 : z ≠ 0) : (z : 𝕊)⁻¹ = ↑(z : ℂ)⁻¹ := by
  simp only [inv_def, inv, z0, WithTop.coe_eq_zero, toComplex_coe, if_false, coe_eq_zero]
@[simp] theorem inv_eq_inf {z : 𝕊} : z⁻¹ = ∞ ↔ z = 0 := by
  induction z using OnePoint.rec
  · simp only [inv_inf]; exact ⟨Eq.symm, Eq.symm⟩
  · simp only [inv_def, inv, not_not, imp_false, ite_eq_left_iff, OnePoint.coe_ne_infty]
@[simp] theorem inv_eq_zero {z : 𝕊} : z⁻¹ = 0 ↔ z = ∞ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, eq_self_iff_true]
  · simp only [inv_def, inv, toComplex_coe]
    by_cases z0 : (z : 𝕊) = 0; simp only [if_pos, z0, inf_ne_zero, inf_ne_zero.symm]
    simp only [if_neg z0, coe_ne_inf, iff_false_iff]; rw [coe_eq_zero, _root_.inv_eq_zero]
    simpa only [coe_eq_zero] using z0
theorem toComplex_inv {z : 𝕊} : z⁻¹.toComplex = z.toComplex⁻¹ := by
  induction' z using OnePoint.rec with z
  · simp only [inv_inf, toComplex_zero, toComplex_inf, inv_zero', inv_zero, eq_self_iff_true]
  · by_cases z0 : z = 0
    · simp only [z0, coe_zero, inv_zero', toComplex_inf, toComplex_zero, inv_zero]
    · simp only [z0, inv_coe, Ne.def, not_false_iff, toComplex_coe]

/-- `coe` tends to `∞` `atInf` -/
theorem coe_tendsto_inf : Tendsto (fun z : ℂ ↦ (z : 𝕊)) atInf (𝓝 ∞) := by
  rw [Filter.tendsto_iff_comap, OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact]
  exact atInf_le_cocompact

/-- `coe` tends to `∞` `atInf`, but without touching `∞` -/
theorem coe_tendsto_inf' : Tendsto (fun z : ℂ ↦ (z : 𝕊)) atInf (𝓝[{∞}ᶜ] ∞) := by
  have e : {(∞ : 𝕊)}ᶜ = range (fun z : ℂ ↦ (z : 𝕊)) := by
    ext z; induction' z using OnePoint.rec with z
    · simp only [mem_compl_iff, mem_singleton_iff, not_true, mem_range, OnePoint.coe_ne_infty,
        exists_false]
    · simp only [mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty, not_false_eq_true,
        mem_range, coe_eq_coe, exists_eq]
  simp only [e, tendsto_nhdsWithin_range, coe_tendsto_inf]

/-- Inversion is continuous -/
theorem continuous_inv : Continuous fun z : 𝕊 ↦ z⁻¹ := by
  rw [continuous_iff_continuousOn_univ]; intro z _; apply ContinuousAt.continuousWithinAt
  induction' z using OnePoint.rec with z
  · simp only [OnePoint.continuousAt_infty', Function.comp, Filter.coclosedCompact_eq_cocompact,
      inv_inf, ← atInf_eq_cocompact]
    have e : ∀ᶠ z : ℂ in atInf, ↑z⁻¹ = (↑z : 𝕊)⁻¹ := by
      refine' (eventually_atInf 0).mp (eventually_of_forall fun z z0 ↦ _)
      simp only [gt_iff_lt, Complex.norm_eq_abs, AbsoluteValue.pos_iff] at z0; rw [inv_coe z0]
    apply Filter.Tendsto.congr' e
    exact Filter.Tendsto.comp continuous_coe.continuousAt inv_tendsto_atInf'
  · simp only [OnePoint.continuousAt_coe, Function.comp, inv_def, inv, WithTop.coe_eq_zero,
      toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, ContinuousAt, OnePoint.nhds_infty_eq, eq_self_iff_true, if_true,
        Filter.coclosedCompact_eq_cocompact]
      simp only [← nhdsWithin_compl_singleton_sup_pure, Filter.tendsto_sup]
      constructor
      · refine' Filter.Tendsto.mono_right _ le_sup_left
        apply tendsto_nhdsWithin_congr (f := fun z : ℂ ↦ (↑z⁻¹ : 𝕊))
        · intro z m; rw [mem_compl_singleton_iff] at m; simp only [coe_eq_zero, m, ite_false]
        · simp only [coe_zero, ite_true]; apply coe_tendsto_inf'.comp
          rw [← @tendsto_atInf_iff_tendsto_nhds_zero ℂ ℂ _ _ fun z : ℂ ↦ z]
          exact Filter.tendsto_id
      · refine' Filter.Tendsto.mono_right _ le_sup_right
        simp only [Filter.pure_zero, Filter.tendsto_pure, ite_eq_left_iff, Filter.eventually_zero,
          eq_self_iff_true, not_true, IsEmpty.forall_iff]
    · have e : ∀ᶠ w : ℂ in 𝓝 z, (if w = 0 then ∞ else ↑w⁻¹ : 𝕊) = ↑w⁻¹ := by
        refine' (continuousAt_id.eventually_ne z0).mp (eventually_of_forall fun w w0 ↦ _)
        simp only [Ne.def, id.def] at w0; simp only [w0, if_false]
      simp only [coe_eq_zero, continuousAt_congr e]
      exact continuous_coe.continuousAt.comp (tendsto_inv₀ z0)
instance : ContinuousInv 𝕊 := ⟨continuous_inv⟩

/-- Inversion as an equivalence -/
def invEquiv : 𝕊 ≃ 𝕊 where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv

/-- Inversion as a homeomorphism -/
def invHomeomorph : 𝕊 ≃ₜ 𝕊 where
  toEquiv := invEquiv
  continuous_toFun := continuous_inv
  continuous_invFun := continuous_inv
@[simp] theorem invEquiv_apply (z : 𝕊) : invEquiv z = z⁻¹ := by
  simp only [invEquiv, Equiv.coe_fn_mk]
@[simp] theorem invEquiv_symm : invEquiv.symm = invEquiv := by
  simp only [Equiv.ext_iff, invEquiv, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk, eq_self_iff_true,
    forall_const]
@[simp] theorem invHomeomorph_apply (z : 𝕊) : invHomeomorph z = z⁻¹ := by
  simp only [invHomeomorph, Homeomorph.homeomorph_mk_coe, invEquiv_apply]
@[simp] theorem invHomeomorph_symm : invHomeomorph.symm = invHomeomorph := Homeomorph.ext (by
  simp only [invHomeomorph, Homeomorph.homeomorph_mk_coe_symm, invEquiv_symm,
    Homeomorph.homeomorph_mk_coe, eq_self_iff_true, forall_const])

/-- `coe : ℂ → 𝕊` as an equivalence -/
def coePartialEquiv : PartialEquiv ℂ 𝕊 where
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
def coePartialHomeomorph : PartialHomeomorph ℂ 𝕊 where
  toPartialEquiv := coePartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_compl_singleton
  continuousOn_toFun := continuous_coe.continuousOn
  continuousOn_invFun := continuousOn_toComplex

/-- `inv ∘ coe : ℂ → 𝕊` as a partial homeomorphism.  This is the second chart of `𝕊`. -/
def invCoePartialHomeomorph : PartialHomeomorph ℂ 𝕊 :=
  coePartialHomeomorph.trans invHomeomorph.toPartialHomeomorph

@[simp] lemma coePartialEquiv_target : coePartialEquiv.target = {∞}ᶜ := rfl
@[simp] lemma coePartialHomeomorph_target : coePartialHomeomorph.target = {∞}ᶜ := by
  simp only [coePartialHomeomorph, coePartialEquiv_target]
@[simp] lemma invCoePartialHomeomorph_target : invCoePartialHomeomorph.target = {0}ᶜ := by
  ext z; simp only [invCoePartialHomeomorph, PartialHomeomorph.trans_toPartialEquiv,
    PartialEquiv.trans_target, Homeomorph.toPartialHomeomorph_target, PartialHomeomorph.coe_coe_symm,
    Homeomorph.toPartialHomeomorph_symm_apply, invHomeomorph_symm, coePartialHomeomorph_target,
    preimage_compl, univ_inter, mem_compl_iff, mem_preimage, invHomeomorph_apply, mem_singleton_iff,
    inv_eq_inf]
@[simp] lemma coePartialEquiv_apply (z : ℂ) : coePartialEquiv z = ↑z := rfl
@[simp] lemma coePartialEquiv_symm_apply (z : 𝕊) : coePartialEquiv.symm z = z.toComplex := rfl
@[simp] lemma invCoePartialHomeomorph_apply (z : ℂ) : invCoePartialHomeomorph z = (z : 𝕊)⁻¹ := rfl
@[simp] lemma invCoePartialHomeomorph_symm_apply (z : 𝕊) :
    invCoePartialHomeomorph.symm z = (z⁻¹).toComplex := rfl

/-- Chart structure for `𝕊` -/
instance : ChartedSpace ℂ 𝕊 where
  atlas := {e | e = coePartialHomeomorph.symm ∨ e = invCoePartialHomeomorph.symm}
  chartAt z := z.rec invCoePartialHomeomorph.symm (fun _ ↦ coePartialHomeomorph.symm)
  mem_chart_source := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        invCoePartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, inf_ne_zero,
        not_false_eq_true]
    · simp only [rec_coe, PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source,
        coePartialHomeomorph_target, mem_compl_iff, mem_singleton_iff, OnePoint.coe_ne_infty,
        not_false_eq_true]
  chart_mem_atlas := by
    intro z; induction z using OnePoint.rec
    · simp only [rec_inf, eq_self_iff_true, mem_setOf_eq, or_true_iff]
    · simp only [rec_coe, mem_setOf_eq, eq_self_iff_true, true_or_iff]

/-- There are just two charts on `𝕊` -/
theorem two_charts {e : PartialHomeomorph 𝕊 ℂ} (m : e ∈ atlas ℂ 𝕊) :
    e = coePartialHomeomorph.symm ∨ e = invCoePartialHomeomorph.symm := m

-- Chart simplification lemmas
@[simp] theorem chartAt_coe {z : ℂ} : chartAt ℂ (z : 𝕊) = coePartialHomeomorph.symm := rfl
@[simp] theorem chartAt_inf : @chartAt ℂ _ 𝕊 _ _ ∞ = invCoePartialHomeomorph.symm := rfl
theorem extChartAt_coe {z : ℂ} : extChartAt I (z : 𝕊) = coePartialEquiv.symm := by
  simp only [coePartialHomeomorph, extChartAt, PartialHomeomorph.extend, chartAt_coe,
    PartialHomeomorph.symm_toPartialEquiv, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl]
theorem extChartAt_zero : extChartAt I (0 : 𝕊) = coePartialEquiv.symm := by
  simp only [← coe_zero, extChartAt_coe]
theorem extChartAt_inf : extChartAt I (∞ : 𝕊) = invEquiv.toPartialEquiv.trans coePartialEquiv.symm := by
  apply PartialEquiv.ext
  · intro z
    simp only [extChartAt, invCoePartialHomeomorph, coePartialHomeomorph, invHomeomorph,
      PartialHomeomorph.extend, chartAt_inf, PartialHomeomorph.symm_toPartialEquiv,
      PartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_coe_symm,
      Homeomorph.toPartialHomeomorph_symm_apply, Homeomorph.homeomorph_mk_coe_symm, invEquiv_symm,
      PartialEquiv.coe_trans, Equiv.toPartialEquiv_apply]
  · intro z
    simp only [extChartAt, invCoePartialHomeomorph, coePartialHomeomorph, invHomeomorph,
      invEquiv, PartialHomeomorph.extend, chartAt_inf, PartialHomeomorph.symm_toPartialEquiv,
      PartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl, PartialEquiv.symm_symm, PartialEquiv.coe_trans,
      PartialHomeomorph.coe_coe, Homeomorph.toPartialHomeomorph_apply, Homeomorph.homeomorph_mk_coe,
      Equiv.coe_fn_mk, PartialEquiv.coe_trans_symm, Equiv.toPartialEquiv_symm_apply,
      Equiv.coe_fn_symm_mk]
  · simp only [extChartAt, invCoePartialHomeomorph, coePartialHomeomorph, invHomeomorph,
      PartialHomeomorph.extend, chartAt_inf, PartialHomeomorph.symm_toPartialEquiv,
      PartialHomeomorph.trans_toPartialEquiv, modelWithCornersSelf_partialEquiv,
      PartialEquiv.trans_refl,
      PartialEquiv.symm_source, PartialEquiv.trans_target, Homeomorph.toPartialHomeomorph_target,
      PartialHomeomorph.coe_coe_symm, Homeomorph.toPartialHomeomorph_symm_apply,
      Homeomorph.homeomorph_mk_coe_symm, invEquiv_symm, PartialEquiv.trans_source,
      Equiv.toPartialEquiv_source, Equiv.toPartialEquiv_apply]
theorem extChartAt_inf_apply {x : 𝕊} : extChartAt I ∞ x = x⁻¹.toComplex := by
  simp only [extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
    Equiv.toPartialEquiv_apply, invEquiv_apply]

/-- `𝕊`'s charts have analytic groupoid structure -/
instance : HasGroupoid 𝕊 (analyticGroupoid I) where
  compatible := by
    have e0 : ((fun z : ℂ ↦ (z : 𝕊)) ⁻¹' {0})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, coe_eq_zero]
    have e1 : ((fun z : ℂ ↦ (z : 𝕊)⁻¹) ⁻¹' {∞})ᶜ = {(0 : ℂ)}ᶜ := by
      ext; simp only [mem_compl_iff, mem_preimage, mem_singleton_iff, inv_eq_inf, coe_eq_zero]
    have a : AnalyticOn ℂ (fun z : ℂ ↦ OnePoint.toComplex (z : 𝕊)⁻¹) {0}ᶜ := by
      apply AnalyticOn.congr (f := fun z ↦ z⁻¹)
      · exact isOpen_compl_singleton
      · apply analyticOn_inv
      · intro z z0; simp only [mem_compl_iff, mem_singleton_iff] at z0
        simp only [inv_coe z0, toComplex_coe]
    intro f g fa ga; simp only [mem_analyticGroupoid_of_boundaryless]
    cases' two_charts fa with fh fh
    · cases' two_charts ga with gh gh
      · simp only [←fh, gh]; constructor; repeat apply extChartAt_self_analytic
      · simp [fh, gh, invCoePartialHomeomorph, coePartialHomeomorph, coePartialEquiv, invHomeomorph,
          invEquiv, Function.comp, e0, e1, and_self, a]
    · cases' two_charts ga with gh gh
      · simp [fh, gh, invCoePartialHomeomorph, coePartialHomeomorph, coePartialEquiv, invHomeomorph,
          invEquiv, Function.comp, e0, e1, and_self, a]
      · simp only [←fh, gh]; constructor; repeat apply extChartAt_self_analytic

/-- `𝕊` is an analytic manifold -/
instance : AnalyticManifold I 𝕊 where

/-- Composing with `coe` turns convergence `atInf` into convergence to `𝓝 ∞` -/
theorem tendsto_inf_iff_tendsto_atInf {X : Type} {f : Filter X} {g : X → ℂ} :
    Tendsto (fun x ↦ (g x : 𝕊)) f (𝓝 ∞) ↔ Tendsto (fun x ↦ g x) f atInf := by
  constructor
  · intro t; simp only [Filter.tendsto_iff_comap] at t ⊢
    rw [←Function.comp_def, ←Filter.comap_comap, OnePoint.comap_coe_nhds_infty,
      Filter.coclosedCompact_eq_cocompact, ←atInf_eq_cocompact] at t
    exact t
  · exact fun h ↦ coe_tendsto_inf.comp h

variable {X : Type} [TopologicalSpace X]
variable {Y : Type} [TopologicalSpace Y]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [AnalyticManifold I T]

/-- `coe : ℂ → 𝕊` is an open map -/
theorem isOpenMap_coe : IsOpenMap (fun z : ℂ ↦ (z : 𝕊)) := by
  intro s o
  have e : (fun z : ℂ ↦ (z : 𝕊)) '' s = {∞}ᶜ ∩ OnePoint.toComplex ⁻¹' s := by
    apply Set.ext; intro z
    simp only [mem_image, mem_inter_iff, mem_compl_singleton_iff, mem_preimage]
    constructor
    intro ⟨x, m, e⟩; simp only [← e, toComplex_coe, m, and_true_iff]; exact inf_ne_coe.symm
    intro ⟨n, m⟩; use z.toComplex, m, coe_toComplex n
  rw [e]; exact continuousOn_toComplex.isOpen_inter_preimage isOpen_compl_singleton o

theorem prod_nhds_eq {x : X} {z : ℂ} :
    𝓝 (x, (z : 𝕊)) = Filter.map (fun p : X × ℂ ↦ (p.1, ↑p.2)) (𝓝 (x, z)) := by
  refine le_antisymm ?_ (continuousAt_fst.prod (continuous_coe.continuousAt.comp continuousAt_snd))
  apply IsOpenMap.nhds_le; exact IsOpenMap.id.prod isOpenMap_coe

theorem mem_inf_of_mem_atInf {s : Set ℂ} (f : s ∈ @atInf ℂ _) :
    (fun z : ℂ ↦ (z : 𝕊)) '' s ∪ {∞} ∈ 𝓝 (∞ : 𝕊) := by
  simp only [OnePoint.nhds_infty_eq, Filter.mem_sup, Filter.coclosedCompact_eq_cocompact, ←
    atInf_eq_cocompact, Filter.mem_map]
  exact ⟨Filter.mem_of_superset f fun _ m ↦ Or.inl (mem_image_of_mem _ m), Or.inr rfl⟩

theorem prod_mem_inf_of_mem_atInf {s : Set (X × ℂ)} {x : X} (f : s ∈ (𝓝 x).prod (@atInf ℂ _)) :
    (fun p : X × ℂ ↦ (p.1, (p.2 : 𝕊))) '' s ∪ univ ×ˢ {∞} ∈ 𝓝 (x, (∞ : 𝕊)) := by
  rcases Filter.mem_prod_iff.mp f with ⟨t, tx, u, ui, sub⟩
  rw [nhds_prod_eq]
  refine Filter.mem_prod_iff.mpr ⟨t, tx, (fun z : ℂ ↦ (z : 𝕊)) '' u ∪ {∞}, mem_inf_of_mem_atInf ui,
    ?_⟩
  intro ⟨y, z⟩ ⟨yt, m⟩
  simp only [mem_prod_eq, mem_image, mem_union, mem_singleton_iff, mem_univ, true_and_iff,
    Prod.ext_iff] at yt m ⊢
  induction' z using OnePoint.rec with z
  · simp only [eq_self_iff_true, or_true_iff]
  · simp only [coe_eq_inf_iff, or_false_iff, coe_eq_coe] at m ⊢
    rcases m with ⟨w, wu, wz⟩; refine ⟨⟨y, z⟩, sub (mk_mem_prod yt ?_), rfl, rfl⟩; rw [← wz]
    exact wu

/-- `coe : ℂ → 𝕊` is holomorphic -/
theorem holomorphic_coe : Holomorphic I I (fun z : ℂ ↦ (z : 𝕊)) := by
  rw [holomorphic_iff]; use continuous_coe; intro z
  simp only [extChartAt_coe, extChartAt_eq_refl, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, id.def, Function.comp, PartialEquiv.invFun_as_coe]
  rw [← PartialEquiv.invFun_as_coe]; simp only [coePartialEquiv, toComplex_coe]; apply analyticAt_id

/-- `OnePoint.toComplex : 𝕊 → ℂ` is holomorphic except at `∞` -/
theorem holomorphicAt_toComplex {z : ℂ} : HolomorphicAt I I (OnePoint.toComplex : 𝕊 → ℂ) z := by
  rw [holomorphicAt_iff]; use continuousAt_toComplex
  simp only [toComplex_coe, Function.comp, extChartAt_coe, extChartAt_eq_refl, PartialEquiv.refl_coe,
    id, PartialEquiv.symm_symm, coePartialEquiv_apply, coePartialEquiv_symm_apply]
  apply analyticAt_id

/-- Inversion is holomorphic -/
theorem holomorphic_inv : Holomorphic I I fun z : 𝕊 ↦ z⁻¹ := by
  rw [holomorphic_iff]; use continuous_inv; intro z; induction' z using OnePoint.rec with z
  · simp only [inv_inf, extChartAt_inf, ← coe_zero, extChartAt_coe, Function.comp,
      PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, coePartialEquiv_symm_apply,
      toComplex_coe, PartialEquiv.coe_trans_symm, PartialEquiv.symm_symm, coePartialEquiv_apply,
      Equiv.toPartialEquiv_symm_apply, invEquiv_symm, inv_inv]
    apply analyticAt_id
  · simp only [extChartAt_coe, PartialEquiv.symm_symm, Function.comp, coePartialEquiv_apply,
      coePartialEquiv_symm_apply, toComplex_coe]
    by_cases z0 : z = 0
    · simp only [z0, coe_zero, extChartAt_inf, PartialEquiv.trans_apply, coePartialEquiv_symm_apply,
        invEquiv_apply, Equiv.toPartialEquiv_apply, inv_zero', inv_inv, toComplex_coe]
      apply analyticAt_id
    · simp only [inv_coe z0, extChartAt_coe, coePartialEquiv_symm_apply]
      refine' ((analyticAt_id _ _).inv z0).congr _
      refine (continuousAt_id.eventually_ne z0).mp (eventually_of_forall fun w w0 ↦ ?_)
      rw [id] at w0; simp only [inv_coe w0, toComplex_coe, id]

/-- Given `f : ℂ → X`, fill in the value at `∞` to get `𝕊 → X` -/
def fill {X : Type} (f : ℂ → X) (y : X) : 𝕊 → X := fun z ↦ z.rec y f

/-- Lift `f : ℂ → ℂ` to `𝕊 → 𝕊` by filling in a value at `∞` -/
def lift (f : ℂ → ℂ) (y : 𝕊) : 𝕊 → 𝕊 := fun z ↦ z.rec y (fun z ↦ f z)

/-- Lift `f : X → ℂ → ℂ` to `X → 𝕊 → 𝕊` by filling in a value at `∞` -/
def lift' (f : X → ℂ → ℂ) (y : 𝕊) : X → 𝕊 → 𝕊 := fun x z ↦ z.rec y (fun z ↦ f x z)

variable {f : ℂ → ℂ}
variable {g : X → ℂ → ℂ}
variable {y : 𝕊} {x : X} {z : ℂ}

-- Values of `fill` and `lift` at `coe` and `∞`
@[simp] lemma fill_coe {f : ℂ → X} {y : X} : fill f y z = f z := rfl
@[simp] lemma fill_inf {f : ℂ → X} {y : X} : fill f y ∞ = y := rfl
@[simp] lemma lift_coe : lift f y z = ↑(f z) := rfl
@[simp] lemma lift_coe' : lift' g y x z = ↑(g x z) := rfl
@[simp] lemma lift_inf : lift f y ∞ = y := rfl
@[simp] lemma lift_inf' : lift' g y x ∞ = y := rfl

/-- `lift` in terms of `fill` -/
theorem lift_eq_fill : lift f y = fill (fun z ↦ (f z : 𝕊)) y := rfl

/-- `fill` is continuous at finite values -/
theorem continuousAt_fill_coe {f : ℂ → X} {y : X} (fc : ContinuousAt f z) :
    ContinuousAt (fill f y) z := by
  simp only [OnePoint.continuousAt_coe, Function.comp, fill_coe, fc]

/-- `fill` is continuous at `∞` -/
theorem continuousAt_fill_inf {f : ℂ → X} {y : X} (fi : Tendsto f atInf (𝓝 y)) :
    ContinuousAt (fill f y) ∞ := by
  simp only [OnePoint.continuousAt_infty', lift_inf, Filter.coclosedCompact_eq_cocompact, ←
    atInf_eq_cocompact, Function.comp, fill_coe, fill_inf, fi]

/-- `fill` is continuous -/
theorem continuous_fill {f : ℂ → X} {y : X} (fc : Continuous f) (fi : Tendsto f atInf (𝓝 y)) :
    Continuous (fill f y) := by
  rw [continuous_iff_continuousAt]; intro z; induction z using OnePoint.rec
  · exact continuousAt_fill_inf fi
  · exact continuousAt_fill_coe fc.continuousAt

/-- `fill` is holomorphic at finite values -/
theorem holomorphicAt_fill_coe {f : ℂ → T} {y : T} (fa : HolomorphicAt I I f z) :
    HolomorphicAt I I (fill f y) z := by
  have e : (fun x : 𝕊 ↦ f x.toComplex) =ᶠ[𝓝 ↑z] fill f y := by
    simp only [OnePoint.nhds_coe_eq, Filter.EventuallyEq, Filter.eventually_map, toComplex_coe,
      fill_coe, eq_self_iff_true, Filter.eventually_true]
  refine' HolomorphicAt.congr _ e
  refine' fa.comp_of_eq holomorphicAt_toComplex _
  simp only [toComplex_coe]

/-- `fill` is holomorphic at `∞` -/
theorem holomorphicAt_fill_inf {f : ℂ → T} {y : T} (fa : ∀ᶠ z in atInf, HolomorphicAt I I f z)
    (fi : Tendsto f atInf (𝓝 y)) : HolomorphicAt I I (fill f y) ∞ := by
  rw [holomorphicAt_iff]; use continuousAt_fill_inf fi
  simp only [Function.comp, extChartAt, PartialHomeomorph.extend, fill, rec_inf,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, chartAt_inf,
    PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_symm, PartialHomeomorph.toFun_eq_coe,
    invCoePartialHomeomorph_apply, PartialHomeomorph.coe_coe_symm, invCoePartialHomeomorph_symm_apply,
    inv_inf, toComplex_zero]
  have e : (fun z : ℂ ↦ chartAt ℂ y (OnePoint.rec y f (↑z)⁻¹)) = fun z : ℂ ↦
      extChartAt I y (if z = 0 then y else f z⁻¹) := by
    funext z; by_cases z0 : z = 0
    · simp only [if_pos z0, z0, coe_zero, inv_zero', rec_inf, extChartAt, PartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, PartialHomeomorph.toFun_eq_coe,
        if_true]
    · simp only [inv_coe z0, rec_coe, extChartAt, PartialHomeomorph.extend,
        modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, z0, ite_false,
        PartialHomeomorph.toFun_eq_coe]
  rw [e]; clear e
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · apply (inv_tendsto_atInf.eventually fa).mp
    apply (inv_tendsto_atInf.eventually (fi.eventually
      ((isOpen_extChartAt_source I y).eventually_mem (mem_extChartAt_source I y)))).mp
    apply eventually_nhdsWithin_of_forall; intro z z0 m fa
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at z0
    have e : (fun z ↦ extChartAt I y (if z = 0 then y else f z⁻¹)) =ᶠ[𝓝 z]
        fun z ↦ extChartAt I y (f z⁻¹) := by
      refine (continuousAt_id.eventually_ne z0).mp (eventually_of_forall fun w w0 ↦ ?_)
      simp only [Ne.def, id.def] at w0; simp only [w0, if_false]
    refine' DifferentiableAt.congr_of_eventuallyEq _ e
    apply AnalyticAt.differentiableAt; apply HolomorphicAt.analyticAt I I
    refine' (HolomorphicAt.extChartAt _).comp _; exact m
    exact fa.comp (holomorphicAt_id.inv z0)
  · refine' (continuousAt_extChartAt' I _).comp _
    · simp only [eq_self_iff_true, if_pos, mem_extChartAt_source]
    · simp only [← continuousWithinAt_compl_self, ContinuousWithinAt]
      apply tendsto_nhdsWithin_congr (f := fun z ↦ f z⁻¹)
      intro z z0; simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at z0
      simp only [z0, if_false]
      exact Filter.Tendsto.comp fi inv_tendsto_atInf

/-- `fill` is holomorphic -/
theorem holomorphic_fill {f : ℂ → T} {y : T} (fa : Holomorphic I I f) (fi : Tendsto f atInf (𝓝 y)) :
    Holomorphic I I (fill f y) := by
  intro z; induction z using OnePoint.rec
  · exact holomorphicAt_fill_inf (eventually_of_forall fa) fi
  · exact holomorphicAt_fill_coe (fa _)

/-- `lift'` is continuous at finite values -/
theorem continuousAt_lift_coe' (gc : ContinuousAt (uncurry g) (x, z)) :
    ContinuousAt (uncurry (lift' g y)) (x, ↑z) := by
  simp only [lift', ContinuousAt, uncurry, rec_coe, OnePoint.nhds_coe_eq, prod_nhds_eq,
    Filter.tendsto_map'_iff, Function.comp]
  exact Filter.Tendsto.comp Filter.tendsto_map gc

/-- `lift'` is continuous at `∞` -/
theorem continuousAt_lift_inf' (gi : Tendsto (uncurry g) ((𝓝 x).prod atInf) atInf) :
    ContinuousAt (uncurry (lift' g ∞)) (x, ∞) := by
  simp only [ContinuousAt, Filter.Tendsto, Filter.le_def, Filter.mem_map]; intro s m
  simp only [OnePoint.nhds_infty_eq, Filter.coclosedCompact_eq_cocompact, Filter.mem_sup,
    Filter.mem_map, Filter.mem_pure, ← atInf_eq_cocompact, lift', rec_inf, uncurry] at m
  simp only [true_imp_iff, mem_setOf, uncurry, Tendsto] at gi; specialize gi m.1
  simp only [Filter.mem_map, preimage_preimage] at gi
  have e : uncurry (lift' g ∞) ⁻¹' s =
      (fun x : X × ℂ ↦ (x.1, (x.2 : 𝕊))) ''
        ((fun x : X × ℂ ↦ (g x.1 x.2 : 𝕊)) ⁻¹' s) ∪ univ ×ˢ {∞} := by
    apply Set.ext; intro ⟨x, z⟩; induction z using OnePoint.rec
    · simp only [mem_preimage, mem_image, mem_union, mem_prod_eq, mem_univ, true_and_iff,
        mem_singleton_iff, eq_self_iff_true, or_true_iff, iff_true_iff, uncurry, lift', rec_inf,
        m.2]
    · simp only [uncurry, lift', mem_preimage, rec_coe, prod_singleton, image_univ, mem_union,
        mem_image, Prod.ext_iff, coe_eq_coe, Prod.exists, exists_eq_right_right, exists_eq_right,
        mem_range, OnePoint.infty_ne_coe, and_false, exists_false, or_false]
  rw [e]; exact prod_mem_inf_of_mem_atInf gi

/-- `lift'` is continuous -/
theorem continuous_lift' (gc : Continuous (uncurry g))
    (gi : ∀ x, Tendsto (uncurry g) ((𝓝 x).prod atInf) atInf) :
    Continuous (uncurry (lift' g ∞)) := by
  rw [continuous_iff_continuousOn_univ]; intro ⟨x, z⟩ _; apply ContinuousAt.continuousWithinAt
  induction z using OnePoint.rec
  · exact continuousAt_lift_inf' (gi x)
  · exact continuousAt_lift_coe' gc.continuousAt

/-- `lift` is continuous at finite values -/
theorem continuousAt_lift_coe (fc : ContinuousAt f z) : ContinuousAt (lift f y) z :=
  haveI gc : ContinuousAt (uncurry fun _ : Unit ↦ f) ((), z) := by
    refine ContinuousAt.comp fc ?_; exact continuousAt_snd
  (continuousAt_lift_coe' gc).comp (ContinuousAt.prod continuousAt_const continuousAt_id)

/-- `lift` is continuous at `∞` -/
theorem continuousAt_lift_inf (fi : Tendsto f atInf atInf) : ContinuousAt (lift f ∞) ∞ :=
  haveI gi : Tendsto (uncurry fun _ : Unit ↦ f) ((𝓝 ()).prod atInf) atInf :=
    fi.comp Filter.tendsto_snd
  (continuousAt_lift_inf' gi).comp (ContinuousAt.prod continuousAt_const continuousAt_id)

/-- `lift` is continuous -/
theorem continuous_lift (fc : Continuous f) (fi : Tendsto f atInf atInf) :
    Continuous (lift f ∞) := by
  rw [continuous_iff_continuousAt]; intro z; induction z using OnePoint.rec
  · exact continuousAt_lift_inf fi
  · exact continuousAt_lift_coe fc.continuousAt

/-- `lift` is holomorphic at finite values -/
theorem holomorphicAt_lift_coe (fa : AnalyticAt ℂ f z) : HolomorphicAt I I (lift f y) z := by
  rw [lift_eq_fill]; exact holomorphicAt_fill_coe ((holomorphic_coe _).comp (fa.holomorphicAt I I))

/-- `lift` is holomorphic at `∞` -/
theorem holomorphicAt_lift_inf (fa : ∀ᶠ z in atInf, AnalyticAt ℂ f z) (fi : Tendsto f atInf atInf) :
    HolomorphicAt I I (lift f ∞) ∞ := by
  rw [lift_eq_fill]; apply holomorphicAt_fill_inf
  exact fa.mp (eventually_of_forall fun z fa ↦ (holomorphic_coe _).comp (fa.holomorphicAt I I))
  exact coe_tendsto_inf.comp fi

/-- `lift` is holomorphic -/
theorem holomorphic_lift (fa : AnalyticOn ℂ f univ) (fi : Tendsto f atInf atInf) :
    Holomorphic I I (lift f ∞) := by
  intro z; induction z using OnePoint.rec
  · exact holomorphicAt_lift_inf (eventually_of_forall fun z ↦ fa z (mem_univ _)) fi
  · exact holomorphicAt_lift_coe (fa _ (mem_univ _))

/-- `lift'` is holomorphic (the parameterized version) -/
theorem holomorphicLift' {f : ℂ → ℂ → ℂ} (fa : AnalyticOn ℂ (uncurry f) univ)
    (fi : ∀ x, Tendsto (uncurry f) ((𝓝 x).prod atInf) atInf) :
    Holomorphic II I (uncurry (lift' f ∞)) := by
  apply osgoodManifold (continuous_lift' fa.continuous fi)
  · intro x z; induction z using OnePoint.rec
    · simp only [uncurry, lift_inf']; exact holomorphicAt_const
    · exact (holomorphic_coe _).comp ((fa _ (mem_univ ⟨_,_⟩)).along_fst.holomorphicAt _ _)
  · intro x z; refine holomorphic_lift (fun _ _ ↦ (fa _ (mem_univ ⟨_,_⟩)).along_snd) ?_ z
    exact (fi x).comp (tendsto_const_nhds.prod_mk Filter.tendsto_id)

/-- `𝕊` is path connected -/
instance : PathConnectedSpace 𝕊 := by
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

end RiemannSphere
