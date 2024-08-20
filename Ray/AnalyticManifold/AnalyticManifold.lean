import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Manifold.AnalyticManifold
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Ray.Analytic.HolomorphicUpstream

/-!
## Analytic manifolds

We define `AnalyticManifold`s over any complete, nontrivially normed field `𝕜`, as
charted spaces where all charts conversions are locally analytic.  We consider only
the boundaryless case for simplicity, though the `analyticGroupoid` is defined in the
boundary case too so this is a future generalization.  We then define the analogs to
`Smooth` for the analytic case:

1. `HolomorphicAt I J f x` means `f` is locally analytic at `x`
2. `HolomorphicOn I J f s` means `f` is locally analytic at each `x ∈ s`
3. `Holomorphic I J f` means `f` is analytic everywhere in the manifold

Possibly these should be renamed to `MAnalytic...`, though that name sounds bad.

Other things we show:

1. `extChartAt` and `.symm` are holomorphic with invertible derivatives
2. Arithmetic on holomorphic functions into `ℂ` are holomorphic
3. Holomorphic functions are differentiable, smooth, etc.
4. A variety of other small things
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- An analytic manifold w.r.t. a model `I : ModelWithCorners 𝕜 E H` is a charted space over H
    s.t. all extended chart conversion maps are analytic. -/
@[class]
structure AnalyticManifold {E H : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type)
    [TopologicalSpace M] [ChartedSpace H M] extends HasGroupoid M (analyticGroupoid I) : Prop

/-- Normed spaces are analytic manifolds over themselves -/
instance AnalyticManifold.self_of_nhds {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    AnalyticManifold (modelWithCornersSelf 𝕜 E) E :=
  AnalyticManifold.mk (by infer_instance)

/-- `f ∈ analyticGroupoid` iff its in the `contDiffGroupoid`, is analytic in the interior, and
maps interior to interior -/
lemma mem_analyticGroupoid {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] {I : ModelWithCorners 𝕜 E A} {f : PartialHomeomorph A A} :
    f ∈ analyticGroupoid I ↔ f ∈ contDiffGroupoid ∞ I ∧
      (AnalyticOn 𝕜 (I ∘ f ∘ I.symm) (I.symm ⁻¹' f.source ∩ interior (range I)) ∧
        (I.symm ⁻¹' f.source ∩ interior (range I)).image (I ∘ f ∘ I.symm) ⊆ interior (range I)) ∧
      (AnalyticOn 𝕜 (I ∘ f.symm ∘ I.symm) (I.symm ⁻¹' f.target ∩ interior (range I)) ∧
        (I.symm ⁻¹' f.target ∩ interior (range I)).image (I ∘ f.symm ∘ I.symm) ⊆ interior (range I))
    := by
  rfl

/-- Version of `ModelWithCorners.prod_apply` with `x ∈ H × H'` rather than `ModelProd H H'`.  This
comes up because other simplification doesn't stay in `ModelProd`. -/
@[simp]
lemma ModelWithCorners.prod_apply' {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (x : H × H') :
    (I.prod I') x = (I x.1, I' x.2) :=
  ModelWithCorners.prod_apply _ _ _

/-- The product of two analytic local homeomorphisms is analytic -/
theorem analyticGroupoid_prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {f : PartialHomeomorph A A} {g : PartialHomeomorph B B}
    (fa : f ∈ analyticGroupoid I) (ga : g ∈ analyticGroupoid J) :
    f.prod g ∈ analyticGroupoid (I.prod J) := by
  have er : (range fun x : A × B ↦ (I x.1, J x.2)) = range I ×ˢ range J := range_prod_map
  have ei : interior (range fun x : A × B ↦ (I x.1, J x.2)) =
      interior (range I) ×ˢ interior (range J) := by rw [er, interior_prod_eq]
  -- This proof is made a lot messier because `simp`s tend to fail.  E.g., we can't simplify via
  -- the above `ei` lemma, because the `TopologicalSpace` instances aren't defeq.  Instead, we use
  -- it via `subset_of_eq`.
  simp only [mem_analyticGroupoid, Function.comp, image_subset_iff] at fa ga ⊢
  refine ⟨contDiffGroupoid_prod fa.1 ga.1, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply AnalyticOn.prod
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine fa.2.1.1.comp (analyticOn_fst _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.1, (subset_of_eq ei m.2).1⟩
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine ga.2.1.1.comp (analyticOn_snd _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.2, (subset_of_eq ei m.2).2⟩
  · simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
      PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_symm,
      PartialEquiv.coe_symm_mk, PartialHomeomorph.prod_apply, ModelWithCorners.mk_coe,
      PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source, mk_preimage_prod,
      image_subset_iff]
    intro x ⟨⟨m0,m1⟩,m2⟩
    replace m2 := subset_of_eq ei m2
    exact subset_of_eq ei.symm ⟨fa.2.1.2 ⟨m0,m2.1⟩, ga.2.1.2 ⟨m1,m2.2⟩⟩
  · apply AnalyticOn.prod
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine fa.2.2.1.comp (analyticOn_fst _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.1, (subset_of_eq ei m.2).1⟩
    · simp only [ModelWithCorners.symm, modelWithCorners_prod_toPartialEquiv,
        PartialEquiv.prod_symm, PartialEquiv.prod_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        PartialHomeomorph.prod_apply, PartialHomeomorph.prod_toPartialEquiv,
        PartialEquiv.prod_source]
      refine ga.2.2.1.comp (analyticOn_snd _) ?_
      intro x m
      simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
        PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_coe,
        mem_inter_iff, mem_preimage, mem_prod] at m ⊢
      exact ⟨m.1.2, (subset_of_eq ei m.2).2⟩
  · simp only [ModelWithCorners.prod, ModelWithCorners.source_eq, mem_univ, and_self, setOf_true,
      PartialEquiv.prod_target, ModelWithCorners.target_eq, ModelWithCorners.mk_symm,
      PartialEquiv.coe_symm_mk, PartialHomeomorph.prod_apply, ModelWithCorners.mk_coe,
      PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_source, mk_preimage_prod,
      image_subset_iff]
    intro x ⟨⟨m0,m1⟩,m2⟩
    replace m2 := subset_of_eq ei m2
    exact subset_of_eq ei.symm ⟨fa.2.2.2 ⟨m0,m2.1⟩, ga.2.2.2 ⟨m1,m2.2⟩⟩

/-- `M × N` is a analytic manifold if `M` and `N` are -/
instance AnalyticManifold.prod {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] {I : ModelWithCorners 𝕜 E A} {J : ModelWithCorners 𝕜 F B}
    {M : Type} [TopologicalSpace M] [ChartedSpace A M] [m : AnalyticManifold I M]
    {N : Type} [TopologicalSpace N] [ChartedSpace B N] [n : AnalyticManifold J N] :
    AnalyticManifold (I.prod J) (M × N) where
  compatible := by
    intro f g ⟨f1, f2, hf1, hf2, fe⟩ ⟨g1, g2, hg1, hg2, ge⟩
    rw [←fe, ←ge, PartialHomeomorph.prod_symm, PartialHomeomorph.prod_trans]
    exact analyticGroupoid_prod (m.toHasGroupoid.compatible f2 g2)
      (n.toHasGroupoid.compatible hf2 hg2)

/-- Complex manifolds are smooth manifolds -/
instance AnalyticManifold.smoothManifoldWithCorners {E A : Type} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [TopologicalSpace A] {I : ModelWithCorners 𝕜 E A}
    {M : Type} [TopologicalSpace M] [ChartedSpace A M]
    [cm : AnalyticManifold I M] :
    SmoothManifoldWithCorners I M := by
  have h : HasGroupoid M (analyticGroupoid I) := cm.toHasGroupoid
  simp only [analyticGroupoid, hasGroupoid_inf_iff] at h
  exact SmoothManifoldWithCorners.mk' (gr := h.1)

/-- A typeclass for trivial manifolds where `extChartAt` is the identity.
    In this case, `extChartAt I : E → E`, but the intermediate space `H` might be different.
    This is necessary to handle product spaces, where the intermediate space may be `ModelProd`. -/
@[class]
structure ExtChartEqRefl {E H : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [ChartedSpace H E]
    [AnalyticManifold I E] : Prop where
  eq_refl : ∀ x, extChartAt I x = PartialEquiv.refl E

/-- `extChartAt I x = refl` given [ExtChartEqRefl] -/
theorem extChartAt_eq_refl {E H : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [ChartedSpace H E]
    [AnalyticManifold I E] [e : ExtChartEqRefl I] (x : E) :
    extChartAt I x = PartialEquiv.refl E :=
  e.eq_refl x

/-- `extChartAt = refl` for `I = modelWithCornersSelf 𝕜 E` -/
instance extChartEqReflSelf {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
    ExtChartEqRefl (modelWithCornersSelf 𝕜 E) := ⟨by
  simp only [PartialHomeomorph.singletonChartedSpace_chartAt_eq, PartialHomeomorph.refl_partialEquiv,
    PartialEquiv.refl_source, forall_const, extChartAt, PartialHomeomorph.extend,
    modelWithCornersSelf_partialEquiv, PartialEquiv.refl_trans]⟩

/-- `extChartAt = refl` extends to products -/
instance extChartEqReflProd {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace A] {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace B] (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    [ChartedSpace A E] [AnalyticManifold I E] [ExtChartEqRefl I] [ChartedSpace B F]
    [AnalyticManifold J F] [ExtChartEqRefl J] : ExtChartEqRefl (I.prod J) :=
  ⟨fun x ↦ by simp_rw [extChartAt_prod, extChartAt_eq_refl, PartialEquiv.refl_prod_refl]⟩

/-- Charts are analytic w.r.t. themselves.
    This lemma helps when proving particular spaces are analytic manifolds. -/
theorem extChartAt_self_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : Type} [TopologicalSpace M] (f : PartialHomeomorph M E) :
    AnalyticOn 𝕜 (𝓘(𝕜, E) ∘ (f.symm.trans f) ∘ ⇑𝓘(𝕜, E).symm)
      (𝓘(𝕜, E) '' (f.symm.trans f).toPartialEquiv.source) := by
  apply AnalyticOn.congr (f := fun z ↦ z)
  · simp only [modelWithCornersSelf_coe, id_eq, image_id', PartialHomeomorph.trans_toPartialEquiv,
      PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source, PartialEquiv.symm_source,
      PartialHomeomorph.coe_coe_symm]
    exact f.isOpen_inter_preimage_symm f.open_source
  · exact analyticOn_id _
  · intro x m
    simp only [modelWithCornersSelf_coe, id, image_id', PartialHomeomorph.trans_toPartialEquiv,
      PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source, PartialEquiv.symm_source,
      PartialHomeomorph.coe_coe_symm, mem_inter_iff, mem_preimage, Function.comp,
      modelWithCornersSelf_coe_symm, PartialHomeomorph.coe_trans] at m ⊢
    rw [f.right_inv m.1]

variable {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace A]
variable {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B]
variable {G C : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [TopologicalSpace C]
variable {H D : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [TopologicalSpace D]
variable {M : Type} {I : ModelWithCorners 𝕜 E A} [TopologicalSpace M]
variable {N : Type} {J : ModelWithCorners 𝕜 F B} [TopologicalSpace N]
variable {O : Type} {K : ModelWithCorners 𝕜 G C} [TopologicalSpace O]
variable {P : Type} {L : ModelWithCorners 𝕜 H D} [TopologicalSpace P]
variable [ChartedSpace A M] [ChartedSpace B N] [ChartedSpace C O] [ChartedSpace D P]

/-- Holomorphic at a point -/
def HolomorphicAt (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    (f : M → N) (x : M) :=
  ChartedSpace.LiftPropAt (fun f _ x ↦ AnalyticAt 𝕜 (J ∘ f ∘ I.symm) (I x)) f x

/-- Holomorphic on a set -/
def HolomorphicOn (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    (f : M → N) (s : Set M) :=
  ∀ x, x ∈ s → HolomorphicAt I J f x

/-- Holomorphic everywhere -/
def Holomorphic (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    (f : M → N) :=
  ∀ x, HolomorphicAt I J f x

/-- `HolomorphicOn` is monotonic in the set -/
theorem HolomorphicOn.mono {f : M → N} {s t : Set M} (fa : HolomorphicOn I J f s) (ts : t ⊆ s) :
    HolomorphicOn I J f t := fun _ m ↦ fa _ (ts m)

/-- Functions are `HolomorphicAt` iff they are continuous and analytic in charts -/
theorem holomorphicAt_iff {f : M → N} {x : M} :
    HolomorphicAt I J f x ↔ ContinuousAt f x ∧
      AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  simp only [HolomorphicAt, ChartedSpace.liftPropAt_iff, extChartAt, PartialHomeomorph.extend_coe,
    PartialHomeomorph.extend_coe_symm, Function.comp]

/-- Functions are `Holomorphic` iff they are continuous and analytic in charts everywhere -/
theorem holomorphic_iff {f : M → N} :
    Holomorphic I J f ↔ Continuous f ∧
      ∀ x : M, AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x x) := by
  simp only [Holomorphic, holomorphicAt_iff, continuous_iff_continuousAt]; exact forall_and

/-- Holomorphic functions are continuous -/
theorem HolomorphicAt.continuousAt {f : M → N} {x : M} (h : HolomorphicAt I J f x) :
    ContinuousAt f x := (holomorphicAt_iff.mp h).1

/-- Holomorphic functions are continuous -/
theorem Holomorphic.continuous {f : M → N} (h : Holomorphic I J f) : Continuous f :=
  (holomorphic_iff.mp h).1

/-- Holomorphic functions are continuous (explicit `I`, `J` version) -/
theorem HolomorphicAt.continuousAt' (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    [I.Boundaryless] [AnalyticManifold I M] [J.Boundaryless] [AnalyticManifold J N]
    {f : M → N} {x : M} (h : HolomorphicAt I J f x) :
    ContinuousAt f x := h.continuousAt

/-- `HolomorphicOn` functions are `ContinuousOn` -/
theorem HolomorphicOn.continuousOn {f : M → N} {s : Set M} (h : HolomorphicOn I J f s) :
    ContinuousOn f s := fun x m ↦ (h x m).continuousAt.continuousWithinAt

/-- Analytic functions are holomorphic, and vice versa -/
theorem analyticAt_iff_holomorphicAt [ChartedSpace A E] [AnalyticManifold I E] [ChartedSpace B F]
    [AnalyticManifold J F] [ExtChartEqRefl I] [ExtChartEqRefl J] {f : E → F} {x : E} :
    AnalyticAt 𝕜 f x ↔ HolomorphicAt I J f x := by
  simp only [holomorphicAt_iff, extChartAt_eq_refl, PartialEquiv.refl_coe, PartialEquiv.refl_symm,
    Function.id_comp, Function.comp_id, id_eq, iff_and_self]
  exact AnalyticAt.continuousAt

/-- Analytic functions are holomorphic -/
theorem AnalyticAt.holomorphicAt {f : E → F} {x : E} (fa : AnalyticAt 𝕜 f x)
    (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] [ChartedSpace A E] [AnalyticManifold I E]
    [ExtChartEqRefl I]
    (J : ModelWithCorners 𝕜 F B) [J.Boundaryless] [ChartedSpace B F] [AnalyticManifold J F]
    [ExtChartEqRefl J] :
    HolomorphicAt I J f x :=
  analyticAt_iff_holomorphicAt.mp fa

/-- Holomorphic functions analytic -/
theorem HolomorphicAt.analyticAt
    (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] [ChartedSpace A E] [AnalyticManifold I E]
    [ExtChartEqRefl I]
    (J : ModelWithCorners 𝕜 F B) [J.Boundaryless] [ChartedSpace B F] [AnalyticManifold J F]
    [ExtChartEqRefl J]
    {f : E → F} {x : E} : HolomorphicAt I J f x → AnalyticAt 𝕜 f x :=
  analyticAt_iff_holomorphicAt.mpr

/-- Holomorphic functions compose -/
theorem HolomorphicAt.comp {f : N → O} {g : M → N} {x : M} (fh : HolomorphicAt J K f (g x))
    (gh : HolomorphicAt I J g x) : HolomorphicAt I K (fun x ↦ f (g x)) x := by
  rw [holomorphicAt_iff] at fh gh ⊢; use fh.1.comp gh.1
  have e : extChartAt J (g x) (g x) =
      (extChartAt J (g x) ∘ g ∘ (extChartAt I x).symm) (extChartAt I x x) := by
    simp only [Function.comp_apply, PartialEquiv.left_inv _ (mem_extChartAt_source I x)]
  rw [e] at fh; apply (fh.2.comp gh.2).congr; clear e fh
  simp only [Function.comp]
  have m : ∀ᶠ y in 𝓝 (extChartAt I x x), g ((extChartAt I x).symm y) ∈
      (extChartAt J (g x)).source := by
    apply ContinuousAt.eventually_mem
    · apply ContinuousAt.comp
      · rw [PartialEquiv.left_inv _ (mem_extChartAt_source _ _)]; exact gh.1
      · exact continuousAt_extChartAt_symm I x
    · rw [PartialEquiv.left_inv _ (mem_extChartAt_source _ _)]
      exact extChartAt_source_mem_nhds _ _
  refine m.mp (.of_forall fun y m ↦ ?_)
  simp_rw [PartialEquiv.left_inv _ m]

/-- Holomorphic functions compose -/
theorem Holomorphic.comp {f : N → O} {g : M → N} (fh : Holomorphic J K f) (gh : Holomorphic I J g) :
    Holomorphic I K fun x ↦ f (g x) := fun _ ↦ (fh _).comp (gh _)

/-- Holomorphic functions compose at a point, with a separate argument for point equality -/
theorem HolomorphicAt.comp_of_eq {f : N → O} {g : M → N} {x : M} {y : N}
    (fh : HolomorphicAt J K f y) (gh : HolomorphicAt I J g x) (e : g x = y) :
    HolomorphicAt I K (fun x ↦ f (g x)) x := by
  rw [← e] at fh; exact fh.comp gh

/-- `HolomorphicAt` for `x ↦ (f x, g x)` -/
theorem HolomorphicAt.prod {f : M → N} {g : M → O} {x : M} (fh : HolomorphicAt I J f x)
    (gh : HolomorphicAt I K g x) : HolomorphicAt I (J.prod K) (fun x ↦ (f x, g x)) x := by
  rw [holomorphicAt_iff] at fh gh ⊢; use fh.1.prod gh.1
  refine (fh.2.prod gh.2).congr (.of_forall fun y ↦ ?_)
  simp only [extChartAt_prod, Function.comp, PartialEquiv.prod_coe]

/-- `Holomorphic` for `x ↦ (f x, g x)` -/
theorem Holomorphic.prod {f : M → N} {g : M → O} (fh : Holomorphic I J f) (gh : Holomorphic I K g) :
    Holomorphic I (J.prod K) fun x ↦ (f x, g x) := fun _ ↦ (fh _).prod (gh _)

/-- `HolomorphicAt.comp` for a curried function -/
theorem HolomorphicAt.comp₂ {h : N → O → P} {f : M → N} {g : M → O} {x : M}
    (ha : HolomorphicAt (J.prod K) L (uncurry h) (f x, g x)) (fa : HolomorphicAt I J f x)
    (ga : HolomorphicAt I K g x) : HolomorphicAt I L (fun x ↦ h (f x) (g x)) x :=
  ha.comp (g := fun _ ↦ (_, _)) (fa.prod ga)

/-- `HolomorphicAt.comp₂`, with a separate argument for point equality -/
theorem HolomorphicAt.comp₂_of_eq {h : N → O → P} {f : M → N} {g : M → O} {x : M} {y : N × O}
    (ha : HolomorphicAt (J.prod K) L (uncurry h) y) (fa : HolomorphicAt I J f x)
    (ga : HolomorphicAt I K g x) (e : (f x, g x) = y) :
    HolomorphicAt I L (fun x ↦ h (f x) (g x)) x := by rw [← e] at ha; exact ha.comp₂ fa ga

/-- `id` is holomorphic -/
theorem holomorphicAt_id [I.Boundaryless] [AnalyticManifold I M] {x : M} :
    HolomorphicAt I I (fun x ↦ x) x := by
  rw [holomorphicAt_iff]; use continuousAt_id; apply (analyticAt_id _ _).congr
  filter_upwards [((isOpen_extChartAt_target I x).eventually_mem (mem_extChartAt_target I x))]
  intro y m
  simp only [Function.comp, PartialEquiv.right_inv _ m, id]

/-- `id` is holomorphic -/
theorem holomorphic_id [I.Boundaryless] [AnalyticManifold I M] : Holomorphic I I fun x : M ↦ x :=
  fun _ ↦ holomorphicAt_id

/-- Constants are holomorphic -/
theorem holomorphicAt_const {x : M} {c : N} : HolomorphicAt I J (fun _ ↦ c) x := by
  rw [holomorphicAt_iff]; use continuousAt_const
  simp only [Prod.fst_comp_mk, Function.comp]; exact analyticAt_const

/-- Constants are holomorphic -/
theorem holomorphic_const {c : N} : Holomorphic I J fun _ : M ↦ c := fun _ ↦ holomorphicAt_const

/-- Curried holomorphic functions are holomorphic in the first coordinate -/
theorem HolomorphicAt.along_fst [I.Boundaryless] [AnalyticManifold I M] {f : M → N → O} {x : M}
    {y : N} (fa : HolomorphicAt (I.prod J) K (uncurry f) (x, y)) :
    HolomorphicAt I K (fun x ↦ f x y) x :=
  HolomorphicAt.comp₂ fa holomorphicAt_id holomorphicAt_const

/-- Curried holomorphic functions are holomorphic in the second coordinate -/
theorem HolomorphicAt.along_snd [I.Boundaryless] [J.Boundaryless] [AnalyticManifold I M]
    [AnalyticManifold J N] {f : M → N → O} {x : M} {y : N}
    (fa : HolomorphicAt (I.prod J) K (uncurry f) (x, y)) : HolomorphicAt J K (fun y ↦ f x y) y :=
  HolomorphicAt.comp₂ fa holomorphicAt_const holomorphicAt_id

/-- Curried holomorphic functions are holomorphic in the first coordinate -/
theorem Holomorphic.along_fst [I.Boundaryless] [AnalyticManifold I M] {f : M → N → O}
    (fa : Holomorphic (I.prod J) K (uncurry f)) {y : N} :
    Holomorphic I K fun x ↦ f x y := fun _ ↦ (fa _).along_fst

/-- Curried holomorphic functions are holomorphic in the second coordinate -/
theorem Holomorphic.along_snd [I.Boundaryless] [J.Boundaryless] [AnalyticManifold I M]
    [AnalyticManifold J N] {f : M → N → O} {x : M}
    (fa : Holomorphic (I.prod J) K (uncurry f)) : Holomorphic J K fun y ↦ f x y := fun _ ↦
  (fa _).along_snd

/-- `fst` is holomorphic -/
theorem holomorphicAt_fst [I.Boundaryless] [J.Boundaryless] [AnalyticManifold I M] {x : M × N} :
    HolomorphicAt (I.prod J) I (fun p : M × N ↦ p.fst) x := by
  rw [holomorphicAt_iff]; use continuousAt_fst; refine (analyticAt_fst _).congr ?_
  filter_upwards [((isOpen_extChartAt_target _ x).eventually_mem (mem_extChartAt_target _ _))]
  intro y m
  rw [extChartAt_prod] at m
  simp only [PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_target, mem_prod] at m
  simp only [extChartAt_prod, Function.comp, PartialEquiv.prod_coe_symm]
  exact ((extChartAt I x.1).right_inv m.1).symm

/-- `snd` is holomorphic -/
theorem holomorphicAt_snd [I.Boundaryless] [J.Boundaryless] {x : M × N} :
    HolomorphicAt (I.prod J) J (fun p : M × N ↦ p.snd) x := by
  rw [holomorphicAt_iff]; use continuousAt_snd; refine (analyticAt_snd _).congr ?_
  filter_upwards [((isOpen_extChartAt_target _ x).eventually_mem (mem_extChartAt_target _ _))]
  intro y m
  rw [extChartAt_prod] at m
  simp only [PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_target, mem_prod] at m
  simp only [extChartAt_prod, Function.comp, PartialEquiv.prod_coe_symm]
  exact ((extChartAt J x.2).right_inv m.2).symm

/-- `fst` is holomorphic -/
theorem holomorphic_fst [I.Boundaryless] [J.Boundaryless] [AnalyticManifold I M] :
    Holomorphic (I.prod J) I fun p : M × N ↦ p.fst := fun _ ↦ holomorphicAt_fst

/-- `snd` is holomorphic -/
theorem holomorphic_snd [I.Boundaryless] [J.Boundaryless] :
    Holomorphic (I.prod J) J fun p : M × N ↦ p.snd := fun _ ↦ holomorphicAt_snd

/-- `I.toPartialEquiv = I` in terms of `coe` -/
theorem ModelWithCorners.coe_coe (I : ModelWithCorners 𝕜 E A) : ⇑I.toPartialEquiv = (I : A → E) := rfl

/-- `I.toPartialEquiv.symm = I.symm` in terms of `coe` -/
theorem ModelWithCorners.coe_coe_symm (I : ModelWithCorners 𝕜 E A) :
    ⇑I.toPartialEquiv.symm = (I.symm : E → A) := rfl

/-- `extChartAt` is holomorphic -/
theorem HolomorphicAt.extChartAt [CompleteSpace E] [I.Boundaryless] [cm : AnalyticManifold I M]
    {x y : M} (ys : y ∈ (extChartAt I x).source) :
    HolomorphicAt I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y := by
  rw [holomorphicAt_iff]; use continuousAt_extChartAt' I ys
  simp only [Function.comp, extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
    PartialHomeomorph.toFun_eq_coe, ModelWithCorners.toPartialEquiv_coe,
    PartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
    PartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, PartialEquiv.trans_symm_eq_symm_trans_symm,
    ModelWithCorners.toPartialEquiv_coe_symm, PartialHomeomorph.coe_coe_symm,
    PartialEquiv.refl_coe, id, _root_.extChartAt]
  have a : (chartAt A x).symm ≫ₕ chartAt A y ∈ analyticGroupoid I := by
    apply StructureGroupoid.compatible_of_mem_maximalAtlas
    exact (@StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid x)
    exact (@StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid y)
  simp only [mem_analyticGroupoid_of_boundaryless, PartialHomeomorph.trans_symm_eq_symm_trans_symm,
    Function.comp, PartialHomeomorph.trans_apply] at a
  apply a.2; clear a; use chartAt A y y; aesop

/-- `extChartAt.symm` is holomorphic -/
theorem HolomorphicAt.extChartAt_symm [CompleteSpace E] [I.Boundaryless] [cm : AnalyticManifold I M]
    {x : M} {y : E} (ys : y ∈ (_root_.extChartAt I x).target) :
    HolomorphicAt (modelWithCornersSelf 𝕜 E) I (_root_.extChartAt I x).symm y := by
  rw [holomorphicAt_iff]; use continuousAt_extChartAt_symm'' I ys
  simp only [extChartAt_eq_refl, PartialEquiv.refl_coe, Function.comp, id, extChartAt,
    PartialHomeomorph.extend, PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm,
    PartialHomeomorph.coe_coe, PartialHomeomorph.coe_coe_symm, ModelWithCorners.coe_coe,
    ModelWithCorners.coe_coe_symm, modelWithCornersSelf_coe, chartAt_self_eq,
    PartialHomeomorph.refl_apply, PartialHomeomorph.refl_symm, modelWithCornersSelf_coe_symm]
  set y' := (chartAt A x).symm (I.symm y)
  have a : (chartAt A x).symm ≫ₕ chartAt A ((chartAt A x).symm (I.symm y)) ∈
      analyticGroupoid I := by
    apply StructureGroupoid.compatible_of_mem_maximalAtlas
    exact @StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid x
    exact @StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid y'
  simp only [mem_analyticGroupoid_of_boundaryless, PartialHomeomorph.trans_symm_eq_symm_trans_symm,
    Function.comp] at a
  apply a.1; clear a; use I.symm y; aesop

/-- Addition is holomorphic -/
theorem HolomorphicAt.add {f g : M → 𝕜} {x : M}
    (fa : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) f x)
    (ga : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) g x) :
    HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x + g x) x := by
  have e : (fun x ↦ f x + g x) = (fun p : 𝕜 × 𝕜 ↦ p.1 + p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]; exact (((analyticAt_fst _).add (analyticAt_snd _)).holomorphicAt _ _).comp (fa.prod ga)

/-- Subtraction is holomorphic -/
theorem HolomorphicAt.sub {f g : M → 𝕜} {x : M}
    (fa : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) f x)
    (ga : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) g x) :
    HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x - g x) x :=
  (((analyticAt_fst _).sub (analyticAt_snd _)).holomorphicAt _ _).comp (fa.prod ga)

/-- Multiplication is holomorphic -/
theorem HolomorphicAt.mul {f g : M → 𝕜} {x : M}
    (fa : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) f x)
    (ga : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) g x) :
    HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x * g x) x :=
  (((analyticAt_fst _).mul (analyticAt_snd _)).holomorphicAt _ _).comp (fa.prod ga)

/-- Inverse is holomorphic away from zeros -/
theorem HolomorphicAt.inv {f : M → 𝕜} {x : M} (fa : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) f x)
    (f0 : f x ≠ 0) : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ (f x)⁻¹) x :=
  (((analyticAt_id _ _).inv f0).holomorphicAt _ _).comp fa

/-- Division is holomorphic away from denominator zeros -/
theorem HolomorphicAt.div {f g : M → 𝕜} {x : M}
    (fa : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) f x)
    (ga : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) g x) (g0 : g x ≠ 0) :
    HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x / g x) x := by
  simp only [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- Powers are holomorphic -/
theorem HolomorphicAt.pow {f : M → 𝕜} {x : M} (fa : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) f x)
    {n : ℕ} : HolomorphicAt I (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x ^ n) x := by
  have e : (fun x ↦ f x ^ n) = (fun z : 𝕜 ↦ z ^ n) ∘ f := rfl
  rw [e]; exact (((analyticAt_id _ _).pow _).holomorphicAt _ _).comp fa

/-- Complex powers `f x ^ g x` are holomorphic if `f x` avoids the negative real axis  -/
theorem HolomorphicAt.cpow {E A M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace A] {I : ModelWithCorners ℂ E A} [TopologicalSpace M] [ChartedSpace A M]
    [I.Boundaryless] [AnalyticManifold I M]
    {f g : M → ℂ} {x : M}
    (fa : HolomorphicAt I (modelWithCornersSelf ℂ ℂ) f x)
    (ga : HolomorphicAt I (modelWithCornersSelf ℂ ℂ) g x) (a : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HolomorphicAt I (modelWithCornersSelf ℂ ℂ) (fun x ↦ f x ^ g x) x := by
  have e : (fun x ↦ f x ^ g x) = (fun p : ℂ × ℂ ↦ p.1 ^ p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  refine (((analyticAt_fst _).cpow (analyticAt_snd _) ?_).holomorphicAt _ _).comp (fa.prod ga)
  exact a

/-- Holomorphic functions are smooth -/
theorem HolomorphicAt.smoothAt [CompleteSpace F] {f : M → N} {x : M} (fa : HolomorphicAt I J f x) :
    SmoothAt I J f x := by
  rw [holomorphicAt_iff] at fa; simp only [SmoothAt, contMDiffAt_iff]
  use fa.1; use fa.2.contDiffAt.contDiffWithinAt

/-- Holomorphic functions are smooth -/
theorem HolomorphicOn.smoothOn [CompleteSpace F] {f : M → N} {s : Set M}
    (fa : HolomorphicOn I J f s) : SmoothOn I J f s :=
  fun x m ↦ (fa x m).smoothAt.smoothWithinAt

/-- Holomorphic functions are differentiable -/
theorem HolomorphicAt.mdifferentiableAt [CompleteSpace F] {f : M → N} {x : M}
    (fa : HolomorphicAt I J f x) : MDifferentiableAt I J f x :=
  fa.smoothAt.mdifferentiableAt

/-- Iterated holomorphic functions are holomorphic -/
theorem Holomorphic.iter [I.Boundaryless] [AnalyticManifold I M] {f : M → M}
    (fa : Holomorphic I I f) (n : ℕ) :
    Holomorphic I I f^[n] := by
  induction' n with n h; simp only [Function.iterate_zero]; exact holomorphic_id
  simp only [Function.iterate_succ']; exact fa.comp h

/-- Chart derivatives are invertible (left inverse) -/
theorem extChartAt_mderiv_left_inverse [CompleteSpace E] [I.Boundaryless] [AnalyticManifold I M]
    {x y : M} (m : y ∈ (extChartAt I x).source) :
    (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm (extChartAt I x y)).comp
        (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I y) := by
  have m' : extChartAt I x y ∈ (extChartAt I x).target := PartialEquiv.map_source _ m
  have c := mfderiv_comp y (HolomorphicAt.extChartAt_symm m').mdifferentiableAt
    (HolomorphicAt.extChartAt m).mdifferentiableAt
  refine _root_.trans c.symm ?_; clear c; rw [←mfderiv_id]; apply Filter.EventuallyEq.mfderiv_eq
  rw [Filter.eventuallyEq_iff_exists_mem]; use(extChartAt I x).source
  use extChartAt_source_mem_nhds' I m
  intro z zm; simp only [Function.comp, id, PartialEquiv.left_inv _ zm]

/-- Chart derivatives are invertible (right inverse) -/
theorem extChartAt_mderiv_right_inverse [CompleteSpace E] [I.Boundaryless] [AnalyticManifold I M]
    {x : M} {y : E} (m : y ∈ (extChartAt I x).target) :
    (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) ((extChartAt I x).symm y)).comp
        (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm y) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) y) := by
  have m' : (extChartAt I x).symm y ∈ (extChartAt I x).source := PartialEquiv.map_target _ m
  have c := mfderiv_comp y (HolomorphicAt.extChartAt m').mdifferentiableAt
    (HolomorphicAt.extChartAt_symm m).mdifferentiableAt
  refine _root_.trans c.symm ?_; clear c; rw [← mfderiv_id]; apply Filter.EventuallyEq.mfderiv_eq
  rw [Filter.eventuallyEq_iff_exists_mem]; use(extChartAt I x).target
  have n := extChartAt_target_mem_nhdsWithin' I m'
  simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ,
    PartialEquiv.right_inv _ m] at n
  use n; intro z zm
  simp only [Function.comp, id, PartialEquiv.right_inv _ zm, Function.comp]

/-- Chart derivatives are invertible (right inverse) -/
theorem extChartAt_mderiv_right_inverse' [CompleteSpace E] [I.Boundaryless] [AnalyticManifold I M]
    {x y : M} (m : y ∈ (extChartAt I x).source) :
    (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y).comp
        (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm (extChartAt I x y)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) (extChartAt I x y)) := by
  have h := extChartAt_mderiv_right_inverse (PartialEquiv.map_source _ m)
  rw [PartialEquiv.left_inv _ m] at h; exact h

/-- `HolomorphicAt` depends only on local values -/
theorem HolomorphicAt.congr {f g : M → N} {x : M} (fa : HolomorphicAt I J f x) (e : f =ᶠ[𝓝 x] g) :
    HolomorphicAt I J g x := by
  rw [holomorphicAt_iff] at fa ⊢; use fa.1.congr e; apply fa.2.congr
  rw [e.self_of_nhds]; refine Filter.EventuallyEq.fun_comp ?_ (_root_.extChartAt J (g x))
  have t := (continuousAt_extChartAt_symm I x).tendsto
  rw [PartialEquiv.left_inv _ (mem_extChartAt_source I x)] at t
  exact e.comp_tendsto t

/-- If we're holomorphic at a point, we're locally holomorphic -/
theorem HolomorphicAt.eventually [CompleteSpace E] [CompleteSpace F] [I.Boundaryless]
    [J.Boundaryless] [AnalyticManifold I M] [AnalyticManifold J N]
    {f : M → N} {x : M} (fa : HolomorphicAt I J f x) :
    ∀ᶠ y in 𝓝 x, HolomorphicAt I J f y := by
  apply (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source J (f x)).mem_nhds
    (mem_extChartAt_source J (f x)))).eventually_nhds.mp
  apply ((isOpen_extChartAt_source I x).eventually_mem (mem_extChartAt_source I x)).mp
  apply ((continuousAt_extChartAt I x).eventually
    ((isOpen_analyticAt _ _).eventually_mem (holomorphicAt_iff.mp fa).2)).mp
  refine .of_forall fun y a m fm ↦ ?_
  simp only at a m fm; rw [mem_setOf] at a
  have h := a.holomorphicAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 F); clear a
  have h' := (HolomorphicAt.extChartAt_symm (PartialEquiv.map_source _ fm.self_of_nhds)).comp_of_eq
      (h.comp (HolomorphicAt.extChartAt m)) ?_
  swap; simp only [Function.comp, PartialEquiv.left_inv _ m]
  apply h'.congr; clear h h'; simp only [Function.comp]
  apply ((isOpen_extChartAt_source I x).eventually_mem m).mp
  refine fm.mp (.of_forall fun z mf m ↦ ?_)
  simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ mf]

/-- The domain of holomorphicity is open -/
theorem isOpen_holomorphicAt [CompleteSpace E] [CompleteSpace F] [I.Boundaryless] [J.Boundaryless]
    [AnalyticManifold I M] [AnalyticManifold J N] {f : M → N} :
    IsOpen {x | HolomorphicAt I J f x} := by
  rw [isOpen_iff_eventually]; intro x fa; exact fa.eventually

/-- `HasMFDerivAt` of `x ↦ (f x, g x)` is `df.prod dg` -/
theorem HasMFDerivAt.prod [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N]
    [SmoothManifoldWithCorners K O]
    {f : M → N} {g : M → O} {x : M}
    {df : TangentSpace I x →L[𝕜] TangentSpace J (f x)} (fh : HasMFDerivAt I J f x df)
    {dg : TangentSpace I x →L[𝕜] TangentSpace K (g x)} (gh : HasMFDerivAt I K g x dg) :
    HasMFDerivAt I (J.prod K) (fun y ↦ (f y, g y)) x (df.prod dg) := by
  simp only [HasMFDerivAt, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ] at fh gh ⊢
  use fh.1.prod gh.1; exact fh.2.prod gh.2

/-- `TangentSpace` commutes with products -/
theorem tangentSpace_prod [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners J N] (x : M) (y : N) :
    TangentSpace (I.prod J) (x, y) = (TangentSpace I x × TangentSpace J y) := by
  simp only [TangentSpace]

/-- `HasMFDerivAt` composition for curried functions.
    This was oddly difficult to prove. -/
theorem MDifferentiableAt.hasMFDerivAt_uncurry [SmoothManifoldWithCorners J N]
    [SmoothManifoldWithCorners K O] [SmoothManifoldWithCorners L P]
    {f : N → O → P} {y : N} {z : O}
    (fd : MDifferentiableAt (J.prod K) L (uncurry f) (y, z))
    {df0 : TangentSpace J y →L[𝕜] TangentSpace L (f y z)}
    (fh0 : HasMFDerivAt J L (fun x ↦ f x z) y df0)
    {df1 : TangentSpace K z →L[𝕜] TangentSpace L (f y z)}
    (fh1 : HasMFDerivAt K L (fun x ↦ f y x) z df1) :
    HasMFDerivAt (J.prod K) L (uncurry f) (y, z)
      (df0.comp (ContinuousLinearMap.fst 𝕜 (TangentSpace J y) (TangentSpace K z)) +
        df1.comp (ContinuousLinearMap.snd 𝕜 (TangentSpace J y) (TangentSpace K z))) := by
  set fst := ContinuousLinearMap.fst 𝕜 (TangentSpace J y) (TangentSpace K z)
  set snd := ContinuousLinearMap.snd 𝕜 (TangentSpace J y) (TangentSpace K z)
  generalize hdf : mfderiv (J.prod K) L (uncurry f) (y, z) = df
  have fh := fd.hasMFDerivAt; rw [hdf] at fh
  suffices e : df = df0.comp fst + df1.comp snd by rw [e] at fh; exact fh
  apply ContinuousLinearMap.ext; intro ⟨u, v⟩
  simp only [Function.uncurry_apply_pair, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply]
  have hu : ∀ u : TangentSpace J y, df (u, 0) = df0 u := by
    intro u
    have d : HasMFDerivAt J L (uncurry f ∘ fun x ↦ (x, z)) y
        (df.comp ((ContinuousLinearMap.id 𝕜 (TangentSpace J y)).prod 0)) :=
      fh.comp y ((hasMFDerivAt_id _ _).prod (hasMFDerivAt_const _ _ _ _))
    simp only [hasMFDerivAt_unique fh0 d]
    refine Eq.trans (congr_arg _ ?_) (ContinuousLinearMap.comp_apply _ _ _).symm
    refine Eq.trans ?_ (ContinuousLinearMap.prod_apply _ _ _).symm
    simp only [ContinuousLinearMap.zero_apply, Prod.mk.injEq, and_true]
    exact rfl
  have hv : ∀ v : TangentSpace K z, df (0, v) = df1 v := by
    intro v
    have d : HasMFDerivAt K L (uncurry f ∘ fun x ↦ (y, x)) z (df.comp
        ((0 : TangentSpace K z →L[𝕜] TangentSpace J y).prod
          (ContinuousLinearMap.id 𝕜 (TangentSpace K z)))) :=
      fh.comp z ((hasMFDerivAt_const _ _ _ _).prod (hasMFDerivAt_id _ _))
    rw [hasMFDerivAt_unique fh1 d]
    refine Eq.trans (congr_arg _ ?_) (ContinuousLinearMap.comp_apply _ _ _).symm
    refine Eq.trans ?_ (ContinuousLinearMap.prod_apply _ _ _).symm
    simp only [Prod.mk.injEq]
    exact ⟨(ContinuousLinearMap.zero_apply _).symm, rfl⟩
  have e : (u, v) = (u, 0) + (0, v) := by simp only [Prod.mk_add_mk, add_zero, zero_add]
  nth_rw 1 [e]
  rw [map_add]
  exact congr_arg₂ _ (hu u) (hv v)

/-- `HasMFDerivAt` composition for curried functions -/
theorem MDifferentiableAt.hasMFDerivAt_comp2 [SmoothManifoldWithCorners I M]
    [SmoothManifoldWithCorners J N] [SmoothManifoldWithCorners K O] [SmoothManifoldWithCorners L P]
    {f : N → O → P} {g : M → N} {h : M → O} {x : M}
    (fd : MDifferentiableAt (J.prod K) L (uncurry f) (g x, h x))
    {dg : TangentSpace I x →L[𝕜] TangentSpace J (g x)} (gh : HasMFDerivAt I J g x dg)
    {dh : TangentSpace I x →L[𝕜] TangentSpace K (h x)} (hh : HasMFDerivAt I K h x dh)
    {df0 : TangentSpace J (g x) →L[𝕜] TangentSpace L (f (g x) (h x))}
    (fh0 : HasMFDerivAt J L (fun y ↦ f y (h x)) (g x) df0)
    {df1 : TangentSpace K (h x) →L[𝕜] TangentSpace L (f (g x) (h x))}
    (fh1 : HasMFDerivAt K L (fun y ↦ f (g x) y) (h x) df1) :
    HasMFDerivAt I L (fun y ↦ f (g y) (h y)) x (df0.comp dg + df1.comp dh) := by
  have fh := (fd.hasMFDerivAt_uncurry fh0 fh1).comp x (gh.prod hh)
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc,
    ContinuousLinearMap.fst_comp_prod, ContinuousLinearMap.snd_comp_prod] at fh
  exact fh

/-- More general version of `hasMFDerivAt_iff_hasDerivAt`.
    The mathlib version doesn't handle product spaces. -/
theorem hasMFDerivAt_iff_hasFDerivAt'
    {I : ModelWithCorners 𝕜 E A} [I.Boundaryless] [ChartedSpace A E] [AnalyticManifold I E]
    [ExtChartEqRefl I]
    {J : ModelWithCorners 𝕜 F B} [J.Boundaryless] [ChartedSpace B F] [AnalyticManifold J F]
    [ExtChartEqRefl J]
    {f : E → F} {x : E} {f' : E →L[𝕜] F} :
    HasMFDerivAt I J f x f' ↔ HasFDerivAt f f' x := by
  simp only [HasMFDerivAt, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ,
    writtenInExtChartAt, extChartAt_eq_refl, Function.comp, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, id]
  exact ⟨fun x ↦ x.2, fun d ↦ ⟨d.continuousAt, d⟩⟩

/-- Holomorphic functions have continuous tangent maps.
    Obviously more is true and the tangent map is holomorphic, but I don't need that yet -/
theorem HolomorphicOn.continuousOn_tangentMap [CompleteSpace E] [CompleteSpace F] [I.Boundaryless]
    [J.Boundaryless] [AnalyticManifold I M] [AnalyticManifold J N]
    {f : M → N} {s : Set M} (fa : HolomorphicOn I J f s) :
    ContinuousOn (tangentMap I J f) (Bundle.TotalSpace.proj ⁻¹' s) := by
  generalize ht : {x | HolomorphicAt I J f x} = t
  have o : IsOpen t := by rw [← ht]; exact isOpen_holomorphicAt
  have sub : s ⊆ t := by rw [← ht]; exact fa
  replace fa : HolomorphicOn I J f t := by
    simp only [HolomorphicOn, mem_setOf_eq, imp_self, implies_true, ← ht]
  refine ContinuousOn.mono ?_ (preimage_mono sub)
  apply (fa.smoothOn.contMDiffOn.continuousOn_tangentMapWithin le_top o.uniqueMDiffOn).congr
  intro x m; simp only [mem_preimage] at m
  rw [tangentMapWithin_eq_tangentMap (o.uniqueMDiffOn _ m) (fa _ m).mdifferentiableAt]

/-- `extChartAt` as a `PartialHomeomorph` -/
def extChartAt' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type} [TopologicalSpace M]
    [ChartedSpace A M] (x : M) : PartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source I x
  open_target := isOpen_extChartAt_target I x
  continuousOn_toFun := continuousOn_extChartAt I x
  continuousOn_invFun := continuousOn_extChartAt_symm I x

/-- `extChartAt` maps `𝓝` to `𝓝` -/
theorem extChartAt_map_nhds [I.Boundaryless] {x y : M} (m : y ∈ (extChartAt I x).source) :
    Filter.map (extChartAt I x) (𝓝 y) = 𝓝 (extChartAt I x y) :=
  (extChartAt' I x).map_nhds_eq m

/-- `extChartAt` maps `𝓝` to `𝓝` -/
theorem extChartAt_map_nhds' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type}
    [TopologicalSpace M] [ChartedSpace A M] [AnalyticManifold I M] (x : M) :
    Filter.map (extChartAt I x) (𝓝 x) = 𝓝 (extChartAt I x x) :=
  extChartAt_map_nhds (mem_extChartAt_source I x)

/-- `extChartAt.symm` maps `𝓝` to `𝓝` -/
theorem extChartAt_symm_map_nhds [I.Boundaryless] {x : M} {y : E} (m : y ∈ (extChartAt I x).target) :
    Filter.map (extChartAt I x).symm (𝓝 y) = 𝓝 ((extChartAt I x).symm y) :=
  (extChartAt' I x).symm.map_nhds_eq m

/-- `extChartAt.symm` maps `𝓝` to `𝓝` -/
theorem extChartAt_symm_map_nhds' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type}
    [TopologicalSpace M] [ChartedSpace A M] [AnalyticManifold I M] (x : M) :
    Filter.map (extChartAt I x).symm (𝓝 (extChartAt I x x)) = 𝓝 x := by
  convert extChartAt_symm_map_nhds (mem_extChartAt_target I x)
  simp only [PartialEquiv.left_inv _ (mem_extChartAt_source I x)]

/-- Nontrivial manifolds have no isolated points.
    Unfortunately, making this an instance gives "cannot find synthesization order for instance" -/
theorem AnalyticManifold.punctured_nhds_neBot (I : ModelWithCorners 𝕜 E A) [I.Boundaryless]
    [AnalyticManifold I M] [Nontrivial E] (x : M) : (𝓝[{x}ᶜ] x).NeBot := by
  have p := Module.punctured_nhds_neBot 𝕜 E (extChartAt I x x)
  simp only [← Filter.frequently_true_iff_neBot, frequently_nhdsWithin_iff, ←
    extChartAt_symm_map_nhds' I x, Filter.frequently_map, true_and_iff,
    mem_compl_singleton_iff] at p ⊢
  apply p.mp
  apply ((isOpen_extChartAt_target I x).eventually_mem (mem_extChartAt_target I x)).mp
  refine .of_forall fun y m h ↦ ?_
  contrapose h; simp only [not_not] at m h ⊢; nth_rw 2 [← h]
  rw [PartialEquiv.right_inv _ m]

/-- Variant of `mfderiv_comp` that doesn't use `∘` -/
theorem mfderiv_comp' {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {H : Type} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type}
    [TopologicalSpace M] [cs : ChartedSpace H M] {E' : Type} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {M' : Type} [TopologicalSpace M'] [cs' : ChartedSpace H' M'] {E'' : Type}
    [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type} [TopologicalSpace H'']
    {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type} [TopologicalSpace M'']
    [cs'' : ChartedSpace H'' M''] {f : M → M'} (x : M) {g : M' → M''}
    [sm : SmoothManifoldWithCorners I M] [sm' : SmoothManifoldWithCorners I' M']
    [sm'' : SmoothManifoldWithCorners I'' M'']
    (hg : MDifferentiableAt I' I'' g (f x)) (hf : MDifferentiableAt I I' f x) :
    mfderiv I I'' (fun x ↦ g (f x)) x = (mfderiv I' I'' g (f x)).comp (mfderiv I I' f x) := by
  apply mfderiv_comp; repeat assumption
