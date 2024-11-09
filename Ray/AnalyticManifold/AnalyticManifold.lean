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
import Ray.Analytic.Within
import Ray.AnalyticManifold.SmoothManifoldWithCorners

/-!
## Analytic manifolds

We define `AnalyticManifold`s over any complete, nontrivially normed field `𝕜`, as
charted spaces where all charts conversions are locally analytic.  We consider only
the boundaryless case for simplicity, though the `analyticGroupoid` is defined in the
boundary case too so this is a future generalization.  We then define the analogs to
`Smooth` for the analytic case:

1. `MAnalyticAt I J f x` means `f` is locally analytic at `x`
2. `MAnalyticOn I J f s` means `f` is locally analytic at each `x ∈ s`
3. `MAnalytic I J f` means `f` is analytic everywhere in the manifold

Possibly these should be renamed to `MAnalytic...`, though that name sounds bad.

Other things we show:

1. `extChartAt` and `.symm` are analytic with invertible derivatives
2. Arithmetic on analytic functions into `ℂ` are analytic
3. MAnalytic functions are differentiable, smooth, etc.
4. A variety of other small things
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

/-- Normed spaces are analytic manifolds over themselves -/
instance AnalyticManifold.self_of_nhds {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] : AnalyticManifold (modelWithCornersSelf 𝕜 E) E :=
  AnalyticManifold.mk

/-- Version of `ModelWithCorners.prod_apply` with `x ∈ H × H'` rather than `ModelProd H H'`.  This
comes up because other simplification doesn't stay in `ModelProd`. -/
@[simp]
lemma ModelWithCorners.prod_apply' {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (x : H × H') :
    (I.prod I') x = (I x.1, I' x.2) :=
  ModelWithCorners.prod_apply _ _ _

/-- Charts are analytic w.r.t. themselves.
    This lemma helps when proving particular spaces are analytic manifolds. -/
theorem extChartAt_self_analytic {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {M : Type} [TopologicalSpace M] (f : PartialHomeomorph M E) :
    AnalyticOnNhd 𝕜 (𝓘(𝕜, E) ∘ (f.symm.trans f) ∘ ⇑𝓘(𝕜, E).symm)
      (𝓘(𝕜, E) '' (f.symm.trans f).toPartialEquiv.source) := by
  apply AnalyticOnNhd.congr (f := fun z ↦ z)
  · simp only [modelWithCornersSelf_coe, id_eq, image_id', PartialHomeomorph.trans_toPartialEquiv,
      PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source, PartialEquiv.symm_source,
      PartialHomeomorph.coe_coe_symm]
    exact f.isOpen_inter_preimage_symm f.open_source
  · exact analyticOnNhd_id
  · intro x m
    simp only [modelWithCornersSelf_coe, id, image_id', PartialHomeomorph.trans_toPartialEquiv,
      PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source, PartialEquiv.symm_source,
      PartialHomeomorph.coe_coe_symm, mem_inter_iff, mem_preimage, Function.comp,
      modelWithCornersSelf_coe_symm, PartialHomeomorph.coe_trans] at m ⊢
    rw [f.right_inv m.1]

variable {E A : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F B : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G C : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H D : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
variable [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
variable {M : Type} {I : ModelWithCorners 𝕜 E A} [TopologicalSpace M]
variable {N : Type} {J : ModelWithCorners 𝕜 F B} [TopologicalSpace N]
variable {O : Type} {K : ModelWithCorners 𝕜 G C} [TopologicalSpace O]
variable {P : Type} {L : ModelWithCorners 𝕜 H D} [TopologicalSpace P]
variable [ChartedSpace A M] [ChartedSpace B N] [ChartedSpace C O] [ChartedSpace D P]

/-- MAnalytic at a point -/
def MAnalyticAt (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    (f : M → N) (x : M) :=
  ContinuousAt f x ∧
    AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x)

/-- MAnalytic on a set -/
def MAnalyticOn (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    (f : M → N) (s : Set M) :=
  ∀ x, x ∈ s → MAnalyticAt I J f x

/-- MAnalytic everywhere -/
def MAnalytic (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    (f : M → N) :=
  ∀ x, MAnalyticAt I J f x

/-- `MAnalyticOn` is monotonic in the set -/
theorem MAnalyticOn.mono {f : M → N} {s t : Set M} (fa : MAnalyticOn I J f s) (ts : t ⊆ s) :
    MAnalyticOn I J f t := fun _ m ↦ fa _ (ts m)

/-- Functions are `MAnalyticAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff {f : M → N} {x : M} :
    MAnalyticAt I J f x ↔ ContinuousAt f x ∧
      AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
      (extChartAt I x x) := by
  rfl

/-- Functions are `MAnalyticAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff_of_boundaryless [I.Boundaryless] {f : M → N} {x : M} :
    MAnalyticAt I J f x ↔ ContinuousAt f x ∧
      AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  simp only [mAnalyticAt_iff, I.range_eq_univ, analyticWithinAt_univ]

/-- Functions are `MAnalytic` iff they are continuous and analytic in charts everywhere -/
theorem mAnalytic_iff {f : M → N} :
    MAnalytic I J f ↔ Continuous f ∧
      ∀ x : M, AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (range I) (extChartAt I x x) := by
  simp only [MAnalytic, mAnalyticAt_iff, continuous_iff_continuousAt]
  exact forall_and

/-- Functions are `MAnalytic` iff they are continuous and analytic in charts everywhere -/
theorem mAnalytic_iff_of_boundaryless [I.Boundaryless] {f : M → N} :
    MAnalytic I J f ↔ Continuous f ∧
      ∀ x : M, AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x x) := by
  simp only [mAnalytic_iff, I.range_eq_univ, analyticWithinAt_univ]

/-- MAnalytic functions are continuous -/
theorem MAnalyticAt.continuousAt {f : M → N} {x : M} (h : MAnalyticAt I J f x) :
    ContinuousAt f x := (mAnalyticAt_iff.mp h).1

/-- MAnalytic functions are continuous -/
theorem MAnalytic.continuous {f : M → N} (h : MAnalytic I J f) : Continuous f :=
  (mAnalytic_iff.mp h).1

/-- MAnalytic functions are continuous (explicit `I`, `J` version) -/
theorem MAnalyticAt.continuousAt' (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    [I.Boundaryless] [J.Boundaryless]
    {f : M → N} {x : M} (h : MAnalyticAt I J f x) :
    ContinuousAt f x := h.continuousAt

/-- `MAnalyticOn` functions are `ContinuousOn` -/
theorem MAnalyticOn.continuousOn {f : M → N} {s : Set M} (h : MAnalyticOn I J f s) :
    ContinuousOn f s := fun x m ↦ (h x m).continuousAt.continuousWithinAt

/-- Constants are analytic -/
theorem mAnalyticAt_const {x : M} {c : N} : MAnalyticAt I J (fun _ ↦ c) x := by
  rw [mAnalyticAt_iff]; use continuousAt_const
  simp only [Prod.fst_comp_mk, Function.comp_def]
  exact analyticAt_const.analyticWithinAt

/-- Constants are analytic -/
theorem mAnalytic_const {c : N} : MAnalytic I J fun _ : M ↦ c := fun _ ↦ mAnalyticAt_const

/-- `fst` is analytic -/
theorem mAnalyticAt_fst [I.Boundaryless] [J.Boundaryless] {x : M × N} :
    MAnalyticAt (I.prod J) I (fun p : M × N ↦ p.fst) x := by
  rw [mAnalyticAt_iff]
  use continuousAt_fst
  refine (analyticAt_fst.congr ?_).analyticWithinAt
  filter_upwards [((isOpen_extChartAt_target x).eventually_mem (mem_extChartAt_target _))]
  intro y m
  rw [extChartAt_prod] at m
  simp only [PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_target, mem_prod] at m
  simp only [extChartAt_prod, Function.comp, PartialEquiv.prod_coe_symm]
  exact ((extChartAt I x.1).right_inv m.1).symm

/-- `snd` is analytic -/
theorem mAnalyticAt_snd [I.Boundaryless] [J.Boundaryless] {x : M × N} :
    MAnalyticAt (I.prod J) J (fun p : M × N ↦ p.snd) x := by
  rw [mAnalyticAt_iff]
  use continuousAt_snd
  refine (analyticAt_snd.congr ?_).analyticWithinAt
  filter_upwards [((isOpen_extChartAt_target x).eventually_mem (mem_extChartAt_target _))]
  intro y m
  rw [extChartAt_prod] at m
  simp only [PartialHomeomorph.prod_toPartialEquiv, PartialEquiv.prod_target, mem_prod] at m
  simp only [extChartAt_prod, Function.comp, PartialEquiv.prod_coe_symm]
  exact ((extChartAt J x.2).right_inv m.2).symm

/-- `fst` is analytic -/
theorem mAnalytic_fst [I.Boundaryless] [J.Boundaryless] :
    MAnalytic (I.prod J) I fun p : M × N ↦ p.fst := fun _ ↦ mAnalyticAt_fst

/-- `snd` is analytic -/
theorem mAnalytic_snd [I.Boundaryless] [J.Boundaryless] :
    MAnalytic (I.prod J) J fun p : M × N ↦ p.snd := fun _ ↦ mAnalyticAt_snd

/-- `I.toPartialEquiv = I` in terms of `coe` -/
lemma ModelWithCorners.coe_coe (I : ModelWithCorners 𝕜 E A) :
    ⇑I.toPartialEquiv = (I : A → E) := rfl

/-- `I.toPartialEquiv.symm = I.symm` in terms of `coe` -/
theorem ModelWithCorners.coe_coe_symm (I : ModelWithCorners 𝕜 E A) :
    ⇑I.toPartialEquiv.symm = (I.symm : E → A) := rfl

/-- `extChartAt` is analytic (boundary or not) -/
lemma MAnalyticAt.extChartAt [CompleteSpace E] [cm : AnalyticManifold I M]
    {x y : M} (ys : y ∈ (extChartAt I x).source) :
    MAnalyticAt I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y := by
  rw [mAnalyticAt_iff]
  use continuousAt_extChartAt' ys
  simp only [Function.comp, mfld_simps]
  have a : (chartAt A x).symm ≫ₕ chartAt A y ∈ analyticGroupoid I := by
    apply StructureGroupoid.compatible_of_mem_maximalAtlas
    exact (@StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid x)
    exact (@StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid y)
  simp only [mem_analyticGroupoid, PartialHomeomorph.trans_symm_eq_symm_trans_symm,
    Function.comp, PartialHomeomorph.trans_apply, PartialHomeomorph.symm_symm] at a
  refine (a.2 _ ?_).congr_set ?_
  · simpa only [mfld_simps, extChartAt] using ys
  · clear a
    simp only [mfld_simps] at ys
    simp only [PartialHomeomorph.trans_toPartialEquiv, PartialHomeomorph.symm_toPartialEquiv,
      PartialEquiv.trans_target, PartialHomeomorph.coe_coe_symm, PartialEquiv.symm_target]
    nth_rw 2 [← univ_inter (range I)]
    rw [eventuallyEq_inter, Filter.EventuallyEq, ← I.map_nhds_eq, Filter.eventually_map]
    simp only [preimage_inter, mem_inter_iff, mem_preimage, ModelWithCorners.left_inv, mem_univ,
      eq_iff_iff, iff_true, Filter.eventually_and, Filter.eventually_mem_set, chart_target_mem_nhds,
      true_and]
    rw [← PartialHomeomorph.map_nhds_eq _ (mem_chart_source _ _), Filter.eventually_map]
    filter_upwards [(chartAt A x).open_source.eventually_mem ys,
      (chartAt A y).open_source.eventually_mem (mem_chart_source _ _)]
    intro z zx zy
    simpa only [PartialHomeomorph.left_inv _ zy]

/-- `I` preserves `𝓝` if it is boundaryless -/
lemma ModelWithCorners.map_nhds_eq_of_boundaryless [I.Boundaryless] {x : A} :
    (𝓝 x).map I = 𝓝 (I x) := by
  simp only [I.map_nhds_eq, I.range_eq_univ, nhdsWithin_univ]

/-- `extChartAt.symm` is analytic if we're boundaryless -/
theorem MAnalyticAt.extChartAt_symm [CompleteSpace E] [I.Boundaryless] [cm : AnalyticManifold I M]
    {x : M} {y : E} (ys : y ∈ (_root_.extChartAt I x).target) :
    MAnalyticAt (modelWithCornersSelf 𝕜 E) I (_root_.extChartAt I x).symm y := by
  rw [mAnalyticAt_iff]
  use continuousAt_extChartAt_symm'' ys
  simp only [Function.comp, mfld_simps]
  set y' := (chartAt A x).symm (I.symm y)
  have a : (chartAt A x).symm ≫ₕ chartAt A ((chartAt A x).symm (I.symm y)) ∈
      analyticGroupoid I := by
    apply StructureGroupoid.compatible_of_mem_maximalAtlas
    exact @StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid x
    exact @StructureGroupoid.chart_mem_maximalAtlas _ _ _ _ _ (analyticGroupoid I)
      cm.toHasGroupoid y'
  simp only [mem_analyticGroupoid, PartialHomeomorph.trans_symm_eq_symm_trans_symm,
    Function.comp] at a
  refine (a.1 _ ?_).congr_set ?_
  · simpa only [mfld_simps, extChartAt, And.comm] using ys
  · clear a
    simp only [mfld_simps] at ys
    obtain ⟨z, zy⟩ := ys.1
    simp only [← zy, mem_range, exists_apply_eq_apply, I.left_inv, true_and] at ys
    simp only [mfld_simps, Filter.EventuallyEq, eq_iff_iff, iff_true, I.range_eq_univ, ← zy,
      ← I.map_nhds_eq_of_boundaryless, Filter.eventually_map, Filter.eventually_and,
      Filter.eventually_mem_set, (chartAt A x).open_target.mem_nhds ys]
    refine (Filter.eventually_map (m := (chartAt A x).symm)).mp ?_
    rw [PartialHomeomorph.map_nhds_eq]
    · exact (_root_.chartAt _ _).open_source.eventually_mem (ChartedSpace.mem_chart_source _)
    · simpa only [PartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source]

/-- Analytic functions are smooth -/
theorem MAnalyticAt.smoothAt [CompleteSpace F] {f : M → N} {x : M} (fa : MAnalyticAt I J f x) :
    SmoothAt I J f x := by
  rw [mAnalyticAt_iff] at fa
  simp only [SmoothAt, contMDiffAt_iff]
  exact ⟨fa.1, fa.2.contDiffWithinAt⟩

/-- Analytic functions are smooth -/
theorem MAnalyticOn.smoothOn [CompleteSpace F] {f : M → N} {s : Set M}
    (fa : MAnalyticOn I J f s) : SmoothOn I J f s :=
  fun x m ↦ (fa x m).smoothAt.smoothWithinAt

/-- Analytic functions are differentiable -/
theorem MAnalyticAt.mdifferentiableAt [CompleteSpace F] {f : M → N} {x : M}
    (fa : MAnalyticAt I J f x) : MDifferentiableAt I J f x :=
  fa.smoothAt.mdifferentiableAt

/-- `MAnalyticAt` depends only on local values -/
theorem MAnalyticAt.congr [CompleteSpace F] {f g : M → N} {x : M} (fa : MAnalyticAt I J f x)
    (e : f =ᶠ[𝓝 x] g) : MAnalyticAt I J g x := by
  rw [mAnalyticAt_iff] at fa ⊢
  use fa.1.congr e
  apply fa.2.congr_of_eventuallyEq
  · rw [e.self_of_nhds]
    refine Filter.EventuallyEq.fun_comp ?_ (_root_.extChartAt J (g x))
    have t := (continuousAt_extChartAt_symm (I := I) x).tendsto
    rw [PartialEquiv.left_inv _ (mem_extChartAt_source x)] at t
    exact (e.comp_tendsto (t.mono_left nhdsWithin_le_nhds)).symm
  · simp only [e.self_of_nhds, Function.comp, PartialEquiv.left_inv _ (mem_extChartAt_source _)]

/-- `MAnalyticAt` for `x ↦ (f x, g x)` -/
theorem MAnalyticAt.prod {f : O → M} {g : O → N} {x : O}
    (fh : MAnalyticAt K I f x) (gh : MAnalyticAt K J g x) :
    MAnalyticAt K (I.prod J) (fun x ↦ (f x, g x)) x := by
  rw [mAnalyticAt_iff] at fh gh ⊢; use fh.1.prod gh.1
  refine (fh.2.prod gh.2).congr_of_eventuallyEq ?_ ?_
  simp only [eventuallyEq_nhdsWithin_iff]
  refine .of_forall fun y _ ↦ ?_
  simp only [extChartAt_prod, Function.comp, PartialEquiv.prod_coe]
  simp only [mfld_simps]

/-- `MAnalytic` for `x ↦ (f x, g x)` -/
theorem MAnalytic.prod {f : O → M} {g : O → N} (fh : MAnalytic K I f) (gh : MAnalytic K J g) :
    MAnalytic K (I.prod J) fun x ↦ (f x, g x) := fun x ↦ (fh x).prod (gh x)

/-- `id` is analytic -/
theorem mAnalyticAt_id {x : M} : MAnalyticAt I I (fun x ↦ x) x := by
  rw [mAnalyticAt_iff]
  use continuousAt_id
  refine analyticAt_id.analyticWithinAt.congr_of_eventuallyEq ?_ ?_
  · simp only [mfld_simps, Filter.EventuallyEq, id, ← I.map_nhds_eq, Filter.eventually_map]
    filter_upwards [(chartAt A x).open_target.eventually_mem (mem_chart_target _ _)]
    intro y m
    simp only [(chartAt A x).right_inv m]
  · simp only [mfld_simps]

/-- `id` is analytic -/
theorem mAnalytic_id : MAnalytic I I fun x : M ↦ x :=
  fun _ ↦ mAnalyticAt_id

/-- MAnalytic functions compose -/
theorem MAnalyticAt.comp {f : N → M} {g : O → N} {x : O}
    (fh : MAnalyticAt J I f (g x)) (gh : MAnalyticAt K J g x) :
    MAnalyticAt K I (fun x ↦ f (g x)) x := by
  rw [mAnalyticAt_iff] at fh gh ⊢
  use fh.1.comp gh.1
  have e : _root_.extChartAt J (g x) (g x) = (_root_.extChartAt J (g x) ∘ g ∘
      (_root_.extChartAt K x).symm) (_root_.extChartAt K x x) := by
    simp only [Function.comp_apply, PartialEquiv.left_inv _ (mem_extChartAt_source x)]
  rw [e] at fh
  clear e
  refine (fh.2.comp gh.2 ?_).congr_of_eventuallyEq ?_ ?_
  · intro _ _
    simp only [mfld_simps]
  · simp only [Function.comp, eventuallyEq_nhdsWithin_iff]
    have m : ∀ᶠ y in 𝓝 (_root_.extChartAt K x x), g ((_root_.extChartAt K x).symm y) ∈
        (_root_.extChartAt J (g x)).source := by
      apply ContinuousAt.eventually_mem
      · apply ContinuousAt.comp
        · rw [PartialEquiv.left_inv _ (mem_extChartAt_source _)]; exact gh.1
        · exact continuousAt_extChartAt_symm x
      · rw [PartialEquiv.left_inv _ (mem_extChartAt_source _)]
        exact extChartAt_source_mem_nhds _
    refine m.mp (.of_forall fun y m _ ↦ ?_)
    simp only [PartialEquiv.left_inv _ m]
  · simp only [mfld_simps]

/-- MAnalytic functions compose -/
theorem MAnalytic.comp {f : N → M} {g : O → N} (fh : MAnalytic J I f)
    (gh : MAnalytic K J g) : MAnalytic K I fun x ↦ f (g x) :=
  fun _ ↦ (fh _).comp (gh _)

/-- MAnalytic functions compose at a point, with a separate argument for point equality -/
theorem MAnalyticAt.comp_of_eq {f : N → M} {g : O → N} {x : O} {y : N}
    (fh : MAnalyticAt J I f y) (gh : MAnalyticAt K J g x) (e : g x = y) :
    MAnalyticAt K I (fun x ↦ f (g x)) x := by
  rw [← e] at fh; exact fh.comp gh

/-- `MAnalyticAt.comp` for a function of two arguments -/
theorem MAnalyticAt.comp₂ [CompleteSpace H] {h : N × M → P} {f : O → N}
    {g : O → M} {x : O}
    (ha : MAnalyticAt (J.prod I) L h (f x, g x)) (fa : MAnalyticAt K J f x)
    (ga : MAnalyticAt K I g x) : MAnalyticAt K L (fun x ↦ h (f x, g x)) x :=
  ha.comp (g := fun x ↦ (f x, g x)) (fa.prod ga)

/-- `MAnalyticAt.comp₂`, with a separate argument for point equality -/
theorem MAnalyticAt.comp₂_of_eq [CompleteSpace H] {h : N × M → P} {f : O → N}
    {g : O → M} {x : O} {y : N × M} (ha : MAnalyticAt (J.prod I) L h y) (fa : MAnalyticAt K J f x)
    (ga : MAnalyticAt K I g x) (e : (f x, g x) = y) :
    MAnalyticAt K L (fun x ↦ h (f x, g x)) x := by
  rw [← e] at ha
  exact ha.comp₂ fa ga

section Iff

variable (I J)

/-- Analytic functions are analytic, and vice versa -/
theorem analyticAt_iff_mAnalyticAt [I.Boundaryless] [ChartedSpace A E] [AnalyticManifold I E]
    [ChartedSpace B F] [AnalyticManifold J F] [ExtChartEqRefl I] [ExtChartEqRefl J]
    {f : E → F} {x : E} : AnalyticAt 𝕜 f x ↔ MAnalyticAt I J f x := by
  simp only [mAnalyticAt_iff_of_boundaryless, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq, iff_and_self]
  exact AnalyticAt.continuousAt

end Iff

/-- Analytic functions are analytic -/
theorem AnalyticAt.mAnalyticAt {f : E → F} {x : E} (fa : AnalyticAt 𝕜 f x)
    (I : ModelWithCorners 𝕜 E A) [ChartedSpace A E] [AnalyticManifold I E] [ExtChartEqRefl I]
    (J : ModelWithCorners 𝕜 F B) [ChartedSpace B F] [AnalyticManifold J F] [ExtChartEqRefl J] :
    MAnalyticAt I J f x := by
  simp only [mAnalyticAt_iff, fa.continuousAt, true_and, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq]
  exact fa.analyticWithinAt

/-- MAnalytic functions are analytic -/
theorem MAnalyticAt.analyticAt (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] [ChartedSpace A E]
    [AnalyticManifold I E] [ExtChartEqRefl I] (J : ModelWithCorners 𝕜 F B) [ChartedSpace B F]
    [AnalyticManifold J F] [ExtChartEqRefl J] {f : E → F} {x : E} :
    MAnalyticAt I J f x → AnalyticAt 𝕜 f x :=
  (analyticAt_iff_mAnalyticAt _ _).mpr

/-- Curried analytic functions are analytic in the first coordinate -/
theorem MAnalyticAt.along_fst [CompleteSpace G] [CompleteSpace H] [AnalyticManifold I M]
    {f : M → O → P} {x : M} {y : O} (fa : MAnalyticAt (I.prod K) L (uncurry f) (x, y)) :
    MAnalyticAt I L (fun x ↦ f x y) x :=
  MAnalyticAt.comp₂ fa mAnalyticAt_id mAnalyticAt_const

/-- Curried analytic functions are analytic in the second coordinate -/
theorem MAnalyticAt.along_snd [CompleteSpace G] [AnalyticManifold I M]
    [AnalyticManifold J N] {f : M → N → O} {x : M} {y : N}
    (fa : MAnalyticAt (I.prod J) K (uncurry f) (x, y)) : MAnalyticAt J K (fun y ↦ f x y) y :=
  MAnalyticAt.comp₂ fa mAnalyticAt_const mAnalyticAt_id

/-- Curried analytic functions are analytic in the first coordinate -/
theorem MAnalytic.along_fst [CompleteSpace G] [CompleteSpace H] [AnalyticManifold I M]
    {f : M → O → P} (fa : MAnalytic (I.prod K) L (uncurry f)) {y : O} :
    MAnalytic I L fun x ↦ f x y :=
  fun _ ↦ (fa _).along_fst

/-- Curried analytic functions are analytic in the second coordinate -/
theorem MAnalytic.along_snd [CompleteSpace G] [AnalyticManifold I M]
    [AnalyticManifold J N] {f : M → N → O} {x : M} (fa : MAnalytic (I.prod J) K (uncurry f)) :
    MAnalytic J K fun y ↦ f x y :=
  fun _ ↦ (fa _).along_snd

/-- Addition is analytic -/
theorem MAnalyticAt.add [CompleteSpace G] {f g : O → F} {x : O}
    (fa : MAnalyticAt K (modelWithCornersSelf 𝕜 F) f x)
    (ga : MAnalyticAt K (modelWithCornersSelf 𝕜 F) g x) :
    MAnalyticAt K (modelWithCornersSelf 𝕜 F) (fun x ↦ f x + g x) x := by
  have e : (fun x ↦ f x + g x) = (fun p : F × F ↦ p.1 + p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  exact ((analyticAt_fst.add analyticAt_snd).mAnalyticAt _ _).comp (fa.prod ga)

/-- Subtraction is analytic -/
theorem MAnalyticAt.sub [CompleteSpace G] {f g : O → F} {x : O}
    (fa : MAnalyticAt K (modelWithCornersSelf 𝕜 F) f x)
    (ga : MAnalyticAt K (modelWithCornersSelf 𝕜 F) g x) :
    MAnalyticAt K (modelWithCornersSelf 𝕜 F) (fun x ↦ f x - g x) x :=
  ((analyticAt_fst.sub analyticAt_snd).mAnalyticAt _ _).comp (fa.prod ga)

/-- Multiplication is analytic -/
theorem MAnalyticAt.mul [CompleteSpace 𝕜] [CompleteSpace G] {f g : O → 𝕜} {x : O}
    (fa : MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) f x)
    (ga : MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) g x) :
    MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x * g x) x :=
  ((analyticAt_fst.mul analyticAt_snd).mAnalyticAt _ _).comp (fa.prod ga)

/-- Inverse is analytic away from zeros -/
theorem MAnalyticAt.inv [CompleteSpace 𝕜] [CompleteSpace G] {f : O → 𝕜} {x : O}
    (fa : MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) f x) (f0 : f x ≠ 0) :
    MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ (f x)⁻¹) x :=
  ((analyticAt_id.inv f0).mAnalyticAt _ _).comp fa

/-- Division is analytic away from denominator zeros -/
theorem MAnalyticAt.div [CompleteSpace 𝕜] [CompleteSpace G] {f g : O → 𝕜} {x : O}
    (fa : MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) f x)
    (ga : MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) g x) (g0 : g x ≠ 0) :
    MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x / g x) x := by
  simp only [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- Powers are analytic -/
theorem MAnalyticAt.pow [CompleteSpace 𝕜] [CompleteSpace G] {f : O → 𝕜} {x : O}
    (fa : MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) f x) {n : ℕ} :
    MAnalyticAt K (modelWithCornersSelf 𝕜 𝕜) (fun x ↦ f x ^ n) x := by
  have e : (fun x ↦ f x ^ n) = (fun z : 𝕜 ↦ z ^ n) ∘ f := rfl
  rw [e]; exact ((analyticAt_id.pow _).mAnalyticAt _ _).comp fa

/-- Complex powers `f x ^ g x` are analytic if `f x` avoids the negative real axis  -/
theorem MAnalyticAt.cpow {E A M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [TopologicalSpace A] {I : ModelWithCorners ℂ E A} [TopologicalSpace M] [ChartedSpace A M]
    {f g : M → ℂ} {x : M}
    (fa : MAnalyticAt I (modelWithCornersSelf ℂ ℂ) f x)
    (ga : MAnalyticAt I (modelWithCornersSelf ℂ ℂ) g x) (a : 0 < (f x).re ∨ (f x).im ≠ 0) :
    MAnalyticAt I (modelWithCornersSelf ℂ ℂ) (fun x ↦ f x ^ g x) x := by
  have e : (fun x ↦ f x ^ g x) = (fun p : ℂ × ℂ ↦ p.1 ^ p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  refine ((analyticAt_fst.cpow analyticAt_snd ?_).mAnalyticAt _ _).comp (fa.prod ga)
  exact a

/-- Iterated analytic functions are analytic -/
theorem MAnalytic.iter {f : M → M} (fa : MAnalytic I I f) (n : ℕ) : MAnalytic I I f^[n] := by
  induction' n with n h; simp only [Function.iterate_zero]; exact mAnalytic_id
  simp only [Function.iterate_succ']; exact fa.comp h

/-- If we're analytic at a point, we're locally analytic.
This is true even with boundary, but for now we prove only the `Boundaryless` case. -/
theorem MAnalyticAt.eventually [I.Boundaryless] [J.Boundaryless] [CompleteSpace E] [CompleteSpace F]
    [AnalyticManifold I M] [AnalyticManifold J N] {f : M → N} {x : M} (fa : MAnalyticAt I J f x) :
    ∀ᶠ y in 𝓝 x, MAnalyticAt I J f y := by
  have ea := (mAnalyticAt_iff_of_boundaryless.mp fa).2.eventually_analyticAt
  simp only [Function.comp, ← extChartAt_map_nhds', Filter.eventually_map] at ea
  filter_upwards [ea, (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source (f x)).mem_nhds
    (mem_extChartAt_source (I := J) (f x)))).eventually_nhds,
    (isOpen_extChartAt_source x).eventually_mem (mem_extChartAt_source (I := I) x)]
  intro y a fm m
  have h := a.mAnalyticAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 F)
  clear a
  have h' := (MAnalyticAt.extChartAt_symm (PartialEquiv.map_source _ fm.self_of_nhds)).comp_of_eq
      (h.comp (MAnalyticAt.extChartAt m)) ?_
  · apply h'.congr
    clear h h'
    apply ((isOpen_extChartAt_source x).eventually_mem m).mp
    refine fm.mp (.of_forall fun z mf m ↦ ?_)
    simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ mf, Function.comp_def]
  · simp only [Function.comp, PartialEquiv.left_inv _ m]

/-- The domain of analyticity is open -/
theorem isOpen_mAnalyticAt [I.Boundaryless] [J.Boundaryless] [CompleteSpace E] [CompleteSpace F]
    [AnalyticManifold I M] [AnalyticManifold J N] {f : M → N} :
    IsOpen {x | MAnalyticAt I J f x} := by
  rw [isOpen_iff_eventually]; intro x fa; exact fa.eventually

variable [CompleteSpace E] [CompleteSpace F]

/-- MAnalytic functions have continuous tangent maps.
    Obviously more is true and the tangent map is analytic, but I don't need that yet -/
theorem MAnalyticOn.continuousOn_tangentMap [I.Boundaryless] [J.Boundaryless] [AnalyticManifold I M]
    [AnalyticManifold J N] {f : M → N} {s : Set M} (fa : MAnalyticOn I J f s) :
    ContinuousOn (tangentMap I J f) (Bundle.TotalSpace.proj ⁻¹' s) := by
  generalize ht : {x | MAnalyticAt I J f x} = t
  have o : IsOpen t := by rw [← ht]; exact isOpen_mAnalyticAt
  have sub : s ⊆ t := by rw [← ht]; exact fa
  replace fa : MAnalyticOn I J f t := by
    simp only [MAnalyticOn, mem_setOf_eq, imp_self, implies_true, ← ht]
  refine ContinuousOn.mono ?_ (preimage_mono sub)
  apply (fa.smoothOn.contMDiffOn.continuousOn_tangentMapWithin le_top o.uniqueMDiffOn).congr
  intro x m; simp only [mem_preimage] at m
  rw [tangentMapWithin_eq_tangentMap (o.uniqueMDiffOn _ m) (fa _ m).mdifferentiableAt]
