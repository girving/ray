import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Ray.Analytic.Within
import Ray.Manifold.ManifoldUpstream

/-!
## Facts about analytic manifolds

This file used to define `AnalyticManifold`, but now `IsManifold I ω M` handles that natively!
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped ContDiff Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

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

-- begin #28286

/-- Functions are `ContMDiffAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff {f : M → N} {x : M} [CompleteSpace F] :
    ContMDiffAt I J ω f x ↔ ContinuousAt f x ∧
      AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (range I)
      (extChartAt I x x) := by
  rw [contMDiffAt_iff, contDiffWithinAt_omega_iff_analyticWithinAt]

/-- Functions are `ContMDiffAt` iff they are continuous and analytic in charts -/
theorem mAnalyticAt_iff_of_boundaryless [I.Boundaryless] [CompleteSpace F] {f : M → N} {x : M} :
    ContMDiffAt I J ω f x ↔ ContinuousAt f x ∧
      AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  simp only [mAnalyticAt_iff, I.range_eq_univ, analyticWithinAt_univ]

/-- Functions are `ContMDiff` iff they are continuous and analytic in charts everywhere -/
theorem mAnalytic_iff {f : M → N} [CompleteSpace F] [IsManifold I ω M] [IsManifold J ω N] :
    ContMDiff I J ω f ↔ Continuous f ∧
      ∀ x : M, AnalyticWithinAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (range I) (extChartAt I x x) := by
  simp only [ContMDiff, contMDiffAt_iff, continuous_iff_continuousAt,
    contDiffWithinAt_omega_iff_analyticWithinAt]
  aesop

/-- Functions are `ContMDiff` iff they are continuous and analytic in charts everywhere -/
theorem mAnalytic_iff_of_boundaryless [I.Boundaryless] [IsManifold I ω M] [IsManifold J ω N]
    [CompleteSpace F] {f : M → N} :
    ContMDiff I J ω f ↔ Continuous f ∧
      ∀ x : M, AnalyticAt 𝕜 (extChartAt J (f x) ∘ f ∘ (extChartAt I x).symm)
        (extChartAt I x x) := by
  simp only [mAnalytic_iff, I.range_eq_univ, analyticWithinAt_univ]

-- end #28286

/- /-- ContMDiff functions are continuous (explicit `I`, `J` version) -/
theorem ContMDiffAt.continuousAt' (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    {M N : Type} [TopologicalSpace M] [ChartedSpace A M] [TopologicalSpace N] [ChartedSpace B N]
    [I.Boundaryless] [J.Boundaryless] [CompleteSpace F]
    {f : M → N} {x : M} (h : ContMDiffAt I J ω f x) :
    ContinuousAt f x := h.continuousAt -/

/- /-- `I.toPartialEquiv = I` in terms of `coe` -/
lemma ModelWithCorners.coe_coe (I : ModelWithCorners 𝕜 E A) :
    ⇑I.toPartialEquiv = (I : A → E) := rfl

/-- `I.toPartialEquiv.symm = I.symm` in terms of `coe` -/
theorem ModelWithCorners.coe_coe_symm (I : ModelWithCorners 𝕜 E A) :
    ⇑I.toPartialEquiv.symm = (I.symm : E → A) := rfl -/

/- /-- `extChartAt` is analytic (boundary or not) -/
lemma ContMDiffAt.extChartAt [CompleteSpace E] [cm : IsManifold I ⊤ M]
    {x y : M} (ys : y ∈ (extChartAt I x).source) :
    ContMDiffAt I 𝓘(𝕜, E) ω (extChartAt I x) y := by
  refine contMDiffOn_extChartAt.contMDiffAt ?_

  -- simp only [extChartAt_source] at ys
  -- exact contMDiffAt_extChartAt' ys -/

/- /-- `I` preserves `𝓝` if it is boundaryless -/
lemma ModelWithCorners.map_nhds_eq_of_boundaryless [I.Boundaryless] {x : A} :
    (𝓝 x).map I = 𝓝 (I x) := by
  simp only [I.map_nhds_eq, I.range_eq_univ, nhdsWithin_univ] -/

/-- `extChartAt.symm` is analytic if we're boundaryless -/
theorem ContMDiffAt.extChartAt_symm [CompleteSpace E] [I.Boundaryless] [cm : IsManifold I ω M]
    {x : M} {y : E} (ys : y ∈ (_root_.extChartAt I x).target) :
    ContMDiffAt 𝓘(𝕜, E) I ω (_root_.extChartAt I x).symm y := by
  suffices h : ContMDiffWithinAt 𝓘(𝕜, E) I ω (_root_.extChartAt I x).symm (range I) y by
    simp only [mfld_simps, mAnalyticAt_iff, contMDiffWithinAt_iff, I.range_eq_univ,
      contDiffWithinAt_univ, analyticWithinAt_univ, continuousWithinAt_univ] at h ⊢
    exact ⟨h.1, h.2.analyticAt⟩
  exact contMDiffWithinAt_extChartAt_symm_range x ys

/- /-- `ContMDiffAt` depends only on local values -/
theorem ContMDiffAt.congr [CompleteSpace F] {f g : M → N} {x : M} (fa : ContMDiffAt I J ω f x)
    (e : f =ᶠ[𝓝 x] g) : ContMDiffAt I J ω g x :=
  ContMDiffAt.congr_of_eventuallyEq fa (id (Filter.EventuallyEq.symm e)) -/

-- begin #28292

/-- `ContMDiffAt.comp` for a function of two arguments -/
theorem ContMDiffAt.comp₂ [IsManifold I ω M] [IsManifold J ω N] [IsManifold K ω O]
    [IsManifold L ω P] {h : N × M → P} {f : O → N} {g : O → M} {x : O}
    (ha : ContMDiffAt (J.prod I) L ω h (f x, g x)) (fa : ContMDiffAt K J ω f x)
    (ga : ContMDiffAt K I ω g x) : ContMDiffAt K L ω (fun x ↦ h (f x, g x)) x :=
  ha.comp (f := fun x ↦ (f x, g x)) _ (fa.prodMk ga)

/-- `ContMDiffAt.comp₂`, with a separate argument for point equality -/
theorem ContMDiffAt.comp₂_of_eq [IsManifold I ω M] [IsManifold J ω N] [IsManifold K ω O]
    [IsManifold L ω P] {h : N × M → P} {f : O → N} {g : O → M} {x : O} {y : N × M}
    (ha : ContMDiffAt (J.prod I) L ω h y) (fa : ContMDiffAt K J ω f x)
    (ga : ContMDiffAt K I ω g x) (e : (f x, g x) = y) :
    ContMDiffAt K L ω (fun x ↦ h (f x, g x)) x := by
  rw [← e] at ha
  exact ha.comp₂ fa ga

-- end #28292

section Iff

variable (I J)

/-- Analytic functions are analytic, and vice versa -/
theorem analyticAt_iff_mAnalyticAt [I.Boundaryless] [ChartedSpace A E] [IsManifold I ω E]
    [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl I] [ExtChartEqRefl J] [CompleteSpace F]
    {f : E → F} {x : E} : AnalyticAt 𝕜 f x ↔ ContMDiffAt I J ω f x := by
  simp only [mAnalyticAt_iff_of_boundaryless, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq, iff_and_self]
  exact AnalyticAt.continuousAt

end Iff

/-- Analytic functions are analytic -/
theorem AnalyticAt.mAnalyticAt {f : E → F} {x : E} (fa : AnalyticAt 𝕜 f x) [CompleteSpace F]
    (I : ModelWithCorners 𝕜 E A) [ChartedSpace A E] [IsManifold I ω E] [ExtChartEqRefl I]
    (J : ModelWithCorners 𝕜 F B) [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl J] :
    ContMDiffAt I J ω f x := by
  simp only [mAnalyticAt_iff, fa.continuousAt, true_and, extChartAt_eq_refl, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, Function.id_comp, Function.comp_id, id_eq]
  exact fa.analyticWithinAt

/-- ContMDiff functions are analytic -/
theorem ContMDiffAt.analyticAt [CompleteSpace F] (I : ModelWithCorners 𝕜 E A) [I.Boundaryless]
    [ChartedSpace A E] [IsManifold I ω E] [ExtChartEqRefl I] (J : ModelWithCorners 𝕜 F B)
    [ChartedSpace B F] [IsManifold J ω F] [ExtChartEqRefl J] {f : E → F} {x : E} :
    ContMDiffAt I J ω f x → AnalyticAt 𝕜 f x :=
  (analyticAt_iff_mAnalyticAt _ _).mpr

-- begin #28292

/-- Curried analytic functions are analytic in the first coordinate -/
theorem ContMDiffAt.along_fst [CompleteSpace G] [CompleteSpace H] [IsManifold I ω M]
    [IsManifold K ω O] [IsManifold L ω P]
    {f : M → O → P} {x : M} {y : O} (fa : ContMDiffAt (I.prod K) L ω (uncurry f) (x, y)) :
    ContMDiffAt I L ω (fun x ↦ f x y) x :=
  fa.comp₂ contMDiffAt_id contMDiffAt_const

/-- Curried analytic functions are analytic in the second coordinate -/
theorem ContMDiffAt.along_snd [CompleteSpace G] [IsManifold I ω M] [IsManifold J ω N]
    [IsManifold K ω O] [CompleteSpace E] {f : M → N → O} {x : M} {y : N}
    (fa : ContMDiffAt (I.prod J) K ω (uncurry f) (x, y)) :
    ContMDiffAt J K ω (fun y ↦ f x y) y :=
  fa.comp₂ contMDiffAt_const contMDiffAt_id

/-- Curried analytic functions are analytic in the first coordinate -/
theorem ContMDiff.along_fst [CompleteSpace G] [CompleteSpace H] [IsManifold I ω M]
    [IsManifold K ω O] [IsManifold L ω P]
    {f : M → O → P} (fa : ContMDiff (I.prod K) L ω (uncurry f)) {y : O} :
    ContMDiff I L ω (fun x ↦ f x y) :=
  fun _ ↦ (fa _).along_fst

/-- Curried analytic functions are analytic in the second coordinate -/
theorem ContMDiff.along_snd [CompleteSpace G] [IsManifold I ω M] [IsManifold J ω N]
    [IsManifold K ω O] [CompleteSpace E] {f : M → N → O} {x : M}
    (fa : ContMDiff (I.prod J) K ω (uncurry f)) :
    ContMDiff J K ω (fun y ↦ f x y) :=
  fun _ ↦ (fa _).along_snd

-- end #28292

/-

/-- Addition is analytic -/
theorem ContMDiffAt.add [CompleteSpace F] [CompleteSpace G] [IsManifold K ω O] {f g : O → F} {x : O}
    (fa : ContMDiffAt K (𝓘(𝕜, F)) ω f x) (ga : ContMDiffAt K (𝓘(𝕜, F)) ω g x) :
    ContMDiffAt K (𝓘(𝕜, F)) ω (fun x ↦ f x + g x) x := by
  have e : (fun x ↦ f x + g x) = (fun p : F × F ↦ p.1 + p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  exact ((analyticAt_fst.add analyticAt_snd).mAnalyticAt _ _).comp _ (fa.prodMk ga)

/-- Subtraction is analytic -/
theorem ContMDiffAt.sub [CompleteSpace F] [CompleteSpace G] [IsManifold K ω O] {f g : O → F} {x : O}
    (fa : ContMDiffAt K (𝓘(𝕜, F)) ω f x) (ga : ContMDiffAt K (𝓘(𝕜, F)) ω g x) :
    ContMDiffAt K (𝓘(𝕜, F)) ω (fun x ↦ f x - g x) x :=
  ((analyticAt_fst.sub analyticAt_snd).mAnalyticAt _ _).comp _ (fa.prodMk ga)

/-- Multiplication is analytic -/
theorem ContMDiffAt.mul' [CompleteSpace 𝕜] [CompleteSpace G] [IsManifold K ω O] {f g : O → 𝕜} {x : O}
    (fa : ContMDiffAt K (𝓘(𝕜, 𝕜)) ω f x) (ga : ContMDiffAt K (𝓘(𝕜, 𝕜)) ω g x) :
    ContMDiffAt K (𝓘(𝕜, 𝕜)) ω (fun x ↦ f x * g x) x :=
  ((analyticAt_fst.mul analyticAt_snd).mAnalyticAt _ _).comp _ (fa.prodMk ga)

/-- Inverse is analytic away from zeros -/
theorem ContMDiffAt.inv [CompleteSpace 𝕜] [CompleteSpace G] [IsManifold K ω O] {f : O → 𝕜} {x : O}
    (fa : ContMDiffAt K (𝓘(𝕜, 𝕜)) ω f x) (f0 : f x ≠ 0) :
    ContMDiffAt K (𝓘(𝕜, 𝕜)) ω (fun x ↦ (f x)⁻¹) x :=
  ((analyticAt_id.inv f0).mAnalyticAt _ _).comp _ fa

/-- Division is analytic away from denominator zeros -/
theorem ContMDiffAt.div [CompleteSpace 𝕜] [CompleteSpace G] [IsManifold K ω O] {f g : O → 𝕜} {x : O}
    (fa : ContMDiffAt K (𝓘(𝕜, 𝕜)) ω f x) (ga : ContMDiffAt K (𝓘(𝕜, 𝕜)) ω g x) (g0 : g x ≠ 0) :
    ContMDiffAt K (𝓘(𝕜, 𝕜)) ω (fun x ↦ f x / g x) x := by
  simp only [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

-/

/-- Powers are analytic -/
theorem ContMDiffAt.pow [CompleteSpace 𝕜] [CompleteSpace G] [IsManifold K ω O] {f : O → 𝕜} {x : O}
    (fa : ContMDiffAt K (𝓘(𝕜, 𝕜)) ω f x) {n : ℕ} :
    ContMDiffAt K (𝓘(𝕜, 𝕜)) ω (fun x ↦ f x ^ n) x := by
  have e : (fun x ↦ f x ^ n) = (fun z : 𝕜 ↦ z ^ n) ∘ f := rfl
  rw [e]; exact ((analyticAt_id.pow _).mAnalyticAt _ _).comp _ fa

/-- Complex powers `f x ^ g x` are analytic if `f x` avoids the negative real axis  -/
theorem ContMDiffAt.cpow [NormedSpace ℂ E] [CompleteSpace E] {I : ModelWithCorners ℂ E A}
    [IsManifold I ω M] {f g : M → ℂ} {x : M} (fa : ContMDiffAt I (𝓘(ℂ, ℂ)) ω f x)
    (ga : ContMDiffAt I (𝓘(ℂ, ℂ)) ω g x) (a : 0 < (f x).re ∨ (f x).im ≠ 0) :
    ContMDiffAt I (𝓘(ℂ, ℂ)) ω (fun x ↦ f x ^ g x) x := by
  have e : (fun x ↦ f x ^ g x) = (fun p : ℂ × ℂ ↦ p.1 ^ p.2) ∘ fun x ↦ (f x, g x) := rfl
  rw [e]
  refine ((analyticAt_fst.cpow analyticAt_snd ?_).mAnalyticAt _ _).comp _ (fa.prodMk ga)
  exact a

/-- Iterated analytic functions are analytic -/
theorem ContMDiff.iter {f : M → M} (fa : ContMDiff I I ω f) (n : ℕ) :
    ContMDiff I I ω (f^[n]) := by
  induction' n with n h; simp only [Function.iterate_zero]; exact contMDiff_id
  simp only [Function.iterate_succ']; exact fa.comp h

/-- If we're analytic at a point, we're locally analytic.
This is true even with boundary, but for now we prove only the `Boundaryless` case. -/
theorem ContMDiffAt.eventually [I.Boundaryless] [J.Boundaryless] [CompleteSpace E] [CompleteSpace F]
    [IsManifold I ω M] [IsManifold J ω N] {f : M → N} {x : M} (fa : ContMDiffAt I J ω f x) :
    ∀ᶠ y in 𝓝 x, ContMDiffAt I J ω f y := by
  have ea := (mAnalyticAt_iff_of_boundaryless.mp fa).2.eventually_analyticAt
  simp only [← extChartAt_map_nhds', Filter.eventually_map] at ea
  filter_upwards [ea, (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source (f x)).mem_nhds
    (mem_extChartAt_source (I := J) (f x)))).eventually_nhds,
    (isOpen_extChartAt_source x).eventually_mem (mem_extChartAt_source (I := I) x)]
  intro y a fm m
  have h := a.mAnalyticAt (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 F)
  clear a
  have h' := (ContMDiffAt.extChartAt_symm (PartialEquiv.map_source _ fm.self_of_nhds)).comp_of_eq
      (h.comp _ (contMDiffAt_extChartAt' (extChartAt_source I x ▸ m))) ?_
  · apply h'.congr_of_eventuallyEq
    clear h h'
    apply ((isOpen_extChartAt_source x).eventually_mem m).mp
    refine fm.mp (.of_forall fun z mf m ↦ ?_)
    simp only [PartialEquiv.left_inv _ m, PartialEquiv.left_inv _ mf, Function.comp_def]
  · simp only [Function.comp, PartialEquiv.left_inv _ m]

/-- The domain of analyticity is open -/
theorem isOpen_mAnalyticAt [I.Boundaryless] [J.Boundaryless] [CompleteSpace E] [CompleteSpace F]
    [IsManifold I ω M] [IsManifold J ω N] {f : M → N} :
    IsOpen {x | ContMDiffAt I J ω f x} := by
  rw [isOpen_iff_eventually]; intro x fa; exact fa.eventually

/-- Analyticity in a neighborhood of a set (the manifold analogue of `AnalyticOnNhd`) -/
def ContMDiffOnNhd (I : ModelWithCorners 𝕜 E A) (J : ModelWithCorners 𝕜 F B)
    (f : M → N) (s : Set M) : Prop := ∀ x ∈ s, ContMDiffAt I J ω f x

/-- `ContMDiffOnNhd` restricts to subsets -/
lemma ContMDiffOnNhd.mono {f : M → N} {s t : Set M} (fa : ContMDiffOnNhd I J f s) (st : t ⊆ s) :
    ContMDiffOnNhd I J f t := fun x m ↦ fa x (st m)

/-- `ContMDiffOnNhd` extends `ContMDiffOn` -/
lemma ContMDiffOnNhd.contMDiffOn {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) :
    ContMDiffOn I J ω f s := fun x m ↦ (fa x m).contMDiffWithinAt

/-- `ContMDiffOnNhd` implies analyticity -/
lemma ContMDiffOnNhd.contMDiffAt {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) {x : M}
    (xs : x ∈ s) : ContMDiffAt I J ω f x := fa x xs

/-- `ContMDiffOnNhd` implies continuity -/
lemma ContMDiffOnNhd.continuousAt {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) {x : M}
    (xs : x ∈ s) : ContinuousAt f x := (fa x xs).continuousAt

/-- `ContMDiffOnNhd` implies continuity on the domain -/
lemma ContMDiffOnNhd.continuousOn {f : M → N} {s : Set M} (fa : ContMDiffOnNhd I J f s) :
    ContinuousOn f s := fun x m ↦ (fa x m).continuousAt.continuousWithinAt
