module
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Ray.Manifold.Defs
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
## Manifold lemmas
-/

open ChartedSpace (chartAt)
open Function (uncurry)
open Set
open scoped Manifold Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {H : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

variable {A M : Type} [TopologicalSpace A] [TopologicalSpace M]
variable {B N : Type} [TopologicalSpace B] [TopologicalSpace N]
variable {C O : Type} [TopologicalSpace C] [TopologicalSpace O]
variable {D P : Type} [TopologicalSpace D] [TopologicalSpace P]

/-- Version of `ModelWithCorners.prod_apply` with `x ∈ H × H'` rather than `ModelProd H H'`.  This
comes up because other simplification doesn't stay in `ModelProd`. -/
@[simp]
lemma ModelWithCorners.prod_apply' {E H E' H' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H') (x : H × H') :
    (I.prod I') x = (I x.1, I' x.2) :=
  ModelWithCorners.prod_apply _ _ _

variable {I : ModelWithCorners 𝕜 E A} [ChartedSpace A M]
variable {J : ModelWithCorners 𝕜 F B} [ChartedSpace B N]
variable {K : ModelWithCorners 𝕜 G C} [ChartedSpace C O]
variable {L : ModelWithCorners 𝕜 H D} [ChartedSpace D P]

section Nhds

/-- `extChartAt` as a `PartialHomeomorph` -/
@[expose] public def extChartAt' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type}
    [TopologicalSpace M] [ChartedSpace A M] (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

/-- `extChartAt.symm` maps `𝓝` to `𝓝` -/
public theorem extChartAt_symm_map_nhds [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) :
    Filter.map (extChartAt I x).symm (𝓝 y) = 𝓝 ((extChartAt I x).symm y) :=
  (extChartAt' I x).symm.map_nhds_eq m

/-- `extChartAt.symm` maps `𝓝` to `𝓝` -/
public theorem extChartAt_symm_map_nhds' (I : ModelWithCorners 𝕜 E A) [I.Boundaryless] {M : Type}
    [TopologicalSpace M] [ChartedSpace A M] (x : M) :
    Filter.map (extChartAt I x).symm (𝓝 (extChartAt I x x)) = 𝓝 x := by
  convert extChartAt_symm_map_nhds (mem_extChartAt_target x)
  simp only [PartialEquiv.left_inv _ (mem_extChartAt_source x)]
  infer_instance

/-- Nontrivial manifolds have no isolated points.
    Unfortunately, making this an instance gives "cannot find synthesization order for instance" -/
public theorem AnalyticManifold.punctured_nhds_neBot (I : ModelWithCorners 𝕜 E A) [I.Boundaryless]
    [Nontrivial E] (x : M) : (𝓝[{x}ᶜ] x).NeBot := by
  have p := Module.punctured_nhds_neBot 𝕜 E (extChartAt I x x)
  simp only [← Filter.frequently_true_iff_neBot, frequently_nhdsWithin_iff, ←
    extChartAt_symm_map_nhds' I x, Filter.frequently_map, true_and,
    mem_compl_singleton_iff] at p ⊢
  apply p.mp
  apply ((isOpen_extChartAt_target x).eventually_mem (mem_extChartAt_target x)).mp
  refine .of_forall fun y m h ↦ ?_
  contrapose h; nth_rw 2 [← h]
  rw [PartialEquiv.right_inv _ m]

end Nhds

section Deriv

/-- `TangentSpace` commutes with products -/
theorem tangentSpace_prod (x : M) (y : N) :
    TangentSpace (I.prod J) (x, y) = (TangentSpace I x × TangentSpace J y) := by
  simp only [TangentSpace]

/-- `HasMFDerivAt` composition for curried functions.
    This was oddly difficult to prove. -/
theorem MDifferentiableAt.hasMFDerivAt_uncurry {f : N → O → P} {y : N} {z : O}
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
      fh.comp y ((hasMFDerivAt_id _).prodMk (hasMFDerivAt_const _ _))
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
      fh.comp z ((hasMFDerivAt_const _ _).prodMk (hasMFDerivAt_id _))
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
public theorem MDifferentiableAt.hasMFDerivAt_comp2 {f : N → O → P} {g : M → N} {h : M → O} {x : M}
    (fd : MDifferentiableAt (J.prod K) L (uncurry f) (g x, h x))
    {dg : TangentSpace I x →L[𝕜] TangentSpace J (g x)} (gh : HasMFDerivAt I J g x dg)
    {dh : TangentSpace I x →L[𝕜] TangentSpace K (h x)} (hh : HasMFDerivAt I K h x dh)
    {df0 : TangentSpace J (g x) →L[𝕜] TangentSpace L (f (g x) (h x))}
    (fh0 : HasMFDerivAt J L (fun y ↦ f y (h x)) (g x) df0)
    {df1 : TangentSpace K (h x) →L[𝕜] TangentSpace L (f (g x) (h x))}
    (fh1 : HasMFDerivAt K L (fun y ↦ f (g x) y) (h x) df1) :
    HasMFDerivAt I L (fun y ↦ f (g y) (h y)) x (df0.comp dg + df1.comp dh) := by
  have fh := (fd.hasMFDerivAt_uncurry fh0 fh1).comp x (gh.prodMk hh)
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_assoc] at fh
  exact fh

/-- More general version of `hasMFDerivAt_iff_hasDerivAt`.
    The mathlib version doesn't handle product spaces. -/
public theorem hasMFDerivAt_iff_hasFDerivAt' {I : ModelWithCorners 𝕜 E A} [I.Boundaryless]
    [ChartedSpace A E] [IsManifold I ⊤ E] [ExtChartEqRefl I]
    {J : ModelWithCorners 𝕜 F B} [J.Boundaryless] [ChartedSpace B F] [IsManifold J ⊤ F]
    [ExtChartEqRefl J] {f : E → F} {x : E} {f' : E →L[𝕜] F} :
    HasMFDerivAt I J f x f' ↔ HasFDerivAt f f' x := by
  simp only [HasMFDerivAt, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ,
    writtenInExtChartAt, extChartAt_eq_refl, Function.comp_def, PartialEquiv.refl_coe,
    PartialEquiv.refl_symm, id]
  exact ⟨fun x ↦ x.2, fun d ↦ ⟨d.continuousAt, d⟩⟩

/-- Variant of `mfderiv_comp` that doesn't use `∘` for better inference -/
theorem mfderiv_comp' {f : M → N} (x : M) {g : N → O} (hg : MDifferentiableAt J K g (f x))
    (hf : MDifferentiableAt I J f x) :
    mfderiv I K (fun x ↦ g (f x)) x = (mfderiv J K g (f x)).comp (mfderiv I J f x) :=
  mfderiv_comp _ hg hf

variable [IsManifold I ⊤ M] [IsManifold J ⊤ N] [IsManifold K ⊤ O] [IsManifold L ⊤ P]

/-- Chart derivatives are invertible (left inverse) -/
public theorem extChartAt_mderiv_left_inverse [I.Boundaryless] {x y : M}
    (m : y ∈ (extChartAt I x).source) :
    (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm (extChartAt I x y)).comp
        (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I y) := by
  have m' : extChartAt I x y ∈ (extChartAt I x).target := PartialEquiv.map_source _ m
  have mc : y ∈ (chartAt A x).source := by simpa only [mfld_simps] using m
  have d0 := (contMDiffOn_extChartAt_symm (n := ⊤) _ _ m').mdifferentiableWithinAt (by decide)
  have d1 := (contMDiffAt_extChartAt' (I := I) (n := ⊤) mc).mdifferentiableWithinAt (by decide)
  replace d0 := d0.mdifferentiableAt (extChartAt_target_mem_nhds' m')
  simp only [mdifferentiableWithinAt_univ] at d1
  have c := mfderiv_comp y d0 d1
  refine Eq.trans c.symm ?_
  rw [← mfderiv_id]
  apply Filter.EventuallyEq.mfderiv_eq
  rw [Filter.eventuallyEq_iff_exists_mem]; use(extChartAt I x).source
  use extChartAt_source_mem_nhds' m
  intro z zm
  simp only [Function.comp, id, PartialEquiv.left_inv _ zm]

/-- Chart derivatives are invertible (right inverse) -/
public theorem extChartAt_mderiv_right_inverse [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) :
    (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) ((extChartAt I x).symm y)).comp
        (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm y) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) y) := by
  have m' : (extChartAt I x).symm y ∈ (extChartAt I x).source := PartialEquiv.map_target _ m
  have mc : (extChartAt I x).symm y ∈ (chartAt A x).source := by simpa only [mfld_simps] using m'
  have d0 := (contMDiffOn_extChartAt_symm (n := ⊤) _ _ m).mdifferentiableWithinAt (by decide)
  have d1 := (contMDiffAt_extChartAt' (I := I) (n := ⊤) mc).mdifferentiableWithinAt (by decide)
  replace d0 := d0.mdifferentiableAt (extChartAt_target_mem_nhds' m)
  simp only [mdifferentiableWithinAt_univ] at d1
  have c := mfderiv_comp y d1 d0
  refine Eq.trans c.symm ?_; clear c; rw [← mfderiv_id]; apply Filter.EventuallyEq.mfderiv_eq
  rw [Filter.eventuallyEq_iff_exists_mem]; use(extChartAt I x).target
  have n := extChartAt_target_mem_nhdsWithin' m'
  simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ,
    PartialEquiv.right_inv _ m] at n
  use n; intro z zm
  simp only [Function.comp, id, PartialEquiv.right_inv _ zm, Function.comp]

/-- Chart derivatives are invertible (right inverse) -/
public theorem extChartAt_mderiv_right_inverse' [I.Boundaryless] {x y : M}
    (m : y ∈ (extChartAt I x).source) :
    (mfderiv I (modelWithCornersSelf 𝕜 E) (extChartAt I x) y).comp
        (mfderiv (modelWithCornersSelf 𝕜 E) I (extChartAt I x).symm (extChartAt I x y)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (modelWithCornersSelf 𝕜 E) (extChartAt I x y)) := by
  have h := extChartAt_mderiv_right_inverse (PartialEquiv.map_source _ m)
  rw [PartialEquiv.left_inv _ m] at h; exact h

end Deriv
