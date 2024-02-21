import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners

/-!
## Smooth manifold lemmas
-/

open ChartedSpace (chartAt)
open Set
open scoped Topology
noncomputable section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- If we're boundaryless, `extChartAt` has open target -/
theorem isOpen_extChartAt_target (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] [ChartedSpace H M]
    (x : M) : IsOpen (extChartAt I x).target := by
  simp only [extChartAt, PartialHomeomorph.extend, ModelWithCorners.range_eq_univ,
    PartialEquiv.trans_target, ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm,
    univ_inter]
  exact IsOpen.preimage (ModelWithCorners.continuous_symm I) (PartialHomeomorph.open_target _)

-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of the key point -/
theorem extChartAt_target_mem_nhds {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] [ChartedSpace H M] (x : M) :
    (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := by
  convert extChartAt_target_mem_nhdsWithin I x
  simp only [I.range_eq_univ, nhdsWithin_univ]

-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of any of its points -/
theorem extChartAt_target_mem_nhds' {𝕜 E M H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M]
    (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] [ChartedSpace H M] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) :
    (extChartAt I x).target ∈ 𝓝 y :=
  (isOpen_extChartAt_target I x).mem_nhds m
