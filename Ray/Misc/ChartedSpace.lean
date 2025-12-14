module
import Mathlib.Geometry.Manifold.ChartedSpace

/-!
## Charted space lemmas
-/

open ChartedSpace (chartAt)
open Set
open scoped Topology
noncomputable section

variable {A M : Type} [TopologicalSpace A] [TopologicalSpace M] [ChartedSpace A M]

/-- Charted spaces are regular if `A` is regular and locally compact and `M` is `T2`.
    This is a weird set of assumptions, but I don't know how to prove T2 naturally. -/
theorem ChartedSpace.regularSpace [T2Space M] [LocallyCompactSpace A] : RegularSpace M := by
  apply RegularSpace.of_exists_mem_nhds_isClosed_subset; intro x s n
  set t := (chartAt A x).target ∩ (chartAt A x).symm ⁻¹' ((chartAt A x).source ∩ s)
  have cn : (chartAt A x).source ∈ 𝓝 x :=
    (chartAt A x).open_source.mem_nhds (mem_chart_source A x)
  have tn : t ∈ 𝓝 (chartAt A x x) := by
    apply Filter.inter_mem ((chartAt A x).open_target.mem_nhds (mem_chart_target A x))
    apply ((chartAt A x).continuousAt_symm (mem_chart_target _ _)).preimage_mem_nhds
    rw [(chartAt A x).left_inv (mem_chart_source _ _)]; exact Filter.inter_mem cn n
  rcases local_compact_nhds tn with ⟨u, un, ut, uc⟩
  refine ⟨(chartAt A x).symm '' u, ?_, ?_, ?_⟩
  · convert (chartAt A x).symm.image_mem_nhds _ un
    rw [(chartAt A x).left_inv (mem_chart_source _ _)]
    rw [OpenPartialHomeomorph.symm_source]; exact mem_chart_target _ _
  · have c : IsCompact ((chartAt A x).symm '' u) :=
      uc.image_of_continuousOn ((chartAt A x).continuousOn_symm.mono
        (_root_.trans ut inter_subset_left))
    exact c.isClosed
  · intro y m; rcases(mem_image _ _ _).mp m with ⟨z, zu, zy⟩; rw [← zy]
    rcases ut zu with ⟨_, m1⟩; simp only [mem_preimage] at m1; exact m1.2
