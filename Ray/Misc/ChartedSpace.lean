import Mathlib.Geometry.Manifold.ChartedSpace

/-!
## Charted space lemmas
-/

open ChartedSpace (chartAt)
open Set
open scoped Topology
noncomputable section

variable {A M : Type} [TopologicalSpace A] [TopologicalSpace M] [ChartedSpace A M]

/-- Charted space are T1.
    Making this an instance seems to cause infinite instance resolution loops. -/
theorem ChartedSpace.t1Space [T1Space A] : T1Space M where
  t1 := by
    intro x; rw [←compl_compl ({x} : Set M)]; apply IsOpen.isClosed_compl
    rw [isOpen_iff_mem_nhds]; intro y m; simp only [mem_compl_singleton_iff] at m
    simp only [mem_nhds_iff, subset_compl_singleton_iff]
    by_cases xm : x ∈ (chartAt A y).source
    · set t := (chartAt A y).source \ {x}
      have e : t = (chartAt A y).source ∩ chartAt A y ⁻¹'
          ((chartAt A y).target \ {chartAt A y x}) := by
        apply Set.ext; intro z
        simp only [mem_diff, mem_singleton_iff, mem_inter_iff, mem_preimage]; constructor
        intro ⟨zm, zx⟩; use zm, PartialEquiv.map_source _ zm, (PartialEquiv.injOn _).ne zm xm zx
        intro ⟨zm, _, zx⟩; use zm, ((PartialEquiv.injOn _).ne_iff zm xm).mp zx
      use t; refine ⟨_, _, _⟩
      simp only [mem_diff, mem_singleton_iff, eq_self_iff_true, not_true, and_false_iff,
        not_false_iff]
      rw [e]
      apply (chartAt A y).continuousOn.isOpen_inter_preimage (_root_.chartAt _ _).open_source
      exact IsOpen.sdiff (_root_.chartAt _ _).open_target isClosed_singleton
      rw [e]
      simp only [mem_inter_iff, mem_chart_source, true_and_iff, mem_preimage, mem_diff,
        mem_chart_target, mem_singleton_iff]
      exact (PartialEquiv.injOn _).ne (mem_chart_source A y) xm m
    · use(chartAt A y).source, xm, (chartAt A y).open_source, mem_chart_source A y

/-- Charted spaces are regular if `A` is regular and locally compact and `M` is `T2`.
    This is a weird set of assumptions, but I don't know how to prove T2 naturally. -/
theorem ChartedSpace.regularSpace [T2Space M] [LocallyCompactSpace A] : RegularSpace M := by
  apply RegularSpace.ofExistsMemNhdsIsClosedSubset; intro x s n
  set t := (chartAt A x).target ∩ (chartAt A x).symm ⁻¹' ((chartAt A x).source ∩ s)
  have cn : (chartAt A x).source ∈ 𝓝 x :=
    (chartAt A x).open_source.mem_nhds (mem_chart_source A x)
  have tn : t ∈ 𝓝 (chartAt A x x) := by
    apply Filter.inter_mem ((chartAt A x).open_target.mem_nhds (mem_chart_target A x))
    apply ((chartAt A x).continuousAt_symm (mem_chart_target _ _)).preimage_mem_nhds
    rw [(chartAt A x).left_inv (mem_chart_source _ _)]; exact Filter.inter_mem cn n
  rcases local_compact_nhds tn with ⟨u, un, ut, uc⟩
  refine ⟨(chartAt A x).symm '' u, _, _, _⟩
  · convert (chartAt A x).symm.image_mem_nhds _ un
    rw [(chartAt A x).left_inv (mem_chart_source _ _)]
    rw [PartialHomeomorph.symm_source]; exact mem_chart_target _ _
  · have c : IsCompact ((chartAt A x).symm '' u) :=
      uc.image_of_continuousOn ((chartAt A x).continuousOn_symm.mono
        (_root_.trans ut (inter_subset_left _ _)))
    exact c.isClosed
  · intro y m; rcases(mem_image _ _ _).mp m with ⟨z, zu, zy⟩; rw [← zy]
    rcases ut zu with ⟨_, m1⟩; simp only [mem_preimage] at m1; exact m1.2
