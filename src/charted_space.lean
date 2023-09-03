-- Charted space lemmas

import geometry.manifold.charted_space

open charted_space (chart_at)
open set
open_locale topology
noncomputable theory

-- Charted space are T1
-- Making this an instance seems to cause infinite instance resolution loops
theorem charted_space.t1_space (A M : Type) [topological_space A] [topological_space M] [charted_space A M]
    [t1_space A] : t1_space M := {t1 := begin
  intro x, rw ←compl_compl {x}, apply is_open.is_closed_compl,
  rw is_open_iff_mem_nhds, intros y m, simp only [mem_compl_singleton_iff] at m,
  simp only [mem_nhds_iff, subset_compl_singleton_iff],
  by_cases xm : x ∈ (chart_at A y).source, {
    set t := (chart_at A y).source \ {x},
    have e : t = (chart_at A y).source ∩
        chart_at A y ⁻¹' ((chart_at A y).target \ {chart_at A y x}), {
      apply set.ext, intros z,
      simp only [mem_diff, mem_singleton_iff, mem_inter_iff, mem_preimage], constructor,
      rintros ⟨zm,zx⟩, use [zm, local_equiv.map_source _ zm, (local_equiv.inj_on _).ne zm xm zx],
      rintros ⟨zm,zmt,zx⟩, use [zm, ((local_equiv.inj_on _).ne_iff zm xm).mp zx],
    },
    use t, refine ⟨_,_,_⟩,
    simp only [mem_diff, mem_singleton_iff, eq_self_iff_true, not_true, and_false, not_false_iff],
    rw e, apply (chart_at A y).continuous_on.preimage_open_of_open (chart_at _ _).open_source,
    exact is_open.sdiff (chart_at _ _).open_target is_closed_singleton,
    rw e, simp only [mem_inter_iff, mem_chart_source, true_and, mem_preimage, mem_diff,
      mem_chart_target, mem_singleton_iff],
    exact (local_equiv.inj_on _).ne (mem_chart_source A y) xm m,
  }, {
    use [(chart_at A y).source, xm, (chart_at A y).open_source, mem_chart_source A y],
  },
end}

-- Charted spaces are regular if A is regular and locally_compact and M is T2
-- This is a pretty useless set of assumptions, but unfortunately I don't know how to prove T2 naturally.
theorem charted_space.regular_space (A M : Type) [topological_space A] [topological_space M] [charted_space A M]
    [regular_space A] [t2_space M] [locally_compact_space A] : regular_space M := begin
  apply regular_space.of_exists_mem_nhds_is_closed_subset, intros x s n,
  set t := (chart_at A x).target ∩ (chart_at A x).symm ⁻¹' ((chart_at A x).source ∩ s),
  have cn : (chart_at A x).source ∈ 𝓝 x := (chart_at A x).open_source.mem_nhds (mem_chart_source A x),
  have tn : t ∈ 𝓝 (chart_at A x x), {
    apply filter.inter_mem ((chart_at A x).open_target.mem_nhds (mem_chart_target A x)),
    apply ((chart_at A x).continuous_at_symm (mem_chart_target _ _)).preimage_mem_nhds,
    rw (chart_at A x).left_inv (mem_chart_source _ _), exact filter.inter_mem cn n,
  },
  rcases local_compact_nhds tn with ⟨u,un,ut,uc⟩,
  refine ⟨(chart_at A x).symm '' u, _, _, _⟩, {
    convert (chart_at A x).symm.image_mem_nhds _ un,
    rw (chart_at A x).left_inv (mem_chart_source _ _),
    rw local_homeomorph.symm_source, exact mem_chart_target _ _,
  }, {
    have c : is_compact ((chart_at A x).symm '' u) :=
      uc.image_of_continuous_on ((chart_at A x).continuous_on_symm.mono (trans ut (inter_subset_left _ _))),
    exact c.is_closed,
  }, {
    intros y m, rcases (mem_image _ _ _).mp m with ⟨z,zu,zy⟩, rw ←zy,
    rcases ut zu with ⟨m0,m1⟩, simp only [mem_preimage] at m1, exact m1.2,
  },
end