-- Results about limit points of open rays

import measure_theory.integral.circle_integral
import tactic.converter.binders

import topology

open filter (tendsto at_top at_bot)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball ball_mem_nhds mem_ball_self nonempty_ball sphere)
open set
open_locale nnreal topology real
noncomputable theory

variables {X : Type} [topological_space X]
variables {I : Type} [topological_space I] [conditionally_complete_linear_order I]
variables [densely_ordered I] [order_topology I]

-- We're closed if the closure doesn't add new points
lemma is_closed_iff_closure_diff {s : set X} : is_closed s ↔ closure s \ s = ∅ := begin
  constructor, {
    intros h, simp only [h.closure_eq, diff_self],
  }, {
    intros h, simp only [diff_eq_empty] at h, exact is_closed_of_closure_subset h,
  },
end

-- Lemmas for is_preconnected_iff_subset_of_fully_disjoint_open
lemma closure_inter_subset_compl {s u v : set X} (sc : is_closed s) (vo : is_open v) (d : disjoint u v)
    : closure (s ∩ u) ⊆ vᶜ := begin
  rw ←vo.is_closed_compl.closure_eq, apply closure_mono, 
  exact trans (inter_subset_right _ _) (disjoint.subset_compl_left d.symm),
end
lemma is_closed_closed_inter {s u v : set X} (sc : is_closed s) (vo : is_open v) (d : disjoint u v)
    (suv : s ⊆ u ∪ v) : is_closed (s ∩ u) := begin
  rw is_closed_iff_closure_diff, by_contradiction h, simp only [←ne.def, ←nonempty_iff_ne_empty] at h,
  rcases h with ⟨x,h⟩, simp only [mem_diff, mem_inter_iff, not_and] at h,
  have sus : closure (s ∩ u) ⊆ s, { nth_rewrite 1 ←sc.closure_eq, apply closure_mono, apply inter_subset_left },
  have xs := sus h.1,
  have m := not_or_distrib.mpr ⟨h.2 xs, not_mem_of_mem_compl (closure_inter_subset_compl sc vo d h.1)⟩,
  rw ←mem_union _ _ _ at m, exact not_mem_subset suv m xs,
end

-- open version of is_preconnected_iff_subset_of_disjoint_closed, if normal_space X
lemma is_preconnected_iff_subset_of_fully_disjoint_open [normal_space X] {s : set X} (sc : is_closed s)
    : is_preconnected s ↔ ∀ u v, is_open u → is_open v → s ⊆ u ∪ v → disjoint u v → s ⊆ u ∨ s ⊆ v := begin
  rw is_preconnected_iff_subset_of_fully_disjoint_closed sc, constructor, {
    intros h u v uo vo suv uv,
    have suc : is_closed (s ∩ u) := is_closed_closed_inter sc vo uv suv,
    have svc : is_closed (s ∩ v) := is_closed_closed_inter sc uo uv.symm ((union_comm u v).subst suv),
    cases h (s ∩ u) (s ∩ v) suc svc _ _ with su sv,
    left, exact (subset_inter_iff.mp su).2,
    right, exact (subset_inter_iff.mp sv).2,
    simp only [←inter_distrib_left], exact subset_inter (subset_refl _) suv,
    exact disjoint.inter_left' _ (disjoint.inter_right' _ uv),
  }, {
    intros h u v uc vc suv uv,
    rcases normal_space.normal u v uc vc uv with ⟨u',v',uo,vo,uu,vv,uv'⟩,  
    cases h u' v' uo vo (trans suv (union_subset_union uu vv)) uv' with h h, {
      left, intros x m, cases (mem_union _ _ _).mp (suv m) with mu mv,
      exact mu, exfalso, exact disjoint_left.mp uv' (h m) (vv mv),
    }, {
      right, intros x m, cases (mem_union _ _ _).mp (suv m) with mu mv,
      exfalso, exact disjoint_right.mp uv' (h m) (uu mu), exact mv,
    },
  },
end    

-- Directed intersections are preconnected
lemma is_preconnected.directed_Inter {I : Type} {s : I → set X} [nonempty I] [normal_space X]
    (d : directed superset s) (p : ∀ a, is_preconnected (s a)) (c : ∀ a, is_compact (s a))
    : is_preconnected (⋂ a, s a) := begin
  contrapose p,
  have ci : is_closed (⋂ a, s a) := is_closed_Inter (λ i, (c i).is_closed),
  simp only [is_preconnected_iff_subset_of_fully_disjoint_open ci, not_forall] at p,
  simp only [is_preconnected_iff_subset_of_fully_disjoint_open (c _).is_closed, not_forall],
  rcases p with ⟨u,v,uo,vo,suv,uv,no⟩,
  have e : ∃ a, s a ⊆ u ∪ v, {
    by_contradiction h, simp only [not_exists, set.not_subset] at h,
    set t := λ a, s a \ (u ∪ v),
    suffices n : (⋂ a, t a).nonempty, {
      rcases n with ⟨x,n⟩, simp only [mem_Inter, mem_diff, forall_and_distrib, forall_const] at n,
      rw ←mem_Inter at n, simp only [suv n.1, not_true, imp_false] at n, exact n.2,
    },
    apply is_compact.nonempty_Inter_of_directed_nonempty_compact_closed,
    intros a b, rcases d a b with ⟨c,ac,bc⟩, use [c, diff_subset_diff_left ac, diff_subset_diff_left bc],
    intros a, rcases h a with ⟨x,xa,xuv⟩, use [x, mem_diff_of_mem xa xuv],
    intros a, exact (c a).diff (uo.union vo),
    intros a, exact ((c a).diff (uo.union vo)).is_closed,
  },
  rcases e with ⟨a,auv⟩,
  use [a,u,v,uo,vo,auv,uv],
  contrapose no, simp only [not_not] at no ⊢,
  cases no with su sv,
  left, exact trans (Inter_subset _ _) su,
  right, exact trans (Inter_subset _ _) sv,
end

-- The limit points of a ray at_top are preconnected
lemma is_preconnected.limits_at_top [compact_space X] [normal_space X]
    {P : Type} [semilattice_sup P] [topological_space P] [order_topology P] [nonempty P]
    (p : ∀ a : P, is_preconnected (Ici a)) {r : P → X} (rc : continuous r)
    : is_preconnected {x | map_cluster_pt x at_top r} := begin
  set s := λ a, closure (r '' Ici a),
  have m : antitone s := λ a b ab, closure_mono (monotone_image (Ici_subset_Ici.mpr ab)),
  have d : directed superset s := λ a b, ⟨a ⊔ b, m le_sup_left, m le_sup_right⟩,
  have p : ∀ a, is_preconnected (s a) := λ a, ((p _).image _ rc.continuous_on).closure,
  have c : ∀ a, is_compact (s a) := λ a, is_closed_closure.is_compact,
  have e : {x | map_cluster_pt x at_top r} = ⋂ a, s a, {
    apply set.ext, intro x,
    simp only [mem_set_of, mem_Inter, map_cluster_pt_iff, mem_closure_iff_nhds, set.nonempty, @forall_comm P],
    apply forall_congr, intro t,
    simp only [@forall_comm P, mem_inter_iff, mem_image, mem_Ici, and_comm (_ ∈ t),
      exists_exists_and_eq_and, filter.frequently_at_top, exists_prop],
  },
  rw e, exact is_preconnected.directed_Inter d p c,
end

-- The limit points of a ray at_bot are preconnected
lemma is_preconnected.limits_at_bot [compact_space X] [normal_space X]
    {P : Type} [semilattice_inf P] [topological_space P] [order_topology P] [nonempty P]
    (p : ∀ a : P, is_preconnected (Iic a)) {r : P → X} (rc : continuous r)
    : is_preconnected {x | map_cluster_pt x at_bot r} := begin
  set r' : Pᵒᵈ → X := r,
  have rc' : continuous r' := rc,
  have p' : ∀ a : Pᵒᵈ, is_preconnected (Ici a) := λ a, p a,
  convert is_preconnected.limits_at_top p' rc',
end

-- ⊥ has no cluster_pts
lemma cluster_pt.bot {x : X} : ¬cluster_pt x ⊥ := begin
  simp only [cluster_pt_iff, filter.mem_bot, not_forall, not_nonempty_iff_eq_empty],
  use [univ, filter.univ_mem, ∅], simp only [univ_inter, eq_self_iff_true, and_self],
end 

-- The limits points of an open curve on Ioc a b are preconnected
-- Ideally I'd use is_preconnected.limits_at_top to prove this, but when I tried that
-- I hit horrible instance resolution mismatches.
lemma is_preconnected.limits_Ioc [compact_space X] [normal_space X]
    {r : ℝ → X} {a b : ℝ} (rc : continuous_on r (Ioc a b))
    : is_preconnected {x | map_cluster_pt x (𝓝[Ioc a b] a) r} := begin
  by_cases ab : ¬a < b, {
    simp only [Ioc_eq_empty ab, nhds_within_empty, map_cluster_pt, filter.map_bot, cluster_pt.bot, set_of_false,
      is_preconnected_empty],
  },
  simp only [not_not] at ab,
  set s := λ t : Ioc a b, closure (r '' Ioc a t),
  have n : nonempty (Ioc a b) := by use [b, right_mem_Ioc.mpr ab],
  have m : monotone s, {
    intros a b ab, refine closure_mono (monotone_image _),
    exact Ioc_subset_Ioc (le_refl _) (subtype.coe_le_coe.mpr ab),
  },
  have d : directed superset s := λ a b, ⟨min a b, m (min_le_left _ _), m (min_le_right _ _)⟩,
  have p : ∀ t, is_preconnected (s t), {
    rintros ⟨t,m⟩, refine (is_preconnected_Ioc.image _ (rc.mono _)).closure,
    simp only [mem_Ioc] at m, simp only [subtype.coe_mk, Ioc_subset_Ioc_iff m.1, m.2, le_refl, true_and],
  },
  have c : ∀ t, is_compact (s t) := λ t, is_closed_closure.is_compact,
  have e : {x | map_cluster_pt x (𝓝[Ioc a b] a) r} = ⋂ t, s t, {
    apply set.ext, intro x,
    simp only [mem_set_of, mem_Inter, map_cluster_pt_iff, mem_closure_iff_nhds, set.nonempty,
      @forall_comm _ (set X)],
    apply forall_congr, intro u, nth_rewrite 1 forall_comm, apply forall_congr, intro ux,
    simp only [mem_inter_iff, filter.frequently_iff, nhds_within_Ioc_eq_nhds_within_Ioi ab],
    constructor, {
      rintros h ⟨t,m⟩,
      have tm : Ioc a t ∈ 𝓝[Ioi a] a, {
        apply Ioc_mem_nhds_within_Ioi,
        simp only [mem_Ioc] at m, simp only [mem_Ico], use [le_refl _, m.1],
      },
      rcases h tm with ⟨v,vm,vu⟩, use [r v, vu, mem_image_of_mem _ vm],
    }, {
      intros h v vm,
      rcases mem_nhds_within_Ioi_iff_exists_Ioc_subset.mp vm with ⟨w,wa,wv⟩,
      simp only [mem_Ioi] at wa,
      have m : min w b ∈ Ioc a b, { simp only [mem_Ioc], use [lt_min wa ab, min_le_right _ _] },
      rcases h ⟨_,m⟩ with ⟨x,xu,rx⟩,
      simp only [subtype.coe_mk, mem_image, mem_Ioc, le_min_iff] at rx,
      rcases rx with ⟨c,⟨ac,cw,cb⟩,cx⟩,
      use [c, wv (mem_Ioc.mpr ⟨ac,cw⟩)], rwa cx,
    },
  },
  rw e, exact @is_preconnected.directed_Inter _ _ _ _ n _ d p c,
end

-- Nonempty, relatively clopen subsets of preconnected sets are empty or the full set
lemma is_preconnected.relative_clopen {s t : set X} (sp : is_preconnected s)
    (ne : (s ∩ t).nonempty) (op : s ∩ t ⊆ interior t) (cl : s ∩ closure t ⊆ t) : s ⊆ interior t := begin
  set u : set s := coe ⁻¹' t,
  have uo : is_open u, {
    rw ←subset_interior_iff_is_open, rintros ⟨x,m⟩ h,
    simp only [mem_preimage, subtype.coe_mk] at h,
    have n := op ⟨m,h⟩,
    simp only [mem_interior_iff_mem_nhds, preimage_coe_mem_nhds_subtype, subtype.coe_mk] at ⊢ n,
    exact nhds_within_le_nhds n,
  },
  have uc : is_closed u, {
    rw ←closure_eq_iff_is_closed, refine subset_antisymm _ subset_closure,
    refine trans (continuous_subtype_coe.closure_preimage_subset _) _,
    rintros ⟨x,m⟩ h, exact cl ⟨m,h⟩,
  },
  have p : is_preconnected (univ : set s) := (subtype.preconnected_space sp).is_preconnected_univ,
  cases disjoint_or_subset_of_clopen p ⟨uo,uc⟩, {
    simp only [univ_disjoint, preimage_eq_empty_iff, subtype.range_coe] at h,
    exfalso, exact ne.not_disjoint h.symm,
  }, {
    rw [←subtype.coe_preimage_self, preimage_subset_preimage_iff] at h,
    exact trans (subset_inter (subset_refl _) h) op, simp only [subtype.range_coe],
  },
end  

-- Version of is_path_connected.image assuming only continuous_on
lemma is_path_connected.image_of_continuous_on {X Y : Type} [topological_space X] [topological_space Y]
    {s : set X} (sc : is_path_connected s) {f : X → Y} (fc : continuous_on f s)
    : is_path_connected (f '' s) := begin
  set u : set s := univ,
  have uc : is_path_connected u, {
    convert sc.preimage_coe (subset_refl _), apply set.ext, intro x,
    simp only [mem_univ, true_iff, mem_preimage, subtype.mem],
  },
  have e : f '' s = s.restrict f '' u, {
    apply set.ext, intros y, constructor,
    rintros ⟨x,m,e⟩, use [⟨x,m⟩,mem_univ _,e], 
    rintros ⟨⟨x,m⟩,mu,e⟩, use [x,m,e],
  },
  rw e, exact uc.image (continuous_on_iff_continuous_restrict.mp fc),
end

-- Circles are path connected
lemma is_path_connected_sphere {z : ℂ} {r : ℝ} (r0 : 0 ≤ r) : is_path_connected (sphere z r) := begin
  rw [←abs_of_nonneg r0, ←image_circle_map_Ioc z r],
  refine is_path_connected.image _ (continuous_circle_map _ _),
  exact (convex_Ioc 0 (2*π)).is_path_connected (nonempty_Ioc.mpr real.two_pi_pos),
end

-- Path connectedness of f ⁻¹' frontier s implies path connectedness of f ⁻¹' s, for compact s.
-- Proof: Walk out of s until we hit the frontier, then move within the frontier.
-- Unfortunately this seems very tedious to write out, so I'm clearly missing some tricks.
lemma is_path_connected.of_frontier {X Y : Type} [topological_space X] [topological_space Y] [path_connected_space X]
    [t2_space Y] {f : X → Y} {s : set Y} (pc : is_path_connected (f ⁻¹' frontier s)) (fc : continuous f)
    (sc : is_closed s) : is_path_connected (f ⁻¹' s) := begin
  have pc' := pc, rcases pc' with ⟨b,fb,j⟩, use b,
  simp only [mem_preimage, mem_singleton_iff] at fb j ⊢,
  have bs : f b ∈ s := sc.frontier_subset fb,
  use bs, intros x fx,
  rcases path_connected_space.joined x b with ⟨p⟩,
  generalize hu : (Icc (0:ℝ) 1 ∩ ⋂ a (m : f (p.extend a) ∉ s), Iic a) = u,
  have bdd : bdd_above u, { rw [←hu, bdd_above_def], use 1, rintros t ⟨m,h⟩, exact m.2 },
  have un : u.nonempty, {
    rw ←hu, use [0, left_mem_Icc.mpr zero_le_one], simp only [mem_Inter₂, mem_Iic], intros a m,
    contrapose m, simp only [not_not, p.extend_of_le_zero (le_of_lt (not_le.mp m)), fx],
  },
  have uc : is_closed u, {
    rw ←hu, apply is_closed_Icc.inter, apply is_closed_Inter, intros a, apply is_closed_Inter,
    intro h, exact is_closed_Iic, apply_instance,
  },
  set t := Sup u,
  have tu : t ∈ u, { rw ←uc.closure_eq, exact cSup_mem_closure un bdd },
  have m : t ∈ Icc (0:ℝ) 1, { rw ←hu at tu, exact tu.1 },
  have lo : ∀ a, a ≤ t → f (p.extend a) ∈ s, {
    rintros a h, contrapose h, simp only [not_le],
    replace h : ∀ᶠ b in 𝓝 a, f (p.extend b) ∉ s :=
      (fc.comp p.continuous_extend).continuous_at.eventually_mem sc.is_open_compl h,
    simp only [←hu, mem_inter_iff, mem_Inter₂, mem_Iic] at tu,
    rcases (a.frequently_smaller.and_eventually h).exists with ⟨c,ca,cs⟩,
    exact lt_of_le_of_lt (tu.2 c cs) ca,
  },
  by_cases t1 : t = 1, {
    use p.symm, intro a, simp only [p.symm_apply, function.comp, mem_preimage],
    rw ←path.extend_extends', apply lo, rw t1, unit_interval, 
  },
  replace t1 : t < 1 := ne.lt_of_le t1 m.2,
  have ft : f (p ⟨t,m⟩) ∈ frontier s, {
    simp only [frontier, mem_diff, sc.closure_eq], constructor, {
      convert lo t (le_refl _), simp only [min_eq_right m.2, max_eq_right m.1],
    }, {
      have e : p ⟨t,m⟩ = p.extend t, { simp only [path.extend, Icc_extend_apply, min_eq_right m.2, max_eq_right m.1] },
      rw e, clear e, rw ←@mem_preimage  _ _ (f.comp p.extend),
      by_contradiction h,
      have o : is_open (f ∘ p.extend ⁻¹' interior s) := is_open_interior.preimage (fc.comp p.continuous_extend),
      rcases (nhds_basis_Ioo t).mem_iff.mp (o.mem_nhds h) with ⟨⟨x,y⟩,⟨xt,ty⟩,h⟩,
      simp only [subset_def, mem_Ioo, and_imp, mem_preimage, function.comp] at xt ty h,
      rcases exists_between (lt_min ty t1) with ⟨z,tz,zy1⟩, rcases lt_min_iff.mp zy1 with ⟨zy,z1⟩,
      suffices h : z ∈ u, linarith [le_cSup bdd h],
      rw ←hu, refine ⟨⟨trans m.1 (le_of_lt tz), le_of_lt z1⟩, _⟩,
      simp only [mem_Inter₂, mem_Iic], intros w ws,
      contrapose ws, simp only [not_not, not_le] at ws ⊢,
      by_cases xw : x < w, refine interior_subset (h _ xw (trans ws zy)),
      simp only [not_lt] at xw, exact lo _ (trans xw (le_of_lt xt)),
    },
  },
  -- Walk from b to p t
  refine ((pc.joined_in _ ft b fb).mono (preimage_mono sc.frontier_subset)).symm.trans (joined_in.symm _),
  -- Walk from x to p t
  have n : ∀ a : unit_interval, min ↑a t ∈ unit_interval, {
    rintros ⟨a,⟨a0,a1⟩⟩, use [le_min a0 m.1, trans (min_le_right _ _) m.2],
  },
  generalize hq : (λ a : unit_interval, p.extend (min a t)) = q,
  have qc : continuous q, { rw ←hq, exact p.continuous_extend.comp (continuous_subtype_coe.min continuous_const) },
  set q' : C(unit_interval,X) := ⟨q,qc⟩, use q', {
    simp only [←hq], simp only [Icc.coe_zero, min_eq_left m.1, p.extend_zero],
  }, {
    simp only [←hq], simp only [Icc.coe_one, min_eq_right m.2, path.extend, Icc_extend_apply, max_eq_right m.1],
  }, {
    rintros ⟨a,n⟩, simp only [mem_preimage, path.coe_mk, ←hq, subtype.coe_mk], exact lo _ (min_le_right _ _),
  },
end
