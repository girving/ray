-- Sets that don't separate open sets when they are removed

import holomorphic
import one_dimension

open complex (abs)
open filter (eventually_of_forall)
open metric (ball mem_ball)
open one_dimension
open set
open_locale real topology
noncomputable theory

variables {X : Type} [topological_space X]
variables {Y : Type} [topological_space Y]
variables {S : Type} [topological_space S] [complex_manifold I S]

-- A sufficient condition on t such that removing it from an open set does not disconnect the set
structure nonseparating (t : set X) : Prop :=
  (dense : dense tᶜ)
  (loc : ∀ x u, x ∈ t → u ∈ 𝓝 x → ∃ c, c ⊆ u \ t ∧ c ∈ 𝓝[tᶜ] x ∧ is_preconnected c)

-- univ ×ˢ t is nonseparating if t is
lemma nonseparating.univ_prod [_root_.locally_connected_space X] {t : set Y}
    (n : nonseparating t) : nonseparating ((univ : set X) ×ˢ t) := begin
  have e : ((univ : set X) ×ˢ t)ᶜ = univ ×ˢ tᶜ, {
    apply set.ext, rintros ⟨a,x⟩, rw mem_compl_iff,
    simp only [prod_mk_mem_set_prod_eq, mem_univ, mem_compl_iff, true_and],
  },
  constructor, {
    rw e, exact dense_univ.prod n.dense,
  }, {
    rintros ⟨a,x⟩ u m un, simp only [mem_prod_eq, mem_univ, true_and] at m,
    rcases mem_nhds_prod_iff.mp un with ⟨u0,n0,u1,n1,uu⟩,
    rcases n.loc x u1 m n1 with ⟨c1,cs1,cn1,cp1⟩,
    rcases locally_connected_space_iff_open_connected_subsets.mp (by apply_instance) a u0 n0
      with ⟨c0,cs0,co0,cm0,cc0⟩,
    use c0 ×ˢ c1, refine ⟨_,_,_⟩, {
      rintros ⟨b,y⟩ m', simp only [mem_prod_eq, mem_diff, mem_univ, true_and] at m' ⊢,
      refine ⟨_,(cs1 m'.2).2⟩, apply uu, use [cs0 m'.1, (cs1 m'.2).1],
    }, {
      rw [e, nhds_within_prod_eq, nhds_within_univ], exact filter.prod_mem_prod (co0.mem_nhds cm0) cn1,
    }, {
      exact cc0.is_preconnected.prod cp1,
    },
  },
end

-- Nonseparation in a manifold is the same as nonseparation in each chart
lemma nonseparating.complex_manifold {t : set S}
    (h : ∀ z, nonseparating ((ext_chart_at I z).target ∩ (ext_chart_at I z).symm ⁻¹' t))
    : nonseparating t := {
  dense := begin
    rw dense_iff_inter_open, rintros u uo ⟨z,m⟩,
    by_cases zt : z ∉ t, use [z, m, zt],
    simp only [not_not] at zt,
    set v := (ext_chart_at I z).target ∩ (ext_chart_at I z).symm ⁻¹' u,
    have vo : is_open v := (continuous_on_ext_chart_at_symm I z).preimage_open_of_open
      (ext_chart_at_open_target I z) uo,
    have vn : v.nonempty, {
      use ext_chart_at I z z, simp only [mem_inter_iff, mem_ext_chart_target, true_and, mem_preimage,
        local_equiv.left_inv _ (mem_ext_chart_source I z), m],
    },
    rcases dense_iff_inter_open.mp (h z).dense v vo vn with ⟨y,m⟩,
    use (ext_chart_at I z).symm y,
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, not_and] at m, rcases m with ⟨⟨ym,yu⟩,yt⟩,
    simp only [mem_inter_iff, ym, yu, true_and, mem_compl_iff], exact yt ym,
  end,
  loc := begin
    intros z u zt un,
    have m : ext_chart_at I z z ∈ (ext_chart_at I z).target ∩ (ext_chart_at I z).symm ⁻¹' t :=
      by simp only [mem_inter_iff, mem_ext_chart_target I z, true_and, mem_preimage,
        local_equiv.left_inv _ (mem_ext_chart_source I z), zt],
    have n : (ext_chart_at I z).target ∩ (ext_chart_at I z).symm ⁻¹' u ∈ 𝓝 (ext_chart_at I z z), {
      apply filter.inter_mem,
      exact (ext_chart_at_open_target I z).mem_nhds (mem_ext_chart_target I z),
      exact ext_chart_at_preimage_mem_nhds _ _ un,
    },
    rcases (h z).loc _ _ m n with ⟨c,cs,cn,cp⟩,
    have e : (ext_chart_at I z).source ∩ ext_chart_at I z ⁻¹' c = (ext_chart_at I z).symm '' c, {
      apply set.ext, intros x, simp only [mem_inter_iff, mem_preimage, mem_image], constructor, {
        rintros ⟨xz,xc⟩, refine ⟨_,xc,_⟩, simp only [local_equiv.left_inv _ xz],
      }, {
        rintros ⟨y,yc,yx⟩, rw ←yx,  
        have xc := cs yc, simp only [mem_diff, mem_inter_iff, mem_preimage] at xc,
        have yz := xc.1.1, use local_equiv.map_target _ yz,
        simp only [local_equiv.right_inv _ yz, yc],
      },
    },
    use (ext_chart_at I z).source ∩ ext_chart_at I z ⁻¹' c, refine ⟨_,_,_⟩, {
      intros x xm, simp only [mem_inter_iff, mem_preimage] at xm, rcases xm with ⟨xz,xc⟩,
      replace xc := cs xc,
      simp only [mem_diff, mem_inter_iff, mem_preimage, local_equiv.map_source _ xz, true_and,
        local_equiv.left_inv _ xz] at xc,
      exact xc,
    }, {
      rw e, convert filter.image_mem_map cn,
      have ee : ⇑((ext_chart_at I z).symm) = (ext_chart_at' I z).symm := rfl,
      rw ee, rw (ext_chart_at' I z).symm.map_nhds_within_eq (mem_ext_chart_target I z), rw ←ee,
      simp only [ext_chart_at', local_homeomorph.symm_source,
        local_equiv.left_inv _ (mem_ext_chart_source I z), compl_inter, inter_union_distrib_left,
        inter_compl_self, empty_union, image_inter],
      apply nhds_within_eq_nhds_within (mem_ext_chart_source I z) (is_open_ext_chart_at_source I z),
      apply set.ext, intro x,
      simp only [mem_inter_iff, mem_compl_iff, mem_image, mem_preimage], constructor, {
        rintros ⟨xt,xz⟩, refine ⟨⟨ext_chart_at I z x,_⟩,xz⟩,
        simp only [local_equiv.left_inv _ xz, xt, local_equiv.map_source _ xz, not_false_iff, and_self,
          eq_self_iff_true],
      }, {
        rintros ⟨⟨y,⟨⟨yz,yt⟩,yx⟩⟩,xz⟩,
        simp only [←yx, yt, local_equiv.map_target _ yz, not_false_iff, true_and],
      },
    }, {
      rw e, apply cp.image, apply (continuous_on_ext_chart_at_symm I z).mono,
      exact trans cs (trans (diff_subset _ _) (inter_subset_left _ _)),
    },
  end,
}

-- A sufficient condition on t for s \ t to be preconnected, for s open and preconnected.
-- Roughly, t has empty interior and there are arbitrarily small connected rings around each x ∈ t.
lemma is_preconnected.open_diff {s t : set X} (sc : is_preconnected s) (so : is_open s) (ts : nonseparating t)
    : is_preconnected (s \ t) := begin
  rw is_preconnected_iff_subset_of_disjoint at ⊢ sc,
  intros u v uo vo suv duv,
  set f := λ u : set X, u ∪ {x | x ∈ s ∧ x ∈ t ∧ ∀ᶠ y in 𝓝[tᶜ] x, y ∈ u},
  have mono : ∀ u, u ⊆ f u := λ _, subset_union_left _ _,
  have fopen : ∀ {u}, is_open u → is_open (f u), {
    intros u o, rw is_open_iff_eventually, intros x m,
    by_cases xu : x ∈ u, {
      exact (o.eventually_mem xu).mp (eventually_of_forall (λ q m, subset_union_left _ _ m)),
    },
    by_cases xt : x ∉ t, {
      contrapose xu, simp only [mem_union, mem_set_of, xt, false_and, and_false, or_false] at m,
      simp only [not_not], exact m,
    },
    simp only [not_not] at xt,
    have n := m, simp only [mem_union, xt, xu, false_or, true_and, mem_set_of, eventually_nhds_within_iff] at n,
    refine (so.eventually_mem n.1).mp (n.2.eventually_nhds.mp (eventually_of_forall (λ y n m, _))),
    by_cases yt : y ∈ t,
    simp only [mem_union, mem_set_of, eventually_nhds_within_iff], right, use [m,yt,n],
    exact mono _ (n.self yt),
  },
  have mem : ∀ {x u c}, x ∈ s → x ∈ t → c ∈ 𝓝[tᶜ] x → c ⊆ u → x ∈ f u, {
    intros x u c m xt cn cu, right, use [m,xt],
    simp only [filter.eventually_iff, set_of_mem_eq], exact filter.mem_of_superset cn cu,
  },
  have cover : s ⊆ f u ∪ f v, {
    intros x m,
    by_cases xt : x ∉ t, exact union_subset_union (mono _) (mono _) (suv (mem_diff_of_mem m xt)),
    simp only [not_not] at xt,
    rcases ts.loc x s xt (so.mem_nhds m) with ⟨c,cst,cn,cp⟩,
    have d := inter_subset_inter_left (u ∩ v) cst, rw [duv, subset_empty_iff] at d,
    cases is_preconnected_iff_subset_of_disjoint.mp cp u v uo vo (trans cst suv) d with cu cv,
    exact subset_union_left _ _ (mem m xt cn cu),
    exact subset_union_right _ _ (mem m xt cn cv),
  },
  have fdiff : ∀ {u}, f u \ t ⊆ u, {
    intros u x m, simp only [mem_diff, mem_union, mem_set_of] at m,
    simp only [m.2, false_and, and_false, or_false, not_false_iff, and_true] at m, exact m,
  },
  have fnon : ∀ {x u}, is_open u → x ∈ f u → ∀ᶠ y in 𝓝[tᶜ] x, y ∈ u, {
    intros x u o m, simp only [mem_union, mem_set_of] at m,
    cases m with xu m, exact (o.eventually_mem xu).filter_mono nhds_within_le_nhds, exact m.2.2,
  },
  have disj : s ∩ (f u ∩ f v) = ∅, {
    contrapose duv, simp only [←ne.def, ←nonempty_iff_ne_empty] at duv ⊢,
    rcases duv with ⟨x,m⟩, simp only [mem_inter_iff] at m,
    have b := ((so.eventually_mem m.1).filter_mono nhds_within_le_nhds).and
      ((fnon uo m.2.1).and (fnon vo m.2.2)),
    simp only [eventually_nhds_within_iff] at b,
    rcases eventually_nhds_iff.mp b with ⟨n,h,no,xn⟩,
    rcases ts.dense.exists_mem_open no ⟨_,xn⟩ with ⟨y,yt,yn⟩,
    use y, simp only [mem_inter_iff, mem_diff, ←mem_compl_iff], specialize h y yn yt,
    use h.1, use [h.2.1, h.2.2],
  },
  cases sc (f u) (f v) (fopen uo) (fopen vo) cover disj with su sv,
  left, exact trans (diff_subset_diff_left su) fdiff,
  right, exact trans (diff_subset_diff_left sv) fdiff,
end

-- ∅ is nonseparating
lemma nonseparating.empty : nonseparating (∅ : set X) := {
  dense := by simp only [compl_empty, dense_univ],
  loc := by simp only [mem_empty_iff_false, is_empty.forall_iff, forall_forall_const, implies_true_iff],
}

-- Punctured complex balls are preconnected
lemma is_preconnected.ball_diff_center {a : ℂ} {r : ℝ} : is_preconnected (ball a r \ {a}) := begin
  by_cases rp : r ≤ 0, simp only [metric.ball_eq_empty.mpr rp, empty_diff], exact is_preconnected_empty,
  simp only [not_le] at rp,
  have e : ball a r \ {a} = (λ p : ℝ × ℝ, a + p.1 * complex.exp (p.2 * complex.I)) '' Ioo 0 r ×ˢ univ, {
    apply set.ext, intros z,
    simp only [mem_diff, mem_ball, complex.dist_eq, mem_singleton_iff, mem_image, prod.exists, mem_prod_eq,
      mem_Ioo, mem_univ, and_true],
    constructor, {
      rintros ⟨zr,za⟩, use [abs (z - a), complex.arg (z - a)],
      simp only [absolute_value.pos_iff, ne.def, complex.abs_mul_exp_arg_mul_I, add_sub_cancel'_right,
        eq_self_iff_true, sub_eq_zero, za, zr, not_false_iff, and_true],
    }, {
      rintros ⟨s,t,⟨s0,sr⟩,e⟩,
      simp only [←e, add_sub_cancel', complex.abs.map_mul, complex.abs_of_real, abs_of_pos s0,
        complex.abs_exp_of_real_mul_I, mul_one, sr, true_and, add_right_eq_self, mul_eq_zero,
        complex.exp_ne_zero, or_false, complex.of_real_eq_zero],
      exact ne_of_gt s0,
    },
  },
  rw e, apply is_preconnected.image, exact is_preconnected_Ioo.prod is_preconnected_univ,
  apply continuous.continuous_on, continuity,
end

-- {z}ᶜ is nonseparating in ℂ, and in 1D manifolds
lemma complex.nonseparating_singleton (a : ℂ) : nonseparating ({a} : set ℂ) := {
  dense := begin
    rw dense_iff_inter_open, rintros u uo ⟨z,m⟩,
    by_cases za : z ≠ a, use [z, m],
    simp only [not_not] at za, rw za at m, clear za z,
    rcases metric.is_open_iff.mp uo a m with ⟨r,rp,rs⟩,
    use a + r/2,
    simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, add_right_eq_self, div_eq_zero_iff,
      complex.of_real_eq_zero, bit0_eq_zero, one_ne_zero, or_false, ne_of_gt rp, not_false_iff, and_true],
    apply rs,
    simp only [mem_ball, dist_self_add_left, complex.norm_eq_abs, map_div₀, complex.abs_of_real, complex.abs_two,
      abs_of_pos rp, half_lt_self rp],
  end,
  loc := begin
    intros z u m n, simp only [mem_singleton_iff] at m, simp only [m] at ⊢ n, clear m z,
    rcases metric.mem_nhds_iff.mp n with ⟨r,rp,rs⟩,
    use ball a r \ {a}, refine ⟨diff_subset_diff_left rs, _, is_preconnected.ball_diff_center⟩,
    exact diff_mem_nhds_within_compl (metric.ball_mem_nhds _ rp) _,
  end,
}
lemma complex_manifold.nonseparating_singleton (a : S) : nonseparating ({a} : set S) := begin
  apply nonseparating.complex_manifold, intro z,
  by_cases az : a ∈ (ext_chart_at I z).source, {
    convert complex.nonseparating_singleton (ext_chart_at I z a),
    simp only [eq_singleton_iff_unique_mem, mem_inter_iff, local_equiv.map_source _ az, true_and,
      mem_preimage, mem_singleton_iff, local_equiv.left_inv _ az, eq_self_iff_true],
    rintros x ⟨m,e⟩, simp only [←e, local_equiv.right_inv _ m],
  }, {
    convert nonseparating.empty,
    simp only [eq_empty_iff_forall_not_mem, mem_inter_iff, mem_preimage, mem_singleton_iff, not_and],
    intros x m, contrapose az, simp only [not_not] at az ⊢, rw ←az, exact local_equiv.map_target _ m,
  },
end

-- Removing a point in S leaves it locally connected
lemma is_preconnected.open_diff_singleton {s : set S} (sc : is_preconnected s) (so : is_open s) (a : S)
    : is_preconnected (s \ {a}) :=
  is_preconnected.open_diff sc so (complex_manifold.nonseparating_singleton a)

-- Removing a line in ℂ × S leaves it locally connected
lemma is_preconnected.open_diff_line {s : set (ℂ × S)} (sc : is_preconnected s) (so : is_open s) (a : S)
    : is_preconnected (s \ {p | p.2 = a}) := begin
  apply is_preconnected.open_diff sc so,
  have e : {p : ℂ × S | p.2 = a} = univ ×ˢ {a}, {
    apply set.ext, rintros ⟨c,z⟩, simp only [mem_prod_eq, mem_set_of, mem_univ, true_and, mem_singleton_iff],
  },
  rw e, exact nonseparating.univ_prod (complex_manifold.nonseparating_singleton _),
end