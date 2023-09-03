-- Non-injectivity near multiple roots

import bottcher_near
import inverse

open complex (exp log abs cpow)
open filter (eventually_of_forall tendsto at_top)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball ball_mem_nhds mem_ball_self nonempty_ball)
open nat (iterate)
open set
open_locale nnreal topology real
noncomputable theory

variables {S : Type} [topological_space S] [complex_manifold I S]
variables {T : Type} [topological_space T] [complex_manifold I T]

-- Nontrivial roots of unity exists
lemma exist_root_of_unity {d : ℕ} (d2 : 2 ≤ d) : ∃ a : ℂ, a ≠ 1 ∧ a^d = 1 := begin 
  set n : ℕ+ := ⟨d, lt_of_lt_of_le (by norm_num) d2⟩,
  have two : nontrivial (roots_of_unity n ℂ), {
    rw [←fintype.one_lt_card_iff_nontrivial, complex.card_roots_of_unity],
    simp only [pnat.mk_coe], exact lt_of_lt_of_le (by norm_num) d2,
  },
  rcases two with ⟨⟨a,am⟩,⟨b,bm⟩,ab⟩,
  simp only [ne.def, subtype.mk_eq_mk, mem_roots_of_unity, pnat.mk_coe] at am bm ab,
  by_cases a1 : a = 1, {
    use b, rw a1 at ab, constructor,
    simp only [ne.def, units.coe_eq_one, ne.symm ab], exact not_false,
    rw [←units.coe_pow, bm, units.coe_one],
  }, {
    use a, constructor,
    simp only [ne.def, units.coe_eq_one, a1], exact not_false,
    rw [←units.coe_pow, am, units.coe_one],
  },
end
 
-- If f' = 0 at a point, every nearby point is achieved at least twice.
-- We operationalize this statement via a nontrivial function taking z → z' s.t. f z = f z'.
-- First, the cases c = 0, f 0 = 0.
theorem super_at.not_local_inj {f : ℂ → ℂ} {d : ℕ} (s : super_at f d)
    : ∃ g : ℂ → ℂ, analytic_at ℂ g 0 ∧ g 0 = 0 ∧ ∀ᶠ z in 𝓝[{0}ᶜ] 0, g z ≠ z ∧ f (g z) = f z := begin
  rcases s.super_near with ⟨t,s⟩,
  have ba : analytic_at ℂ (bottcher_near f d) 0 := bottcher_near_analytic_z s _ s.t0,
  have nc : mfderiv I I (bottcher_near f d) 0 ≠ 0, {
    rw [mfderiv_eq_fderiv, ←deriv_fderiv, (bottcher_near_monic s).deriv],
    rw [ne.def, continuous_linear_map.ext_iff, not_forall], use 1,
    simp only [continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply, algebra.id.smul_eq_mul,
      mul_one, continuous_linear_map.zero_apply],
    norm_num,
  },
  rcases complex_inverse_fun' (ba.holomorphic_at I I) nc with ⟨i,ia,ib,bi⟩,
  rw bottcher_near_zero at bi ia,
  have i0 : i 0 = 0, { nth_rewrite 0 ←bottcher_near_zero, rw ib.self },
  have inj : ∀ᶠ p : ℂ × ℂ in 𝓝 (0,0), i p.1 = i p.2 → p.1 = p.2, {
    refine ia.local_inj _,
    have d0 : mfderiv I I (λ z : ℂ, z) 0 ≠ 0 := id_mderiv_ne_zero,
    rw (filter.eventually_eq.symm ib).mfderiv_eq at d0,
    rw mfderiv_comp 0 _ ba.differentiable_at.mdifferentiable_at at d0,
    simp only [ne.def, mderiv_comp_eq_zero_iff, nc, or_false] at d0,
    rw bottcher_near_zero at d0, exact d0,
    rw bottcher_near_zero, exact ia.mdifferentiable_at,
  },
  rcases exist_root_of_unity s.d2 with ⟨a,a1,ad⟩,
  refine ⟨λ z, i (a * bottcher_near f d z), _, _, _⟩, {
    apply holomorphic_at.analytic_at I I,
    refine ia.comp_of_eq (holomorphic_at_const.mul (ba.holomorphic_at I I)) _,
    simp only [bottcher_near_zero, s.f0, mul_zero],
  }, {
    simp only [bottcher_near_zero, mul_zero, i0],
  }, {
    simp only [eventually_nhds_within_iff, mem_compl_singleton_iff],
    have t0 : continuous_at (λ z, a * bottcher_near f d z) 0 := continuous_at_const.mul ba.continuous_at,
    have t1 : continuous_at (λ z, f (i (a * bottcher_near f d z))) 0, {
      refine s.fa0.continuous_at.comp_of_eq (ia.continuous_at.comp_of_eq t0 _) _,
      repeat { simp only [bottcher_near_zero, mul_zero, i0] },
    },
    have t2 : continuous_at f 0 := s.fa0.continuous_at,
    have m0 : ∀ᶠ z in 𝓝 0, i (a * bottcher_near f d z) ∈ t, {
      refine continuous_at.eventually_mem (ia.continuous_at.comp_of_eq t0 _) s.o _,
      repeat { simp only [bottcher_near_zero, mul_zero, i0, s.t0] },
    },
    have m1 : ∀ᶠ z in 𝓝 0, z ∈ t := s.o.eventually_mem s.t0,
    simp only [continuous_at, bottcher_near_zero, mul_zero, i0, s.f0] at t0 t1 t2,
    have tp := t0.prod_mk ba.continuous_at, simp only [←nhds_prod_eq, continuous_at, bottcher_near_zero] at tp,
    apply (tp.eventually inj).mp,
    refine ib.mp (bi.mp ((t1.eventually ib).mp ((t0.eventually bi).mp ((t2.eventually ib).mp (m0.mp (m1.mp _)))))),
    refine eventually_of_forall (λ z m1 m0 t2 t0 t1 bi ib tp z0, ⟨_,_⟩), {
      contrapose tp, simp only [id, prod.fst, prod.snd, not_not, not_imp] at tp ⊢, rw ib, use tp,
      contrapose a1, simp only [not_not] at ⊢ a1,
      have b0 := bottcher_near_ne_zero s m1 z0,
      calc a = a * bottcher_near f d z / bottcher_near f d z : by rw mul_div_cancel _ b0
      ... = bottcher_near f d z / bottcher_near f d z : by rw a1
      ... = 1 : div_self b0,
    }, {
      -- f (i (a * b z)) = i (b (f (i (a * b z)))) = i (b (i (a * b z)) ^ d)
      --   = i ((a * b z) ^ d) = i (b z ^ d) = i (b (f z)) = f z
      rw [←t1, bottcher_near_eqn s m0, t0, mul_pow, ad, one_mul, ←bottcher_near_eqn s m1, t2],
    },
  },
end

 -- If f' = 0 at a point, every nearby point is achieved at least twice.
-- We operationalize this statement via a nontrivial function taking z → z' s.t. f z = f z'.
-- First, the cases c = 0, f 0 = 0.
theorem not_local_inj_of_deriv_zero' {f : ℂ → ℂ} (fa : analytic_at ℂ f 0) (df : has_deriv_at f 0 0) (f0 : f 0 = 0)
    : ∃ g : ℂ → ℂ, analytic_at ℂ g 0 ∧ g 0 = 0 ∧ ∀ᶠ z in 𝓝[{0}ᶜ] 0, g z ≠ z ∧ f (g z) = f z := begin
  by_cases o0 : order_at f 0 = 0, {
    simp only [order_at_eq_zero_iff fa, f0, ne.def, eq_self_iff_true, not_true, or_false] at o0,
    use [λ z, -z, analytic_at_id.neg, neg_zero], rw eventually_nhds_within_iff,
    have e0 : ∀ᶠ z in 𝓝 0, f (-z) = 0, { nth_rewrite 0 ←neg_zero at o0, exact continuous_at_neg.eventually o0 },
    refine o0.mp (e0.mp (eventually_of_forall (λ z f0' f0 z0, _))),
    simp only [mem_compl_singleton_iff] at z0, rw pi.zero_apply at f0,
    rw [f0, f0', eq_self_iff_true, and_true, ne.def, neg_eq_self_iff], exact z0,
  },
  have o1 : order_at f 0 ≠ 1, {
    have d := df.deriv, contrapose d, simp only [not_not] at d, exact deriv_ne_zero_of_order_at_eq_one d,
  },
  have d2 : 2 ≤ order_at f 0, { rw nat.two_le_iff, use [o0,o1] },
  clear o1 df f0,
  set a := leading_coeff f 0,
  have a0 : a ≠ 0 := leading_coeff_ne_zero fa o0,
  set g := λ z, a⁻¹ • f z,
  have s : super_at g (order_at f 0) := {
    d2 := d2,
    fa0 := analytic_at_const.mul fa,
    fd := by rw order_at_const_smul (inv_ne_zero a0),
    fc := by simp only [leading_coeff_const_smul, smul_eq_mul, inv_mul_cancel a0], 
  },
  rcases s.not_local_inj with ⟨h,ha,h0,e⟩,
  use [h,ha,h0], refine e.mp (eventually_of_forall _),
  rintros z ⟨h0,hz⟩, use h0,
  exact (is_unit.smul_left_cancel (ne.is_unit (inv_ne_zero a0))).mp hz,
end

-- If f' = 0 at a point, every nearby point is achieved at least twice.
-- We operationalize this statement via a nontrivial function taking z → z' s.t. f z = f z'.
-- General case.
theorem not_local_inj_of_deriv_zero {f : ℂ → ℂ} {c : ℂ} (fa : analytic_at ℂ f c) (df : has_deriv_at f 0 c)
    : ∃ g : ℂ → ℂ, analytic_at ℂ g c ∧ g c = c ∧ ∀ᶠ z in 𝓝[{c}ᶜ] c, g z ≠ z ∧ f (g z) = f z := begin
  set f' := λ z, f (z + c) - f c,
  have fa' : analytic_at ℂ f' 0 :=
    analytic_at.sub (analytic_at.comp (by simp only [zero_add, fa]) (analytic_at_id.add analytic_at_const))
      analytic_at_const,
  have df' : has_deriv_at f' (0*1) 0, {
    refine has_deriv_at.sub_const _ _,
    have e : (λ z, f (z + c)) = f ∘ (λ z, z + c) := rfl,
    rw e, apply has_deriv_at.comp, simp only [zero_add, df],
    exact has_deriv_at.add_const (has_deriv_at_id _) _,
  },
  simp only [zero_mul] at df',
  have f0' : (λ z, f (z + c) - f c) 0 = 0, { simp only [zero_add, sub_self] },
  rcases not_local_inj_of_deriv_zero' fa' df' f0' with ⟨g,ga,e,h⟩, clear fa df fa' df',
  refine ⟨λ z, g (z - c) + c, _, _, _⟩, {
    exact analytic_at.add (analytic_at.comp (by simp only [sub_self, ga]) (analytic_at_id.sub analytic_at_const))
      analytic_at_const,
  }, {
    simp only [sub_self, e, zero_add],
  }, {
    simp only [eventually_nhds_within_iff] at h ⊢,
    have sc : tendsto (λ z, z - c) (𝓝 c) (𝓝 0), { rw ←sub_self c, exact continuous_at_id.sub continuous_at_const },
    refine (sc.eventually h).mp (eventually_of_forall _),
    simp only [mem_compl_singleton_iff, sub_ne_zero],
    rintros z h zc, rcases h zc with ⟨gz,ff⟩, constructor,
    contrapose gz, simp only [not_not] at gz ⊢, nth_rewrite 1 ←gz, ring,
    simp only [sub_left_inj, sub_add_cancel] at ff, exact ff,
  },
end

-- If f' = 0 at a point, every nearby point is achieved at least twice (manifold version)
theorem not_local_inj_of_mfderiv_zero {f : S → T} {c : S} (fa : holomorphic_at I I f c) (df : mfderiv I I f c = 0)
    : ∃ g : S → S, holomorphic_at I I g c ∧ g c = c ∧ ∀ᶠ z in 𝓝[{c}ᶜ] c, g z ≠ z ∧ f (g z) = f z := begin
  generalize hg : (λ z, ext_chart_at I (f c) (f ((ext_chart_at I c).symm z))) = g,
  have dg : mfderiv I I g (ext_chart_at I c c) = 0, {
    have fd : mdifferentiable_at I I f ((ext_chart_at I c).symm (ext_chart_at I c c)), {
      rw local_equiv.left_inv, exact fa.mdifferentiable_at, apply mem_ext_chart_source,
    },
    rw [←hg, mfderiv_comp _ (holomorphic_at.ext_chart_at _).mdifferentiable_at _,
      mfderiv_comp _ fd (holomorphic_at.ext_chart_at_symm _).mdifferentiable_at, local_equiv.left_inv,
      df, continuous_linear_map.zero_comp, continuous_linear_map.comp_zero],
    apply mem_ext_chart_source, apply mem_ext_chart_target, rw local_equiv.left_inv,
    apply mem_ext_chart_source, apply mem_ext_chart_source,
    refine mdifferentiable_at.comp _ fd (holomorphic_at.ext_chart_at_symm (mem_ext_chart_target _ _)).mdifferentiable_at,
  },
  simp only [holomorphic_at_iff, function.comp, hg] at fa,
  have dg' := fa.2.differentiable_at.mdifferentiable_at.has_mfderiv_at,
  rw [dg, has_mfderiv_at_iff_has_fderiv_at] at dg',
  replace dg := dg'.has_deriv_at, clear dg',
  rcases not_local_inj_of_deriv_zero fa.2 dg with ⟨h,ha,h0,e⟩,
  refine ⟨λ z, (ext_chart_at I c).symm (h (ext_chart_at I c z)), _, _, _⟩, {
    apply (holomorphic_at.ext_chart_at_symm (mem_ext_chart_target I c)).comp_of_eq,
    apply (ha.holomorphic_at I I).comp_of_eq (holomorphic_at.ext_chart_at (mem_ext_chart_source I c)) rfl,
    exact h0,
  }, {
    rw [h0, local_equiv.left_inv _ (mem_ext_chart_source I c)],
  }, {
    rw eventually_nhds_within_iff at e ⊢,
    apply ((continuous_at_ext_chart_at I c).eventually e).mp,
    apply ((is_open_ext_chart_at_source I c).eventually_mem (mem_ext_chart_source I c)).mp,
    have m1 : ∀ᶠ z in 𝓝 c, h (ext_chart_at I c z) ∈ (ext_chart_at I c).target, {
      apply continuous_at.eventually_mem _ (ext_chart_at_open_target I c),
      rw h0, exact mem_ext_chart_target I c,
      exact ha.continuous_at.comp_of_eq (continuous_at_ext_chart_at I c) rfl,
    },
    have m2 : ∀ᶠ z in 𝓝 c, f z ∈ (ext_chart_at I (f c)).source :=
      fa.1.eventually_mem (is_open_ext_chart_at_source I _) (mem_ext_chart_source I _),
    have m3 : ∀ᶠ z in 𝓝 c, f ((ext_chart_at I c).symm (h (ext_chart_at I c z))) ∈ (ext_chart_at I (f c)).source, {
      refine continuous_at.eventually_mem _ (is_open_ext_chart_at_source I _) _,
      apply fa.1.comp_of_eq, apply (continuous_at_ext_chart_at_symm I _).comp_of_eq,
      apply ha.continuous_at.comp_of_eq, exact continuous_at_ext_chart_at I _,
      refl, exact h0, rw [h0, local_equiv.left_inv _ (mem_ext_chart_source I _)],
      rw [h0, local_equiv.left_inv _ (mem_ext_chart_source I _)], exact mem_ext_chart_source I _,
    },
    refine m1.mp (m2.mp (m3.mp (eventually_of_forall _))),
    simp only [mem_compl_singleton_iff],
    intros z m3 m2 m1 m0 even zc,
    rcases even ((local_equiv.inj_on _).ne m0 (mem_ext_chart_source I c) zc) with ⟨hz,gh⟩,
    constructor, {
      nth_rewrite 1 ←local_equiv.left_inv _ m0,
      rw (local_equiv.inj_on _).ne_iff, exact hz,
      rw local_equiv.symm_source, exact m1,
      rw local_equiv.symm_source, exact local_equiv.map_source _ m0,
    }, {
      simp only [←hg] at gh,
      rw local_equiv.left_inv _ m0 at gh,
      rw (local_equiv.inj_on _).eq_iff m3 m2 at gh, exact gh,
    },
  },
end

-- Injectivity on an open set implies nonsingularity
lemma set.inj_on.mfderiv_ne_zero {f : S → T} {s : set S} (inj : inj_on f s) (so : is_open s)
    {c : S} (m : c ∈ s) (fa : holomorphic_at I I f c) : mfderiv I I f c ≠ 0 := begin
  contrapose inj, simp only [not_not, inj_on, not_forall] at inj ⊢,
  rcases not_local_inj_of_mfderiv_zero fa inj with ⟨g,ga,gc,fg⟩,
  have gm : ∀ᶠ z in 𝓝 c, g z ∈ s := continuous_at.eventually_mem ga.continuous_at so (by simp only [gc, m]),
  replace fg := fg.and (((so.eventually_mem m).and gm).filter_mono nhds_within_le_nhds),
  rcases fg.frequently.exists with ⟨z,⟨gz,fg⟩,zs,gs⟩,
  use [g z, gs, z, zs, fg, gz],
end

-- The global 1D inverse function without a nonsingularity hypothesis
theorem global_complex_inverse_fun_open'' {f : S → T} [nonempty S] {s : set S}
    (fa : holomorphic_on I I f s) (inj : inj_on f s) (so : is_open s)
    : ∃ g : T → S, holomorphic_on I I g (f '' s) ∧ (∀ z, z ∈ s → g (f z) = z) :=
  global_complex_inverse_fun_open' fa (λ z m, inj.mfderiv_ne_zero so m (fa z m)) inj so