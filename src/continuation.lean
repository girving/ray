-- Analytic continuation

import analysis.complex.open_mapping
import analysis.locally_convex.with_seminorms
import ring_theory.roots_of_unity.complex

import connected
import holomorphic
import one_dimension
import totally_disconnected

open classical (some some_spec)
open complex (abs)
open filter (tendsto eventually_of_forall)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball is_closed_ball mem_ball mem_closed_ball mem_ball_self
  mem_closed_ball_self mem_sphere sphere)
open one_dimension
open set
open_locale real topology manifold
noncomputable theory

variables {X : Type} [topological_space X]
variables {S : Type} [topological_space S] [complex_manifold I S]
variables {T : Type} [topological_space T] [complex_manifold I T]
variables {U : Type} [topological_space U] [complex_manifold I U]

section nontrivial
variables {f : ℂ → ℂ} {s : set ℂ}

-- A nontrivial analytic function is one which is not locally constant
structure nontrivial_analytic_on (f : ℂ → ℂ) (s : set ℂ) :=
  (analytic_on : analytic_on ℂ f s)
  (nonconst : ∀ x, x ∈ s → ∃ᶠ y in 𝓝 x, f y ≠ f x)

-- nontrivial analytic functions have isolated values
lemma nontrivial_analytic_on.isolated (n : nontrivial_analytic_on f s) {z : ℂ} (zs : z ∈ s)
    : ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ f z := begin
  have fa : analytic_at ℂ (λ w, f w - f z) z := (n.analytic_on z zs).sub analytic_at_const,
  cases fa.eventually_eq_zero_or_eventually_ne_zero, {
    have b := h.and_frequently (n.nonconst z zs),
    simp only [sub_eq_zero, ne.def, and_not_self, filter.frequently_false] at b,
    exfalso, exact b,
  }, {
    simp only [sub_ne_zero] at h, exact h,
  },
end
lemma nontrivial_analytic_on.isolated' (n : nontrivial_analytic_on f s) {z : ℂ} (zs : z ∈ s) (a : ℂ)
    : ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ a := begin
  by_cases h : f z = a, simp only [←h], exact n.isolated zs,
  exact ((n.analytic_on _ zs).continuous_at.eventually_ne h).filter_mono nhds_within_le_nhds,
end

-- Nonconstant functions on preconnected sets are nontrivial
lemma is_preconnected.nontrivial_analytic_on (p : is_preconnected s) (fa : analytic_on ℂ f s)
    (ne : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a ≠ f b) : nontrivial_analytic_on f s := {
  analytic_on := fa,
  nonconst := begin
    contrapose ne, simp only [not_forall, filter.not_frequently, not_not] at ne, rcases ne with ⟨z,zs,h⟩,  
    simp only [not_exists, exists_and_distrib_left, not_and, not_not],
    have h' := (h.filter_mono (@nhds_within_le_nhds _ _ _ {z}ᶜ)).frequently,
    have e := fa.eq_on_of_preconnected_of_frequently_eq analytic_on_const p zs h',
    intros x xs y ys, rw [e xs, e ys],
  end,
} 

-- Nonconstant entire functions are nontrivial
lemma entire.nontrivial_analytic_on (fa : analytic_on ℂ f univ) (ne : ∃ a b, f a ≠ f b)
    : nontrivial_analytic_on f univ := begin
  refine is_preconnected_univ.nontrivial_analytic_on fa _, simpa only [set.mem_univ, true_and],
end

-- The roots of an analytic function form a discrete topology
lemma nontrivial_analytic_on.discrete_topology (n : nontrivial_analytic_on f s) (a : ℂ)
    : discrete_topology ↥(s ∩ f ⁻¹' {a}) := begin
  rw ←singletons_open_iff_discrete, rintros ⟨z,m⟩,
  simp only [set.mem_inter_iff, set.mem_preimage, set.mem_singleton_iff] at m,
  by_cases h : ∃ᶠ z in 𝓝[{z}ᶜ] z, f z = a, {
    have i := (n.isolated' m.1 a).and_frequently h,
    simp only [not_and_self, filter.frequently_const] at i, exfalso, exact i,
  }, {
    simp only [filter.not_frequently, eventually_nhds_within_iff, set.mem_compl_singleton_iff] at h,
    rcases eventually_nhds_iff.mp h with ⟨t,t0,o,tz⟩,
    simp only [is_open_induced_iff], use [t,o],
    apply set.ext, rintros ⟨w,m⟩,
    simp only [set.mem_preimage, subtype.coe_mk, set.mem_singleton_iff, subtype.mk_eq_mk],
    simp only [set.mem_inter_iff, set.mem_preimage, set.mem_singleton_iff] at m,
    specialize t0 w, simp only [m.2, imp_false, eq_self_iff_true, not_true, not_not] at t0,
    use t0, intro wz, rw wz, exact tz,
  },
end

-- pow is nontrivial
lemma pow_nontrivial {d : ℕ} (dp : d > 0) : nontrivial_analytic_on (λ z, z^d) univ := begin
  apply entire.nontrivial_analytic_on (λ _ _, analytic_at_id.pow), use [0,1],
  simp only [one_pow, zero_pow dp], norm_num,
end

-- All roots of unity as a set
def all_roots_of_unity := {z : ℂ | ∃ n : ℕ, n ≠ 0 ∧ z^n = 1}
lemma all_roots_of_unity.ne_zero {z : ℂ} (m : z ∈ all_roots_of_unity) : z ≠ 0 := begin
  rcases m with ⟨n,n0,z1⟩, contrapose z1, simp only [not_not] at z1,
  simp only [z1, zero_pow' _ n0], exact zero_ne_one,
end

-- Roots of unity are totally disconnected
lemma is_totally_disconnected.all_roots_of_unity : is_totally_disconnected all_roots_of_unity := begin
  apply is_countable.is_totally_disconnected,
  simp only [all_roots_of_unity, set_of_exists], apply countable_Union, intro n,
  by_cases n0 : n = 0,
  simp only [n0, ne.def, eq_self_iff_true, not_true, false_and, set_of_false, countable_empty],
  simp only [ne.def, n0, not_false_iff, true_and],
  have np : 0 < n := nat.pos_of_ne_zero n0,
  set n' : ℕ+ := ⟨n,np⟩,  
  have e : {z : ℂ | z^n = 1} ⊆ coe '' (roots_of_unity n' ℂ : set ℂˣ), {
    intros z e, simp only [mem_set_of] at e,
    simp only [mem_image, set_like.mem_coe, mem_roots_of_unity, pnat.mk_coe],
    by_cases z0 : z = 0, exfalso, simp only [z0, zero_pow' _ n0, zero_ne_one] at e, exact e,
    use units.mk0 z z0,
    simp only [units.coe_mk0, eq_self_iff_true, and_true, ←units.eq_iff, units.coe_pow, units.coe_one, e],
  },
  apply set.countable.mono e, clear e, apply countable.image, apply set.finite.countable,
  rw set.finite_def, use roots_of_unity.fintype ℂ n',
end

-- Given continuous p : X → ℂ on preconnected X, p is const if f ∘ p is const 
lemma nontrivial_analytic_on.const (n : nontrivial_analytic_on f s) {p : X → ℂ} {t : set X}
    (tc : is_preconnected t) (pc : continuous_on p t) (ps : set.maps_to p t s)
    {a b : ℂ} (p1 : ∃ x, x ∈ t ∧ p x = a) (fp : ∀ x, x ∈ t → f (p x) = b) : ∀ x, x ∈ t → p x = a := begin
  have disc : discrete_topology ↥(s ∩ f ⁻¹' {b}) := n.discrete_topology b,
  rcases p1 with ⟨z,zt,z1⟩, simp only [←z1],
  intros x xt,
  refine @is_preconnected.constant_of_maps_to _ _ _ _ _ tc _ disc _ pc _ _ _ xt zt,
  intros y yt, simp only [set.mem_inter_iff, set.mem_preimage, set.mem_singleton_iff],
  use [ps yt, fp _ yt],
end

-- Given p : X → ℂ, p^d = 1 → p = 1 given continuity, X preconnected, and p = 1 somewhere
lemma eq_one_of_pow_eq_one {p : X → ℂ} {t : set X} {d : ℕ} (pc : continuous_on p t) (tc : is_preconnected t)
    (dp : d > 0) (pa : ∃ x, x ∈ t ∧ p x = 1) (pd : ∀ x, x ∈ t → p x ^ d = 1) : ∀ x, x ∈ t → p x = 1 :=
  (pow_nontrivial dp).const tc pc (set.maps_to_univ _ _) pa pd

-- Given p, q : X → ℂ, p^d = q^d → p ≠ 0 → p = q
lemma eq_of_pow_eq {p q : X → ℂ} {t : set X} {d : ℕ}
    (pc : continuous_on p t) (qc : continuous_on q t) (tc : is_preconnected t) (dp : d > 0)
    (pq : ∃ x, x ∈ t ∧ p x = q x) (p0 : ∀ x, x ∈ t → p x ≠ 0)
    (pqd : ∀ x, x ∈ t → p x ^ d = q x ^ d) : ∀ x, x ∈ t → p x = q x := begin
  set r := λ x, q x / p x,
  have rc : continuous_on r t := qc.div pc p0,
  have h := eq_one_of_pow_eq_one rc tc dp _ _,
  intros x m, exact ((div_eq_one_iff_eq (p0 _ m)).mp (h _ m)).symm,
  rcases pq with ⟨x,m,e⟩, use [x,m], exact (div_eq_one_iff_eq (p0 _ m)).mpr e.symm,
  intros x m, simp only [div_pow], rw div_eq_one_iff_eq, exact (pqd _ m).symm, exact pow_ne_zero _ (p0 _ m),
end

-- holomorphic_at version of analytic_at.eventually_eq_or_eventually_ne
theorem holomorphic_at.eventually_eq_or_eventually_ne [t2_space T] {f g : S → T} {z : S}
    (fa : holomorphic_at I I f z) (ga : holomorphic_at I I g z)
    : (∀ᶠ w in 𝓝 z, f w = g w) ∨ (∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ g w) := begin
  simp only [holomorphic_at_iff, function.comp] at fa ga,
  rcases fa with ⟨fc,fa⟩, rcases ga with ⟨gc,ga⟩, 
  by_cases fg : f z ≠ g z, {
    right, contrapose fg, simp only [not_not], simp only [filter.not_eventually, not_not] at fg,
    exact tendsto_nhds_unique_of_frequently_eq fc gc (fg.filter_mono nhds_within_le_nhds),
  },
  simp only [not_not] at fg,
  cases fa.eventually_eq_or_eventually_ne ga with e e, {
    left, clear fa ga,
    replace e := (continuous_at_ext_chart_at I z).eventually e,
    replace e := filter.eventually_eq.fun_comp e (ext_chart_at I (f z)).symm,
    apply e.congr, simp only [function.comp], clear e,
    apply (fc.eventually_mem (is_open_ext_chart_at_source I (f z)) (mem_ext_chart_source I (f z))).mp,
    apply (gc.eventually_mem (is_open_ext_chart_at_source I (g z)) (mem_ext_chart_source I (g z))).mp,
    refine eventually_nhds_iff.mpr ⟨(ext_chart_at I z).source, λ x m gm fm, _,
      is_open_ext_chart_at_source _ _, mem_ext_chart_source I z⟩,
    simp only at fm gm, rw ←fg at gm,
    simp only [←fg, local_equiv.left_inv _ m, local_equiv.left_inv _ fm, local_equiv.left_inv _ gm],
  }, {
    right, clear fa ga,
    simp only [eventually_nhds_within_iff, set.mem_compl_singleton_iff] at e ⊢,
    replace e := (continuous_at_ext_chart_at I z).eventually e,
    apply (fc.eventually_mem (is_open_ext_chart_at_source I (f z)) (mem_ext_chart_source I (f z))).mp,
    apply (gc.eventually_mem (is_open_ext_chart_at_source I (g z)) (mem_ext_chart_source I (g z))).mp,
    apply ((is_open_ext_chart_at_source I z).eventually_mem (mem_ext_chart_source I z)).mp,
    refine e.mp (eventually_of_forall _), clear e,
    intros x h xm gm fm xz, rw ←fg at gm, 
    simp only [←fg, local_equiv.left_inv _ xm] at h,
    specialize h ((local_equiv.inj_on _).ne xm (mem_ext_chart_source _ _) xz),
    rwa ←(local_equiv.inj_on _).ne_iff fm gm,
  },
end

-- Locally constant functions are constant on preconnected sets
theorem holomorphic_on.const_of_locally_const [t2_space T] {f : S → T} {s : set S} (fa : holomorphic_on I I f s)
    {z : S} {a : T} (zs : z ∈ s) (o : is_open s) (p : is_preconnected s) (c : ∀ᶠ w in 𝓝 z, f w = a)
    : ∀ w, w ∈ s → f w = a := begin
  set t := {z | z ∈ s ∧ ∀ᶠ w in 𝓝 z, f w = a},
  suffices st : s ⊆ t, exact λ z m, (st m).2.self,
  refine p.subset_of_closure_inter_subset _ _ _, {
    rw is_open_iff_eventually, intros z m, simp only [set.mem_set_of_eq] at m ⊢,
    exact ((o.eventually_mem m.1).and m.2.eventually_nhds).mp (eventually_of_forall (λ y h, h)),
  }, {
    use z, simp only [set.mem_inter_iff], use [zs, ⟨zs,c⟩],
  }, {
    intros z m, simp only [set.mem_inter_iff, mem_closure_iff_frequently] at m,
    have aa : holomorphic_at I I (λ _, a) z := holomorphic_at_const,
    cases (fa _ m.2).eventually_eq_or_eventually_ne aa with h h, use [m.2, h],
    simp only [eventually_nhds_within_iff, set.mem_compl_singleton_iff] at h,
    have m' := m.1, contrapose m', simp only [filter.not_frequently],
    refine h.mp (eventually_of_forall _), intros x i,
    by_cases xz : x = z, rwa xz, specialize i xz, contrapose i,
    simp only [not_not] at i ⊢, exact i.2.self,
  },
end 

-- If S is locally connected, we don't need the open assumption in holomorphic_on.const_of_locally_const
theorem holomorphic_on.const_of_locally_const' [_root_.locally_connected_space S] [t2_space T]
    {f : S → T} {s : set S} (fa : holomorphic_on I I f s) {z : S} {a : T}
    (zs : z ∈ s) (p : is_preconnected s) (c : ∀ᶠ w in 𝓝 z, f w = a)
    : ∀ w, w ∈ s → f w = a := begin
  rcases local_preconnected_nhds_set p (is_open_holomorphic_at.mem_nhds_set.mpr fa) with ⟨u,uo,su,ua,uc⟩,
  exact λ w ws, holomorphic_on.const_of_locally_const (λ _ m, ua m) (su zs) uo uc c w (su ws),
end

-- A holomorphic function that is nonconstant near a point
structure nontrivial_holomorphic_at (f : S → T) (z : S) : Prop :=
  (holomorphic_at : holomorphic_at I I f z)
  (nonconst : ∃ᶠ w in 𝓝 z, f w ≠ f z)

-- Stronger version of nonconst
lemma nontrivial_holomorphic_at.eventually_ne [t2_space T] {f : S → T} {z : S} (n : nontrivial_holomorphic_at f z)
    : ∀ᶠ w in 𝓝 z, w ≠ z → f w ≠ f z := begin
  have ca : holomorphic_at I I (λ _, f z) z := holomorphic_at_const,
  cases n.holomorphic_at.eventually_eq_or_eventually_ne ca, {
    have b := h.and_frequently n.nonconst,
    simp only [and_not_self, filter.frequently_false] at b,
    exfalso, exact b,
  }, {
    simp only [eventually_nhds_within_iff, mem_compl_singleton_iff] at h, convert h,
  },
end

-- Nontriviality on a set
def nontrivial_holomorphic_on (f : S → T) (s : set S) : Prop := ∀ z, z ∈ s → nontrivial_holomorphic_at f z  

-- Nontrivially extends over preconnected sets
theorem nontrivial_holomorphic_at.on_preconnected [t2_space T] {f : S → T} {s : set S} {z : S}
    (fa : holomorphic_on I I f s) (zs : z ∈ s) (o : is_open s) (p : is_preconnected s)
    (n : nontrivial_holomorphic_at f z) : nontrivial_holomorphic_on f s := begin
  intros w ws, replace n := n.nonconst, refine ⟨fa _ ws, _⟩, contrapose n,
  simp only [filter.not_frequently, not_not] at ⊢ n, generalize ha : f w = a, rw ha at n,
  rw eventually_nhds_iff, refine ⟨s,_,o,zs⟩,
  have c := fa.const_of_locally_const ws o p n,
  intros x m, rw [c _ m, c _ zs],
end

 -- Nontrivial holomorphic functions are locally nontrivial
lemma nontrivial_holomorphic_at.eventually [t2_space T] {f : S → T} {z : S} (n : nontrivial_holomorphic_at f z)
    : ∀ᶠ w in 𝓝 z, nontrivial_holomorphic_at f w := begin
  have lc : locally_connected_space S := by apply_instance,
  rcases eventually_nhds_iff.mp n.holomorphic_at.eventually with ⟨s,fa,os,zs⟩,
  rcases locally_connected_space_iff_open_connected_subsets.mp lc z s (os.mem_nhds zs) with ⟨t,ts,ot,zt,ct⟩, 
  rw eventually_nhds_iff, refine ⟨t,_,ot,zt⟩,
  exact n.on_preconnected (holomorphic_on.mono fa ts) zt ot ct.is_preconnected,
end

-- If the derivative isn't zero, we're nontrivial
lemma nontrivial_holomorphic_at_of_mfderiv_ne_zero {f : S → T} {z : S}
    (fa : holomorphic_at I I f z) (d : mfderiv I I f z ≠ 0) : nontrivial_holomorphic_at f z := begin
  refine ⟨fa, _⟩, contrapose d, simp only [filter.not_frequently, not_not] at d ⊢,
  generalize ha : f z = a, rw ha at d, apply has_mfderiv_at.mfderiv,
  exact (has_mfderiv_at_const I I a _).congr_of_eventually_eq d,
end

-- nontriviality composes
lemma nontrivial_holomorphic_at.comp [t2_space T] [t2_space U] {f : T → U} {g : S → T} {z : S}
    (fn : nontrivial_holomorphic_at f (g z)) (gn : nontrivial_holomorphic_at g z)
    : nontrivial_holomorphic_at (λ z, f (g z)) z := begin
  use fn.holomorphic_at.comp gn.holomorphic_at,
  convert gn.nonconst.and_eventually (gn.holomorphic_at.continuous_at.eventually fn.eventually_ne),
  ext, tautology,
end

-- nontriviality anticomposes
lemma nontrivial_holomorphic_at.anti [t2_space T] [t2_space U] {f : T → U} {g : S → T} {z : S}
    (h : nontrivial_holomorphic_at (λ z, f (g z)) z)
    (fa : holomorphic_at I I f (g z)) (ga : holomorphic_at I I g z)
    : nontrivial_holomorphic_at f (g z) ∧ nontrivial_holomorphic_at g z := begin
  replace h := h.nonconst, refine ⟨⟨fa,_⟩,⟨ga,_⟩⟩, {
    contrapose h, simp only [filter.not_frequently, not_not] at h ⊢,
    exact (ga.continuous_at.eventually h).mp (eventually_of_forall (λ _ h, h)),
  }, {
    contrapose h, simp only [filter.not_frequently, not_not] at h ⊢,
    exact h.mp (eventually_of_forall (λ x h, by rw h)),
  },
end

-- id is nontrivial
-- There's definitely a better way to prove this, but I'm blanking at the moment.
lemma nontrivial_holomorphic_at_id (z : S) : nontrivial_holomorphic_at (λ w, w) z := begin
  use holomorphic_at_id,
  rw filter.frequently_iff, intros s sz,
  rcases mem_nhds_iff.mp sz with ⟨t,ts,ot,zt⟩,
  set u := (ext_chart_at I z).target ∩ (ext_chart_at I z).symm ⁻¹' t,
  have uo : is_open u := (continuous_on_ext_chart_at_symm I z).preimage_open_of_open
    (ext_chart_at_open_target _ _) ot,
  have zu : ext_chart_at I z z ∈ u := by simp only [mem_inter_iff, mem_ext_chart_target, true_and, mem_preimage,
    local_equiv.left_inv _ (mem_ext_chart_source I z), zt],
  rcases metric.is_open_iff.mp uo _ zu with ⟨r,rp,ru⟩,
  generalize ha : ext_chart_at I z z + r/2 = a,
  have au : a ∈ u, {
    rw ←ha, apply ru, simp only [metric.mem_ball, complex.dist_eq, add_sub_cancel'],
    simp only [map_div₀, complex.abs_of_real, abs_of_pos rp, complex.abs_two], exact half_lt_self rp,
  },
  use (ext_chart_at I z).symm a, simp only [mem_inter_iff, mem_preimage] at au,
  use ts au.2,
  rw ←(local_equiv.inj_on _).ne_iff ((ext_chart_at I z).map_target au.1) (mem_ext_chart_source I z),
  rw [local_equiv.right_inv _ au.1, ←ha],
  simp only [ne.def, add_right_eq_self, div_eq_zero_iff, complex.of_real_eq_zero, bit0_eq_zero, one_ne_zero,
    or_false, ne_of_gt rp, not_false_iff],
end

-- Positive order means nontrivial
lemma nontrivial_holomorphic_at_of_order {f : ℂ → ℂ} {z : ℂ} (fa : analytic_at ℂ f z) (h : order_at f z ≠ 0)
    : nontrivial_holomorphic_at f z := begin
  use fa.holomorphic_at I I, contrapose h, simp only [filter.not_frequently, not_not] at ⊢ h,
  have fp : has_fpower_series_at f (const_formal_multilinear_series ℂ ℂ (f z)) z :=
    has_fpower_series_at_const.congr (filter.eventually_eq.symm h),
  simp only [fp.order_at_unique], by_contradiction p0,
  have b := formal_multilinear_series.apply_order_ne_zero' p0,
  simp only [const_formal_multilinear_series_apply p0, ne.def, eq_self_iff_true, not_true] at b,
  exact b,
end

-- nontrivial_analytic_on ℂ → nontrivial_holomorphic_on
lemma nontrivial_analytic_on.nontrivial_holomorphic_on {f : ℂ → ℂ} {s : set ℂ}
    (n : nontrivial_analytic_on f s) : nontrivial_holomorphic_on f s := λ z m, {
  holomorphic_at := (n.analytic_on z m).holomorphic_at I I,
  nonconst := n.nonconst z m,
}

-- pow is nontrivial
lemma nontrivial_holomorphic_at_pow {d : ℕ} (d0 : d > 0) {z : ℂ} : nontrivial_holomorphic_at (λ z, z^d) z :=
  (pow_nontrivial d0).nontrivial_holomorphic_on z (mem_univ _)

-- nontriviality is invariant to powers
lemma nontrivial_holomorphic_at.pow_iff {f : S → ℂ} {z : S} {d : ℕ} (fa : holomorphic_at I I f z) (d0 : d > 0)
    : nontrivial_holomorphic_at (λ z, (f z)^d) z ↔ nontrivial_holomorphic_at f z := begin
  refine ⟨_, (nontrivial_holomorphic_at_pow d0).comp⟩,
  have pa : holomorphic_at I I (λ z, z^d) (f z) := holomorphic_at.pow holomorphic_at_id,
  intro h, refine (nontrivial_holomorphic_at.anti _ pa fa).2, exact h,
end

-- nontriviality is local
lemma nontrivial_holomorphic_at.congr {f g : S → T} {z : S} (n : nontrivial_holomorphic_at f z)
    (e : f =ᶠ[𝓝 z] g) : nontrivial_holomorphic_at g z := begin
  use n.holomorphic_at.congr e,
  refine n.nonconst.mp (e.mp (eventually_of_forall (λ w ew n, _))),
  rwa [←ew, ←e.self],
end

section eq_of_locally_eq
variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
variables {F : Type} [normed_add_comm_group F] [normed_space ℂ F] [complete_space F]
variables {A : Type} [topological_space A] {J : model_with_corners ℂ E A} [model_with_corners.boundaryless J]
variables {B : Type} [topological_space B] {K : model_with_corners ℂ F B} [model_with_corners.boundaryless K]
variables {M : Type} [topological_space M] [complex_manifold J M]
variables {N : Type} [topological_space N] [complex_manifold K N]

-- If two holomorphic functions are equal locally, they are equal on preconnected sets.
-- This is a manifold version of analytic_on.eq_on_of_preconnected_of_eventually_eq.
lemma holomorphic_on.eq_of_locally_eq {f g : M → N} [t2_space N] {s : set M}
    (fa : holomorphic_on J K f s) (ga : holomorphic_on J K g s)
    (sp : is_preconnected s) (e : ∃ x, x ∈ s ∧ f =ᶠ[𝓝 x] g)
    : f =ᶠ[𝓝ˢ s] g := begin
  set t := {x | f =ᶠ[𝓝 x] g},
  suffices h : s ⊆ interior t, {
    simp only [subset_interior_iff_mem_nhds_set, ←filter.eventually_iff] at h,
    exact h.mp (eventually_of_forall (λ _ e, e.self)),
  },
  apply sp.relative_clopen, {
    exact e,
  }, {
    rintros x ⟨xs,xt⟩, rw mem_interior_iff_mem_nhds, exact xt.eventually_nhds,
  }, {
    rintros x ⟨xs,xt⟩, rw mem_closure_iff_frequently at xt,
    have ex' : ∃ᶠ y in 𝓝 x, f y = g y := xt.mp (eventually_of_forall (λ _ e, e.self)),
    have ex : f x = g x :=
      tendsto_nhds_unique_of_frequently_eq (fa _ xs).continuous_at (ga _ xs).continuous_at ex',
    generalize hd : (λ y : E, ext_chart_at K (f x) (f ((ext_chart_at J x).symm y)) -
      ext_chart_at K (g x) (g ((ext_chart_at J x).symm y))) = d,
    generalize hz : ext_chart_at J x x = z,
    suffices h : d =ᶠ[𝓝 z] 0, {
      simp only [←hz, ←ext_chart_at_map_nhds' J x, filter.eventually_map, filter.eventually_eq] at h,
      refine h.mp (((is_open_ext_chart_at_source J x).eventually_mem (mem_ext_chart_source J x)).mp _),
      apply ((fa _ xs).continuous_at.eventually_mem (is_open_ext_chart_at_source _ _)
        (mem_ext_chart_source K (f x))).mp,
      apply ((ga _ xs).continuous_at.eventually_mem (is_open_ext_chart_at_source _ _)
        (mem_ext_chart_source K (g x))).mp,
      refine eventually_of_forall (λ y gm fm m e, _),
      rw [←hd, pi.zero_apply, sub_eq_zero, (ext_chart_at J x).left_inv m, ex] at e,
      rw ex at fm, exact (ext_chart_at K (g x)).inj_on fm gm e,
    },
    have d0 : ∃ᶠ y in 𝓝 z, d =ᶠ[𝓝 y] 0, {
      rw ←hz,  
      have xt' : ∃ᶠ y in 𝓝 x, (ext_chart_at J x).symm (ext_chart_at J x y) ∈ t, {
        apply xt.mp,
        apply ((is_open_ext_chart_at_source J x).eventually_mem (mem_ext_chart_source J x)).mp,
        refine eventually_of_forall (λ y m e, _), rw (ext_chart_at J x).left_inv m, exact e,
      },
      apply (@filter.tendsto.frequently _ _ _ _ _
        (λ y, (ext_chart_at J x).symm y ∈ t) (continuous_at_ext_chart_at J x) xt').mp,
      apply ((ext_chart_at_open_target J x).eventually_mem (mem_ext_chart_target J x)).mp,
      refine eventually_of_forall (λ y m e, _), simp only at e,
      apply ((continuous_at_ext_chart_at_symm'' J x m).eventually e).mp,
      refine eventually_of_forall (λ z e, _), simp only at e,
      simp only [←hd, pi.zero_apply, sub_eq_zero, ex, e],
    },
    have da : analytic_at ℂ d z, { rw [←hd, ←hz], exact (fa _ xs).2.sub (ga _ xs).2 },
    clear hd ex ex' xt t e fa ga f g xs hz x sp,  -- Forget about manifolds
    rcases da.ball with ⟨r,rp,da⟩,
    rcases filter.frequently_iff.mp d0 (is_open_ball.mem_nhds (mem_ball_self rp)) with ⟨z0,m0,ze⟩,
    refine eventually_nhds_iff.mpr ⟨_, _, is_open_ball, mem_ball_self rp⟩,
    exact da.eq_on_zero_of_preconnected_of_eventually_eq_zero (convex_ball _ _).is_preconnected m0 ze,
  },
end

end eq_of_locally_eq

-- The parameterized open mapping theorem
-- mathlib has the open mapping theorem for ℂ → ℂ, but nothing prevents the constants from collapsing
-- if we have a parameterized function ℂ → ℂ → ℂ.  Fortunately, they also expose the effective version
-- as diff_cont_on_cl.ball_subset_image_closed_ball, and we can use that to prove a nicely parameterized
-- version.

-- Nontriviality at a point from nontriviality on a sphere
lemma nontrivial_local_of_global {f : ℂ → ℂ} {z : ℂ} {e r : ℝ}
    (fa : analytic_on ℂ f (closed_ball z r)) (rp : 0 < r) (ep : 0 < e)
    (ef : ∀ w, w ∈ sphere z r → e ≤ ‖f w - f z‖) : nontrivial_holomorphic_at f z := begin
  have fh : holomorphic_on I I f (closed_ball z r) := λ _ m, (fa _ m).holomorphic_at I I,
  have zs : z ∈ closed_ball z r := mem_closed_ball_self (le_of_lt rp),
  use fh _ zs,
  contrapose ef,
  simp only [filter.not_frequently, not_not] at ef,
  simp only [not_forall, not_le],
  have zrs : z + r ∈ sphere z r :=
    by simp only [mem_sphere, complex.dist_eq, add_sub_cancel', complex.abs_of_real, abs_of_pos rp],
  use [z + r, zrs],
  simp only [fh.const_of_locally_const' zs (convex_closed_ball z r).is_preconnected ef (z + r)
    (metric.sphere_subset_closed_ball zrs), sub_self, norm_zero, ep],
end
 
-- First, the effective version mapped to parameterized space (losing some effectiveness)
lemma analytic_on.ball_subset_image_closed_ball_param {f : ℂ → ℂ → ℂ} {c z : ℂ} {e r : ℝ} {u : set ℂ}
    (fa : analytic_on ℂ (uncurry f) (u ×ˢ closed_ball z r)) (rp : 0 < r) (ep : 0 < e) (un : u ∈ 𝓝 c)
    (ef : ∀ d, d ∈ u → ∀ w, w ∈ sphere z r → e ≤ ‖f d w - f d z‖)
    : (λ p : ℂ × ℂ, (p.1, f p.1 p.2)) '' (u ×ˢ closed_ball z r) ∈ 𝓝 (c, f c z) := begin
  have fn : ∀ d, d ∈ u → ∃ᶠ w in 𝓝 z, f d w ≠ f d z, {
    refine λ d m, (nontrivial_local_of_global (fa.in2.mono _) rp ep (ef d m)).nonconst,
    simp only [←closed_ball_prod_same, mem_prod_eq, set_of_mem_eq, (iff_true _).mpr m, true_and],
  },
  have op : ∀ d, d ∈ u → ball (f d z) (e/2) ⊆ f d '' closed_ball z r, {
    intros d du, refine diff_cont_on_cl.ball_subset_image_closed_ball _ rp (ef d du) (fn d du),
    have e : f d = uncurry f ∘ (λ w, (d,w)) := rfl, 
    rw e, apply differentiable_on.diff_cont_on_cl, apply analytic_on.differentiable_on,
    refine fa.comp (analytic_on_const.prod analytic_on_id) _,
    intros w wr, simp only [closure_ball _ (ne_of_gt rp)] at wr,
    simp only [←closed_ball_prod_same, mem_prod_eq, du, wr, true_and, du],
  },
  rcases metric.continuous_at_iff.mp (fa (c,z) (mk_mem_prod (mem_of_mem_nhds un)
    (mem_closed_ball_self (le_of_lt rp)))).continuous_at (e/4) (by bound) with ⟨s,sp,sh⟩,
  rw mem_nhds_prod_iff,
  refine ⟨u ∩ ball c s, filter.inter_mem un (metric.ball_mem_nhds c (by bound)), _⟩,
  use [ball (f c z) (e/4), metric.ball_mem_nhds _ (by bound)],
  rintros ⟨d,w⟩ m,
  simp only [mem_inter_iff, mem_prod_eq, mem_image, @mem_ball _ _ c, lt_min_iff] at m op ⊢,
  have wm : w ∈ ball (f d z) (e/2), {
    simp only [mem_ball] at ⊢ m,
    specialize @sh ⟨d,z⟩, simp only [prod.dist_eq, dist_self, function.uncurry] at sh,
    specialize sh (max_lt m.1.2 sp), rw dist_comm at sh,
    calc dist w (f d z) ≤ dist w (f c z) + dist (f c z) (f d z) : by bound
    ... < e/4 + dist (f c z) (f d z) : by bound [m.2]
    ... ≤ e/4 + e/4 : by bound [sh]
    ... = e/2 : by ring,
  },
  specialize op d m.1.1 wm,
  rcases (mem_image _ _ _).mp op with ⟨y,yr,yw⟩,
  use ⟨d,y⟩,
  simp only [mem_prod_eq, prod.ext_iff, yw, and_true, eq_self_iff_true, true_and, yr, m.1.1],
end

-- Lemma used below
lemma abs_sub_self_lt {z : ℂ} {r : ℝ} (rp : 0 < r) : abs (z - z) < r :=
  by simp [sub_self, complex.abs.map_zero, rp]

-- Next, the ineffective open mapping theorem, assuming only nontriviality (non-manifold case)
lemma nontrivial_holomorphic_at.nhds_le_map_nhds_param' {f : ℂ → ℂ → ℂ} {c z : ℂ}
    (n : nontrivial_holomorphic_at (f c) z) (fa : analytic_at ℂ (uncurry f) (c,z))
    : 𝓝 (c, f c z) ≤ filter.map (λ p : ℂ × ℂ, (p.1, f p.1 p.2)) (𝓝 (c,z)) := begin
  -- Reduce to a neighborhood of (c,z) on which f is analytic
  rw filter.le_map_iff, intros s' sn,
  generalize hs : s' ∩ {p | analytic_at ℂ (uncurry f) p} = s,
  have ss : s ⊆ s', { rw ←hs, apply inter_subset_left, },
  replace sn : s ∈ 𝓝 (c,z), { rw ←hs, exact filter.inter_mem sn fa.eventually },
  replace fa : analytic_on ℂ (uncurry f) s, { rw ←hs, apply inter_subset_right },
  refine filter.mem_of_superset _ (image_subset _ ss),
  clear ss hs s',
  rcases metric.mem_nhds_iff.mp sn with ⟨e,ep,es⟩,
  -- Find a radius within s where f c is nontrivial
  have er : ∃ r, 0 < r ∧ closed_ball (c,z) r ⊆ s ∧ f c z ∉ f c '' sphere z r, {
    have h := n.eventually_ne, contrapose h,
    simp only [not_exists, filter.not_frequently, not_not, not_and, not_exists] at h,
    simp only [filter.not_eventually, not_imp, not_not, filter.eventually_iff, metric.mem_nhds_iff,
      not_exists, not_subset, mem_set_of],
    intros r rp, specialize h (min (e/2) (r/2)) (by bound) _,
    exact trans (metric.closed_ball_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self ep))) es,
    rcases (mem_image _ _ _).mp h with ⟨w,ws,wz⟩,
    use w, refine ⟨_,_,wz⟩,
    exact metric.closed_ball_subset_ball (lt_of_le_of_lt (min_le_right _ _) (half_lt_self rp))
      (metric.sphere_subset_closed_ball ws),
    contrapose ws, simp only [not_not] at ws, simp only [ws, metric.mem_sphere, dist_self],
    exact ne_of_lt (by bound),
  },
  rcases er with ⟨r,rp,rs,fr⟩,
  -- Get a lower bound of f c '' sphere z r, then extend to a neighborhood of c
  have fc : continuous_on (λ w, ‖f c w - f c z‖) (sphere z r), {
    apply continuous_on.norm, refine continuous_on.sub _ continuous_on_const,
    apply fa.in2.continuous_on.mono, intros x xs, apply rs,
    simp only [←closed_ball_prod_same, mem_prod_eq],
    use [metric.mem_closed_ball_self (le_of_lt rp), metric.sphere_subset_closed_ball xs],
  },
  rcases fc.compact_min (is_compact_sphere _ _) (normed_space.sphere_nonempty.mpr (le_of_lt rp)) with ⟨x,xs,xm⟩,
  set e := ‖f c x - f c z‖,
  have ep : 0 < e, {
    contrapose fr, simp only [norm_pos_iff, sub_ne_zero, not_not, mem_image] at fr ⊢, use [x, xs, fr],
  },
  rcases metric.uniform_continuous_on_iff.mp ((is_compact_closed_ball _ _).uniform_continuous_on_of_continuous
    (fa.continuous_on.mono rs)) (e/4) (by bound) with ⟨t,tp,ft⟩,
  have ef : ∀ d, d ∈ ball c (min t r) → ∀ w, w ∈ sphere z r → e/2 ≤ ‖f d w - f d z‖, {
    intros d dt w wr, simp only [complex.norm_eq_abs],
    simp only [complex.dist_eq, prod.forall, mem_closed_ball, prod.dist_eq, max_le_iff, max_lt_iff,
      function.uncurry, and_imp] at ft,
    simp only [mem_ball, complex.dist_eq, lt_min_iff] at dt,
    have a1 : abs (f d w - f c w) ≤ e/4 :=
      le_of_lt (ft d w (le_of_lt dt.2) (le_of_eq wr) c w (le_of_lt (abs_sub_self_lt rp))
        (le_of_eq wr) dt.1 (abs_sub_self_lt tp)),
    have a2 : abs (f c z - f d z) ≤ e/4, {
      refine le_of_lt (ft c z (le_of_lt (abs_sub_self_lt rp)) (le_of_lt (abs_sub_self_lt rp))
        d z (le_of_lt dt.2) (le_of_lt (abs_sub_self_lt rp)) _ (abs_sub_self_lt tp)),
      rw [←neg_sub, complex.abs.map_neg], exact dt.1, 
    },
    calc abs (f d w - f d z) = abs ((f c w - f c z) + (f d w - f c w) + (f c z - f d z)) : by ring_nf
    ... ≥ abs ((f c w - f c z) + (f d w - f c w)) - abs (f c z - f d z) : by bound
    ... ≥ abs (f c w - f c z) - abs (f d w - f c w) - abs (f c z - f d z) : by bound
    ... ≥ e - e/4 - e/4 : by bound [xm wr]
    ... = e/2 : by ring,
  },
  -- Apply the partially effective parameterized open mapping theorem
  have ss : ball c (min t r) ×ˢ closed_ball z r ⊆ s, {
    refine (trans _ rs), rw ←closed_ball_prod_same, apply prod_mono_left,
    exact trans (metric.ball_subset_ball (min_le_right _ _)) metric.ball_subset_closed_ball,
  }, 
  exact filter.mem_of_superset ((fa.mono ss).ball_subset_image_closed_ball_param rp (half_pos ep)
    (metric.ball_mem_nhds _ (by bound)) ef) (image_subset _ ss),
end

-- If f : S → T is nontrivial, it is nontrivial when written in charts
lemma nontrivial_holomorphic_at.in_charts {f : S → T} {z : S} (n : nontrivial_holomorphic_at f z)
    : nontrivial_holomorphic_at (λ w, ext_chart_at I (f z) (f ((ext_chart_at I z).symm w)))
      (ext_chart_at I z z) := begin
  use n.holomorphic_at.2.holomorphic_at I I,
  have c := n.nonconst, contrapose c,
  simp only [filter.not_frequently, not_not, ←ext_chart_at_map_nhds' I z, filter.eventually_map] at c ⊢,
  apply c.mp,
  apply ((is_open_ext_chart_at_source I z).eventually_mem (mem_ext_chart_source I z)).mp,
  apply (n.holomorphic_at.continuous_at.eventually_mem (is_open_ext_chart_at_source I (f z))
    (mem_ext_chart_source I (f z))).mp,
  refine eventually_of_forall (λ w fm m fn, _),
  simp only at fm m fn,
  rw [local_equiv.left_inv _ m, local_equiv.left_inv _ (mem_ext_chart_source I z)] at fn,
  exact ((local_equiv.inj_on _).eq_iff fm (mem_ext_chart_source _ _)).mp fn,
end

-- The local open mapping theorem, manifold version.
-- This is a complex_manifold version of analytic_at.eventually_constant_or_nhds_le_map_nhds.
lemma nontrivial_holomorphic_at.nhds_eq_map_nhds {f : S → T} {z : S} (n : nontrivial_holomorphic_at f z)
    : 𝓝 (f z) = filter.map f (𝓝 z) := begin
  refine le_antisymm _ n.holomorphic_at.continuous_at,
  generalize hg : (λ x, ext_chart_at I (f z) (f ((ext_chart_at I z).symm x))) = g,
  have ga : analytic_at ℂ g (ext_chart_at I z z), { rw ←hg, exact n.holomorphic_at.2 },
  cases ga.eventually_constant_or_nhds_le_map_nhds with h h, {
    contrapose h, simp only [filter.not_eventually],
    apply n.in_charts.nonconst.mp, simp only [←hg, ne.def, imp_self, filter.eventually_true],
  }, {
    -- The open mapping theorem for g = c ∘ f ∘ c⁻¹ (with charts c) is
    --   𝓝 (g (c z)) ≤ map g (𝓝 (c z))
    -- We have
    --   map c⁻¹ (𝓝 (g (c z))) ≤ map c⁻¹ (map g (𝓝 (c z))  -- Monotonicity of map
    --   𝓝 (c⁻¹ (g (c z))) ≤ map (c' ∘ g ∘ c) (𝓝 z)        -- Charts map 𝓝 to 𝓝
    --   𝓝 (f z) ≤ map f (𝓝 z)                             -- Congruence
    simp only [←ext_chart_at_map_nhds' I z, filter.map_map] at h,
    replace h := @filter.map_mono _ _ (ext_chart_at I (f z)).symm _ _ h,
    simp only [←hg] at h, rw local_equiv.left_inv _ (mem_ext_chart_source I z) at h,
    simp only [ext_chart_at_symm_map_nhds' I (f z), filter.map_map, function.comp] at h,
    have e : (λ w, (ext_chart_at I (f z)).symm (ext_chart_at I (f z)
        (f ((ext_chart_at I z).symm (ext_chart_at I z w))))) =ᶠ[𝓝 z] f, {
      apply ((is_open_ext_chart_at_source I z).eventually_mem (mem_ext_chart_source I z)).mp,
      apply (n.holomorphic_at.continuous_at.eventually_mem (is_open_ext_chart_at_source I (f z))
        (mem_ext_chart_source I (f z))).mp,
      refine eventually_of_forall (λ w fm m, _),
      simp only [local_equiv.left_inv _ m, local_equiv.left_inv _ fm],
    },
    rw filter.map_congr e at h, exact h,
  },
end

-- Special case of filter.prod_map_map_eq where the first map is id
lemma filter.prod_map_id_map_eq {A B C : Type} {f : filter A} {g : filter B} {m : B → C}
    : f.prod (filter.map m g) = filter.map (λ p : A × B, (p.1, m p.2)) (f.prod g) :=
  @filter.prod_map_map_eq _ _ _ _ f g id m

-- The local open mapping theorem, parameterized manifold version.
lemma nontrivial_holomorphic_at.nhds_eq_map_nhds_param {f : ℂ → S → T} {c : ℂ} {z : S}
    (n : nontrivial_holomorphic_at (f c) z) (fa : holomorphic_at II I (uncurry f) (c,z))
    : 𝓝 (c, f c z) = filter.map (λ p : ℂ × S, (p.1, f p.1 p.2)) (𝓝 (c,z)) := begin
  refine le_antisymm _ (continuous_at_fst.prod fa.continuous_at),
  generalize hg : (λ e x, ext_chart_at I (f c z) (f e ((ext_chart_at I z).symm x))) = g,
  have ga : analytic_at ℂ (uncurry g) (c, ext_chart_at I z z), { rw ←hg, exact (holomorphic_at_iff.mp fa).2 },
  have gn : nontrivial_holomorphic_at (g c) (ext_chart_at I z z), { rw ←hg, exact n.in_charts },
  have h := gn.nhds_le_map_nhds_param' ga,
  -- We follow the 𝓝 ≤ 𝓝 argument of nontrivial_holomorphic_at.nhds_le_map_nhds 
  -- above, but a bit more complicated due to the parameterization.
  simp only [nhds_prod_eq, ←ext_chart_at_map_nhds' I z, filter.map_map, filter.prod_map_id_map_eq,
    function.comp] at h,
  replace h := @filter.map_mono _ _ (λ p : ℂ × ℂ, (p.1, (ext_chart_at I (f c z)).symm p.2)) _ _ h,
  simp only [←hg] at h, rw local_equiv.left_inv _ (mem_ext_chart_source I z) at h,
  simp only [←filter.prod_map_id_map_eq, ext_chart_at_symm_map_nhds' I (f c z), filter.map_map,
    function.comp] at h,
  simp only [←nhds_prod_eq] at h,
  have e : (λ p : ℂ × S, (p.1, (ext_chart_at I (f c z)).symm (ext_chart_at I (f c z)
      (f p.1 ((ext_chart_at I z).symm (ext_chart_at I z p.2)))))) =ᶠ[𝓝 (c,z)]
      (λ p : ℂ × S, (p.1, f p.1 p.2)), {
    clear h,
    apply ((is_open_ext_chart_at_source II (c,z)).eventually_mem (mem_ext_chart_source II (c,z))).mp,
    apply (fa.continuous_at.eventually_mem (is_open_ext_chart_at_source I (f c z))
      (mem_ext_chart_source I (f c z))).mp,
    apply eventually_of_forall, rintros ⟨e,w⟩ fm m,
    simp only [uncurry, ext_chart_at_prod, local_equiv.prod_source, mem_prod_eq] at fm m,
    simp only [local_equiv.left_inv _ m.2, local_equiv.left_inv _ fm],
  },
  rw filter.map_congr e at h, exact h,
end

end nontrivial

-- Continuation of a functional equation from an open convex set to its closure
section continuation
variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
variables {p : (E → S) → E → Prop} {s : set E} {f : E → S} {z : E}

-- Everything we need to holomorphically continue from s to closure s
--   p f x means f is a valid germ at x
structure base (p : (E → S) → E → Prop) (s : set E) (f : E → S) : Prop :=
  (convex : convex ℝ s)
  (compact : is_compact (closure s))
  (congr : ∀ {f g x}, p f x → f =ᶠ[𝓝 x] g → p g x)
  (start : ∀ᶠ x in 𝓝ˢ s, p f x)
  (point : ∀ {x}, x ∈ closure s → ∃ g, (∀ᶠ z in 𝓝 x, p g z) ∧ (∃ᶠ z in 𝓝 x, z ∈ s ∧ g z = f z))
  (unique : ∀ {f0 f1 : E → S} {t : set E}, is_open t → is_preconnected t →
    (∀ x, x ∈ t → p f0 x) → (∀ x, x ∈ t → p f1 x) → (∃ x, x ∈ t ∧ f0 x = f1 x) → eq_on f0 f1 t)

-- Choose a ball around each x ∈ closure s with an associated defined g
lemma base.ball (b : base p s f) (x : closure s) : ∃ g r, 0 < r ∧
      (∀ z, z ∈ ball (x : E) r → p g z) ∧ g =ᶠ[𝓝ˢ (s ∩ ball (x : E) r)] f := begin
  rcases x with ⟨x,m⟩, simp only [subtype.coe_mk],
  rcases b.point m with ⟨g,pg,e⟩,
  rcases metric.eventually_nhds_iff_ball.mp pg with ⟨r,rp,pg⟩,
  rcases filter.frequently_iff.mp e (metric.ball_mem_nhds _ rp) with ⟨y,yb,ys,e⟩,
  use [g, r, rp, λ z zr, pg z zr],
  simp only [filter.eventually_eq, filter.eventually_iff, mem_nhds_set_iff_forall],
  rintros z ⟨zs,zr⟩, simp only [←filter.eventually_iff],
  have n : {z | p g z ∧ p f z} ∈ 𝓝ˢ (s ∩ ball x r), {
    refine filter.inter_mem _ _,
    exact nhds_set_mono (inter_subset_right _ _) (filter.mem_of_superset (mem_nhds_set_self is_open_ball) pg),
    exact nhds_set_mono (inter_subset_left _ _) b.start,
  },
  rcases local_preconnected_nhds_set (b.convex.inter (convex_ball _ _)).is_preconnected n with ⟨u,uo,iu,up,uc⟩,
  have eq := b.unique uo uc (λ _ m, (up m).1) (λ _ m, (up m).2) ⟨y,iu ⟨ys,yb⟩,e⟩,
  exact eq.eventually_eq_of_mem (uo.mem_nhds (iu ⟨zs,zr⟩)),
end
def base.g (b : base p s f) (x : closure s) : E → S := some (b.ball x)
def base.r (b : base p s f) (x : closure s) : ℝ := some (some_spec (b.ball x))
lemma base.rp (b : base p s f) (x : closure s) : 0 < b.r x := (some_spec (some_spec (b.ball x))).1
lemma base.gp (b : base p s f) (x : closure s) (m : z ∈ ball (x : E) (b.r x)) : p (b.g x) z :=
  (some_spec (some_spec (b.ball x))).2.1 _ m
lemma base.gf (b : base p s f) (x : closure s) : b.g x =ᶠ[𝓝ˢ (s ∩ ball (x : E) (b.r x))] f :=
  (some_spec (some_spec (b.ball x))).2.2

-- Choose a finite subcover of the balls
lemma base.exists_cover (b : base p s f)
    : ∃ c : finset (closure s), closure s ⊆ ⋃ x (h : x ∈ c), ball (x : E) (b.r x) := begin
  refine b.compact.elim_finite_subcover (λ x : closure s, ball (x : E) (b.r x)) (λ _, is_open_ball) _,
  intros x m, exact mem_Union_of_mem ⟨x,m⟩ (mem_ball_self (b.rp ⟨x,m⟩)),
end
def base.c (b : base p s f) : finset (closure s) := some b.exists_cover
def base.t (b : base p s f) : set E := ⋃ x (h : x ∈ b.c), ball (x : E) (b.r x)
def base.y (b : base p s f) (m : z ∈ b.t) : closure s := some (mem_Union.mp m)
lemma base.yt (b : base p s f) (m : z ∈ b.t) : z ∈ ball (b.y m : E) (b.r (b.y m)) := begin
  simp only [base.t, base.y, mem_Union₂, mem_Union] at m ⊢, exact some_spec (some_spec m),
end
lemma base.ot (b : base p s f) : is_open b.t := is_open_Union (λ _, is_open_Union (λ _, is_open_ball))
lemma base.cover (b : base p s f) : closure s ⊆ b.t := some_spec b.exists_cover

-- Given two intersecting balls centered in closure s, their intersection touches s
lemma convex.inter_ball (c : convex ℝ s) (x0 x1 : closure s) {r0 r1 : ℝ}
    (r0p : 0 < r0) (r1p : 0 < r1) (ne : ∃ z, z ∈ ball (x0 : E) r0 ∩ ball (x1 : E) r1)
    : ∃ w, w ∈ s ∩ ball (x0 : E) r0 ∩ ball (x1 : E) r1 := begin
  rcases x0 with ⟨x0,m0⟩, rcases x1 with ⟨x1,m1⟩, simp only [subtype.coe_mk],
  have x01 : ‖x1 - x0‖ < r0 + r1, {
    rcases ne with ⟨z,m0,m1⟩, simp only [mem_ball, dist_eq_norm] at m0 m1,
    calc ‖x1 - x0‖ = ‖z - x0 - (z - x1)‖ : by abel
    ... ≤ ‖z - x0‖ + ‖(z - x1)‖ : norm_sub_le _ _
    ... < r0 + r1 : add_lt_add m0 m1,
  },
  have sub : ∀ (x : E) {a b : ℝ} (ap : 0 < a) (bp : 0 < b), (a / (a + b)) • x - x = -((b / (a + b)) • x), {
    intros x a b ap bp, have rnz := ne_of_gt (add_pos ap bp),
    calc (a / (a + b)) • x - x = (a / (a + b) - (a + b) / (a + b)) • x
        : by simp only [one_smul, sub_smul, div_self rnz]
    ... = -((b / (a + b)) • x) : by rw [←sub_div, sub_add_cancel', neg_div, neg_smul],
  },
  have le : ∀ {a : ℝ} (ap : 0 < a), a / (r0 + r1) * ‖x1 - x0‖ < a, {
    intros a ap, apply lt_of_lt_of_le (mul_lt_mul_of_pos_left x01 (div_pos ap (add_pos r0p r1p))),
    rw div_mul_cancel _ (ne_of_gt (add_pos r0p r1p)),
  },
  have e : ∀ᶠ p : E × E in 𝓝 (x0,x1), (r1/(r0+r1))•p.1 + (r0/(r0+r1))•p.2 ∈ ball x0 r0 ∩ ball x1 r1, {
    refine continuous_at.eventually_mem _ (is_open_ball.inter is_open_ball) _,
    apply continuous.continuous_at, continuity,
    simp only [mem_inter_iff, mem_ball, dist_eq_norm, ←sub_add_eq_add_sub _ x0 _, add_sub_assoc _ _ x1],
    nth_rewrite 0 add_comm r0 r1, simp only [sub _ r0p r1p, sub _ r1p r0p],
    simp only [add_comm r1 r0, neg_add_eq_sub, ←sub_eq_add_neg, ←smul_sub, norm_smul, real.norm_eq_abs,
      abs_div, abs_of_pos r0p, abs_of_pos r1p, abs_of_pos (add_pos r0p r1p), norm_sub_rev (x0 : E) x1],
    use [le r0p, le r1p],
  },
  have f : ∃ᶠ p : E × E in 𝓝 (x0,x1), p.1 ∈ s ∧ p.2 ∈ s, {
    simp only [nhds_prod_eq], rw @prod.frequently _ _ _ _ (λ x, x ∈ s) (λ x, x ∈ s),
    use [mem_closure_iff_frequently.mp m0, mem_closure_iff_frequently.mp m1],
  },
  rcases (f.and_eventually e).exists with ⟨⟨z0,z1⟩,⟨m0,m1⟩,m⟩,
  refine ⟨_,⟨_,m.1⟩,m.2⟩, 
  apply c m0 m1, bound, bound,
  simp only [←add_div, add_comm r1 r0, div_self (ne_of_gt (add_pos r0p r1p))],
end

-- Define our full continuation f
def base.f (b : base p s f) : E → S := λ z, @dite _ (z ∈ b.t) (classical.dec _) (λ m, b.g (b.y m) z) (λ _, f z)
lemma base.fg (b : base p s f) (x : closure s) : eq_on b.f (b.g x) (b.t ∩ ball (x : E) (b.r x)) := begin
  rintros z ⟨zt,m⟩, simp only [base.f, zt, dif_pos],
  refine b.unique (is_open_ball.inter is_open_ball) ((convex_ball _ _).inter (convex_ball _ _)).is_preconnected
      (λ _ m, b.gp _ (inter_subset_left _ _ m)) (λ _ m, b.gp _ (inter_subset_right _ _ m)) _ ⟨b.yt zt,m⟩,
  rcases b.convex.inter_ball (b.y zt) x (b.rp _) (b.rp _) ⟨_,⟨b.yt zt,m⟩⟩ with ⟨w,m⟩,
  exact ⟨w, ⟨m.1.2,m.2⟩, trans ((b.gf _).self_set _ ⟨m.1.1,m.1.2⟩) ((b.gf x).self_set _ ⟨m.1.1,m.2⟩).symm⟩,
end
lemma base.ff (b : base p s f) : b.f =ᶠ[𝓝ˢ s] f := begin
  simp only [filter.eventually_eq, filter.eventually_iff, mem_nhds_set_iff_forall],
  intros z m, simp only [←filter.eventually_iff],
  set x : closure s := ⟨z, subset_closure m⟩,
  have zs : z ∈ ball (x : E) (b.r x) := mem_ball_self (b.rp x),
  have fg := (b.fg x).eventually_eq_of_mem ((b.ot.inter is_open_ball).mem_nhds ⟨b.cover (subset_closure m),zs⟩),
  exact fg.trans ((b.gf x).filter_mono (nhds_le_nhds_set ⟨m,zs⟩)),
end
lemma base.fp (b : base p s f) : ∀ᶠ z in 𝓝ˢ (closure s), p b.f z := begin
  apply filter.eventually_of_mem (b.ot.mem_nhds_set.mpr b.cover),
  intros x m, refine b.congr (b.gp (b.y m) (b.yt m)) _,
  exact ((b.fg _).eventually_eq_of_mem ((b.ot.inter is_open_ball).mem_nhds ⟨m,b.yt m⟩)).symm,
end

end continuation
