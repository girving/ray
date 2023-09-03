-- Complex manifolds

import analysis.analytic.basic
import analysis.complex.basic
import analysis.locally_convex.with_seminorms
import data.complex.basic
import geometry.manifold.charted_space
import geometry.manifold.cont_mdiff
import geometry.manifold.cont_mdiff_mfderiv
import geometry.manifold.local_invariant_properties
import geometry.manifold.mfderiv
import geometry.manifold.smooth_manifold_with_corners
import geometry.manifold.vector_bundle.tangent

import analytic
import holomorphic

open charted_space (chart_at)
open filter (eventually_of_forall)
open function (uncurry)
open set
open_locale manifold topology
noncomputable theory

-- The groupoid of analytic functions H → H (interpreted through I).  We require boundaryless I.
def analytic_groupoid {E H : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    [topological_space H] (I : model_with_corners ℂ E H) [I.boundaryless]
    : structure_groupoid H := pregroupoid.groupoid {
  property := λ f s, analytic_on ℂ (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
  comp := begin
    intros f g u v fa ga uo vo uvo,
    refine (ga.comp (fa.mono _) _).congr _ _, {
      exact set.inter_subset_inter_left _ (set.preimage_mono (set.inter_subset_left u _)),
    }, {
      intros x m, simp only [set.mem_inter_iff, set.mem_preimage, set.mem_range] at m,
      simp only [m.1.2, function.comp_app, set.mem_inter_iff, set.mem_preimage, model_with_corners.left_inv,
        set.mem_range_self, and_true],
    }, {
      simp only [model_with_corners.boundaryless.range_eq_univ, set.inter_univ],
      exact uvo.preimage I.continuous_symm,
    }, {
      intros x m, simp only [function.comp_app, model_with_corners.left_inv],
    },
  end,
  id_mem := begin
    refine analytic_on_id.congr _ _,
    simp only [model_with_corners.boundaryless.range_eq_univ, set.inter_univ, set.preimage_univ, is_open_univ],
    simp only [function.comp, set.preimage_univ, set.univ_inter, set.mem_range, id.def, forall_exists_index,
      forall_apply_eq_imp_iff', model_with_corners.left_inv, eq_self_iff_true, implies_true_iff],
  end,
  locality := begin
    intros f s o h x m, simp only [set.mem_inter_iff, set.mem_preimage, set.mem_range] at m,
    rcases h (I.symm x) m.1 with ⟨v,vo,xv,a⟩, apply a,
    simp only [set.mem_inter_iff, set.mem_preimage, set.mem_range],
    use [m.1, xv, m.2],
  end,
  congr := begin
    intros f g s o e a, simp only [model_with_corners.boundaryless.range_eq_univ, set.inter_univ] at ⊢ a,
    apply a.congr (o.preimage I.continuous_symm),
    intros x m, simp only [set.mem_preimage] at m, simp only [function.comp, e _ m],
  end,
}

@[class] structure complex_manifold
    {E H : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [topological_space H]
    (I : model_with_corners ℂ E H) [I.boundaryless] (M : Type) [topological_space M]
    extends charted_space H M, has_groupoid M (analytic_groupoid I)

-- Normed spaces are complex manifolds over themselves
instance complex_manifold.self {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    : complex_manifold (model_with_corners_self ℂ E) E := complex_manifold.mk

-- The product of two analytic local homeomorphisms is analytic
lemma analytic_groupoid_prod
    {E A : Type} [normed_add_comm_group E] [normed_space ℂ E] [topological_space A] [complete_space E]
    {F B : Type} [normed_add_comm_group F] [normed_space ℂ F] [topological_space B] [complete_space F]
    {I : model_with_corners ℂ E A} {J : model_with_corners ℂ F B} [I.boundaryless] [J.boundaryless]
    {f : local_homeomorph A A} {g : local_homeomorph B B}
    (fa : f ∈ analytic_groupoid I) (ga : g ∈ analytic_groupoid J)
    : f.prod g ∈ analytic_groupoid (I.prod J) := begin
  cases fa with fa fas,
  cases ga with ga gas,
  simp only [analytic_groupoid, mem_groupoid_of_pregroupoid, model_with_corners.boundaryless.range_eq_univ,
    set.inter_univ, local_homeomorph.prod_source, model_with_corners_prod_coe_symm, set.preimage_prod_map_prod,
    local_homeomorph.prod_target, function.comp, local_homeomorph.prod_apply, local_homeomorph.prod_symm_apply,
    model_with_corners.prod_apply, prod.map_fst, prod.map_snd] at fa fas ga gas ⊢,
  constructor, {
    exact (fa.comp analytic_on_fst (λ _ m, (set.mem_prod.mp m).1)).prod
          (ga.comp analytic_on_snd (λ _ m, (set.mem_prod.mp m).2)),
  }, {
    exact (fas.comp analytic_on_fst (λ _ m, (set.mem_prod.mp m).1)).prod
          (gas.comp analytic_on_snd (λ _ m, (set.mem_prod.mp m).2)),
  },
end 

-- M × N is a complex manifold if M and N are
instance complex_manifold.prod
    {E A : Type} [normed_add_comm_group E] [normed_space ℂ E] [topological_space A] [complete_space E]
    {F B : Type} [normed_add_comm_group F] [normed_space ℂ F] [topological_space B] [complete_space F]
    {I : model_with_corners ℂ E A} {J : model_with_corners ℂ F B} [I.boundaryless] [J.boundaryless]
    {M : Type} [topological_space M] [complex_manifold I M]
    {N : Type} [topological_space N] [complex_manifold J N]
    : complex_manifold (I.prod J) (M × N) := {
  compatible := begin
    rintros f g ⟨f1, f2, hf1, hf2, rfl⟩ ⟨g1, g2, hg1, hg2, rfl⟩,
    rw [local_homeomorph.prod_symm, local_homeomorph.prod_trans],
    have h1 := has_groupoid.compatible (analytic_groupoid I) hf1 hg1,
    have h2 := has_groupoid.compatible (analytic_groupoid J) hf2 hg2,
    exact analytic_groupoid_prod h1 h2,
  end
}

-- Complex manifolds are smooth manifolds
instance complex_manifold.smooth_manifold_with_corners
    {E A : Type} [normed_add_comm_group E] [normed_space ℂ E] [topological_space A] [complete_space E]
    {I : model_with_corners ℂ E A} [I.boundaryless]
    {M : Type} [topological_space M] [cm : complex_manifold I M]
    : smooth_manifold_with_corners I M := begin
  apply smooth_manifold_with_corners_of_cont_diff_on,
  intros f g fa ga,
  have fga := cm.compatible fa ga,
  simp only [analytic_groupoid, mem_groupoid_of_pregroupoid] at fga,
  exact fga.1.cont_diff_on,
end

-- When ext_chart_at = refl
@[class] structure ext_chart_eq_refl {E H : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    [topological_space H] (I : model_with_corners ℂ E H) [I.boundaryless] [complex_manifold I E] :=
  (eq_refl : ∀ x, ext_chart_at I x = local_equiv.refl E)

@[simp] lemma ext_chart_at_eq_refl {E H : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    [topological_space H] {I : model_with_corners ℂ E H} [I.boundaryless] [complex_manifold I E]
    [e : ext_chart_eq_refl I] (x : E) : ext_chart_at I x = local_equiv.refl E := e.eq_refl x

-- ext_chart_at = refl for E over E
instance ext_chart_eq_refl_self {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    : ext_chart_eq_refl (model_with_corners_self ℂ E) := ⟨
  by simp only [local_homeomorph.singleton_charted_space_chart_at_eq, local_homeomorph.refl_local_equiv,
    local_equiv.refl_source, forall_const, ext_chart_at, local_homeomorph.extend,
    model_with_corners_self_local_equiv, local_equiv.refl_trans]⟩

-- ext_chart_at = refl extends to products 
instance ext_chart_eq_refl_prod 
    {E A : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [topological_space A]
    {F B : Type} [normed_add_comm_group F] [normed_space ℂ F] [complete_space F] [topological_space B]
    (I : model_with_corners ℂ E A) (J : model_with_corners ℂ F B) [I.boundaryless] [J.boundaryless]
    [complex_manifold I E] [ext_chart_eq_refl I] [complex_manifold J F] [ext_chart_eq_refl J]
    : ext_chart_eq_refl (I.prod J) :=
  ⟨λ x, by simp_rw [ext_chart_at_prod, ext_chart_at_eq_refl, local_equiv.refl_prod_refl]⟩

-- Charts are analytic w.r.t. themselves.
-- This lemma helps when proving particular spaces are complex manifolds.
lemma ext_chart_at_self_analytic
    {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
    {M : Type} [topological_space M] (f : local_homeomorph M E)
    : analytic_on ℂ
        (𝓘(ℂ,E) ∘ ⇑(f.symm.trans f) ∘ ⇑(𝓘(ℂ,E).symm))
        (𝓘(ℂ,E).symm ⁻¹' (f.symm.trans f).to_local_equiv.source ∩ set.range 𝓘(ℂ,E)) := begin
  apply @analytic_on.congr _ _ _ _ _ _ _ _ _ _ (λ z, z), exact analytic_on_id, {
    simp only [model_with_corners_self_coe_symm, local_homeomorph.trans_to_local_equiv,
      local_homeomorph.symm_to_local_equiv, local_equiv.trans_source, local_equiv.symm_source,
      local_homeomorph.coe_coe_symm, set.preimage_id_eq, id.def, model_with_corners_self_coe, set.range_id,
      set.inter_univ],
    exact f.preimage_open_of_open_symm f.open_source,
  }, {
    intros x m, simp only [function.comp, model_with_corners_self_coe, model_with_corners_self_coe_symm, id,
      set.range_id, set.inter_univ, set.preimage_id, local_homeomorph.coe_trans,
      local_homeomorph.trans_source, set.mem_inter_iff] at ⊢ m,
    rw f.right_inv m.1,
  },
  repeat { apply_instance },
end

variables {E A : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [topological_space A]
variables {F B : Type} [normed_add_comm_group F] [normed_space ℂ F] [complete_space F] [topological_space B]
variables {G C : Type} [normed_add_comm_group G] [normed_space ℂ G] [complete_space G] [topological_space C]
variables {H D : Type} [normed_add_comm_group H] [normed_space ℂ H] [complete_space H] [topological_space D]
variables {M : Type} {I : model_with_corners ℂ E A} [topological_space M]
variables {N : Type} {J : model_with_corners ℂ F B} [topological_space N]
variables {O : Type} {K : model_with_corners ℂ G C} [topological_space O]
variables {P : Type} {L : model_with_corners ℂ H D} [topological_space P]
variables [model_with_corners.boundaryless I] [complex_manifold I M]
variables [model_with_corners.boundaryless J] [complex_manifold J N]
variables [model_with_corners.boundaryless K] [complex_manifold K O]
variables [model_with_corners.boundaryless L] [complex_manifold L P]

-- Holomorphic at a point
def holomorphic_at (I : model_with_corners ℂ E A) (J : model_with_corners ℂ F B) [I.boundaryless] [J.boundaryless]
    {M N : Type} [topological_space M] [complex_manifold I M] [topological_space N] [complex_manifold J N]
    (f : M → N) (x : M) :=
  charted_space.lift_prop_at (λ f _ x, analytic_at ℂ (J ∘ f ∘ I.symm) (I x)) f x

-- Holomorphic on a set
def holomorphic_on (I : model_with_corners ℂ E A) (J : model_with_corners ℂ F B) [I.boundaryless] [J.boundaryless]
    {M N : Type} [topological_space M] [complex_manifold I M] [topological_space N] [complex_manifold J N]
    (f : M → N) (s : set M) := ∀ x, x ∈ s → holomorphic_at I J f x

-- Holomorphic everywhere
def holomorphic (I : model_with_corners ℂ E A) (J : model_with_corners ℂ F B) [I.boundaryless] [J.boundaryless]
    {M N : Type} [topological_space M] [complex_manifold I M] [topological_space N] [complex_manifold J N]
    (f : M → N) := ∀ x, holomorphic_at I J f x

-- Holomorphic_on is monotonic
lemma holomorphic_on.mono {f : M → N} {s t : set M} (fa : holomorphic_on I J f s) (ts : t ⊆ s)
    : holomorphic_on I J f t := λ _ m, fa _ (ts m) 

-- Functions are holomorphic_at iff they are ext_chart-analytic_at
lemma holomorphic_at_iff {f : M → N} {x : M} : holomorphic_at I J f x ↔ continuous_at f x ∧
    analytic_at ℂ (ext_chart_at J (f x) ∘ f ∘ (ext_chart_at I x).symm) (ext_chart_at I x x) :=
  by simp only [holomorphic_at, charted_space.lift_prop_at_iff, ext_chart_at, local_homeomorph.extend_coe,
    local_homeomorph.extend_coe_symm, function.comp]

-- Functions are holomorphic iff they are ext_chart-analytic
lemma holomorphic_iff {f : M → N} : holomorphic I J f ↔ continuous f ∧ ∀ x : M, 
        analytic_at ℂ (ext_chart_at J (f x) ∘ f ∘ (ext_chart_at I x).symm) (ext_chart_at I x x) := begin
  simp only [holomorphic, holomorphic_at_iff, continuous_iff_continuous_at], exact forall_and_distrib,
end

-- Holomorphic functions are continuous
lemma holomorphic_at.continuous_at {f : M → N} {x : M} (h : holomorphic_at I J f x) : continuous_at f x :=
  (holomorphic_at_iff.mp h).1
lemma holomorphic.continuous {f : M → N} (h : holomorphic I J f) : continuous f := (holomorphic_iff.mp h).1
lemma holomorphic_at.continuous_at' (I : model_with_corners ℂ E A) (J : model_with_corners ℂ F B)
  [I.boundaryless] [J.boundaryless]
  {M N : Type} [topological_space M] [complex_manifold I M] [topological_space N] [complex_manifold J N]
  {f : M → N} {x : M} (h : holomorphic_at I J f x) : continuous_at f x := h.continuous_at
lemma holomorphic_on.continuous_on {f : M → N} {s : set M} (h : holomorphic_on I J f s)
    : continuous_on f s := λ x m, (h x m).continuous_at.continuous_within_at

-- Analytic functions are holomorphic, and vice versa
lemma analytic_at_iff_holomorphic_at [complex_manifold I E] [complex_manifold J F]
    [ext_chart_eq_refl I] [ext_chart_eq_refl J] {f : E → F} {x : E}
    : analytic_at ℂ f x ↔ holomorphic_at I J f x := begin
  simp only [holomorphic_at_iff, ext_chart_at_eq_refl, local_equiv.refl_coe, local_equiv.refl_symm,
    function.comp.right_id, function.comp.left_id, id.def, iff_and_self],
  exact analytic_at.continuous_at,
end
lemma analytic_at.holomorphic_at
    {f : E → F} {x : E} (fa : analytic_at ℂ f x)
    (I : model_with_corners ℂ E A) [I.boundaryless] [complex_manifold I E] [ext_chart_eq_refl I]
    (J : model_with_corners ℂ F B) [J.boundaryless] [complex_manifold J F] [ext_chart_eq_refl J]
    : holomorphic_at I J f x := analytic_at_iff_holomorphic_at.mp fa
lemma holomorphic_at.analytic_at
    (I : model_with_corners ℂ E A) [I.boundaryless] [complex_manifold I E] [ext_chart_eq_refl I]
    (J : model_with_corners ℂ F B) [J.boundaryless] [complex_manifold J F] [ext_chart_eq_refl J]
    {f : E → F} {x : E} : holomorphic_at I J f x → analytic_at ℂ f x := analytic_at_iff_holomorphic_at.mpr

-- Holomorphic functions compose
lemma holomorphic_at.comp {f : N → O} {g : M → N} {x : M}
    (fh : holomorphic_at J K f (g x)) (gh : holomorphic_at I J g x) : holomorphic_at I K (λ x, f (g x)) x := begin
  rw holomorphic_at_iff at ⊢ fh gh, use fh.1.comp gh.1,
  have e : ext_chart_at J (g x) (g x) = (ext_chart_at J (g x) ∘ g ∘ (ext_chart_at I x).symm) (ext_chart_at I x x) :=
    by simp only [function.comp_app, local_equiv.left_inv _ (mem_ext_chart_source I x)],
  rw e at fh, apply (fh.2.comp gh.2).congr, clear' e fh,
  simp only [function.comp],
  have m : ∀ᶠ y in 𝓝 (ext_chart_at I x x), g ((ext_chart_at I x).symm y) ∈ (ext_chart_at J (g x)).source, {
    apply continuous_at.eventually_mem_nhd, {
      apply continuous_at.comp,
      rw local_equiv.left_inv _ (mem_ext_chart_source _ _), exact gh.1,
      simp only, exact continuous_at_ext_chart_at_symm I x,
    }, {
      rw local_equiv.left_inv _ (mem_ext_chart_source _ _),
      exact ext_chart_at_source_mem_nhds _ _,
    },
  },
  refine m.mp (eventually_of_forall (λ y m, _)),
  simp_rw [local_equiv.left_inv _ m],
end
lemma holomorphic.comp {f : N → O} {g : M → N}
    (fh : holomorphic J K f) (gh : holomorphic I J g) : holomorphic I K (λ x, f (g x)) :=
  λ _, (fh _).comp (gh _)

-- Holomorphic functions compose at a point, with a separate argument for point matching
lemma holomorphic_at.comp_of_eq {f : N → O} {g : M → N} {x : M} {y : N}
    (fh : holomorphic_at J K f y) (gh : holomorphic_at I J g x) (e : g x = y)
    : holomorphic_at I K (λ x, f (g x)) x := begin
  rw ←e at fh, exact fh.comp gh, 
end

-- holomorphic_at for (f x, g x)
lemma holomorphic_at.prod {f : M → N} {g : M → O} {x : M}
    (fh : holomorphic_at I J f x) (gh : holomorphic_at I K g x)
    : holomorphic_at I (J.prod K) (λ x, (f x, g x)) x := begin
  rw holomorphic_at_iff at ⊢ fh gh, use fh.1.prod gh.1,
  refine (fh.2.prod gh.2).congr (eventually_of_forall (λ y, _)),
  funext, simp only [ext_chart_at_prod, function.comp, local_equiv.prod_coe],
end

-- holomorphic for (f x, g x)
lemma holomorphic.prod {f : M → N} {g : M → O} (fh : holomorphic I J f) (gh : holomorphic I K g)
    : holomorphic I (J.prod K) (λ x, (f x, g x)) := λ _, (fh _).prod (gh _)

-- holomorphic_at.comp for a curried function
lemma holomorphic_at.curry_comp {h : N → O → P} {f : M → N} {g : M → O} {x : M}
    (ha : holomorphic_at (J.prod K) L (uncurry h) (f x, g x))
    (fa : holomorphic_at I J f x) (ga : holomorphic_at I K g x)
    : holomorphic_at I L (λ x, h (f x) (g x)) x := begin
  have e : (λ x, h (f x) (g x)) = uncurry h ∘ (λ x, (f x, g x)) := rfl,
  rw e, exact holomorphic_at.comp ha (fa.prod ga),
end

-- holomorphic_at.curry_comp, with a separate argument for point matching
lemma holomorphic_at.curry_comp_of_eq {h : N → O → P} {f : M → N} {g : M → O} {x : M} {y : N × O}
    (ha : holomorphic_at (J.prod K) L (uncurry h) y)
    (fa : holomorphic_at I J f x) (ga : holomorphic_at I K g x)
    (e : (f x, g x) = y)
    : holomorphic_at I L (λ x, h (f x) (g x)) x := begin
  rw ←e at ha, exact ha.curry_comp fa ga, 
end

-- If we're boundaryless, ext_chart_at has open target
lemma ext_chart_at_open_target (I : model_with_corners ℂ E A) [I.boundaryless]
    [charted_space A M] [complex_manifold I M] (x : M) : is_open (ext_chart_at I x).target := begin
  simp only [ext_chart_at, local_homeomorph.extend, model_with_corners.boundaryless.range_eq_univ,
    local_equiv.trans_target, model_with_corners.target_eq, model_with_corners.to_local_equiv_coe_symm,
    set.univ_inter],
  exact is_open.preimage (model_with_corners.continuous_symm I) (local_homeomorph.open_target _),
end

-- mem_chart_target for ext_chart_at
lemma mem_ext_chart_target (I : model_with_corners ℂ E A) [I.boundaryless] {M : Type} [topological_space M]
    [charted_space A M] [complex_manifold I M] (x : M) : ext_chart_at I x x ∈ (ext_chart_at I x).target :=
  local_equiv.maps_to _ (mem_ext_chart_source _ _)

-- id is holomorphic
lemma holomorphic_at_id {x : M} : holomorphic_at I I (λ x, x) x := begin
  rw holomorphic_at_iff, use continuous_at_id, apply analytic_at_id.congr,
  apply ((ext_chart_at_open_target I x).eventually_mem (mem_ext_chart_target I x)).mp
    (eventually_of_forall (λ y m, _)),
  simp only [function.comp, local_equiv.right_inv _ m],
  repeat { apply_instance },
end
lemma holomorphic_id : holomorphic I I (λ x : M, x) := λ _, holomorphic_at_id 

-- Constants are holomorphic
lemma holomorphic_at_const {x : M} {c : N} : holomorphic_at I J (λ x, c) x := begin
  rw holomorphic_at_iff, use continuous_at_const,
  simp only [prod.fst_comp_mk, function.comp_const], exact analytic_at_const,
end
lemma holomorphic_const {c : N} : holomorphic I J (λ x : M, c) := λ _, holomorphic_at_const

-- Curried holomorphic functions are holomorphic in each component
lemma holomorphic_at.in1 [I.boundaryless] {f : M → N → O} {x : M} {y : N}
    (fa : holomorphic_at (I.prod J) K (uncurry f) (x,y)) : holomorphic_at I K (λ x, f x y) x :=
  holomorphic_at.curry_comp fa holomorphic_at_id holomorphic_at_const
lemma holomorphic_at.in2 [J.boundaryless] {f : M → N → O} {x : M} {y : N}
    (fa : holomorphic_at (I.prod J) K (uncurry f) (x,y)) : holomorphic_at J K (λ y, f x y) y :=
  holomorphic_at.curry_comp fa holomorphic_at_const holomorphic_at_id
lemma holomorphic.in1 [I.boundaryless] {f : M → N → O} (fa : holomorphic (I.prod J) K (uncurry f)) {y : N}
    : holomorphic I K (λ x, f x y) := λ _, (fa _).in1
lemma holomorphic.in2 [J.boundaryless] {f : M → N → O} {x : M} (fa : holomorphic (I.prod J) K (uncurry f))
    : holomorphic J K (λ y, f x y) := λ _, (fa _).in2

-- fst and snd are holomorphic
lemma holomorphic_at_fst [I.boundaryless] [J.boundaryless] {x : M × N}
    : holomorphic_at (I.prod J) I (λ p : M × N, p.fst) x := begin
  rw holomorphic_at_iff, use continuous_at_fst, refine analytic_at_fst.congr _,
  refine ((ext_chart_at_open_target _ x).eventually_mem (mem_ext_chart_target _ _)).mp
    (eventually_of_forall (λ y m, _)),
  rw [ext_chart_at_prod] at m,
  simp only [local_homeomorph.prod_to_local_equiv, local_equiv.prod_target, set.mem_prod] at m,
  simp only [ext_chart_at_prod, function.comp, local_equiv.prod_coe_symm],
  exact ((ext_chart_at I x.1).right_inv m.1).symm,
end
lemma holomorphic_at_snd [I.boundaryless] [J.boundaryless] {x : M × N}
    : holomorphic_at (I.prod J) J (λ p : M × N, p.snd) x := begin
  rw holomorphic_at_iff, use continuous_at_snd, refine analytic_at_snd.congr _,
  refine ((ext_chart_at_open_target _ x).eventually_mem (mem_ext_chart_target _ _)).mp
    (eventually_of_forall (λ y m, _)),
  rw [ext_chart_at_prod] at m,
  simp only [local_homeomorph.prod_to_local_equiv, local_equiv.prod_target, set.mem_prod] at m,
  simp only [ext_chart_at_prod, function.comp, local_equiv.prod_coe_symm],
  exact ((ext_chart_at J x.2).right_inv m.2).symm,
end
lemma holomorphic_fst [I.boundaryless] [J.boundaryless] : holomorphic (I.prod J) I (λ p : M × N, p.fst) :=
  λ _, holomorphic_at_fst
lemma holomorphic_snd [I.boundaryless] [J.boundaryless] : holomorphic (I.prod J) J (λ p : M × N, p.snd) :=
  λ _, holomorphic_at_snd
 
-- Remove instances of I.to_local_equiv
lemma model_with_corners.coe_coe (I : model_with_corners ℂ E A) : ⇑(I.to_local_equiv) = (I : A → E) := rfl
lemma model_with_corners.coe_coe_symm (I : model_with_corners ℂ E A)
    : ⇑(I.to_local_equiv.symm) = (I.symm : E → A) := rfl

-- ext_chart_at is holomorphic
lemma holomorphic_at.ext_chart_at {x y : M} (ys : y ∈ (ext_chart_at I x).source)
    : holomorphic_at I (model_with_corners_self ℂ E) (ext_chart_at I x) y := begin
  rw holomorphic_at_iff, use continuous_at_ext_chart_at' I x ys,
  simp only [ext_chart_at_eq_refl, local_equiv.refl_coe, function.comp, id, ext_chart_at, local_homeomorph.extend,
    local_equiv.coe_trans, local_equiv.coe_trans_symm, local_homeomorph.coe_coe, local_homeomorph.coe_coe_symm,
    model_with_corners.coe_coe, model_with_corners.coe_coe_symm, model_with_corners_self_coe, chart_at_self_eq,
    local_homeomorph.refl_apply],
  have a := (structure_groupoid.compatible_of_mem_maximal_atlas
    (structure_groupoid.chart_mem_maximal_atlas (analytic_groupoid I) x)
    (structure_groupoid.chart_mem_maximal_atlas (analytic_groupoid I) y)).2,
  simp only [analytic_groupoid, mem_groupoid_of_pregroupoid, local_homeomorph.coe_trans_symm,
    local_homeomorph.symm_symm, function.comp] at a,
  apply a,
  simp only [ext_chart_at, local_homeomorph.extend, local_equiv.trans_source, model_with_corners.source_eq,
    set.preimage_univ, set.inter_univ] at ys,
  simp only [ys, local_homeomorph.trans_to_local_equiv, local_homeomorph.symm_to_local_equiv,
    local_equiv.trans_target, local_homeomorph.coe_coe_symm, local_equiv.symm_target, set.mem_inter_iff,
    set.mem_preimage, model_with_corners.left_inv, local_homeomorph.map_source, mem_chart_source,
    local_homeomorph.left_inv, true_and, set.mem_range_self, and_true],
end

-- ext_chart_at.symm is holomorphic
lemma holomorphic_at.ext_chart_at_symm {x : M} {y : E} (ys : y ∈ (ext_chart_at I x).target)
    : holomorphic_at (model_with_corners_self ℂ E) I (ext_chart_at I x).symm y := begin
  rw holomorphic_at_iff, use continuous_at_ext_chart_at_symm'' I x ys,
  simp only [ext_chart_at_eq_refl, local_equiv.refl_coe, function.comp, id, ext_chart_at, local_homeomorph.extend,
    local_equiv.coe_trans, local_equiv.coe_trans_symm, local_homeomorph.coe_coe, local_homeomorph.coe_coe_symm,
    model_with_corners.coe_coe, model_with_corners.coe_coe_symm, model_with_corners_self_coe, chart_at_self_eq,
    local_homeomorph.refl_apply, local_homeomorph.refl_symm, model_with_corners_self_coe_symm],
  set y' := (chart_at A x).symm (I.symm y),
  have a := (structure_groupoid.compatible_of_mem_maximal_atlas
    (structure_groupoid.chart_mem_maximal_atlas (analytic_groupoid I) x)
    (structure_groupoid.chart_mem_maximal_atlas (analytic_groupoid I) y')).1,
  simp only [analytic_groupoid, mem_groupoid_of_pregroupoid, local_homeomorph.coe_trans_symm,
    local_homeomorph.symm_symm, function.comp, local_homeomorph.trans_apply] at a,
  apply a,
  simp only [ext_chart_at, local_homeomorph.extend, local_equiv.trans_target, model_with_corners.target_eq,
    model_with_corners.to_local_equiv_coe_symm, set.mem_inter_iff, set.mem_preimage,
    model_with_corners.boundaryless.range_eq_univ, set.mem_univ, true_and] at ys,
  simp only [ys, local_homeomorph.trans_to_local_equiv, local_homeomorph.symm_to_local_equiv,
    local_equiv.trans_source, local_equiv.symm_source, local_homeomorph.coe_coe_symm, set.mem_inter_iff,
    set.mem_preimage, mem_chart_source, model_with_corners.boundaryless.range_eq_univ, true_and],
end

-- Addition, subtraction, multiplication, inversion, division, and powers are holomorphic
lemma holomorphic_at.add {f g : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x)
    (ga : holomorphic_at I (model_with_corners_self ℂ ℂ) g x)
    : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, f x + g x) x := begin
  have e : (λ x, f x + g x) = (λ p : ℂ × ℂ, p.1 + p.2) ∘ (λ x, (f x, g x)) := rfl,
  rw e, refine holomorphic_at.comp _ (fa.prod ga),
  apply analytic_at.holomorphic_at, exact analytic_at_fst.add analytic_at_snd,
end
lemma holomorphic_at.sub {f g : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x)
    (ga : holomorphic_at I (model_with_corners_self ℂ ℂ) g x)
    : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, f x - g x) x := begin
  have e : (λ x, f x - g x) = (λ p : ℂ × ℂ, p.1 - p.2) ∘ (λ x, (f x, g x)) := rfl,
  rw e, refine holomorphic_at.comp _ (fa.prod ga),
  apply analytic_at.holomorphic_at, exact analytic_at_fst.sub analytic_at_snd,
end
lemma holomorphic_at.mul {f g : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x)
    (ga : holomorphic_at I (model_with_corners_self ℂ ℂ) g x)
    : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, f x * g x) x := begin
  have e : (λ x, f x * g x) = (λ p : ℂ × ℂ, p.1 * p.2) ∘ (λ x, (f x, g x)) := rfl,
  rw e, refine holomorphic_at.comp _ (fa.prod ga),
  apply analytic_at.holomorphic_at, exact analytic_at_fst.mul analytic_at_snd,
end
lemma holomorphic_at.inv {f : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x)
    (f0 : f x ≠ 0) : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, (f x)⁻¹) x := begin
  have e : (λ x, (f x)⁻¹) = (λ z : ℂ, z⁻¹) ∘ f := rfl,
  rw e, refine holomorphic_at.comp _ fa, apply analytic_at.holomorphic_at, exact analytic_at_id.inv f0,
end
lemma holomorphic_at.div {f g : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x)
    (ga : holomorphic_at I (model_with_corners_self ℂ ℂ) g x) (g0 : g x ≠ 0)
    : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, f x / g x) x := begin
  simp only [div_eq_mul_inv], exact fa.mul (ga.inv g0),
end
lemma holomorphic_at.pow {f : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x) {n : ℕ}
    : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, f x ^ n) x := begin
  have e : (λ x, f x ^ n) = (λ z : ℂ, z^n) ∘ f := rfl,
  rw e, refine holomorphic_at.comp _ fa, apply analytic_at.holomorphic_at, exact analytic_at_id.pow,
end
lemma holomorphic_at.cpow {f g : M → ℂ} {x : M} (fa : holomorphic_at I (model_with_corners_self ℂ ℂ) f x)
    (ga : holomorphic_at I (model_with_corners_self ℂ ℂ) g x) (a : 0 < (f x).re ∨ (f x).im ≠ 0)
    : holomorphic_at I (model_with_corners_self ℂ ℂ) (λ x, f x ^ g x) x := begin
  have e : (λ x, f x ^ g x) = (λ p : ℂ × ℂ, p.1 ^ p.2) ∘ (λ x, (f x, g x)) := rfl, 
  rw e, refine holomorphic_at.comp _ (fa.prod ga),
  apply analytic_at.holomorphic_at, exact analytic_at_fst.cpow analytic_at_snd a,
end

-- Holomorphic functions are smooth
lemma holomorphic_at.smooth_at {f : M → N} {x : M} (fa : holomorphic_at I J f x) : smooth_at I J f x := begin
  rw holomorphic_at_iff at fa, simp only [smooth_at, cont_mdiff_at_iff],
  use fa.1, use fa.2.cont_diff_at.cont_diff_within_at,
end
lemma holomorphic_on.smooth_on {f : M → N} {s : set M} (fa : holomorphic_on I J f s) : smooth_on I J f s :=
  λ x m, (fa x m).smooth_at.smooth_within_at
  
-- Holomorphic functions are differentiable
lemma holomorphic_at.mdifferentiable_at {f : M → N} {x : M} (fa : holomorphic_at I J f x)
    : mdifferentiable_at I J f x := fa.smooth_at.mdifferentiable_at

-- Iterated holomorphic functions are holomorphic
lemma holomorphic.iter {f : M → M} (fa : holomorphic I I f) (n : ℕ) : holomorphic I I (f^[n]) := begin
  induction n with n h, simp only [function.iterate_zero], exact holomorphic_id,
  simp only [function.iterate_succ'], exact fa.comp h,
end

-- Chart derivatives are invertible
lemma ext_chart_at_mderiv_left_inverse {x y : M} (m : y ∈ (ext_chart_at I x).source)
    : (mfderiv (model_with_corners_self ℂ E) I (ext_chart_at I x).symm (ext_chart_at I x y)).comp
        (mfderiv I (model_with_corners_self ℂ E) (ext_chart_at I x) y) =
      continuous_linear_map.id ℂ (tangent_space I y) := begin
  have m' : ext_chart_at I x y ∈ (ext_chart_at I x).target := local_equiv.map_source _ m,
  have c := mfderiv_comp y (holomorphic_at.ext_chart_at_symm m').mdifferentiable_at
    (holomorphic_at.ext_chart_at m).mdifferentiable_at,
  refine trans c.symm _, clear c, rw ←mfderiv_id, apply filter.eventually_eq.mfderiv_eq,
  rw filter.eventually_eq_iff_exists_mem, use (ext_chart_at I x).source,
  use ext_chart_at_source_mem_nhds' I x m,
  intros z zm, simp only [function.comp, id, local_equiv.left_inv _ zm],
end
lemma ext_chart_at_mderiv_right_inverse {x : M} {y : E} (m : y ∈ (ext_chart_at I x).target)
    : (mfderiv I (model_with_corners_self ℂ E) (ext_chart_at I x) ((ext_chart_at I x).symm y)).comp
        (mfderiv (model_with_corners_self ℂ E) I (ext_chart_at I x).symm y) =
      continuous_linear_map.id ℂ (tangent_space (model_with_corners_self ℂ E) y)  := begin
  have m' : (ext_chart_at I x).symm y ∈ (ext_chart_at I x).source := local_equiv.map_target _ m,
  have c := mfderiv_comp y (holomorphic_at.ext_chart_at m').mdifferentiable_at
    (holomorphic_at.ext_chart_at_symm m).mdifferentiable_at,
  refine trans c.symm _, clear c, rw ←mfderiv_id, apply filter.eventually_eq.mfderiv_eq,
  rw filter.eventually_eq_iff_exists_mem, use (ext_chart_at I x).target,
  have n := ext_chart_at_target_mem_nhds_within' I x m',
  simp only [model_with_corners.boundaryless.range_eq_univ, nhds_within_univ, local_equiv.right_inv _ m] at n,
  use n, intros z zm, simp only [function.comp, id, local_equiv.right_inv _ zm],
end
lemma ext_chart_at_mderiv_right_inverse' {x y : M} (m : y ∈ (ext_chart_at I x).source)
    : (mfderiv I (model_with_corners_self ℂ E) (ext_chart_at I x) y).comp
        (mfderiv (model_with_corners_self ℂ E) I (ext_chart_at I x).symm ((ext_chart_at I x y))) =
      continuous_linear_map.id ℂ (tangent_space (model_with_corners_self ℂ E) (ext_chart_at I x y)) := begin
  have h := ext_chart_at_mderiv_right_inverse (local_equiv.map_source _ m),
  rw local_equiv.left_inv _ m at h, exact h,
end

-- holomorphic_at depends only on local values
lemma holomorphic_at.congr {f g : M → N} {x : M} (fa : holomorphic_at I J f x) (e : f =ᶠ[𝓝 x] g)
    : holomorphic_at I J g x := begin
  rw holomorphic_at_iff at fa ⊢, use fa.1.congr e, apply fa.2.congr,
  rw e.self, refine filter.eventually_eq.fun_comp _ (ext_chart_at J (g x)),
  have t := (continuous_at_ext_chart_at_symm I x).tendsto,
  rw local_equiv.left_inv _ (mem_ext_chart_source I x) at t,
  exact e.comp_tendsto t,
end

 -- If we're holomorphic at a point, we're locally holomorphic
lemma holomorphic_at.eventually {f : M → N} {x : M} (fa : holomorphic_at I J f x)
    : ∀ᶠ y in 𝓝 x, holomorphic_at I J f y := begin
  apply (fa.continuous_at.eventually_mem (is_open_ext_chart_at_source J (f x))
    (mem_ext_chart_source J (f x))).eventually_nhds.mp,
  apply ((is_open_ext_chart_at_source I x).eventually_mem (mem_ext_chart_source I x)).mp,
  apply ((continuous_at_ext_chart_at I x).eventually
    ((is_open_analytic_at _ _).eventually_mem (holomorphic_at_iff.mp fa).2)).mp,
  refine eventually_of_forall (λ y a m fm, _),
  simp only at a m fm, rw set.mem_set_of at a,
  have h := a.holomorphic_at (model_with_corners_self ℂ E) (model_with_corners_self ℂ F), clear a,
  have h' := (holomorphic_at.ext_chart_at_symm (local_equiv.map_source _ fm.self)).comp_of_eq
    (h.comp (holomorphic_at.ext_chart_at m)) _,
  swap, simp only [function.comp, local_equiv.left_inv _ m],
  apply h'.congr, clear h h', simp only [function.comp],
  apply ((is_open_ext_chart_at_source I x).eventually_mem m).mp,
  refine fm.mp (eventually_of_forall (λ z mf m, _)),
  simp only [local_equiv.left_inv _ m, local_equiv.left_inv _ mf],
end

-- The domain of holomorphicity is open
lemma is_open_holomorphic_at {f : M → N} : is_open {x | holomorphic_at I J f x} := begin
  rw is_open_iff_eventually, intros x fa, exact fa.eventually,
end

-- has_mfderiv_at for pairs
lemma has_mfderiv_at.prod {f : M → N} {g : M → O} {x : M}
    {df : tangent_space I x →L[ℂ] tangent_space J (f x)} (fh : has_mfderiv_at I J f x df)
    {dg : tangent_space I x →L[ℂ] tangent_space K (g x)} (gh : has_mfderiv_at I K g x dg)
    : has_mfderiv_at I (J.prod K) (λ y, (f y, g y)) x (df.prod dg) := begin
  simp only [has_mfderiv_at, model_with_corners.boundaryless.range_eq_univ, has_fderiv_within_at_univ] at fh gh ⊢,
  use fh.1.prod gh.1, use fh.2.prod gh.2,
end

-- tangent_space commutes with prod
lemma tangent_space_prod (x : M) (y : N)
    : tangent_space (I.prod J) (x,y) = (tangent_space I x × tangent_space J y) :=
  by simp only [tangent_space]

 -- has_mfderiv_at composition for curried functions
 -- This was oddly difficult.
lemma mdifferentiable_at.has_mfderiv_at_uncurry {f : N → O → P} {y : N} {z : O}
    (fd : mdifferentiable_at (J.prod K) L (uncurry f) (y,z))
    {df0 : tangent_space J y →L[ℂ] tangent_space L (f y z)} (fh0 : has_mfderiv_at J L (λ x, f x z) y df0)
    {df1 : tangent_space K z →L[ℂ] tangent_space L (f y z)} (fh1 : has_mfderiv_at K L (λ x, f y x) z df1)
    : has_mfderiv_at (J.prod K) L (uncurry f) (y,z)
        (df0.comp (continuous_linear_map.fst ℂ (tangent_space J y) (tangent_space K z)) +
         df1.comp (continuous_linear_map.snd ℂ (tangent_space J y) (tangent_space K z))) := begin
  set fst := continuous_linear_map.fst ℂ (tangent_space J y) (tangent_space K z),
  set snd := continuous_linear_map.snd ℂ (tangent_space J y) (tangent_space K z),
  generalize hdf : mfderiv (J.prod K) L (uncurry f) (y, z) = df,
  have fh := fd.has_mfderiv_at, rw hdf at fh,
  suffices e : df = df0.comp fst + df1.comp snd, rw e at fh, exact fh,
  apply continuous_linear_map.ext, rintro ⟨u,v⟩,
  simp only [continuous_linear_map.add_apply, continuous_linear_map.comp_apply,
    continuous_linear_map.coe_fst', continuous_linear_map.coe_snd'],
  have hu : ∀ u : tangent_space J y, df (u,0) = df0 u, {
    intro u,
    have d : has_mfderiv_at J L (uncurry f ∘ (λ x, (x,z))) y
        (df.comp ((continuous_linear_map.id ℂ (tangent_space J y)).prod 0)) :=
      fh.comp y ((has_mfderiv_at_id _ _).prod (has_mfderiv_at_const _ _ _ _)),
    have e := has_mfderiv_at_unique fh0 d,
    simp only [e, continuous_linear_map.comp_apply, continuous_linear_map.prod_apply,
      continuous_linear_map.id_apply, continuous_linear_map.zero_apply],
  },
  have hv : ∀ v : tangent_space K z, df (0,v) = df1 v, {
    intro v,
    have d : has_mfderiv_at K L (uncurry f ∘ (λ x, (y,x))) z
        (df.comp ((0 : tangent_space K z →L[ℂ] tangent_space J y).prod
                  (continuous_linear_map.id ℂ (tangent_space K z)))) :=
      fh.comp z ((has_mfderiv_at_const _ _ _ _).prod (has_mfderiv_at_id _ _)),
    have e := has_mfderiv_at_unique fh1 d,
    simp only [e, continuous_linear_map.comp_apply, continuous_linear_map.prod_apply,
      continuous_linear_map.id_apply, continuous_linear_map.zero_apply],
  },
  have e : (u,v) = (u,0) + (0,v) := by simp only [prod.mk_add_mk, add_zero, zero_add],
  simp only [e, continuous_linear_map.map_add, hu u, hv v],
end

-- has_mfderiv_at composition for curried functions
lemma mdifferentiable_at.has_mfderiv_at_comp2 {f : N → O → P} {g : M → N} {h : M → O} {x : M}
    (fd : mdifferentiable_at (J.prod K) L (uncurry f) (g x, h x))
    {dg : tangent_space I x →L[ℂ] tangent_space J (g x)} (gh : has_mfderiv_at I J g x dg)
    {dh : tangent_space I x →L[ℂ] tangent_space K (h x)} (hh : has_mfderiv_at I K h x dh)
    {df0 : tangent_space J (g x) →L[ℂ] tangent_space L (f (g x) (h x))}
    (fh0 : has_mfderiv_at J L (λ y, f y (h x)) (g x) df0)
    {df1 : tangent_space K (h x) →L[ℂ] tangent_space L (f (g x) (h x))}
    (fh1 : has_mfderiv_at K L (λ y, f (g x) y) (h x) df1)
    : has_mfderiv_at I L (λ y, f (g y) (h y)) x (df0.comp dg + df1.comp dh) := begin
  have fh := (fd.has_mfderiv_at_uncurry fh0 fh1).comp x (gh.prod hh),
  simp only [continuous_linear_map.add_comp, continuous_linear_map.comp_assoc,
    continuous_linear_map.fst_comp_prod, continuous_linear_map.snd_comp_prod] at fh,
  exact fh,
end

-- More general version of has_mfderiv_at_iff_has_fderiv_at.
-- The mathlib version doesn't handle product spaces.
lemma has_mfderiv_at_iff_has_fderiv_at'
    {I : model_with_corners ℂ E A} [I.boundaryless] [complex_manifold I E] [ext_chart_eq_refl I]
    {J : model_with_corners ℂ F B} [J.boundaryless] [complex_manifold J F] [ext_chart_eq_refl J]
    {f : E → F} {x : E} {f' : E →L[ℂ] F}
    : has_mfderiv_at I J f x f' ↔ has_fderiv_at f f' x := begin
  simp only [has_mfderiv_at, model_with_corners.boundaryless.range_eq_univ, has_fderiv_within_at_univ,
    written_in_ext_chart_at, ext_chart_at_eq_refl, function.comp, local_equiv.refl_coe, local_equiv.refl_symm, id],
  exact ⟨λ x, x.2, λ d, ⟨d.continuous_at, d⟩⟩,
end

-- Complex manifolds are locally connected
instance complex_manifold.to_locally_connected_space [complex_manifold I M] : locally_connected_space M := begin
  have c : locally_connected_space E :=
    @locally_convex_space.to_locally_connected_space E _ _ _ _ _ normed_space.to_locally_convex_space,
  rw locally_connected_space_iff_open_connected_subsets at ⊢ c,
  intros x s sx,
  set t := (ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' s,
  have tx : t ∈ 𝓝 (ext_chart_at I x x) := filter.inter_mem ((ext_chart_at_open_target I x).mem_nhds
    (mem_ext_chart_target I x)) (ext_chart_at_preimage_mem_nhds I x sx),
  rcases c _ _ tx with ⟨t',tt,ot',xt',tc'⟩,
  use [(ext_chart_at I x).source ∩ ext_chart_at I x ⁻¹' t'], refine ⟨_,_,_,_⟩, {
    intros y m, simp only [mem_inter_iff, mem_preimage] at m, have yt := tt m.2,
    simp only [mem_inter_iff, mem_preimage, local_equiv.left_inv _ m.1] at yt, use yt.2,
  }, {
    exact (continuous_on_ext_chart_at I x).preimage_open_of_open (is_open_ext_chart_at_source _ _) ot',
  }, {
    apply mem_inter (mem_ext_chart_source _ _), simp only [mem_preimage], exact xt',
  }, {
    have e : (ext_chart_at I x).source ∩ ext_chart_at I x ⁻¹' t' = (ext_chart_at I x).symm '' t', {
      apply set.ext, intros z, simp only [mem_inter_iff, mem_preimage, mem_image], constructor,
      rintros ⟨zx,zt⟩, use [ext_chart_at I x z, zt], simp only [local_equiv.left_inv _ zx],
      intros h, rcases h with ⟨w,wt',wz⟩, have wt := tt wt', simp only [mem_inter_iff, mem_preimage] at wt,
      simp only [←wz, local_equiv.map_target _ wt.1, true_and, local_equiv.right_inv _ wt.1, wt'],
    },
    rw e, exact tc'.image _ ((continuous_on_ext_chart_at_symm I x).mono (trans tt (inter_subset_left _ _))),
  },
end

-- Holomorphic functions have continuous tangent maps
-- Obviously more is true and the tangent map is holomorphic, but I don't need that yet
theorem holomorphic_on.continuous_on_tangent_map {f : M → N} {s : set M} (fa : holomorphic_on I J f s)
    : continuous_on (tangent_map I J f) (bundle.total_space.proj ⁻¹' s) := begin
  wlog o : is_open s, {
    apply (this _ is_open_holomorphic_at).mono,
    apply preimage_mono fa, intros x m, exact m,
  },
  apply (cont_mdiff_on.continuous_on_tangent_map_within fa.smooth_on le_top o.unique_mdiff_on).congr,
  intros x m, simp only [mem_preimage] at m,
  rw tangent_map_within_eq_tangent_map (o.unique_mdiff_on _ m) (fa _ m).mdifferentiable_at,
end

-- ext_chart_at as a local_homeomorph
def ext_chart_at' (I : model_with_corners ℂ E A) [I.boundaryless]
    {M : Type} [topological_space M] [complex_manifold I M] (x : M) : local_homeomorph M E := {
  to_local_equiv := ext_chart_at I x,
  open_source := is_open_ext_chart_at_source I x,
  open_target := ext_chart_at_open_target I x,
  continuous_to_fun := continuous_on_ext_chart_at I x,
  continuous_inv_fun := continuous_on_ext_chart_at_symm I x,
}

-- ext_chart_at maps 𝓝 to 𝓝
lemma ext_chart_at_map_nhds {x y : M} (m : y ∈ (ext_chart_at I x).source)
    : filter.map (ext_chart_at I x) (𝓝 y) = 𝓝 (ext_chart_at I x y) := (ext_chart_at' I x).map_nhds_eq m
lemma ext_chart_at_map_nhds' (I : model_with_corners ℂ E A) [I.boundaryless]
    {M : Type} [topological_space M] [complex_manifold I M] (x : M)
    : filter.map (ext_chart_at I x) (𝓝 x) = 𝓝 (ext_chart_at I x x) :=
  ext_chart_at_map_nhds (mem_ext_chart_source I x)

-- ext_chart_at.symm maps 𝓝 to 𝓝
lemma ext_chart_at_symm_map_nhds {x : M} {y : E} (m : y ∈ (ext_chart_at I x).target)
    : filter.map (ext_chart_at I x).symm (𝓝 y) = 𝓝 ((ext_chart_at I x).symm y) :=
  (ext_chart_at' I x).symm.map_nhds_eq m
lemma ext_chart_at_symm_map_nhds' (I : model_with_corners ℂ E A) [I.boundaryless]
    {M : Type} [topological_space M] [complex_manifold I M] (x : M)
    : filter.map (ext_chart_at I x).symm (𝓝 (ext_chart_at I x x)) = 𝓝 x := begin
  convert ext_chart_at_symm_map_nhds (mem_ext_chart_target I x),
  simp only [local_equiv.left_inv _ (mem_ext_chart_source I x)],
end

-- Nontrivial manifolds have no isolated points
@[instance] lemma complex_manifold.punctured_nhds_ne_bot (I : model_with_corners ℂ E A) [I.boundaryless] [nontrivial E]
    [complex_manifold I M] (x : M) : (𝓝[{x}ᶜ] x).ne_bot := begin
  have p := module.punctured_nhds_ne_bot ℂ E (ext_chart_at I x x),
  simp only [←filter.frequently_true_iff_ne_bot, frequently_nhds_within_iff, ←ext_chart_at_symm_map_nhds' I x,
    filter.frequently_map, true_and, mem_compl_singleton_iff] at ⊢ p,
  apply p.mp,
  apply ((ext_chart_at_open_target I x).eventually_mem (mem_ext_chart_target I x)).mp,
  refine eventually_of_forall (λ y m h, _),
  contrapose h, simp only [not_not] at m h ⊢, nth_rewrite 1 ←h, rw local_equiv.right_inv _ m,
end