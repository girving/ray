-- The (parameterized) inverse function theorem on complex manifolds (1D case)
-- Given f : ℂ × S → T, we seek g : ℂ × T → S s.t. g c (f c z) = z.

import complex_manifold
import continuation
import geometry.manifold.mfderiv
import one_dimension

open filter (eventually_of_forall tendsto)
open function (uncurry)
open one_dimension
open set
open_locale topology
noncomputable theory

variables {S : Type} [topological_space S] [complex_manifold I S]
variables {T : Type} [topological_space T] [complex_manifold I T]

-- Data for our 1D inverse function theorem
structure cinv (f : ℂ → S → T) (c : ℂ) (z : S) : Prop :=
  (fa : holomorphic_at II I (uncurry f) (c,z))
  (nc : mfderiv I I (f c) z ≠ 0)

variables {f : ℂ → S → T} {c : ℂ} {z : S}

-- Useful abbreviations
def cinv.z' (i : cinv f c z) : ℂ := ext_chart_at I z z
def cinv.fz' (i : cinv f c z) : ℂ := ext_chart_at I (f c z) (f c z) 
lemma cinv.zz (i : cinv f c z) : (ext_chart_at I z).symm (c, i.z').snd = z :=
    by simp only [prod.snd, cinv.z', local_equiv.left_inv _ (mem_ext_chart_source _ _)]

-- f in chart form
def cinv.f' (i : cinv f c z) : ℂ × ℂ → ℂ :=
  λ x, ext_chart_at I (f c z) (f x.1 ((ext_chart_at I z).symm x.2))

-- (c,z) → (c, f c z)
def cinv.h (i : cinv f c z) : ℂ × ℂ → ℂ × ℂ := λ x, (x.1, i.f' x)

-- f' and h are analytic
lemma cinv.fa' (i : cinv f c z) : analytic_at ℂ i.f' (c,i.z') := begin
  rw cinv.f', have fa := i.fa,
  simp only [holomorphic_at_iff, uncurry, ext_chart_at_prod, function.comp, local_equiv.prod_coe_symm,
    local_equiv.prod_coe] at fa,
  exact fa.2, repeat { apply_instance },
end
lemma cinv.ha (i : cinv f c z) : analytic_at ℂ i.h (c,i.z') := analytic_at_fst.prod i.fa'

-- The key derivative
def cinv.dfz (i : cinv f c z) := mfderiv I I (f c) z
def cinv.dfzi (i : cinv f c z) : tangent_space I (f c z) →L[ℂ] tangent_space I z := (mderiv_equiv i.dfz i.nc).symm
lemma cinv.dfzi_dfz (i : cinv f c z) : ∀ t, i.dfzi (i.dfz t) = t := λ t, (mderiv_equiv _ i.nc).left_inv _
lemma cinv.dfz_dfzi (i : cinv f c z) : ∀ t, i.dfz (i.dfzi t) = t := λ t, (mderiv_equiv _ i.nc).right_inv _ 

-- The derivative i.dh of i.h
--   dh = i.dc.prod (i.de'.comp (i.dfc.comp i.dc + i.dfz.comp (i.de.comp i.dz)))
--      = (    1               0      )
--        (de' ∘ dfc    de' ∘ dfz ∘ de)
def cinv.de (i : cinv f c z) := mfderiv I I (ext_chart_at I z).symm i.z'
def cinv.de' (i : cinv f c z) := mfderiv I I (ext_chart_at I (f c z)) (f c z)
def cinv.dc (i : cinv f c z) := continuous_linear_map.fst ℂ (tangent_space I c) (tangent_space I z)
def cinv.dz (i : cinv f c z) := continuous_linear_map.snd ℂ (tangent_space I c) (tangent_space I z)
def cinv.dfc (i : cinv f c z) := mfderiv I I (λ c : ℂ, f c z) c
def cinv.df (i : cinv f c z) := i.dfc.comp i.dc + i.dfz.comp (i.de.comp i.dz)
def cinv.df' (i : cinv f c z) : ℂ × ℂ →L[ℂ] ℂ := i.de'.comp i.df
def cinv.dh (i : cinv f c z) : ℂ × ℂ →L[ℂ] ℂ × ℂ := i.dc.prod i.df'
lemma cinv.has_df' (i : cinv f c z) : has_mfderiv_at II I i.f' (c,i.z') i.df' := begin
  apply has_mfderiv_at.comp (c,i.z'), {
    rw i.zz, exact (holomorphic_at.ext_chart_at (mem_ext_chart_source _ _)).mdifferentiable_at.has_mfderiv_at,
  }, {
    apply mdifferentiable_at.has_mfderiv_at_comp2,
    rw i.zz, exact i.fa.mdifferentiable_at,
    apply has_mfderiv_at_fst,
    refine has_mfderiv_at.comp _ _ (has_mfderiv_at_snd _ _ _),
    exact (holomorphic_at.ext_chart_at_symm (mem_ext_chart_target _ _)).mdifferentiable_at.has_mfderiv_at,
    rw i.zz, exact i.fa.in1.mdifferentiable_at.has_mfderiv_at,
    rw i.zz, exact i.fa.in2.mdifferentiable_at.has_mfderiv_at,
  },
end
lemma cinv.has_dh (i : cinv f c z) : has_mfderiv_at II II i.h (c,i.z') i.dh := begin
  refine has_mfderiv_at.prod _ i.has_df', apply has_mfderiv_at_fst,
end

-- dh is invertible
--   dh (u,v) = (a,b)
--   (u, (de' ∘ dfc)u + (de' ∘ dfz ∘ de)v) = (a,b)
--   u = a
--   (de' ∘ dfc)a + (de' ∘ dfz ∘ de)v = b
--   v = (de' ∘ dfz ∘ de)⁻¹ (b - (de' ∘ dfc)a)
--   v = (de⁻¹  ∘ dfz⁻¹ ∘ de'⁻¹) (b - (de' ∘ dfc)a)
def cinv.dei (i : cinv f c z) := mfderiv I I (ext_chart_at I z) z
def cinv.dei' (i : cinv f c z) := mfderiv I I (ext_chart_at I (f c z)).symm i.fz'
def cinv.dfi' (i : cinv f c z) := (i.dei.comp i.dfzi).comp i.dei'
def cinv.dhi (i : cinv f c z) : ℂ × ℂ →L[ℂ] ℂ × ℂ := i.dc.prod (i.dfi'.comp (i.dz - (i.de'.comp i.dfc).comp i.dc))
lemma cinv.dei_de (i : cinv f c z) : ∀ t, i.dei (i.de t) = t := begin
  intro t,
  have h := continuous_linear_map.ext_iff.mp (ext_chart_at_mderiv_right_inverse' (mem_ext_chart_source I z)) t,
  simp only [continuous_linear_map.comp_apply, continuous_linear_map.id_apply] at h, exact h,
end
lemma cinv.dei_de' (i : cinv f c z) : ∀ t, i.dei' (i.de' t) = t := begin
  intro t,
  have h := continuous_linear_map.ext_iff.mp (ext_chart_at_mderiv_left_inverse (mem_ext_chart_source I (f c z))) t,
  simp only [continuous_linear_map.comp_apply, continuous_linear_map.id_apply] at h, exact h,
end
lemma cinv.de_dei (i : cinv f c z) : ∀ t, i.de (i.dei t) = t := begin
  intro t,
  have h := continuous_linear_map.ext_iff.mp (ext_chart_at_mderiv_left_inverse (mem_ext_chart_source I z)) t,
  simp only [continuous_linear_map.comp_apply, continuous_linear_map.id_apply] at h, exact h,
end
lemma cinv.de_dei' (i : cinv f c z) : ∀ t, i.de' (i.dei' t) = t := begin
  intro t,
  have h := continuous_linear_map.ext_iff.mp (ext_chart_at_mderiv_right_inverse' (mem_ext_chart_source I (f c z))) t,
  simp only [continuous_linear_map.comp_apply, continuous_linear_map.id_apply] at h, exact h,
end
lemma cinv.dhi_dh (i : cinv f c z) : ∀ t, i.dhi (i.dh t) = t := begin
  rintros ⟨u,v⟩,
  simp only [cinv.dh, cinv.dhi, cinv.dc, cinv.dz, cinv.dfi', cinv.df', cinv.df, i.dei_de', i.dei_de, i.dfzi_dfz,
    continuous_linear_map.comp_apply, continuous_linear_map.prod_apply, continuous_linear_map.sub_apply,
    continuous_linear_map.coe_fst', continuous_linear_map.coe_snd', continuous_linear_map.add_apply,
    continuous_linear_map.map_add, continuous_linear_map.map_sub, add_sub_cancel'],
end
lemma cinv.dh_dhi (i : cinv f c z) : ∀ t, i.dh (i.dhi t) = t := begin
  rintros ⟨u,v⟩,
  simp only [cinv.dh, cinv.dhi, cinv.dc, cinv.dz, cinv.dfi', cinv.df', cinv.df, i.de_dei', i.de_dei, i.dfz_dfzi,
    continuous_linear_map.comp_apply, continuous_linear_map.prod_apply, continuous_linear_map.sub_apply,
    continuous_linear_map.coe_fst', continuous_linear_map.coe_snd', continuous_linear_map.add_apply,
    continuous_linear_map.map_add, continuous_linear_map.map_sub, add_sub_cancel', ←add_sub_assoc],
end

-- dh as a continuous_linear_equiv
def cinv.dhe (i : cinv f c z) : (ℂ × ℂ) ≃L[ℂ] ℂ × ℂ :=
  continuous_linear_equiv.equiv_of_inverse i.dh i.dhi i.dhi_dh i.dh_dhi
lemma cinv.has_dhe (i : cinv f c z) : has_fderiv_at i.h (i.dhe : ℂ × ℂ →L[ℂ] ℂ × ℂ) (c,i.z') :=
  has_mfderiv_at_iff_has_fderiv_at'.mp i.has_dh

-- h as a local_homeomorph
def cinv.he (i : cinv f c z) := cont_diff_at.to_local_homeomorph i.h i.ha.cont_diff_at i.has_dhe le_top

-- h inverts at the point
lemma cinv.inv_at (i : cinv f c z) : (i.he.symm (c, ext_chart_at I (f c z) (f c z))).2 = ext_chart_at I z z := begin
  have a := cont_diff_at.local_inverse_apply_image i.ha.cont_diff_at i.has_dhe le_top,
  have e : cont_diff_at.local_inverse i.ha.cont_diff_at i.has_dhe le_top = i.he.symm := rfl,
  rw e at a, clear e,
  simp only [cinv.z', cinv.h, cinv.f', local_equiv.left_inv _ (mem_ext_chart_source _ _)] at a,
  rw a,
end

-- Our inverse function!
def cinv.g (i : cinv f c z) : ℂ → T → S :=
  λ b w, (ext_chart_at I z).symm (i.he.symm (b, ext_chart_at I (f c z) w)).2

-- g left inverts locally
lemma cinv.left_inv (i : cinv f c z) : ∀ᶠ x : ℂ × S in 𝓝 (c,z), i.g x.1 (f x.1 x.2) = x.2 := begin
  set t : set (ℂ × S) := (ext_chart_at II (c,z)).source ∩ (ext_chart_at II (c,z)) ⁻¹' i.he.source,
  have o : is_open t :=
    (continuous_on_ext_chart_at _ _).preimage_open_of_open (is_open_ext_chart_at_source _ _) i.he.open_source,
  have m : (c,z) ∈ t, {
    simp only [mem_inter_iff, mem_preimage, mem_ext_chart_source, true_and],
    exact cont_diff_at.mem_to_local_homeomorph_source i.ha.cont_diff_at i.has_dhe le_top,
  },
  apply filter.eventually_eq_of_mem (o.mem_nhds m), rintros x m,
  simp only [mem_inter_iff, mem_preimage, ext_chart_at_prod, ext_chart_at_eq_refl,
    local_equiv.prod_source, local_equiv.refl_source, mem_prod_eq, mem_univ, true_and,
    local_equiv.prod_coe, local_equiv.refl_coe, id] at m,
  have inv := i.he.left_inv m.2,
  simp only [cinv.g],
  generalize hq : i.he.symm = q, rw hq at inv,
  rw [cinv.he, cont_diff_at.to_local_homeomorph_coe i.ha.cont_diff_at i.has_dhe le_top] at inv,
  simp only [cinv.h, cinv.f', local_equiv.left_inv _ m.1] at inv,
  simp only [inv, local_equiv.left_inv _ m.1],
end

-- h⁻¹ passes through it's first argument
lemma cinv.inv_fst (i : cinv f c z) : ∀ x, x ∈ i.he.target → (i.he.symm x).1 = x.1 := begin
  intros x m,
  have e : i.he (i.he.symm x) = x := i.he.right_inv m,
  generalize hq : i.he.symm x = q, rw hq at e,
  rw [cinv.he, cont_diff_at.to_local_homeomorph_coe i.ha.cont_diff_at i.has_dhe le_top, cinv.h] at e,
  rw ←e, 
end

-- g right inverts locally
lemma cinv.right_inv (i : cinv f c z) : ∀ᶠ x : ℂ × T in 𝓝 (c,f c z), f x.1 (i.g x.1 x.2) = x.2 := begin
  set t : set (ℂ × T) := (ext_chart_at II (c,f c z)).source ∩ (ext_chart_at II (c,f c z)) ⁻¹' i.he.target,
  have o : is_open t :=
    (continuous_on_ext_chart_at _ _).preimage_open_of_open (is_open_ext_chart_at_source _ _) i.he.open_target,
  have m' : (c, ext_chart_at I (f c z) (f c z)) ∈ i.he.to_local_equiv.target, {
    have m := cont_diff_at.image_mem_to_local_homeomorph_target i.ha.cont_diff_at i.has_dhe le_top,
    have e : i.h (c, i.z') = (c, ext_chart_at I (f c z) (f c z)) :=
      by simp only [cinv.h, cinv.z', cinv.f', local_equiv.left_inv _ (mem_ext_chart_source _ _)],
    rw e at m, exact m,
  },
  have m : (c,f c z) ∈ t :=
    by simp only [m', mem_inter_iff, mem_preimage, mem_ext_chart_source, true_and, ext_chart_at_prod,
        local_equiv.prod_coe, ext_chart_at_eq_refl, local_equiv.refl_coe, id, local_equiv.prod_source,
        prod_mk_mem_set_prod_eq, local_equiv.refl_source, mem_univ],
  have fm : ∀ᶠ x : ℂ × T in 𝓝 (c,f c z),
      f x.1 ((ext_chart_at I z).symm (i.he.symm (x.1, ext_chart_at I (f c z) x.2)).2)
      ∈ (ext_chart_at I (f c z)).source, {
    refine continuous_at.eventually_mem _ (is_open_ext_chart_at_source _ _) _, {
      apply i.fa.continuous_at.curry_comp_of_eq continuous_at_fst,
      refine continuous_at.comp _ _,
      simp only [i.inv_at], exact continuous_at_ext_chart_at_symm I _,
      apply continuous_at_snd.comp,
      refine (local_homeomorph.continuous_at i.he.symm _).comp _,
      simp only [m', local_homeomorph.symm_source],
      refine continuous_at_fst.prod ((continuous_at_ext_chart_at I _).comp_of_eq continuous_at_snd rfl),
      simp only [i.inv_at, local_equiv.left_inv _ (mem_ext_chart_source _ _)],
    }, {
      simp only [i.inv_at, local_equiv.left_inv _ (mem_ext_chart_source _ _)], apply mem_ext_chart_source,
    },
  },
  refine fm.mp (filter.eventually_of_mem (o.mem_nhds m) _), rintros x m mf,
  simp only [mem_inter_iff, mem_preimage, ext_chart_at_prod, ext_chart_at_eq_refl,
    local_equiv.prod_source, local_equiv.refl_source, mem_prod_eq, mem_univ, true_and,
    local_equiv.prod_coe, local_equiv.refl_coe, id] at m,
  have inv := i.he.right_inv m.2,
  simp only [cinv.g],
  generalize hq : i.he.symm = q, rw hq at inv mf,
  rw [cinv.he, cont_diff_at.to_local_homeomorph_coe i.ha.cont_diff_at i.has_dhe le_top] at inv,
  have q1 : (q (x.1, ext_chart_at I (f c z) x.2)).1 = x.1 := by simp only [←hq, i.inv_fst _ m.2],
  simp only [cinv.h, cinv.f', prod.eq_iff_fst_eq_snd_eq, q1] at inv,
  nth_rewrite 1 ←local_equiv.left_inv _ m.1, nth_rewrite 1 ←inv.2, refine (local_equiv.left_inv _ mf).symm,
end
 
-- The inverse is holomorphic
lemma cinv.he_symm_holomorphic (i : cinv f c z) : holomorphic_at II II i.he.symm (c,i.fz') := begin
  apply analytic_at.holomorphic_at,
  have d : cont_diff_at ℂ ⊤ i.he.symm _ := cont_diff_at.to_local_inverse i.ha.cont_diff_at i.has_dhe le_top,
  have e : i.h (c, i.z') = (c, i.fz') := by simp only [cinv.h, cinv.fz', cinv.f', i.zz],
  rw e at d, exact (cont_diff_at_iff_analytic_at2 le_top).mp d,
end
lemma cinv.ga (i : cinv f c z) : holomorphic_at II I (uncurry i.g) (c,f c z) := begin
  simp only [cinv.g, uncurry],
  apply (holomorphic_at.ext_chart_at_symm (mem_ext_chart_target I z)).comp_of_eq,
  refine holomorphic_at_snd.comp (i.he_symm_holomorphic.comp_of_eq _ _),
  apply holomorphic_at_fst.prod,
  refine (holomorphic_at.ext_chart_at _).comp holomorphic_at_snd,
  exact mem_ext_chart_source _ _, refl, exact i.inv_at,
end

-- The 1D inverse function theorem for complex manifolds (parameterized version)
theorem complex_inverse_fun {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : holomorphic_at II I (uncurry f) (c,z)) (nc : mfderiv I I (f c) z ≠ 0)
    : ∃ g : ℂ → T → S, holomorphic_at II I (uncurry g) (c,f c z) ∧
        (∀ᶠ x : ℂ × S in 𝓝 (c,z), g x.1 (f x.1 x.2) = x.2) ∧
        (∀ᶠ x : ℂ × T in 𝓝 (c,f c z), f x.1 (g x.1 x.2) = x.2) := begin
  have i : cinv f c z := { fa := fa, nc := nc },
  use [i.g, i.ga, i.left_inv, i.right_inv],
end

-- The 1D inverse function theorem for complex manifolds (nonparameterized version)
theorem complex_inverse_fun' {f : S → T} {z : S} (fa : holomorphic_at I I f z) (nc : mfderiv I I f z ≠ 0)
    : ∃ g : T → S, holomorphic_at I I g (f z) ∧
        (∀ᶠ x in 𝓝 z, g (f x) = x) ∧ (∀ᶠ x in 𝓝 (f z), f (g x) = x) := begin
  set f' : ℂ → S → T := λ c z, f z,
  have fa' : holomorphic_at II I (uncurry f') (0,z) := fa.comp_of_eq holomorphic_at_snd rfl,
  rcases complex_inverse_fun fa' nc with ⟨g,ga,gf,fg⟩,
  use [g 0, ga.comp (holomorphic_at_const.prod holomorphic_at_id),
    (continuous_at_const.prod continuous_at_id).eventually gf,
    (continuous_at_const.prod continuous_at_id).eventually fg],
end

-- The global 1D inverse function theorem (open case)
theorem global_complex_inverse_fun_open {f : ℂ → S → T} [nonempty S] {s : set (ℂ × S)}
    (fa : holomorphic_on II I (uncurry f) s) (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : inj_on (λ p : ℂ × S, (p.1, f p.1 p.2)) s) (so : is_open s)
    : ∃ g : ℂ → T → S, holomorphic_on II I (uncurry g) ((λ p : ℂ × S, (p.1, f p.1 p.2)) '' s) ∧
        (∀ p : ℂ × S, p ∈ s → g p.1 (f p.1 p.2) = p.2) := begin
  have i : ∀ p : ℂ × S, p ∈ s → cinv f p.1 p.2, { rintros ⟨c,z⟩ m, exact { fa := fa _ m, nc := nc _ m } },
  generalize hg : (λ c w, @dite S (∃ z, (c,z) ∈ s ∧ f c z = w) (classical.dec _)
    (λ h, classical.some h) (λ h, classical.arbitrary S)) = g,
  have left : ∀ c z, (c,z) ∈ s → g c (f c z) = z, {
    intros c z m,
    have h : ∃ x, (c,x) ∈ s ∧ f c x = f c z := ⟨z,m,rfl⟩,
    simp only [←hg, @dif_pos _ (classical.dec _) h],
    rcases classical.some_spec h with ⟨m0,w0⟩,
    have left := (i _ m).left_inv.self,
    have e : (c, classical.some h) = (c, ((i _ m).g c (f c z))), {
      refine (inj.eq_iff m0 _).mp _, simp only [left, m], simp only [left, w0],
    },
    rw left at e, exact (prod.ext_iff.mp e).2,
  },
  have ge : ∀ (p : ℂ × S) (m : p ∈ s), ∀ᶠ q : ℂ × T in 𝓝 (p.1, f p.1 p.2), g q.1 q.2 = (i p m).g q.1 q.2, {
    rintros ⟨c,z⟩ m, simp only,
    have n := nontrivial_holomorphic_at_of_mfderiv_ne_zero (fa _ m).in2 (nc _ m), simp only at n,
    simp only [n.nhds_eq_map_nhds_param (fa _ m), filter.eventually_map],
    apply (i _ m).left_inv.mp, apply (so.eventually_mem m).mp,
    apply eventually_of_forall, rintros ⟨e,w⟩ wm gf,
    simp only [left _ _ wm, gf],
  },
  use g, constructor, {
    rintros ⟨c,w⟩ wm,
    rcases (mem_image _ _ _).mp wm with ⟨⟨c',z⟩,zm,e⟩,
    simp only [prod.ext_iff] at e, simp only [e.1] at e zm, simp only [←e.2],
    exact (i _ zm).ga.congr (filter.eventually_eq.symm (ge _ zm)),
  }, {
    rintros ⟨c,z⟩ m, exact left _ _ m,
  },
end

-- The global 1D inverse function theorem (compact case)
-- Given a compact set on which f is injective and locally injective, it has a neighborhood 
theorem global_complex_inverse_fun_compact {f : ℂ → S → T} [nonempty S] [t2_space T] {s : set (ℂ × S)}
    (fa : holomorphic_on II I (uncurry f) s) (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : inj_on (λ p : ℂ × S, (p.1, f p.1 p.2)) s) (sc : is_compact s)
    : ∃ g : ℂ → T → S, holomorphic_on II I (uncurry g) ((λ p : ℂ × S, (p.1, f p.1 p.2)) '' s) ∧
        (∀ᶠ p : ℂ × S in 𝓝ˢ s, g p.1 (f p.1 p.2) = p.2) := begin
  -- Enlarge s while preserving injectivity
  have t : ∃ t, is_open t ∧ s ⊆ t ∧ inj_on (λ p : ℂ × S, (p.1, f p.1 p.2)) t, {
    apply locally_injective_on_compact (λ _ m, continuous_at_fst.prod (fa _ m).continuous_at) sc inj,
    rintros ⟨c,z⟩ m, rcases complex_inverse_fun (fa _ m) (nc _ m) with ⟨g,ga,gf,fg⟩,
    rcases eventually_nhds_iff.mp gf with ⟨t,gf,o,m⟩,
    use [t, o.mem_nhds m], rintros ⟨c0,z0⟩ m0 ⟨c1,z1⟩ m1 e,
    simp only [uncurry, prod.ext_iff] at e ⊢, use e.1,
    have e0 := gf _ m0, have e1 := gf _ m1, simp only at e0 e1,
    rw [←e0, ←e1, e.2, ←e.1],
  },
  rcases t with ⟨t,ot,st,ti⟩,
  -- Shrink t to recover openness and deriv ≠ 0 
  set u := t ∩ {p | holomorphic_at II I (uncurry f) p ∧ mfderiv I I (f p.1) p.2 ≠ 0},
  have tu : u ⊆ t := inter_subset_left _ _,  
  have su : s ⊆ u := subset_inter st (subset_inter fa nc),
  have uo : is_open u, {
    apply ot.inter, rw is_open_iff_eventually, rintros ⟨c,z⟩ ⟨fa,nc⟩,
    refine fa.eventually.mp ((mfderiv_ne_zero_eventually' fa nc).mp (eventually_of_forall _)),
    rintros ⟨c,z⟩ nc fa, use [fa, nc],
  },
  -- Find our inverse on u
  rcases global_complex_inverse_fun_open _ _ (ti.mono tu) uo with ⟨g,ga,gf⟩,
  use [g, ga.mono (image_subset _ su), filter.eventually_of_mem (uo.mem_nhds_set.mpr su) gf],
  exact λ _ m, (inter_subset_right _ _ m).1,
  exact λ _ m, (inter_subset_right _ _ m).2,
end
 
-- The global 1D inverse function theorem on an open set, nonparameterized version.
theorem global_complex_inverse_fun_open' {f : S → T} [nonempty S] {s : set S}
    (fa : holomorphic_on I I f s) (nc : ∀ z, z ∈ s → mfderiv I I f z ≠ 0) (inj : inj_on f s) (so : is_open s)
    : ∃ g : T → S, holomorphic_on I I g (f '' s) ∧ (∀ z, z ∈ s → g (f z) = z) := begin
  set f' := λ (c : ℂ) (z : S), f z,
  have nc' : ∀ p : ℂ × S, p ∈ (univ : set ℂ) ×ˢ s → mfderiv I I (f' p.1) p.2 ≠ 0, {
    rintros ⟨c,z⟩ ⟨cu,zs⟩, exact nc _ zs,
  },
  have inj' : inj_on (λ p : ℂ × S, (p.1, f' p.1 p.2)) (univ ×ˢ s), {
    rintros ⟨c0,z0⟩ ⟨cu0,zs0⟩ ⟨c1,z1⟩ ⟨cu1,zs1⟩ h, simp only [prod.ext_iff] at h zs0 zs1,
    rw [h.1, inj zs0 zs1], exact h.2,
  },
  have fa' : holomorphic_on II I (uncurry f') (univ ×ˢ s), {
    rintros ⟨c,z⟩ ⟨cu,zs⟩, exact (fa z zs).comp_of_eq holomorphic_at_snd rfl,
  },
  rcases global_complex_inverse_fun_open fa' nc' inj' (is_open_univ.prod so) with ⟨g,ga,gf⟩,
  use g 0, constructor, {
    rintros z ⟨w,m⟩, refine (ga ⟨0,z⟩ ⟨⟨0,w⟩,⟨mem_univ _,m.1⟩,_⟩).in2,
    simp only [prod.ext_iff, eq_self_iff_true, true_and], exact m.2,
  }, {
    intros z m, exact gf ⟨0,z⟩ ⟨mem_univ _,m⟩,
  },
end

-- Nonzero derivative holomorphic functions are locally injective
theorem holomorphic_at.local_inj {f : S → T} {z : S} [t2_space S] [t2_space T]
    (fa : holomorphic_at I I f z) (nc : mfderiv I I f z ≠ 0)
    : ∀ᶠ p : S × S in 𝓝 (z,z), f p.1 = f p.2 → p.1 = p.2 := begin 
  rcases complex_inverse_fun' fa nc with ⟨g,ga,gf,fg⟩,
  have n : nontrivial_holomorphic_at g (f z), {
    rw ←gf.self at fa,
    refine (nontrivial_holomorphic_at.anti _ fa ga).2,
    exact (nontrivial_holomorphic_at_id _).congr (filter.eventually_eq.symm fg),
  },
  have o := n.nhds_eq_map_nhds, rw gf.self at o,
  simp only [nhds_prod_eq, o, filter.prod_map_map_eq, filter.eventually_map],
  refine (fg.prod_mk fg).mp (eventually_of_forall _), rintros ⟨x,y⟩ ⟨ex,ey⟩ h,
  simp only [ex,ey] at h, simp only [h],
end

-- Nonzero derivative holomorphic functions are locally injective, parameterized versions
theorem holomorphic_at.local_inj'' {f : ℂ → S → T} {c : ℂ} {z : S} [t2_space S] [t2_space T]
    (fa : holomorphic_at II I (uncurry f) (c,z)) (nc : mfderiv I I (f c) z ≠ 0)
    : ∀ᶠ p : (ℂ × S) × (ℂ × S) in 𝓝 ((c,z),(c,z)),
        p.1.1 = p.2.1 → f p.1.1 p.1.2 = f p.2.1 p.2.2 → p.1 = p.2 := begin 
  rcases complex_inverse_fun fa nc with ⟨g,ga,gf,fg⟩,
  have n : nontrivial_holomorphic_at (g c) (f c z), {
    have e : (c,z) = (c,g c (f c z)) := by rw gf.self,
    rw e at fa,
    refine (nontrivial_holomorphic_at.anti _ fa.in2 ga.in2).2,
    refine (nontrivial_holomorphic_at_id _).congr _,
    refine ((continuous_at_const.prod continuous_at_id).eventually fg).mp (eventually_of_forall _),
    exact λ _ e, e.symm,
  },
  have o := n.nhds_eq_map_nhds_param ga, simp only [gf.self] at o,
  rw [nhds_prod_eq, o], simp only [filter.prod_map_map_eq, filter.eventually_map],
  refine (fg.prod_mk fg).mp (eventually_of_forall _), rintros ⟨x,y⟩ ⟨ex,ey⟩ h1 h2,
  simp only [h1] at ex ey h2 ⊢, simp only [ex,ey] at h2, simp only [h2],
end
theorem holomorphic_at.local_inj' {f : ℂ → S → T} {c : ℂ} {z : S} [t2_space S] [t2_space T]
    (fa : holomorphic_at II I (uncurry f) (c,z)) (nc : mfderiv I I (f c) z ≠ 0)
    : ∀ᶠ p : ℂ × S × S in 𝓝 (c,z,z), f p.1 p.2.1 = f p.1 p.2.2 → p.2.1 = p.2.2 := begin 
  set g : ℂ × S × S → (ℂ × S) × (ℂ × S) := λ p, ((p.1,p.2.1),(p.1,p.2.2)), 
  have t : tendsto g (𝓝 (c,z,z)) (𝓝 ((c,z),(c,z))) := continuous.continuous_at (by continuity),
  refine (t.eventually (fa.local_inj'' nc)).mp (eventually_of_forall _),
  rintros ⟨e,x,y⟩ inj fe, exact (prod.ext_iff.mp (inj rfl fe)).2,
end