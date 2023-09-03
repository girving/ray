-- The Riemann sphere (𝕊)

import analysis.analytic.basic
import analysis.complex.basic
import analysis.complex.removable_singularity
import data.complex.basic
import topology.alexandroff

import analytic
import at_inf
import complex_manifold
import one_dimension

open complex (abs)
open filter (eventually_of_forall tendsto at_top)
open function (curry uncurry)
open set
open_locale topology alexandroff
noncomputable theory

-- The Riemann sphere, as a complex manifold
def riemann_sphere : Type := alexandroff ℂ

namespace riemann_sphere
localized "notation (name := riemann_sphere) `𝕊` := riemann_sphere" in riemann_sphere

-- Basic instances for 𝕊
instance : has_coe_t ℂ 𝕊 := ⟨λ z, (z : alexandroff ℂ)⟩
instance : has_zero 𝕊 := ⟨((0 : ℂ) : 𝕊)⟩
instance : inhabited 𝕊 := ⟨0⟩
instance : topological_space 𝕊 := alexandroff.topological_space
instance riemann_sphere.t1_space : t1_space 𝕊 := alexandroff.t1_space
instance riemann_sphere.normal_space : normal_space 𝕊 := alexandroff.normal_space
instance : compact_space 𝕊 := alexandroff.compact_space
instance : connected_space 𝕊 := alexandroff.connected_space

lemma coe_zero : (↑(0 : ℂ) : 𝕊) = 0 := rfl
lemma coe_zero_c : (↑(0 : ℂ) : ℂ) = 0 := rfl
@[simp] lemma coe_eq_coe {z w : ℂ} : (z : 𝕊) = w ↔ z = w := alexandroff.coe_eq_coe
lemma coe_eq_zero (z : ℂ) : (z : 𝕊) = 0 ↔ z = 0 := by simp only [←coe_zero, coe_eq_coe]

-- ℂ → 𝕊 is injective and continuous
lemma injective_coe : function.injective (coe : ℂ → 𝕊) := option.some_injective ℂ
lemma continuous_coe : continuous (coe : ℂ → 𝕊) := alexandroff.continuous_coe

-- Clean recursion principle
def rec {C : 𝕊 → Sort*} (h_finite : Π z : ℂ, C ↑z) (h_inf : C ∞) : ∀ z : 𝕊, C z := begin
  intro z, induction z using option.rec, exact h_inf, exact h_finite z,
end
@[simp] lemma rec_coe {C : 𝕊 → Sort*} {f : Π z : ℂ, C ↑z} {i : C ∞} (z : ℂ) : (z : 𝕊).rec f i = f z := rfl
@[simp] lemma rec_inf {C : 𝕊 → Sort*} {f : Π z : ℂ, C ↑z} {i : C ∞} : riemann_sphere.rec f i ∞ = i := rfl
lemma map_rec {A B : Sort*} (g : A → B) {f : ℂ → A} {i : A} {z : 𝕊} : g (z.rec f i) = z.rec (g ∘ f) (g i) := begin
  induction z using riemann_sphere.rec, simp only [rec_coe], simp only [rec_inf],
end

-- ∞ is not 0 or finite
lemma inf_ne_coe {z : ℂ} : (∞ : 𝕊) ≠ ↑z :=
  by simp only [ne.def, alexandroff.infty_ne_coe, not_false_iff]
lemma inf_ne_zero : (∞ : 𝕊) ≠ (0 : 𝕊) := begin
  have e : (0 : 𝕊) = ((0 : ℂ) : 𝕊) := rfl, rw e, exact inf_ne_coe,
end
lemma coe_ne_inf {z : ℂ} : (z : 𝕊) ≠ ∞ := inf_ne_coe.symm 
lemma coe_eq_inf_iff {z : ℂ} : (z : 𝕊) = ∞ ↔ false := ⟨coe_ne_inf, false.elim⟩

-- Conversion to ℂ, sending ∞ to 0
def to_complex (z : 𝕊) : ℂ := z.elim 0 id
@[simp] lemma to_complex_coe {z : ℂ} : (z : 𝕊).to_complex = z := rfl 
@[simp] lemma to_complex_inf : riemann_sphere.to_complex (∞ : 𝕊) = 0 := rfl
lemma coe_to_complex {z : 𝕊} (h : z ≠ ∞) : ↑(z.to_complex) = z := begin
  induction z using riemann_sphere.rec, simp only [to_complex_coe],
  simp only [ne.def, eq_self_iff_true, not_true] at h, exfalso, exact h,
end
@[simp] lemma to_complex_zero : (0 : 𝕊).to_complex = 0 := by rw [←coe_zero, to_complex_coe]
lemma continuous_at_to_complex {z : ℂ} : continuous_at to_complex z := begin
  simp only [alexandroff.continuous_at_coe, function.comp, to_complex_coe], exact continuous_at_id,
end
lemma continuous_on_to_complex : continuous_on to_complex {∞}ᶜ := begin
  intros z m, induction z using riemann_sphere.rec, exact continuous_at_to_complex.continuous_within_at,
  simp only [mem_compl_iff, mem_singleton, not_true] at m, exfalso, exact m,
end

-- Inversion in 𝕊
def inv (z : 𝕊) : 𝕊 := if z = 0 then ∞ else ↑(z.to_complex⁻¹)
instance : has_inv 𝕊 := ⟨riemann_sphere.inv⟩
lemma inv_def (z : 𝕊) : z⁻¹ = riemann_sphere.inv z := rfl
instance : has_involutive_inv 𝕊 := {
  inv := has_inv.inv,
  inv_inv := begin
    simp_rw [inv_def, inv], apply rec, {
      intro z, by_cases z0 : z = 0,
      simp only [z0, inf_ne_zero, with_top.coe_zero, eq_self_iff_true, if_true, to_complex_inf, inv_zero, if_false],
      simp only [z0, with_top.coe_eq_zero, to_complex_coe, if_false, inv_eq_zero, inv_inv],
    }, {
      simp only [to_complex_inf, inv_zero, with_top.coe_zero, ite_eq_right_iff, imp_self, if_true],
    },
  end,
}
@[simp] lemma inv_zero' : (0 : 𝕊)⁻¹ = ∞ := by simp only [inv_def, inv, eq_self_iff_true, if_true]
@[simp] lemma inv_inf : ((∞ : 𝕊)⁻¹ : 𝕊) = 0 := by simp [inv_def, inv, inf_ne_zero]  -- squeeze_simp fails for some reason
lemma inv_coe {z : ℂ} (z0 : z ≠ 0) : (z : 𝕊)⁻¹ = ↑((z : ℂ)⁻¹) :=
  by simp only [inv_def, inv, z0, with_top.coe_eq_zero, to_complex_coe, if_false]
@[simp] lemma inv_eq_inf {z : 𝕊} : z⁻¹ = ∞ ↔ z = 0 := begin
  induction z using riemann_sphere.rec,
  simp only [inv_def, inv, not_not, imp_false, ite_eq_left_iff, alexandroff.coe_ne_infty],
  simp only [inv_inf], exact ⟨eq.symm, eq.symm⟩,
end
@[simp] lemma inv_eq_zero {z : 𝕊} : z⁻¹ = 0 ↔ z = ∞ := begin
  induction z using riemann_sphere.rec,
  simp only [inv_def, inv, to_complex_coe],
  by_cases z0 : (z : 𝕊) = 0, simp only [if_pos, z0, inf_ne_zero, inf_ne_zero.symm],
  simp only [if_neg z0, coe_ne_inf, iff_false], rw [coe_eq_zero, inv_eq_zero],
  simp only [with_top.coe_eq_zero] at z0, exact z0,
  simp only [inv_inf, eq_self_iff_true],
end

lemma to_complex_inv {z : 𝕊} : z⁻¹.to_complex = z.to_complex⁻¹ := begin
  induction z using riemann_sphere.rec, by_cases z0 : z = 0,
  simp only [z0, with_top.coe_zero, inv_zero, to_complex_inf, to_complex_zero, inv_zero', eq_self_iff_true],
  simp only [z0, inv_coe, ne.def, not_false_iff, to_complex_coe],
  simp only [inv_inf, to_complex_zero, to_complex_inf, inv_zero', inv_zero, eq_self_iff_true],
end

-- Inversion is continuous
lemma continuous_inv : continuous (λ z : 𝕊, z⁻¹) := begin
  rw continuous_iff_continuous_on_univ, intros z _, apply continuous_at.continuous_within_at,
  induction z using riemann_sphere.rec, {
    simp only [alexandroff.continuous_at_coe, function.comp, inv_def, inv, with_top.coe_eq_zero, to_complex_coe],
    by_cases z0 : z = 0, {
      simp only [z0, continuous_at, alexandroff.nhds_infty_eq, eq_self_iff_true, if_true,
        filter.coclosed_compact_eq_cocompact],
      simp only [←nhds_within_compl_singleton_sup_pure, filter.tendsto_sup],
      constructor, {
        refine filter.tendsto.mono_right _ le_sup_left,
        apply @tendsto_nhds_within_congr _ _ _ (λ z : ℂ, (↑z⁻¹ : 𝕊)),
        intros z m, rw mem_compl_singleton_iff at m, simp only [m, if_false],
        apply filter.tendsto_map.comp,
        rw ←@tendsto_at_inf_iff_tendsto_nhds_zero ℂ ℂ _ _ (λ z : ℂ, z),
        exact filter.tendsto_id.mono_right at_inf_le_cocompact,
      }, {
        refine filter.tendsto.mono_right _ le_sup_right,
        simp only [filter.pure_zero, filter.tendsto_pure, ite_eq_left_iff, filter.eventually_zero,
          eq_self_iff_true, not_true, is_empty.forall_iff],
      },
    }, {
      have e : ∀ᶠ w : ℂ in 𝓝 z, ite (w = 0) ∞ (↑w⁻¹ : 𝕊) = ↑w⁻¹, {
        refine (continuous_at_id.eventually_ne z0).mp (eventually_of_forall (λ w w0, _)),
        simp only [ne.def, id.def] at w0, simp only [w0, if_false],
      },
      rw continuous_at_congr e, exact continuous_coe.continuous_at.comp (tendsto_inv₀ z0),
    },
  }, {
    simp only [alexandroff.continuous_at_infty', function.comp, filter.coclosed_compact_eq_cocompact, inv_inf,
      ←at_inf_eq_cocompact],
    have e : ∀ᶠ z : ℂ in at_inf, ↑z⁻¹ = (↑z : 𝕊)⁻¹, {
      refine (eventually_at_inf 0).mp (eventually_of_forall (λ z z0, _)),
      simp only [gt_iff_lt, complex.norm_eq_abs, absolute_value.pos_iff] at z0, rw inv_coe z0,
    },
    apply filter.tendsto.congr' e,
    exact filter.tendsto.comp continuous_coe.continuous_at inv_tendsto_at_inf',
  },
end
instance : has_continuous_inv 𝕊 := ⟨continuous_inv⟩

-- Inversion is a homeomorphism
def inv_equiv : 𝕊 ≃ 𝕊 := {
  to_fun := has_inv.inv, inv_fun := has_inv.inv,
  left_inv := inv_inv, right_inv := inv_inv,
}
def inv_homeomorph : 𝕊 ≃ₜ 𝕊 := {
  to_equiv := inv_equiv,
  continuous_to_fun := continuous_inv,
  continuous_inv_fun := continuous_inv,
}
@[simp] lemma inv_equiv_apply (z : 𝕊) : inv_equiv z = z⁻¹ := by simp only [inv_equiv, equiv.coe_fn_mk]
@[simp] lemma inv_equiv_symm : inv_equiv.symm = inv_equiv :=
  by simp only [equiv.ext_iff, inv_equiv, equiv.coe_fn_symm_mk, equiv.coe_fn_mk, eq_self_iff_true, forall_const]
@[simp] lemma inv_homeomorph_apply (z : 𝕊) : inv_homeomorph z = z⁻¹ :=
  by simp only [inv_homeomorph, homeomorph.homeomorph_mk_coe, inv_equiv_apply]
@[simp] lemma inv_homeomorph_symm : inv_homeomorph.symm = inv_homeomorph :=
  homeomorph.ext (by simp only [inv_homeomorph, homeomorph.homeomorph_mk_coe_symm, inv_equiv_symm,
    homeomorph.homeomorph_mk_coe, eq_self_iff_true, forall_const])

-- Charts for 𝕊
def coe_local_equiv : local_equiv ℂ 𝕊 := {
  to_fun := coe,
  inv_fun := to_complex,
  source := univ,
  target := {∞}ᶜ,
  map_source' := λ z m,
    by simp only [mem_compl_iff, mem_singleton_iff, alexandroff.coe_ne_infty, not_false_iff],
  map_target' := λ z m, mem_univ _,
  left_inv' := λ z m, to_complex_coe,
  right_inv' := λ z m, coe_to_complex m,
}
def coe_local_homeomorph : local_homeomorph ℂ 𝕊 := {
  to_local_equiv := coe_local_equiv,
  open_source := is_open_univ,
  open_target := is_open_compl_singleton,
  continuous_to_fun := continuous_coe.continuous_on,
  continuous_inv_fun := continuous_on_to_complex,
}
def inv_coe_local_homeomorph : local_homeomorph ℂ 𝕊 :=
  coe_local_homeomorph.trans inv_homeomorph.to_local_homeomorph
lemma coe_local_equiv_apply (z : ℂ) : coe_local_equiv z = ↑z := rfl
lemma coe_local_equiv_symm_apply (z : 𝕊) : coe_local_equiv.symm z = z.to_complex := rfl

-- Chart structure for 𝕊
instance : charted_space ℂ 𝕊 := {
  atlas := {e | e = coe_local_homeomorph.symm ∨ e = inv_coe_local_homeomorph.symm},
  chart_at := λ z, z.rec (λ _, coe_local_homeomorph.symm) inv_coe_local_homeomorph.symm,
  mem_chart_source := begin
    intro z, induction z using riemann_sphere.rec, {
      simp only [coe_local_homeomorph, coe_local_equiv, rec_coe, local_homeomorph.symm_to_local_equiv,
        local_equiv.symm_source, mem_compl_iff, mem_singleton_iff, alexandroff.coe_ne_infty, not_false_iff],
    }, {
      simp only [inv_coe_local_homeomorph, coe_local_homeomorph, coe_local_equiv, rec_inf,
        local_homeomorph.symm_to_local_equiv, local_homeomorph.trans_to_local_equiv, local_equiv.symm_source,
        local_equiv.trans_target, homeomorph.to_local_homeomorph_target, local_homeomorph.coe_coe_symm,
        homeomorph.to_local_homeomorph_symm_apply, inv_homeomorph_symm, univ_inter, mem_compl_iff,
        mem_preimage, inv_homeomorph_apply, inv_inf, mem_singleton_iff],
      exact inf_ne_zero.symm,
    },
  end,
  chart_mem_atlas := begin
    intro z, induction z using riemann_sphere.rec,
    simp only [rec_coe, mem_set_of_eq, eq_self_iff_true, true_or],
    simp only [rec_inf, eq_self_iff_true, mem_set_of_eq, or_true],
  end,
}

-- There are just two charts, and chart_at is what you expect
lemma two_charts {e : local_homeomorph 𝕊 ℂ} (m : e ∈ charted_space.atlas ℂ 𝕊)
    : e = coe_local_homeomorph.symm ∨ e = inv_coe_local_homeomorph.symm := m
@[simp] lemma chart_at_coe {z : ℂ} : chart_at ℂ (z : 𝕊) = coe_local_homeomorph.symm := rfl
@[simp] lemma chart_at_inf : @chart_at ℂ _ 𝕊 _ _ ∞ = inv_coe_local_homeomorph.symm := rfl
@[simp] lemma ext_chart_at_coe {z : ℂ} : ext_chart_at I (z : 𝕊) = coe_local_equiv.symm :=
  by simp only [coe_local_homeomorph, ext_chart_at, local_homeomorph.extend, chart_at_coe,
    local_homeomorph.symm_to_local_equiv, model_with_corners_self_local_equiv, local_equiv.trans_refl]
@[simp] lemma ext_chart_at_zero : ext_chart_at I (0 : 𝕊) = coe_local_equiv.symm :=
  by simp only [←coe_zero, ext_chart_at_coe]
@[simp] lemma ext_chart_at_inf : @ext_chart_at ℂ ℂ 𝕊 ℂ _ _ _ _ _ I _ ∞ =
    inv_equiv.to_local_equiv.trans coe_local_equiv.symm := begin
  apply local_equiv.ext, {
    intro z, simp only [ext_chart_at, inv_coe_local_homeomorph, coe_local_homeomorph, inv_homeomorph,
      local_homeomorph.extend, chart_at_inf, local_homeomorph.symm_to_local_equiv, local_homeomorph.trans_to_local_equiv,
      model_with_corners_self_local_equiv, local_equiv.trans_refl, local_equiv.coe_trans_symm,
      local_homeomorph.coe_coe_symm, homeomorph.to_local_homeomorph_symm_apply, homeomorph.homeomorph_mk_coe_symm,
      inv_equiv_symm, local_equiv.coe_trans, equiv.to_local_equiv_apply],
  }, {
    intro z, simp only [ext_chart_at, inv_coe_local_homeomorph, coe_local_homeomorph, inv_homeomorph, inv_equiv,
      local_homeomorph.extend, chart_at_inf, local_homeomorph.symm_to_local_equiv,
      local_homeomorph.trans_to_local_equiv, model_with_corners_self_local_equiv, local_equiv.trans_refl,
      local_equiv.symm_symm, local_equiv.coe_trans, local_homeomorph.coe_coe, homeomorph.to_local_homeomorph_apply,
      homeomorph.homeomorph_mk_coe, equiv.coe_fn_mk, local_equiv.coe_trans_symm, equiv.to_local_equiv_symm_apply,
      equiv.coe_fn_symm_mk],
  }, {
    simp only [ext_chart_at, inv_coe_local_homeomorph, coe_local_homeomorph, inv_homeomorph,
      local_homeomorph.extend, chart_at_inf, local_homeomorph.symm_to_local_equiv,
      local_homeomorph.trans_to_local_equiv, model_with_corners_self_local_equiv, local_equiv.trans_refl,
      local_equiv.symm_source, local_equiv.trans_target, homeomorph.to_local_homeomorph_target,
      local_homeomorph.coe_coe_symm, homeomorph.to_local_homeomorph_symm_apply, homeomorph.homeomorph_mk_coe_symm,
      inv_equiv_symm, local_equiv.trans_source, equiv.to_local_equiv_source, equiv.to_local_equiv_apply],
  },
end
@[simp] lemma ext_chart_at_inf_apply {x : 𝕊} : @ext_chart_at ℂ ℂ 𝕊 ℂ _ _ _ _ _ I _ ∞ x = x⁻¹.to_complex :=
  by simp only [ext_chart_at_inf, local_equiv.trans_apply, coe_local_equiv_symm_apply, equiv.to_local_equiv_apply,
    inv_equiv_apply]

-- 𝕊 has consistently analytic charts
instance : has_groupoid 𝕊 (analytic_groupoid I) := begin
  apply has_groupoid_of_pregroupoid, intros f g fa ga,
  cases two_charts fa with fh fh, {
    cases two_charts ga with gh gh, {
      simp only [fh, gh], exact ext_chart_at_self_analytic _,
    }, {
      simp [fh, gh, inv_coe_local_homeomorph, coe_local_homeomorph, coe_local_equiv, inv_homeomorph, inv_equiv,
        function.comp],
      have e : ((coe : ℂ → 𝕊) ⁻¹' {0})ᶜ = {(0 : ℂ)}ᶜ, {
        ext, simp only [mem_singleton_iff, mem_compl_iff, mem_preimage, with_top.coe_eq_zero],
      },
      rw e, clear e,
      apply @analytic_on.congr _ _ _ _ _ _ _ _ _ _ (λ z, z⁻¹),
      apply analytic_on_inv, exact is_open_compl_singleton,
      intros z z0, simp only [mem_compl_iff, mem_singleton_iff] at z0,
      simp only [inv_coe z0, to_complex_coe],
      repeat { apply_instance },
    },
  }, {
    cases two_charts ga with gh gh, {
      simp [fh, gh, inv_coe_local_homeomorph, coe_local_homeomorph, coe_local_equiv, inv_homeomorph,
        inv_equiv, function.comp],
      apply @analytic_on.congr _ _ _ _ _ _ _ _ _ _ (λ z, z⁻¹), {
        intros z m, apply analytic_at_id.inv,
        contrapose m, simp only [not_not] at m,
        simp only [m, mem_compl_iff, mem_preimage, with_top.coe_zero, inv_zero', mem_singleton,
          not_true, not_false_iff],
      }, {
        have e : (λ (x : ℂ), (x : 𝕊)⁻¹) ⁻¹' {(∞ : 𝕊)} = {0}, {
          apply set.ext, intro x, simp only [mem_preimage, mem_singleton_iff, inv_eq_inf, coe_eq_zero],
        },
        rw e, exact is_open_compl_singleton,
      }, {
        intros z m, rw inv_coe, simp only [to_complex_coe],
        contrapose m, simp only [not_not] at m,
        simp only [m, mem_compl_iff, mem_preimage, with_top.coe_zero, inv_zero', mem_singleton,
          not_true, not_false_iff],
      },
      repeat { apply_instance },
    }, {
      simp only [fh, gh], exact ext_chart_at_self_analytic _,
    },
  },
end

-- 𝕊 is a complex manifold
instance : complex_manifold I 𝕊 := {}

-- coe tends to ∞ at_inf
lemma coe_tendsto_inf : tendsto (coe : ℂ → 𝕊) at_inf (𝓝 ∞) := begin
  rw [filter.tendsto_iff_comap, alexandroff.comap_coe_nhds_infty, filter.coclosed_compact_eq_cocompact],
  exact at_inf_le_cocompact,
end
lemma tendsto_inf_iff_tendsto_at_inf {X : Type} {f : filter X} {g : X → ℂ}
    : tendsto (λ x, (g x : 𝕊)) f (𝓝 ∞) ↔ tendsto (λ x, g x) f at_inf := begin
  constructor, {
    intros t, simp only [filter.tendsto_iff_comap] at t ⊢,
    rw [←filter.comap_comap, alexandroff.comap_coe_nhds_infty, filter.coclosed_compact_eq_cocompact,
      ←at_inf_eq_cocompact] at t, exact t,
  }, {
    exact λ h, coe_tendsto_inf.comp h,
  },
end

variables {X : Type} [topological_space X]
variables {Y : Type} [topological_space Y]
variables {T : Type} [topological_space T] [complex_manifold I T]

lemma is_open_map_coe : is_open_map (coe : ℂ → 𝕊) := begin
  intros s o,
  have e : coe '' s = {∞}ᶜ ∩ to_complex ⁻¹' s, {
    apply set.ext, intros z, simp only [mem_image, mem_inter_iff, mem_compl_singleton_iff, mem_preimage],
    constructor,
    rintros ⟨x,m,e⟩, simp only [←e, to_complex_coe, m, and_true], exact inf_ne_coe.symm,
    rintros ⟨n,m⟩, use [z.to_complex,m, coe_to_complex n],
  },
  rw e, exact continuous_on_to_complex.preimage_open_of_open is_open_compl_singleton o,
end

lemma prod_nhds_eq {x : X} {z : ℂ} : 𝓝 (x,(z:𝕊)) = filter.map (λ p : X × ℂ, (p.1,↑p.2)) (𝓝 (x,z)) := begin
  refine le_antisymm _ (continuous_at_fst.prod (continuous_coe.continuous_at.comp continuous_at_snd)),
  apply is_open_map.nhds_le, exact is_open_map.id.prod is_open_map_coe,
end

lemma mem_inf_of_mem_at_inf {s : set ℂ} (f : s ∈ @at_inf ℂ _) : coe '' s ∪ {∞} ∈ 𝓝 (∞:𝕊) := begin
  simp only [alexandroff.nhds_infty_eq, filter.mem_sup, filter.coclosed_compact_eq_cocompact, ←at_inf_eq_cocompact,
    filter.mem_map],
  exact ⟨filter.mem_of_superset f (λ _ m, or.inl (mem_image_of_mem _ m)), or.inr rfl⟩,
end

lemma prod_mem_inf_of_mem_at_inf {s : set (X × ℂ)} {x : X} (f : s ∈ (𝓝 x).prod (@at_inf ℂ _))
    : (λ p : X × ℂ, (p.1,(p.2:𝕊))) '' s ∪ univ ×ˢ {∞} ∈ 𝓝 (x,(∞:𝕊)) := begin
  rcases filter.mem_prod_iff.mp f with ⟨t,tx,u,ui,sub⟩,
  rw nhds_prod_eq, refine filter.mem_prod_iff.mpr ⟨t,tx,coe '' u ∪ {∞},mem_inf_of_mem_at_inf ui,_⟩,
  rintros ⟨y,z⟩ ⟨yt,m⟩,
  simp only [mem_prod_eq, mem_image, mem_union, mem_singleton_iff, mem_univ, true_and, prod.ext_iff] at ⊢ yt m,
  induction z using riemann_sphere.rec, {
    simp only [coe_eq_inf_iff, or_false, coe_eq_coe] at ⊢ m,
    rcases m with ⟨w,wu,wz⟩, refine ⟨⟨y,z⟩,sub (mk_mem_prod yt _),rfl,rfl⟩, rw ←wz, exact wu, 
  }, {
    simp only [eq_self_iff_true, or_true],
  },
end

lemma holomorphic_coe : holomorphic I I (coe : ℂ → 𝕊) := begin
  rw holomorphic_iff, use continuous_coe, intros z,
  simp only [ext_chart_at_coe, ext_chart_at_eq_refl, local_equiv.refl_symm, local_equiv.refl_coe, function.comp.right_id,
    id.def, function.comp, local_equiv.inv_fun_as_coe],
  rw ←local_equiv.inv_fun_as_coe, simp only [coe_local_equiv, to_complex_coe], exact analytic_at_id,
end

lemma holomorphic_at_to_complex {z : ℂ} : holomorphic_at I I (to_complex : 𝕊 → ℂ) z := begin
  rw holomorphic_at_iff, use continuous_at_to_complex,
  simp only [to_complex_coe, function.comp, ext_chart_at_coe, ext_chart_at_eq_refl, local_equiv.refl_coe, id,
    local_equiv.symm_symm, coe_local_equiv_apply, coe_local_equiv_symm_apply],
  exact analytic_at_id,
end

lemma holomorphic_inv : holomorphic I I (λ z : 𝕊, z⁻¹) := begin
  rw holomorphic_iff, use continuous_inv, intros z, induction z using riemann_sphere.rec, {
    simp only [ext_chart_at_coe, local_equiv.symm_symm, function.comp, coe_local_equiv_apply, coe_local_equiv_symm_apply,
      to_complex_coe],
    by_cases z0 : z = 0, {
      simp only [z0, coe_zero, ext_chart_at_inf, local_equiv.trans_apply, coe_local_equiv_symm_apply,
        inv_equiv_apply, equiv.to_local_equiv_apply, inv_zero', inv_inv, to_complex_coe],
      exact analytic_at_id,
    }, {
      simp only [inv_coe z0, ext_chart_at_coe, coe_local_equiv_symm_apply],
      refine (analytic_at_id.inv z0).congr _,
      apply (continuous_at_id.eventually_ne z0).mp (eventually_of_forall (λ w w0, _)),
      rw id at w0, simp only [inv_coe w0, to_complex_coe],
    },
  }, {
    simp only [inv_inf, ext_chart_at_inf, ←coe_zero, ext_chart_at_coe, function.comp, local_equiv.trans_apply,
      equiv.to_local_equiv_apply, inv_equiv_apply, coe_local_equiv_symm_apply, to_complex_coe,
      local_equiv.coe_trans_symm, local_equiv.symm_symm, coe_local_equiv_apply, equiv.to_local_equiv_symm_apply,
      inv_equiv_symm, inv_inv],
    exact analytic_at_id,
  },
end

-- Given ℂ → X, fill in the value at infinity to get 𝕊 → X 
def fill {X : Type} (f : ℂ → X) (y : X) : 𝕊 → X := λ z, z.rec f y

-- Lifting functions from ℂ → ℂ to 𝕊 → 𝕊
def lift (f : ℂ → ℂ) (y : 𝕊) : 𝕊 → 𝕊 := λ z, z.rec (λ z, f z) y
def lift' (f : X → ℂ → ℂ) (y : 𝕊) : X → 𝕊 → 𝕊 := λ x z, z.rec (λ z, f x z) y

variables {f : ℂ → ℂ}
variables {g : X → ℂ → ℂ}
variables {y : 𝕊} {x : X} {z : ℂ}

-- Values at coe and ∞
lemma fill_coe {f : ℂ → X} {y : X} : fill f y z = f z := rfl
lemma fill_inf {f : ℂ → X} {y : X} : fill f y ∞ = y := rfl
lemma lift_coe : lift f y z = ↑(f z) := rfl
lemma lift_coe' : lift' g y x z = ↑(g x z) := rfl
lemma lift_inf : lift f y ∞ = y := rfl
lemma lift_inf' : lift' g y x ∞ = y := rfl

-- lift in terms of fill
lemma lift_eq_fill : lift f y = fill (λ z, f z) y := rfl

-- fill is continuous
lemma continuous_at_fill_coe {f : ℂ → X} {y : X} (fc : continuous_at f z) : continuous_at (fill f y) z :=
  by simp only [alexandroff.continuous_at_coe, function.comp, fill_coe, fc]
lemma continuous_at_fill_inf {f : ℂ → X} {y : X} (fi : tendsto f at_inf (𝓝 y)) : continuous_at (fill f y) ∞ :=
  by simp only [alexandroff.continuous_at_infty', lift_inf, filter.coclosed_compact_eq_cocompact, ←at_inf_eq_cocompact,
    function.comp, fill_coe, fill_inf, fi]
lemma continuous_fill {f : ℂ → X} {y : X} (fc : continuous f) (fi : tendsto f at_inf (𝓝 y))
    : continuous (fill f y) := begin
  rw continuous_iff_continuous_at, intro z, induction z using riemann_sphere.rec,
  exact continuous_at_fill_coe fc.continuous_at, exact continuous_at_fill_inf fi,
end

-- fill is holomorphic
lemma holomorphic_at_fill_coe {f : ℂ → T} {y : T} (fa : holomorphic_at I I f z) : holomorphic_at I I (fill f y) z := begin
  have e : (λ x : 𝕊, f x.to_complex) =ᶠ[𝓝 ↑z] fill f y :=
    by simp only [alexandroff.nhds_coe_eq, filter.eventually_eq, filter.eventually_map, to_complex_coe, fill_coe,
      eq_self_iff_true, filter.eventually_true],
  refine holomorphic_at.congr _ e,
  refine fa.comp_of_eq holomorphic_at_to_complex _,
  simp only [to_complex_coe],
end
lemma holomorphic_at_fill_inf {f : ℂ → T} {y : T}
    (fa : ∀ᶠ z in at_inf, holomorphic_at I I f z) (fi : tendsto f at_inf (𝓝 y))
    : holomorphic_at I I (fill f y) ∞ := begin
  rw holomorphic_at_iff, use continuous_at_fill_inf fi,
  simp only [fill, function.comp, coe_local_equiv, rec_inf, local_equiv.coe_symm_mk, local_equiv.coe_mk,
    inv_inf, to_complex_zero, ext_chart_at_inf, inv_equiv, local_equiv.coe_trans, equiv.to_local_equiv_apply,
    equiv.coe_fn_mk, local_equiv.coe_trans_symm, equiv.to_local_equiv_symm_apply, equiv.coe_fn_symm_mk,
    local_equiv.symm_symm, ext_chart_at_coe],
  have e : (λ z : ℂ, ext_chart_at I y (@riemann_sphere.rec (λ _, T) f y (↑z)⁻¹)) =
            (λ z : ℂ, ext_chart_at I y (if z = 0 then y else (f z⁻¹))), {
    funext, by_cases z0 : z = 0, rw [if_pos z0, z0, coe_zero, inv_zero', rec_inf], rw [if_neg z0, inv_coe z0, rec_coe],
  },
  rw e, clear e,
  apply complex.analytic_at_of_differentiable_on_punctured_nhds_of_continuous_at, {
    apply (inv_tendsto_at_inf.eventually fa).mp,
    apply (inv_tendsto_at_inf.eventually (fi.eventually
      ((is_open_ext_chart_at_source I y).eventually_mem (mem_ext_chart_source I y)))).mp,
    apply eventually_nhds_within_of_forall, intros z z0 m fa,
    simp only [set.mem_compl_iff, set.mem_singleton_iff] at z0,
    have e : (λ z, ext_chart_at I y (if z = 0 then y else (f z⁻¹))) =ᶠ[𝓝 z] (λ z, ext_chart_at I y (f z⁻¹)), {
      refine (continuous_at_id.eventually_ne z0).mp (eventually_of_forall (λ w w0, _)),
      simp only [ne.def, id.def] at w0, simp only [w0, if_false],
    },
    refine differentiable_at.congr_of_eventually_eq _ e,
    apply analytic_at.differentiable_at, apply holomorphic_at.analytic_at I I,
    refine (holomorphic_at.ext_chart_at _).comp _, exact m,
    exact fa.comp (holomorphic_at_id.inv z0),
  }, {
    refine (continuous_at_ext_chart_at' I y _).comp _, {
      simp only [eq_self_iff_true, if_pos, mem_ext_chart_source],
    }, {
      simp [continuous_at_iff_tendsto_nhds_within],
      apply @tendsto_nhds_within_congr _ _ _ (λ z, f z⁻¹),
      intros z z0, simp only [set.mem_compl_iff, set.mem_singleton_iff] at z0, simp only [z0, if_false],
      exact filter.tendsto.comp fi inv_tendsto_at_inf,
    },
  },
end
lemma holomorphic_fill {f : ℂ → T} {y : T} (fa : holomorphic I I f) (fi : tendsto f at_inf (𝓝 y))
    : holomorphic I I (fill f y) := begin
  intro z, induction z using riemann_sphere.rec,
  exact holomorphic_at_fill_coe (fa _),
  exact holomorphic_at_fill_inf (eventually_of_forall fa) fi,
end
 
-- lift is continuous
lemma continuous_at_lift_coe' (gc : continuous_at (uncurry g) (x,z))
    : continuous_at (uncurry (lift' g y)) (x,↑z) := begin
  simp only [lift', continuous_at, uncurry, rec_coe, alexandroff.nhds_coe_eq, prod_nhds_eq,
    filter.tendsto_map'_iff, function.comp],
  exact filter.tendsto.comp filter.tendsto_map gc,
end
lemma continuous_at_lift_inf' (gi : tendsto (uncurry g) ((𝓝 x).prod at_inf) at_inf)
    : continuous_at (uncurry (lift' g ∞)) (x,∞) := begin
  simp only [continuous_at, filter.tendsto, filter.le_def, filter.mem_map], intros s m,
  simp only [alexandroff.nhds_infty_eq, filter.coclosed_compact_eq_cocompact, filter.mem_sup, filter.mem_map,
    filter.mem_pure, ←at_inf_eq_cocompact, lift', rec_inf, uncurry] at m,
  simp only [true_implies_iff, mem_set_of, uncurry, tendsto] at gi, specialize gi m.1,
  simp only [filter.mem_map, preimage_preimage] at gi,
  have e : uncurry (lift' g ∞) ⁻¹' s =
      (λ x : X × ℂ, (x.1,(x.2:𝕊))) '' ((λ x : X × ℂ, (g x.1 x.2 : 𝕊)) ⁻¹' s) ∪ univ ×ˢ {∞}, {
    apply set.ext, rintros ⟨x,z⟩, induction z using riemann_sphere.rec, {
      simp only [mem_preimage, mem_image, mem_union, mem_prod_eq, mem_univ, true_and, mem_singleton_iff, coe_eq_inf_iff,
        or_false, uncurry, lift', prod.ext_iff, coe_eq_coe], rw rec_coe, constructor,
      intro m, use [x,z,m,rfl],
      rintros ⟨⟨y,w⟩,m,yx,wz⟩, simp only at yx wz m, rw [wz,yx] at m, exact m,
    }, {
      simp only [mem_preimage, mem_image, mem_union, mem_prod_eq, mem_univ, true_and, mem_singleton_iff,
        eq_self_iff_true, or_true, iff_true, uncurry, lift', rec_inf, m.2],
    },
  },
  rw e, exact prod_mem_inf_of_mem_at_inf gi,
end
lemma continuous_lift' (gc : continuous (uncurry g))
    (gi : ∀ x, tendsto (uncurry g) ((𝓝 x).prod at_inf) at_inf) : continuous (uncurry (lift' g ∞)) := begin
  rw [continuous_iff_continuous_on_univ], rintros ⟨x,z⟩ _, apply continuous_at.continuous_within_at,
  induction z using riemann_sphere.rec,
  exact continuous_at_lift_coe' gc.continuous_at,
  exact continuous_at_lift_inf' (gi x),
end
lemma continuous_at_lift_coe (fc : continuous_at f z) : continuous_at (lift f y) z := begin
  have gc : continuous_at (uncurry (λ (u : unit), f)) ((),z), {
    simp only [uncurry], refine continuous_at.comp fc _, exact continuous_at_snd,
  },
  exact (continuous_at_lift_coe' gc).comp (continuous_at.prod continuous_at_const continuous_at_id),
end
lemma continuous_at_lift_inf (fi : tendsto f at_inf at_inf) : continuous_at (lift f ∞) ∞ := begin
  have gi : tendsto (uncurry (λ (u : unit), f)) ((𝓝 ()).prod at_inf) at_inf := fi.comp filter.tendsto_snd,
  exact (continuous_at_lift_inf' gi).comp (continuous_at.prod continuous_at_const continuous_at_id),
end
lemma continuous_lift (fc : continuous f) (fi : tendsto f at_inf at_inf) : continuous (lift f ∞) := begin
  rw continuous_iff_continuous_at, intros z, induction z using riemann_sphere.rec,
  exact continuous_at_lift_coe fc.continuous_at, exact continuous_at_lift_inf fi,
end

-- lift is holomorphic
lemma holomorphic_at_lift_coe (fa : analytic_at ℂ f z) : holomorphic_at I I (lift f y) z := begin
  rw lift_eq_fill, exact holomorphic_at_fill_coe ((holomorphic_coe _).comp (fa.holomorphic_at I I)),
end
lemma holomorphic_at_lift_inf (fa : ∀ᶠ z in at_inf, analytic_at ℂ f z) (fi : tendsto f at_inf at_inf)
    : holomorphic_at I I (lift f ∞) ∞ := begin
  rw lift_eq_fill, apply holomorphic_at_fill_inf,
  exact fa.mp (eventually_of_forall (λ z fa, (holomorphic_coe _).comp (fa.holomorphic_at I I))),
  exact coe_tendsto_inf.comp fi,
end
lemma holomorphic_lift (fa : analytic_on ℂ f univ) (fi : tendsto f at_inf at_inf) : holomorphic I I (lift f ∞) := begin
  intros z, induction z using riemann_sphere.rec,
  exact holomorphic_at_lift_coe (fa _ (mem_univ _)),
  exact holomorphic_at_lift_inf (eventually_of_forall (λ z, fa z (mem_univ _))) fi,
end

-- lift' is holomorphic (the parameterized version)
lemma holomorphic_lift' {f : ℂ → ℂ → ℂ} (fa : analytic_on ℂ (uncurry f) univ)
    (fi : ∀ x, tendsto (uncurry f) ((𝓝 x).prod at_inf) at_inf)
    : holomorphic II I (uncurry (lift' f ∞)) := begin
  apply osgood_manifold (continuous_lift' fa.continuous fi), {
    intros x z, induction z using riemann_sphere.rec,
    exact (holomorphic_coe _).comp ((fa _ (mem_univ _)).in1.holomorphic_at _ _),
    simp only [uncurry, lift_inf'], exact holomorphic_at_const,
  }, {
    intros x z, refine holomorphic_lift (λ _ _, (fa _ (mem_univ _)).in2) _ z,
    exact (fi x).comp (tendsto_const_nhds.prod_mk filter.tendsto_id),
  },
end

-- 𝕊 is path connected
instance : path_connected_space 𝕊 := begin
  use ∞,
  have i1 : joined ∞ ((1 : ℂ) : 𝕊), {
    generalize hp : (λ t : unit_interval, (((t:ℝ):ℂ):𝕊)⁻¹) = p,
    have pc : continuous p, {
      rw ←hp, exact continuous_inv.comp (continuous_coe.comp (complex.continuous_of_real.comp continuous_subtype_coe)),
    },
    use ⟨p,pc⟩,
    simp only [←hp], rw [Icc.coe_zero, complex.of_real_zero, coe_zero, inv_zero'],
    simp only [←hp], rw [Icc.coe_one, complex.of_real_one, inv_coe one_ne_zero, inv_one],
  },
  have cc : ∀ x y : ℂ, joined (x : 𝕊) (y : 𝕊), {
    intros x y, rcases path_connected_space.joined x y with ⟨p⟩,
    use p.map continuous_coe,
  },
  replace ic : ∀ x : ℂ, joined ∞ (x : 𝕊) := λ x, i1.trans (cc _ _),
  intros x y, induction x using riemann_sphere.rec,
  induction y using riemann_sphere.rec, apply cc, exact (ic _).symm,
  induction y using riemann_sphere.rec, apply ic, exact joined.refl _,
end
 
end riemann_sphere