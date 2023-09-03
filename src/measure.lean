-- Measure theory lemmas

import data.set.basic
import data.set.prod
import data.real.ennreal
import measure_theory.integral.circle_integral
import measure_theory.measure.lebesgue.complex
import measure_theory.measure.measure_space_def
import measure_theory.integral.average
import topology.subset_properties

import topology

open filter (liminf limsup at_top tendsto)
open function (curry uncurry)
open measure_theory
open metric (ball closed_ball sphere)
open set (Ioc Icc)
open topological_space (second_countable_topology)
open_locale real ennreal topology
noncomputable theory

variables {E : Type} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E] [second_countable_topology E]
variables {F : Type} [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]
variables {X : Type} [measure_space X] [metric_space X] [borel_space X]
variables {Y : Type} [measure_space Y] [metric_space Y] [borel_space Y]
variables {A : Type} [topological_space A]

lemma ennreal.le_zero_iff {x : ennreal} : x ≤ 0 ↔ x = 0 := begin
  rw ←ennreal.bot_eq_zero, exact le_bot_iff,
end

-- Implication works under ∀ᵐ
lemma ae_imp {f g : X → Prop} : (∀ᵐ x, f x) → (∀ x, f x → g x) → (∀ᵐ x, g x) := begin
  intros h i,
  rw [ae_iff, ←ennreal.le_zero_iff] at ⊢ h,
  have i' := λ x (ng : ¬g x), mt (i x) ng,
  rw ←set.set_of_subset_set_of at i',
  exact trans (measure_mono i') h,
end

-- We can ignore hypotheses under ∀ᵐ
lemma ae_drop_imp {f g : X → Prop} : (∀ᵐ x, g x) → (∀ᵐ x, f x → g x) := begin
  intro h,
  rw ae_iff at ⊢ h, simp only [not_forall, exists_prop], rw set.set_of_and, rw ←ennreal.le_zero_iff at ⊢ h,
  exact trans (measure_mono (set.inter_subset_right _ _)) h,
end

-- If a set has measure 0, any subset does too
lemma null_subset {s t : set ℝ} (h : s ⊆ t) : volume t = 0 → volume s = 0 := begin
  simp_rw ←ennreal.le_zero_iff, exact trans (measure_mono h),
end

-- Two functions are ae = on a set if the expected ae statement holds
lemma ae_eq_on_def {Y : Type} {f g : X → Y} {s : set X} (m : measurable_set s)
    : f =ᵐ[volume.restrict s] g ↔ ∀ᵐ x, x ∈ s → f x = g x :=
  by rw [filter.eventually_eq, ae_restrict_iff' m]

-- Removing a null set isn't significant measure-wise
lemma ae_minus_null {s t : set X} (tz : volume t = 0) : s =ᵐ[volume] (s \ t) := begin
  simp [filter.eventually_eq],
  have e : ∀ x, x ∉ t → (x ∈ s ↔ x ∈ (s \ t)), { intros x h, simp only [set.mem_diff, h, not_false_iff, and_true] },
  simp_rw [set.mem_def] at e, refine ae_imp _ e,
  rw [ae_iff], simpa [set.set_of_set],
end

-- Removing a point isn't significant measure-wise (if there are no atoms)
lemma ae_minus_point [has_no_atoms (volume : measure X)] {s : set X} {x : X}
    : s =ᵐ[volume] (s \ {x} : set X) := ae_minus_null (measure_singleton x)

-- ℂ has additive Haar measure
@[instance] def complex.is_add_haar_measure_volume : (volume : measure ℂ).is_add_haar_measure := begin
  have v : (volume : measure ℂ) = volume.map complex.equiv_real_prod_add_hom.symm, {
    have e : (⇑(complex.measurable_equiv_real_prod.symm) : ℝ × ℝ → ℂ) = ⇑(complex.equiv_real_prod_add_hom.symm), {
      funext x,
      simp only [complex.ext_iff, complex.measurable_equiv_real_prod, homeomorph.to_measurable_equiv_symm_coe,
        continuous_linear_equiv.symm_to_homeomorph, continuous_linear_equiv.coe_to_homeomorph,
        complex.equiv_real_prod_clm_symm_apply_re, complex.equiv_real_prod_add_hom_symm_apply_re, eq_self_iff_true,
        complex.equiv_real_prod_clm_symm_apply_im, complex.equiv_real_prod_add_hom_symm_apply_im, and_self],
    },
    rw ←e, clear e,
    exact (measure_preserving.symm _ complex.volume_preserving_equiv_real_prod).map_eq.symm,
  },
  rw v,
  have e : (⇑(complex.equiv_real_prod_clm.symm) : ℝ × ℝ → ℂ) = ⇑(complex.equiv_real_prod_add_hom.symm.to_add_monoid_hom), {
    funext x,
    simp only [complex.ext_iff, add_equiv.coe_to_add_monoid_hom, complex.equiv_real_prod_clm_symm_apply_re,
      complex.equiv_real_prod_add_hom_symm_apply_re, eq_self_iff_true, complex.equiv_real_prod_clm_symm_apply_im,
      complex.equiv_real_prod_add_hom_symm_apply_im, and_self],
  },
  apply measure.is_add_haar_measure_map (volume : measure (ℝ × ℝ)) complex.equiv_real_prod_add_hom.symm.to_add_monoid_hom, {
    rw ←e, apply continuous_linear_map.continuous,
  }, {
    simp only [add_equiv.coe_to_add_monoid_hom, equiv_like.comp_surjective],
    exact function.surjective_id,
  }, {
    rw ←e, exact complex.equiv_real_prod_clm.symm.to_homeomorph.to_cocompact_map.cocompact_tendsto',
  },
end

-- ℂ has no atoms
@[instance] def complex.has_no_atoms_volume : has_no_atoms (volume : measure ℂ) := {
  measure_singleton := begin
    intro z,
    rw ←(measure_preserving.symm _ complex.volume_preserving_equiv_real_prod).measure_preimage,
    rw ←measurable_equiv.image_eq_preimage, simp [measure_singleton],
    apply measurable_set_singleton,
  end,
}

-- Finite, positive measure sets
structure nice_volume (s : set X) : Prop :=
    (measurable : measurable_set s)
    (finite : volume s < ∞)
    (pos : volume s > 0)

-- Useful lemmas about nice_volume
lemma nice_volume.ne_zero {s : set X} (sn : nice_volume s) : volume s ≠ 0 := ne_of_gt sn.pos
lemma nice_volume.ne_top {s : set X} (sn : nice_volume s) : volume s ≠ ⊤ := ne_of_lt sn.finite
lemma nice_volume.real_pos {s : set X} (sn : nice_volume s) : (volume s).to_real > 0 :=
  ennreal.to_real_pos_iff.mpr ⟨sn.pos, sn.finite⟩
lemma nice_volume.real_nonneg {s : set X} (sn : nice_volume s) : (volume s).to_real ≠ 0 := ne_of_gt sn.real_pos

-- Constants are integrable on nice_volume sets
lemma nice_volume.integrable_on_const {s : set X} (sn : nice_volume s) (c : ℝ) : integrable_on (λ _, c) s :=
  integrable_on_const.mpr (or.inr sn.finite)

-- Uniform limits of continuous functions and integrals commute
lemma tendsto_uniformly_on.integral_tendsto {f : ℕ → X → E} {g : X → E} {s : set X}
    [is_locally_finite_measure (volume : measure X)]
    (u : tendsto_uniformly_on f g at_top s) (fc : ∀ n, continuous_on (f n) s) (sc : is_compact s)
    : tendsto (λ n, ∫ x in s, f n x) at_top (nhds (∫ x in s, g x)) := begin
  rcases u.uniform_cauchy_seq_on.bounded fc sc with ⟨b,bp,bh⟩,
  apply @tendsto_integral_of_dominated_convergence _ _ _ _ _ _ _ f g (λ _, b), {
    intro n, exact (fc n).ae_strongly_measurable sc.measurable_set,
  }, {
    exact continuous_on_const.integrable_on_compact sc,
  }, {
    intro n, specialize bh n, simp only, rw ae_restrict_iff' sc.measurable_set, exact ae_of_all _ bh,
  }, {
    rw ae_restrict_iff' sc.measurable_set, apply ae_of_all, intros x xs, exact u.tendsto_at xs,
  },
end

-- An abbreviation for Ioc 0 (2*π)
def Itau := Ioc 0 (2*π)

-- Lemmas about Itau
lemma Itau_volume : volume Itau = ennreal.of_real (2*π) := by simp [Itau]
lemma Itau_real_volume : (volume Itau).to_real = 2*π :=
  by simp [Itau_volume, ennreal.to_real_of_real (le_of_lt real.two_pi_pos)]
lemma nice_volume.Itau : nice_volume Itau := {
  measurable := by simp [Itau],
  finite := by simp [Itau_volume],
  pos := by simp [Itau_volume, real.pi_pos],
}
lemma measurable_set_Itau : measurable_set Itau := by simp [Itau, measurable_set_Ioc]
lemma tau_mem_Itau : 2*π ∈ Itau := by simp [Itau, real.pi_pos]

-- Continuous functions are integrable on spheres
lemma continuous_on.integrable_on_sphere {f : ℂ → E} {c : ℂ} {r : ℝ} (fc : continuous_on f (closed_ball c r)) (rp : r > 0)
    : integrable_on (λ t, f (circle_map c r t)) Itau := begin
  apply continuous.integrable_on_Ioc, apply fc.comp_continuous (continuous_circle_map _ _),
  intro t, simp [complex.dist_eq, abs_of_pos rp],
end

-- Continuous functions are integrable on closed_balls
lemma continuous_on.integrable_on_closed_ball {f : ℂ → E} {c : ℂ} {r : ℝ} (fc : continuous_on f (closed_ball c r))
    : integrable_on f (closed_ball c r) := fc.integrable_on_compact (is_compact_closed_ball _ _)

-- Averages add
lemma set_average.add {f g : X → E} {s : set X} (fi : integrable_on f s) (gi : integrable_on g s)
    : ⨍ z in s, f z + g z = (⨍ z in s, f z) + ⨍ z in s, g z := by simp_rw [set_average_eq, integral_add fi gi, smul_add]

-- Averages subtract
lemma set_average.sub {f g : X → E} {s : set X} (fi : integrable_on f s) (gi : integrable_on g s)
    : ⨍ z in s, f z - g z = (⨍ z in s, f z) - ⨍ z in s, g z := by simp_rw [set_average_eq, integral_sub fi gi, smul_sub]

-- average commutes with linear maps
lemma average_linear_comm {f : X → E} {s : set X} (fi : integrable_on f s) (g : E →L[ℝ] F)
    : ⨍ x in s, g (f x) = g ⨍ x in s, f x := begin
  simp only [set_average_eq, complex.smul_re],
  by_cases v0 : (volume s).to_real = 0, simp [v0],
  rw g.map_smul, rw (ne.is_unit v0).inv.smul_left_cancel,
  exact continuous_linear_map.integral_comp_comm _ fi,
end

-- Averages on a set depend only on ae values within the set
lemma average_congr_on {f g : X → E} {s : set X} (sn : nice_volume s) (h : ∀ᵐ x, x ∈ s → f x = g x)
    : ⨍ x in s, f x = ⨍ x in s, g x := begin
  rw ←ae_eq_on_def sn.measurable at h, exact average_congr h,
end

-- means are at most the values of the function
lemma mean_bound {f : X → ℝ} {s : set X} {b : ℝ}
    (sn : nice_volume s) (fi : integrable_on f s) (fb : ∀ z, z ∈ s → f z ≤ b)
    : ⨍ x in s, f x ≤ b := begin
  rw [set_average_eq, smul_eq_mul],
  have bi : integrable_on (λ _ : X, b) s := sn.integrable_on_const _,
  have ib := set_integral_mono_on fi bi sn.measurable fb,
  simp at ⊢ ib,
  transitivity (volume s).to_real⁻¹ * ((volume s).to_real * b),
  bound [sn.pos],
  rw [←mul_assoc _ _ b, inv_mul_cancel sn.real_nonneg], simp only [one_mul],
end

-- Sets where each point is near positive volume
def local_volume_set (s : set X) := ∀ x r, x ∈ s → r > 0 → volume (s ∩ ball x r) > 0

-- Sets in the closure of their interior have local volume
lemma local_volume.closure_interior (s : set X)
    (bp : ∀ (x : X) r, r > 0 → volume (ball x r) > 0) (ci : s ⊆ closure (interior s))
    : local_volume_set s := begin
  intros x r xs rp,
  have xci := ci xs,
  rcases metric.mem_closure_iff.mp xci r rp with ⟨y,ys,xy⟩,
  rcases metric.is_open_iff.mp is_open_interior y ys with ⟨e,ep,ye⟩,
  set t := min e (r - dist x y),
  have es : ball y t ⊆ s ∩ ball x r, {
    simp only [set.subset_inter_iff], constructor,
    exact trans (metric.ball_subset_ball (by bound)) (trans ye interior_subset),
    apply metric.ball_subset_ball',
    transitivity r - dist x y + dist y x, bound, simp [dist_comm],
  },
  exact lt_of_lt_of_le (bp y t (by bound)) (measure_mono es),
end

-- Intervals have local volume
lemma local_volume.Ioc {a b : ℝ} : local_volume_set (set.Ioc a b) := begin
  apply local_volume.closure_interior,
  intros x r rp,
  simp only [real.volume_ball, gt_iff_lt, ennreal.of_real_pos, zero_lt_mul_left, zero_lt_bit0, zero_lt_one],
  exact rp,
  by_cases ab : a = b, { simp only [ab, set.Ioc_self, set.empty_subset] },
  simp only [interior_Ioc, closure_Ioo ab, set.Ioc_subset_Icc_self],
end
lemma local_volume.Itau : local_volume_set Itau := local_volume.Ioc

-- If an interval mean is above b, and each value is below b, then each value is exactly b
lemma mean_squeeze {f : X → ℝ} {s : set X} {b : ℝ}
    (sn : nice_volume s) (lv : local_volume_set s) (fc : continuous_on f s) (fi : integrable_on f s)
    (lo : b ≤ ⨍ x in s, f x) (hi : ∀ x, x ∈ s → f x ≤ b)
    : ∀ x, x ∈ s → f x = b := begin
  contrapose lo, rw set_average_eq,
  simp only [algebra.id.smul_eq_mul, not_le],
  simp only [not_forall] at lo,
  rcases lo with ⟨x,xs,fx'⟩,
  have fx := lt_of_le_of_ne (hi x xs) fx', clear fx',
  rcases metric.continuous_on_iff.mp fc x xs ((b - f x)/2) (by bound) with ⟨e,ep,he⟩,
  have vtp' := lv x e xs ep,
  generalize ht : s ∩ ball x e = t, rw ht at vtp',
  have ts : t ⊆ s, { rw ←ht, exact set.inter_subset_left _ _ },
  have tf : volume t < ⊤ := lt_of_le_of_lt (measure_mono ts) sn.finite,
  have tm : measurable_set t, { rw ←ht, exact measurable_set.inter sn.measurable measurable_set_ball },
  have sc : s \ t ∪ t = s := set.diff_union_of_subset ts,
  nth_rewrite 1 ←sc,
  rw integral_union, {
    set m := (b + f x)/2,
    set vs := (volume s).to_real,
    set vt := (volume t).to_real,
    have vsp : vs > 0 := sn.real_pos,
    have vtp : vt > 0 := ennreal.to_real_pos (ne_of_gt vtp') (lt_top_iff_ne_top.mp tf),
    rw inv_mul_lt_iff' vsp,
    have mb : m < b, {
      calc (b + f x)/2 < (b + b)/2 : (div_lt_div_right (by norm_num)).mpr (by bound)
      ... = b : by ring
    },
    have i0 : (∫ x in s \ t, f x) ≤ (vs - vt) * b, {
      set b' := λ x, b,
      have df : volume (s \ t) < ⊤ := lt_of_le_of_lt (measure_mono (set.diff_subset _ _)) sn.finite,
      have dm : measurable_set (s \ t) := measurable_set.diff sn.measurable tm,
      have fb := @set_integral_mono_on _ _ volume f b' (s \ t) (fi.mono (set.diff_subset _ _) (le_refl _))
        (integrable_on_const.mpr (or.inr df)) dm _,
      simp [measure_diff ts tm (lt_top_iff_ne_top.mp tf),
            ennreal.to_real_sub_of_le (measure_mono ts) (lt_top_iff_ne_top.mp sn.finite)] at fb,
      exact fb,
      intros y yd, simp at yd, exact hi y yd.left,
    },
    have i1 : (∫ x in t, f x) ≤ vt * m, {
      set m' := λ x, m,
      have fm := @set_integral_mono_on _ _ volume f m' t (fi.mono ts (le_refl _))
        (integrable_on_const.mpr (or.inr tf)) tm _,
      simp at fm, exact fm,
      intros y yt,
      rw ←ht at yt, simp at ht yt,
      specialize he y yt.left yt.right,
      simp [real.dist_eq] at he,
      calc f y = f x + (f y - f x) : by ring 
      ... ≤ f x + |f y - f x| : by bound [le_abs_self]
      ... ≤ f x + (b - f x)/2 : by bound
      ... = (b + f x)/2 : by ring
    },
    calc (∫ (x : X) in s \ t, f x) + ∫ (x : X) in t, f x
        ≤ (vs - vt) * b + vt * m : by bound
    ... = vs * b - vt * (b - m) : by ring
    ... < vs * b - 0 : sub_lt_sub_left (by bound) _
    ... = b * vs : by ring
  }, {
    rw disjoint.comm, exact set.disjoint_sdiff_right,
  }, {
    exact tm,
  }, {
    exact fi.mono (set.diff_subset _ _) (le_refl _),
  }, {
    exact fi.mono ts (le_refl _),
  },
end

lemma continuous_on.interval_integral {f : X → ℝ → E} {s : set X} {a b : ℝ}
    (fc : continuous_on (uncurry f) (s ×ˢ (Icc a b))) (sc : is_compact s) (ab : a ≤ b)
    : continuous_on (λ x, ∫ t in a..b, f x t) s := begin
  rcases fc.bounded_norm (sc.prod is_compact_Icc) with ⟨c,cp,fb⟩,
  simp only [set.forall_prod_set, uncurry] at fb,
  have e : ∀ x t, f x t = (uncurry f) (x,t) :=
    by simp only [function.uncurry_apply_pair, eq_self_iff_true, forall_forall_const, implies_true_iff],
  intros x xs,
  apply @interval_integral.continuous_within_at_of_dominated_interval _ _ _ _ _ _ _ _ _ _ (λ _, c), {
    apply eventually_nhds_within_of_forall, intros y ys,
    refine continuous_on.ae_strongly_measurable _ measurable_set_Ioc,
    rw [set.uIoc_of_le ab], simp_rw e, apply fc.comp, {
      apply continuous.continuous_on, continuity,
    }, {
     intros t ts, exact set.mk_mem_prod ys (set.Ioc_subset_Icc_self ts),
    },
  }, {
    apply eventually_nhds_within_of_forall, intros y ys, rw [set.uIoc_of_le ab],
    apply ae_of_all, intros t ts, apply fb _ ys _ (set.Ioc_subset_Icc_self ts),
  }, {
    exact interval_integrable_const,
  }, {
    apply ae_of_all, intros t ts, simp_rw e, apply fc.comp, {
      apply continuous.continuous_on, continuity,
    }, {
      rw [set.uIoc_of_le ab] at ts,
      intros y ys, exact set.mk_mem_prod ys (set.Ioc_subset_Icc_self ts),
    },
    assumption,
  }, {
    apply_instance,
  },
end

-- liminf preserves ae_measurability, general filter version
lemma ae_measurable_liminf' {I I' : Type} {u : filter I} {f : I → X → ennreal} {μ : measure X} {p : I' → Prop} {s : I' → set I}
    (fm : ∀ n, ae_measurable (f n) μ) (uc : u.has_countable_basis p s) (sc : ∀ i, (s i).countable)
    : ae_measurable (λ x, u.liminf (λ n, f n x)) μ := begin
  simp_rw [uc.to_has_basis.liminf_eq_supr_infi],
  refine ae_measurable_bsupr _ uc.countable _,
  exact λ i, ae_measurable_binfi _ (sc i) fm
end

-- liminf preserves ae_measurability, ℕ version
lemma ae_measurable_liminf {f : ℕ → X → ennreal} {μ : measure X} (fm : ∀ n, ae_measurable (f n) μ)
    : ae_measurable (λ x, at_top.liminf (λ n, f n x)) μ :=
  ae_measurable_liminf' fm filter.at_top_countable_basis (λ i, set.to_countable _)

lemma set_lintegral_mono_ae_measurable {s : set X} {f g : X → ennreal}
    (fm : ae_measurable f (volume.restrict s)) (gm : ae_measurable g (volume.restrict s)) (sm : measurable_set s)
    (fg : ∀ x, x ∈ s → f x ≤ g x)
    : ∫⁻ x in s, f x ≤ ∫⁻ x in s, g x := begin
  apply lintegral_mono_ae, rw ae_restrict_iff' sm, exact ae_of_all _ fg,
end
