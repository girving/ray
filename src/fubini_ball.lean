-- Integration over the complex closed disk

import analysis.special_functions.integrals
import measure_theory.constructions.prod.integral
import measure_theory.function.jacobian
import measure_theory.integral.circle_integral
import measure_theory.measure.lebesgue.complex

import measure
import prod
import tactics

open complex (abs arg exp I)
open linear_map (to_matrix_apply)
open measure_theory
open metric (ball closed_ball sphere)
open real (cos sin)
open set (Icc Ioc)
open_locale real
noncomputable theory

section real_circle_map

-- circle_map as a map from ℝ² → ℝ²
def real_circle_map (c : ℂ) (x : ℝ × ℝ) : ℝ × ℝ := ⟨c.re + x.1 * cos x.2, c.im + x.1 * sin x.2⟩
def real_circle_map_eq_circle_map (c : ℂ) (x : ℝ × ℝ)
    : real_circle_map c x = complex.equiv_real_prod (circle_map c x.1 x.2) :=
  by simp [real_circle_map, circle_map]

-- The derivative of real_circle_map
def d1 := continuous_linear_map.fst ℝ ℝ ℝ
def d2 := continuous_linear_map.snd ℝ ℝ ℝ
def rcm_deriv (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (0 + (x.1 • (-sin x.2) • d2 + cos x.2 • d1)).prod (0 + (x.1 • cos x.2 • d2 + sin x.2 • d1))
lemma real_circle_map.fderiv {c : ℂ} {x : ℝ × ℝ} : has_fderiv_at (λ x, real_circle_map c x) (rcm_deriv x) x := begin
  simp_rw [real_circle_map],
  apply_rules [has_fderiv_at_const, has_fderiv_at_fst, has_fderiv_at_snd, has_fderiv_at.cos, has_fderiv_at.sin,
               has_fderiv_at.add, has_fderiv_at.mul, has_fderiv_at.prod],
end

-- det rcm_deriv
def rcm_matrix (x : ℝ × ℝ) := linear_map.to_matrix (basis.fin_two_prod ℝ) (basis.fin_two_prod ℝ) (rcm_deriv x)
lemma rcm00 (x : ℝ × ℝ) : rcm_matrix x 0 0 = cos x.2 := by simp [rcm_matrix, rcm_deriv, to_matrix_apply, d1, d2]
lemma rcm01 (x : ℝ × ℝ) : rcm_matrix x 0 1 = -x.1 * sin x.2 := by simp [rcm_matrix, rcm_deriv, to_matrix_apply, d1, d2]
lemma rcm10 (x : ℝ × ℝ) : rcm_matrix x 1 0 = sin x.2 := by simp [rcm_matrix, rcm_deriv, to_matrix_apply, d1, d2]
lemma rcm11 (x : ℝ × ℝ) : rcm_matrix x 1 1 = x.1 * cos x.2 := by simp [rcm_matrix, rcm_deriv, to_matrix_apply, d1, d2]
lemma rcm_deriv.det (x : ℝ × ℝ) : (rcm_deriv x).det = x.1 := begin
  rw [continuous_linear_map.det, ←linear_map.det_to_matrix (basis.fin_two_prod ℝ), ←rcm_matrix],
  rw [matrix.det_fin_two, rcm00, rcm01, rcm10, rcm11], ring_nf,
  calc x.1 * cos x.2^2 + sin x.2^2 * x.1 = x.1 * (cos x.2^2 + sin x.2^2) : by ring
  ... = x.1 : by simp only [real.cos_sq_add_sin_sq, mul_one],
end

end real_circle_map

@[simp] lemma metric.sphere_eq_empty {S : Type} [is_R_or_C S] {c : S} {r : ℝ}
    : sphere c r = ∅ ↔ r < 0 := begin
  constructor, {
    intros rp, contrapose rp, simp at rp,
    refine set.nonempty.ne_empty ⟨c+r, _⟩,
    simpa [is_R_or_C.norm_of_real],
  }, {
    intros n, contrapose n,
    rw ←set.not_nonempty_iff_eq_empty at n, simp at n ⊢, assumption,
  },
end

-- range (circle_map c r _) = sphere c r even when restricted to set.Ioc
lemma circle_map_Ioc {c z : ℂ} {r : ℝ} (zs : z ∈ sphere c r) : ∃ t, t ∈ Ioc 0 (2*π) ∧ z = circle_map c r t := begin
  by_cases rp : r < 0, { simp [metric.sphere_eq_empty.mpr rp] at zs, finish },
  simp at rp,
  rw [←abs_of_nonneg rp, ←range_circle_map, set.mem_range] at zs,
  rcases zs with ⟨t,ht⟩,
  generalize ha : 2*π = a,
  have ap : a > 0, { rw ←ha, exact real.two_pi_pos },
  set s := t + a - a*⌈t/a⌉,
  use s, constructor, {
    simp only [set.mem_Ioc, sub_pos, tsub_le_iff_right],
    constructor, {
      calc a*⌈t/a⌉ < a*(t/a+1) : by bound [(mul_lt_mul_left ap).mpr, int.ceil_lt_add_one]
      ... = a/a*t + a : by ring
      ... = t + a : by field_simp [ne_of_gt ap]
    }, {
      calc a + a*⌈t/a⌉ ≥ a + a*(t/a) : by bound [int.le_ceil]
      ... = a/a*t + a : by ring
      ... = t + a : by field_simp [ne_of_gt ap]
    }
  }, {
    rw [←ht, circle_map],
    simp only [complex.of_real_sub, complex.of_real_add, complex.of_real_mul, complex.of_real_int_cast, add_right_inj,
      mul_eq_mul_left_iff, complex.of_real_eq_zero],
    rw [mul_sub_right_distrib, right_distrib, complex.exp_sub, complex.exp_add],
    rw [mul_comm _ ↑⌈_⌉, mul_assoc, complex.exp_int_mul, ←ha],
    simp only [complex.of_real_mul, complex.of_real_bit0, complex.of_real_one, complex.exp_two_pi_mul_I, mul_one, one_zpow, div_one,
      eq_self_iff_true, true_or],
  },
end

section fubini_helper

-- The square that we'll map onto the ball
def square (r : ℝ) : set (ℝ × ℝ) := set.Ioc 0 r ×ˢ (Ioc 0 (2*π))

lemma square.rp {r : ℝ} {x : ℝ × ℝ} : x ∈ square r → x.1 > 0 := begin simp [square], finish end
lemma measurable.square {r : ℝ} : measurable_set (square r) := by apply_rules [measurable_set.prod, measurable_set_Ioc]

lemma square_eq {c : ℂ} {r : ℝ}
    : complex.measurable_equiv_real_prod.symm ⁻¹' (closed_ball c r \ {c}) = real_circle_map c '' square r := begin
  rw ←measurable_equiv.image_eq_preimage,
  have e : real_circle_map c = (λ x : ℝ × ℝ, complex.measurable_equiv_real_prod (circle_map c x.1 x.2)), {
    funext,
    simp only [real_circle_map_eq_circle_map, complex.measurable_equiv_real_prod, complex.equiv_real_prod_apply,
      homeomorph.to_measurable_equiv_coe, continuous_linear_equiv.coe_to_homeomorph,
      complex.equiv_real_prod_clm_apply],
  },
  have i : (λ x : ℝ × ℝ, circle_map c x.1 x.2) '' square r = closed_ball c r \ {c}, {
    apply set.ext, intro z, rw set.mem_image, constructor, {
      intro gp, rcases gp with ⟨⟨s,t⟩,ss,tz⟩,
      simp only at tz,
      simp only [square, set.prod_mk_mem_set_prod_eq, set.mem_Ioc] at ss,
      rw ←tz,
      simp only [set.mem_diff, metric.mem_closed_ball, set.mem_singleton_iff, circle_map_eq_center_iff],
      exact ⟨by simp [circle_map, abs_of_pos ss.1.1, ss.1.2], ne_of_gt ss.1.1⟩,
    }, {
      intro zr, simp only [set.mem_diff, metric.mem_closed_ball, set.mem_singleton_iff] at zr, rw dist_comm at zr,
      have zz : z ∈ sphere c (dist c z), {
        simp only [complex.dist_eq, mem_sphere_iff_norm, complex.norm_eq_abs], rw complex.abs.map_sub,
      },
      rcases circle_map_Ioc zz with ⟨t,ts,tz⟩,
      use [dist c z, t],
      simp [dist_nonneg, zr, ne.symm zr.2, square, ts, tz.symm],
    },
  },
  rw [e, set.image_comp _ _ (square r), i],
end

-- exp it = cos t + i sin t
lemma exp_of_im (t : ℝ) : exp (t * I) = cos t + sin t*I :=
  by simp [complex.ext_iff, complex.cos_of_real_re, complex.sin_of_real_re]
lemma complex.cos_eq_cos (t : ℝ) : complex.cos t = ↑(real.cos t) := by simp
lemma complex.sin_eq_sin (t : ℝ) : complex.sin t = ↑(real.sin t) := by simp

-- arg e^(it)
lemma arg_exp_of_im (t : ℝ) : ∃ n : ℤ, arg (exp (t * I)) = t - 2*π*n := begin
  generalize hn : ⌈t/(2*π) - 1/2⌉ = n, existsi n,
  have en : exp (2*π*n*I) = 1, { rw [mul_comm _ ↑n, mul_assoc, complex.exp_int_mul], simp [complex.exp_neg] },
  have e : exp (t*I) = exp (↑(t - 2*π*n)*I) := by simp [mul_sub_right_distrib, complex.exp_sub, en],
  have ts : t - 2*π*n ∈ Ioc (-π) π, {
    simp only [set.mem_Ioc, neg_lt_sub_iff_lt_add, tsub_le_iff_right],
    constructor, {
      have h : ↑n < t*(2*π)⁻¹ - 1/2 + 1, { rw ←hn, exact int.ceil_lt_add_one _ },
      calc 2*π*↑n < 2*π*(t*(2*π)⁻¹ - 1/2 + 1) : by bound [(mul_lt_mul_left real.two_pi_pos).mpr]
      ... = π + (2*π)*(2*π)⁻¹*t : by ring
      ... = π + t : by field_simp [ne_of_gt real.two_pi_pos]
    }, {
      have h : ↑n ≥ t*(2*π)⁻¹ - 1/2, { rw ←hn, exact int.le_ceil _ },
      calc π + 2*π*↑n ≥ π + 2*π*(t*(2*π)⁻¹ - 1/2) : by bound [real.two_pi_pos]
      ...  = (2*π)*(2*π)⁻¹*t : by ring
      ... = t : by field_simp [ne_of_gt real.two_pi_pos]
    }
  },
  rw [e, exp_of_im, ←complex.cos_eq_cos, ←complex.sin_eq_sin, complex.arg_cos_add_sin_mul_I ts],
end

-- real_circle_map is injective on the square
lemma rcm_inj {c : ℂ} {r : ℝ} : set.inj_on (real_circle_map c) (square r) := begin
  intros x xs y ys e, simp [square] at xs ys,
  simp_rw [real_circle_map_eq_circle_map, equiv.apply_eq_iff_eq] at e,
  simp_rw [circle_map] at e, simp at e,
  have re : abs (↑(x.1) * exp (x.2*I)) = abs (↑(y.1) * exp (y.2*I)) := by rw e,
  simp [abs_of_pos xs.1.1, abs_of_pos ys.1.1] at re,
  have ae : arg (↑(x.1) * exp (x.2*I)) = arg (↑(y.1) * exp (y.2*I)) := by rw e,
  simp [complex.arg_real_mul _ xs.1.1, complex.arg_real_mul _ ys.1.1] at ae,
  rcases arg_exp_of_im x.2 with ⟨nx,hx⟩,
  rcases arg_exp_of_im y.2 with ⟨ny,h⟩,
  rw [←ae, hx] at h, clear e ae hx,
  have n0 : 2*π*(nx - ny) < (2*π)*1 := by linarith,
  have n1 : (2*π)*-1 < 2*π*(nx - ny) := by linarith,
  have hn : (nx : ℝ) - ny = ↑(nx - ny) := by simp only [int.cast_sub],
  have hn1 : (-1 : ℝ) = ↑(-1 : ℤ) := by simp only [int.cast_neg, algebra_map.coe_one],
  have h1 : (1 : ℝ) = ↑(1 : ℤ) := by simp only [algebra_map.coe_one],
  rw [mul_lt_mul_left real.two_pi_pos, hn] at n0 n1,
  rw hn1 at n1, rw h1 at n0, rw int.cast_lt at n0 n1,
  have n : nx = ny := by linarith,
  rw n at h,
  have i : x.2 = y.2 := by linarith,
  have g : (x.1,x.2) = (y.1,y.2) := by rw [re, i],
  simp only [prod.mk.eta] at g, exact g,
end

end fubini_helper

-- Inverse lemma for fubini_ball
lemma measurable_symm_equiv_inverse {z : ℂ} : complex.measurable_equiv_real_prod.symm (complex.equiv_real_prod z) = z := begin
  simp only [complex.equiv_real_prod_apply],
  rw [complex.measurable_equiv_real_prod, homeomorph.to_measurable_equiv_symm_coe],
  simp only [continuous_linear_equiv.symm_to_homeomorph, continuous_linear_equiv.coe_to_homeomorph],
  apply complex.ext, {
    simp only [complex.equiv_real_prod_clm_symm_apply_re],
  }, {
    simp only [complex.equiv_real_prod_clm_symm_apply_im],
  },
end

-- circle_map is continuous on ℝ × ℝ
lemma continuous_circle_map_full {c : ℂ} : continuous (λ x : ℝ × ℝ, circle_map c x.1 x.2) := by continuity

-- If x.to_real = y is positive, then x = of_real y
lemma invert_to_real {x : ennreal} {y : ℝ} (yp : y > 0) : x.to_real = y → x = ennreal.of_real y := begin
  intro h, rw ←h, refine (ennreal.of_real_to_real _).symm,
  contrapose yp, simp at yp, simp [yp] at h, simp [←h],
end

-- Integration over a complex ball using polar coordinates
lemma fubini_ball {E : Type} [normed_add_comm_group E] [normed_space ℝ E] [complete_space E]
    {f : ℂ → E} {c : ℂ} {r : ℝ} (fc : continuous_on f (closed_ball c r))
    : ∫ z in closed_ball c r, f z = ∫ s in set.Ioc 0 r, s • ∫ t in Ioc 0 (2*π), f (circle_map c s t) := begin
  have center : closed_ball c r =ᵐ[volume] (closed_ball c r \ {c} : set ℂ) := ae_minus_point,
  rw measure_theory.set_integral_congr_set_ae center, clear center,
  have im := measure_preserving.symm _ complex.volume_preserving_equiv_real_prod,
  rw ←measure_preserving.set_integral_preimage_emb im complex.measurable_equiv_real_prod.symm.measurable_embedding f _,
  clear im,
  rw square_eq,
  have dc : ∀ x, x ∈ square r → has_fderiv_within_at (real_circle_map c) (rcm_deriv x) (square r) x :=
    λ _ _, real_circle_map.fderiv.has_fderiv_within_at,
  rw integral_image_eq_integral_abs_det_fderiv_smul volume measurable.square dc rcm_inj, clear dc,
  simp_rw rcm_deriv.det,
  simp_rw real_circle_map_eq_circle_map,
  simp_rw measurable_symm_equiv_inverse,
  have e : ∀ x : ℝ × ℝ, x ∈ square r → |x.1| • f (circle_map c x.1 x.2) = x.1 • f (circle_map c x.1 x.2), {
    intros x xs, rw abs_of_pos (square.rp xs),
  },
  rw measure_theory.set_integral_congr measurable.square e, clear e,
  simp only,
  rw [square, measure.volume_eq_prod, measure_theory.set_integral_prod],
  simp [integral_smul],
  have fi : integrable_on (λ x : ℝ × ℝ, x.1 • f (circle_map c x.1 x.2)) (Icc 0 r ×ˢ Icc 0 (2*π)), {
    apply continuous_on.integrable_on_compact,
    exact is_compact.prod is_compact_Icc is_compact_Icc,
    apply continuous_on.smul,
    exact continuous_fst.continuous_on,
    apply fc.comp (continuous_circle_map_full.continuous_on),
    intros x xs, simp only,
    simp only [set.Icc_prod_Icc, set.mem_Icc] at xs,
    apply metric.closed_ball_subset_closed_ball xs.2.1,
    apply circle_map_mem_closed_ball _ xs.1.1,
  },
  exact fi.mono_set (set.prod_mono set.Ioc_subset_Icc_self set.Ioc_subset_Icc_self),
end 

-- The volume of complex closed balls
lemma complex.volume_closed_ball' {c : ℂ} {r : ℝ} (rp : r ≥ 0)
    : (complex.measure_space.volume (closed_ball c r)).to_real = π * r^2 := begin
  have c : continuous_on (λ _ : ℂ, (1 : ℝ)) (closed_ball c r) := continuous_on_const,
  have f := fubini_ball c, clear c,
  have e : r ^ 2 / 2 * (2 * π) = π * r^2 := by ring,
  simp only [e, ennreal.to_real_of_real (le_of_lt real.two_pi_pos), ←interval_integral.integral_of_le rp, integral_const,
    measure.restrict_apply, measurable_set.univ, set.univ_inter, algebra.id.smul_eq_mul, mul_one, real.volume_Ioc,
    tsub_zero, interval_integral.integral_mul_const, integral_id, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero,
    not_false_iff] at f,
  exact f,
end

lemma complex.volume_closed_ball {c : ℂ} {r : ℝ} (rp : r ≥ 0) : volume (closed_ball c r) = ennreal.of_real (π * r^2) := begin
  by_cases rp' : r > 0, {
    exact invert_to_real (by bound [real.pi_pos]) (complex.volume_closed_ball' rp),
  }, {
    simp at rp', simp [le_antisymm rp' rp],
  },
end

-- The volume of complex open balls
lemma complex.volume_ball' {c : ℂ} {r : ℝ} (rp : r ≥ 0) : (volume (ball c r)).to_real = π * r^2 := begin
  by_cases r0 : r = 0, simp [r0],
  have rs := lt_of_le_of_ne rp (ne.symm r0),
  have hi' : volume (ball c r) ≤ volume (closed_ball c r) := measure_mono metric.ball_subset_closed_ball,
  have hi := ennreal.to_real_mono (by simp [complex.volume_closed_ball rp]) hi',
  have lo : (volume (ball c r)).to_real ≥ (volume (closed_ball c r)).to_real, {
    simp [complex.volume_closed_ball' rp],
    apply @le_of_forall_ge_of_dense _ _ _ (π * r^2) (volume (ball c r)).to_real,
    intros a ar, by_cases an : a < 0, exact trans (le_of_lt an) (by simp), simp at an,
    set s := real.sqrt (a / π),
    have πp := real.pi_pos,
    have sp : s ≥ 0 := real.sqrt_nonneg _,
    have sr : s < r, {
      calc s = real.sqrt (a / π) : rfl
      ... < real.sqrt (π * r^2 / π) : real.sqrt_lt_sqrt (by bound) ((div_lt_div_right (by bound)).mpr (by bound))
      ... = real.sqrt (π / π * r^2) : by ring_nf
      ... = real.sqrt (r^2) : by field_simp [ne_of_gt real.pi_pos]
      ... = r : real.sqrt_sq (by bound)
    },
    have e : a = (volume (closed_ball c s)).to_real, {
      rw complex.volume_closed_ball' sp, symmetry,
      have app : a / π ≥ 0 := by bound,
      calc π * s^2 = π * real.sqrt (a / π)^2 : rfl
      ... = π * (a / π) : by rw real.sq_sqrt app
      ... = π / π * a : by ring
      ... = a : by field_simp [ne_of_gt real.pi_pos]
    },
    rw e, apply ennreal.to_real_mono, {
      rw ←lt_top_iff_ne_top, refine lt_of_le_of_lt hi' _, simp [complex.volume_closed_ball rp],
    }, {
      apply measure_mono (metric.closed_ball_subset_ball sr),
    }
  },
  have e := le_antisymm hi lo, rw e,
  exact complex.volume_closed_ball' rp,
end

lemma complex.volume_ball {c : ℂ} {r : ℝ} (rp : r ≥ 0) : volume (ball c r) = ennreal.of_real (π * r^2) := begin
  by_cases rp' : r > 0, {
    exact invert_to_real (by bound [real.pi_pos]) (complex.volume_ball' rp),
  }, {
    simp at rp', simp [le_antisymm rp' rp],
  },
end

-- closed_balls are nice
lemma nice_volume.closed_ball (c : ℂ) {r : ℝ} (rp : r > 0) : nice_volume (closed_ball c r) := {
  measurable := measurable_set_closed_ball,
  finite := by simp [complex.volume_closed_ball (le_of_lt rp)],
  pos := begin simp [complex.volume_closed_ball (le_of_lt rp)], bound [real.pi_pos], end,
}

-- closed_balls have local volume
lemma local_volume.closed_ball {c : ℂ} {r : ℝ} (rp : r > 0) : local_volume_set (closed_ball c r) := begin
  apply local_volume.closure_interior,
  intros x r rp,
  simp only [complex.volume_ball (le_of_lt rp), gt_iff_lt, ennreal.of_real_pos],
  bound [real.pi_pos],
  have rz := ne_of_gt rp,
  simp only [interior_closed_ball c rz, closure_ball c rz],
end