-- The multibrot set

import analysis.complex.basic
import analysis.calculus.lhopital
import data.real.basic
import data.complex.basic

import at_inf
import bottcher
import holomorphic
import multiple
import riemann_sphere
import tactics

open complex (abs has_zero)
open filter (eventually_of_forall tendsto at_top)
open function (uncurry)
open metric (ball closed_ball is_open_ball mem_ball_self mem_ball mem_closed_ball mem_closed_ball_self)
open real (exp log)
open riemann_sphere
open set
open_locale alexandroff riemann_sphere topology
noncomputable theory

variables {c : ℂ}

-- Fix d ≥ 2
variables {d : ℕ} [fact (2 ≤ d)]
lemma two_le_d [h : fact (2 ≤ d)] : 2 ≤ d := h.elim
lemma d_pos : 0 < d := trans (by norm_num) two_le_d
lemma d_ne_zero : d ≠ 0 := ne_of_gt d_pos
lemma d_minus_one_pos : 0 < d-1 := nat.sub_pos_of_lt (lt_of_lt_of_le one_lt_two two_le_d)
lemma d_minus_one_ge_one : 1 ≤ d-1 := nat.succ_le_iff.mpr d_minus_one_pos
lemma d_gt_one : 1 < d := lt_of_lt_of_le (by norm_num) two_le_d
lemma d_ge_one : 1 ≤ d := le_of_lt d_gt_one

-- The multibrot iteration
def f' (d : ℕ) (c z : ℂ) : ℂ := z^d + c
def f (d : ℕ) : ℂ → 𝕊 → 𝕊 := lift' (f' d) ∞

-- The set of points that do not escape
def multibrot (d : ℕ) : set ℂ := {c | ¬tendsto (λ n, (f d c)^[n] ↑c) at_top (𝓝 ∞)}

-- The exterior, including ∞
def multibrot_ext (d : ℕ) : set 𝕊 := coe '' (multibrot d)ᶜ ∪ {∞}

-- Basic properties of multibrot_ext
lemma multibrot_ext_inf : ∞ ∈ multibrot_ext d := subset_union_right _ _ rfl
lemma multibrot_ext_coe {c : ℂ} : ↑c ∈ multibrot_ext d ↔ c ∉ multibrot d := begin
  simp only [multibrot_ext, mem_union, mem_singleton_iff, coe_eq_inf_iff, or_false, mem_image, mem_compl_iff, coe_eq_coe],
  constructor, rintros ⟨x,m,e⟩, rw e at m, exact m, intro m, use [c,m],
end
lemma coe_preimage_multibrot_ext : coe ⁻¹' multibrot_ext d = (multibrot d)ᶜ := begin
  apply set.ext, intros z, simp only [mem_compl_iff, mem_preimage, multibrot_ext_coe],
end

-- Basic properties of f
lemma f_0' (d : ℕ) [fact (2 ≤ d)] : f' d c 0 = c := by simp only [lift_coe', f', zero_pow d_pos, zero_add]
lemma f_0 (d : ℕ) [fact (2 ≤ d)] : f d c 0 = c := by simp only [f, ←coe_zero, lift_coe', f', zero_pow d_pos, zero_add]
lemma analytic_f' : analytic_on ℂ (uncurry (f' d)) univ := λ _ _, analytic_at_snd.pow.add analytic_at_fst
lemma deriv_f' {z : ℂ} : deriv (f' d c) z = d*z^(d-1) := begin
  have h : has_deriv_at (f' d c) (d*z^(d-1) + 0) z := (has_deriv_at_pow _ _).add (has_deriv_at_const _ _),
  simp only [add_zero] at h, exact h.deriv,
end
lemma tendsto_f'_at_inf (c : ℂ) : tendsto (uncurry (f' d)) ((𝓝 c).prod at_inf) at_inf := begin
  simp only [at_inf_basis.tendsto_right_iff, complex.norm_eq_abs, set.mem_set_of_eq, forall_true_left, uncurry,
    metric.eventually_nhds_prod_iff],
  intros r, use [1, zero_lt_one, λ z, max r 0 + abs c + 1 < abs z], constructor, {
    refine (eventually_at_inf (max r 0 + abs c + 1)).mp (eventually_of_forall (λ w h, _)),
    simp only [complex.norm_eq_abs] at h, exact h,
  }, {
    intros e ec z h, simp only [complex.dist_eq] at ec,
    have zz : abs z ≤ abs (z^d), {
      rw complex.abs.map_pow, refine le_self_pow _ d_ne_zero,
      exact trans (le_add_of_nonneg_left (add_nonneg (le_max_right _ _) (complex.abs.nonneg _))) (le_of_lt h),
    },
    calc abs (f' d e z) = abs (z^d + e) : rfl
    ... = abs (z^d + (c + (e-c))) : by ring_nf
    ... ≥ abs (z^d) - abs (c + (e-c)) : by bound 
    ... ≥ abs (z^d) - (abs c + abs (e-c)) : by bound 
    ... ≥ abs z - (abs c + 1) : by bound [zz]
    ... > max r 0 + abs c + 1 - (abs c + 1) : by bound
    ... = max r 0 : by ring_nf
    ... ≥ r : le_max_left _ _,
  },
end
lemma holomorphic_f : holomorphic II I (uncurry (f d)) := holomorphic_lift' analytic_f' tendsto_f'_at_inf
lemma written_in_ext_chart_at_coe_f {z : ℂ} : written_in_ext_chart_at I I (z : 𝕊) (f d c) = f' d c :=
  by simp only [written_in_ext_chart_at, f, function.comp, lift_coe', riemann_sphere.ext_chart_at_coe,
    local_equiv.symm_symm, coe_local_equiv_apply, coe_local_equiv_symm_apply, to_complex_coe]
lemma fl_f : fl (f d) ∞ = λ c z, z^d/(1 + c*z^d) := begin
  funext c z,
  simp only [fl, riemann_sphere.ext_chart_at_inf, function.comp, inv_equiv_apply, local_equiv.trans_apply,
    equiv.to_local_equiv_apply, local_equiv.coe_trans_symm, coe_local_equiv_symm_apply, local_equiv.symm_symm,
    coe_local_equiv_apply, equiv.to_local_equiv_symm_apply, inv_equiv_symm, inv_inf, to_complex_zero, add_zero,
    sub_zero],
  by_cases z0 : z = 0, {
    simp only [z0, coe_zero, inv_zero', f, lift_inf', inv_inf, to_complex_zero, zero_pow d_pos, zero_div],
  },
  simp only [f, f', inv_coe z0, lift_coe', inv_pow],
  have zd := pow_ne_zero d z0,
  by_cases h : (z^d)⁻¹ + c = 0, {
    simp only [h, coe_zero, inv_zero', to_complex_inf],
    simp only [←add_eq_zero_iff_neg_eq.mp h, neg_mul, inv_mul_cancel zd, ←sub_eq_add_neg, sub_self, div_zero],
  },
  rw [inv_coe h, to_complex_coe, eq_div_iff, inv_mul_eq_iff_eq_mul₀ h, right_distrib, inv_mul_cancel zd],
  contrapose h, rw not_not,
  rw [not_not, add_comm, add_eq_zero_iff_eq_neg, ←eq_div_iff zd, neg_div, ←inv_eq_one_div, ←add_eq_zero_iff_eq_neg,
    add_comm] at h, exact h,
end
def gl (d : ℕ) (c z : ℂ) := (1 + c*z^d)⁻¹
lemma gl_f {z : ℂ} : g (fl (f d) ∞ c) d z = gl d c z := begin
  simp only [fl_f, gl, g],
  by_cases z0 : z = 0, simp only [if_pos, z0, zero_pow d_pos, mul_zero, add_zero, inv_one],
  rw [if_neg z0, div_eq_mul_inv _ (_ + _), mul_comm, mul_div_assoc, div_self (pow_ne_zero _ z0), mul_one],
end
lemma analytic_at_gl : analytic_at ℂ (gl d c) 0 := begin
  apply (analytic_at_const.add (analytic_at_const.mul analytic_at_id.pow)).inv,
  simp only [pi.add_apply, zero_pow d_pos, mul_zero], norm_num,
end
lemma fl_f' : fl (f d) ∞ = λ c z, (z - 0)^d • gl d c z := begin
  funext c z, simp only [fl_f, gl, sub_zero, algebra.id.smul_eq_mul, div_eq_mul_inv],
end 
lemma gl_zero : gl d c 0 = 1 := begin simp only [gl, zero_pow d_pos, mul_zero], norm_num end
lemma gl_frequently_ne_zero : ∃ᶠ z in 𝓝 0, gl d c z ≠ 0 := begin
  refine (analytic_at_gl.continuous_at.eventually_ne _).frequently, simp only [gl_zero], exact one_ne_zero,
end
lemma fc_f : leading_coeff (fl (f d) ∞ c) 0 = 1 := begin
  rw [fl_f', analytic_at_gl.monomial_mul_leading_coeff gl_frequently_ne_zero, leading_coeff_of_ne_zero],
  exact gl_zero, rw gl_zero, exact one_ne_zero, apply_instance, apply_instance,
end
lemma fd_f : order_at (fl (f d) ∞ c) 0 = d := begin
  rw [fl_f', analytic_at_gl.monomial_mul_order_at gl_frequently_ne_zero, order_at_eq_zero, add_zero],
  rw gl_zero, exact one_ne_zero, apply_instance, apply_instance,
end
lemma f_inf : f d c ∞ = ∞ := by simp only [f, f', lift_inf', eq_self_iff_true, imp_true_iff]

-- f has a superattracting fixpoint at ∞
lemma super_f (d : ℕ) [fact (2 ≤ d)]: super (f d) d ∞ := {
  d2 := two_le_d, fa := holomorphic_f, fc := λ c, fc_f, fd := λ c, fd_f, f0 := λ c, f_inf,
}

-- An explicit bound on the near region near ∞
lemma super_near_f (d : ℕ) [fact (2 ≤ d)] (c : ℂ)
    : super_near (fl (f d) ∞ c) d {z | abs z < (max 16 (abs c / 2))⁻¹} := begin
  set s := super_f d,
  generalize ht : {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹} = t,
  have cz : ∀ {z}, z ∈ t → abs (c*z^d) ≤ 1/8, {
    intros z m, simp only [←ht, mem_set_of] at m,
    simp only [complex.abs.map_mul, complex.abs.map_pow],
    transitivity abs c * (max 16 (abs c / 2))⁻¹^d, bound,
    rw [inv_pow, mul_inv_le_iff], swap, bound,
    rw mul_one_div, rw [le_div_iff, mul_comm], swap, norm_num,
    refine trans _ (pow_le_pow (le_max_of_le_left (by norm_num)) two_le_d),
    by_cases cb : abs c / 2 ≤ 16,
    rw [max_eq_left cb, pow_two], linarith,
    rw [max_eq_right (le_of_lt (not_le.mp cb)), pow_two], nlinarith,
  },
  have cz1 : ∀ {z}, z ∈ t → 7/8 ≤ abs (1 + c*z^d), {
    intros z m,
    calc abs (1 + c*z^d) ≥ complex.abs 1 - abs (c*z^d) : by bound
    ... ≥ complex.abs 1 - 1/8 : by bound [cz m]
    ... = 7/8 : by norm_num,
  },
  have zb : ∀ {z}, z ∈ t → abs z ≤ 1/8, {
    intros z m, rw ←ht at m, refine trans (le_of_lt m) _,
    rw one_div, exact inv_le_inv_of_le (by norm_num) (trans (by norm_num) (le_max_left _ _)),
  },
  exact {
    d2 := two_le_d, fa0 := (s.fla c).in2, fd := fd_f, fc := fc_f,
    o := begin rw ←ht, exact is_open_lt complex.continuous_abs continuous_const end,
    t0 := begin simp only [←ht, mem_set_of, complex.abs.map_zero], bound end,
    t2 := λ z m, trans (zb m) (by norm_num),
    fa := begin
      intros z m, rw fl_f,
      refine analytic_at_id.pow.div (analytic_at_const.add (analytic_at_const.mul analytic_at_id.pow)) _,
      rw ←complex.abs.ne_zero_iff, exact ne_of_gt (lt_of_lt_of_le (by norm_num) (cz1 m)),
    end,
    ft := begin
      intros z m, specialize cz1 m, specialize zb m,
      simp only [fl_f, mem_set_of, map_div₀, complex.abs.map_pow, ←ht] at ⊢ m,
      refine lt_of_le_of_lt _ m, rw div_le_iff (lt_of_lt_of_le (by norm_num) cz1),
      refine trans (pow_le_pow_of_le_one (complex.abs.nonneg _) (trans zb (by norm_num)) two_le_d) _,
      rw pow_two, refine mul_le_mul_of_nonneg_left _ (complex.abs.nonneg _),
      exact trans zb (trans (by norm_num) cz1),
    end,
    gs' := begin
      intros z z0 m, simp only [fl_f, div_div_cancel_left' (pow_ne_zero d z0)],
      specialize cz1 m,
      have czp : 0 < abs (1 + c*z^d) := lt_of_lt_of_le (by norm_num) cz1,
      refine le_of_mul_le_mul_right _ czp,
      rw [←complex.abs.map_mul, mul_sub_right_distrib, one_mul,
        inv_mul_cancel (complex.abs.ne_zero_iff.mp (ne_of_gt czp)), ←sub_sub, sub_self, zero_sub, complex.abs.map_neg],
      exact trans (cz m) (trans (by norm_num) (mul_le_mul_of_nonneg_left cz1 (by norm_num))),
    end,
  },
end

-- f has one preimage of ∞
instance one_preimage_f : one_preimage (super_f d) := {eq_a := begin
  intros c z, induction z using riemann_sphere.rec,
  simp only [f, lift_coe', coe_eq_inf_iff], exact λ f, f,
  simp only [eq_self_iff_true, imp_true_iff],
end}

-- 0 and ∞ are the only critical points
lemma critical_f {z : 𝕊} : critical (f d c) z ↔ z = 0 ∨ z = ∞ := begin
  induction z using riemann_sphere.rec, {
    simp only [critical, mfderiv, (holomorphic_f (c,z)).in2.mdifferentiable_at, if_pos,
      model_with_corners.boundaryless.range_eq_univ, fderiv_within_univ, written_in_ext_chart_at_coe_f,
      riemann_sphere.ext_chart_at_coe, coe_local_equiv_symm_apply, to_complex_coe, coe_eq_zero, coe_eq_inf_iff,
      or_false, ←deriv_fderiv, deriv_f', continuous_linear_map.ext_iff, continuous_linear_map.smul_right_apply,
      continuous_linear_map.one_apply, algebra.id.smul_eq_mul, one_mul, continuous_linear_map.zero_apply,
      mul_eq_zero, nat.cast_eq_zero, d_ne_zero, false_or, pow_eq_zero_iff d_minus_one_pos],
    constructor, intro h, specialize h 1, simp only [one_ne_zero, false_or] at h, exact h, exact λ h x, or.inr h,
  }, {
    simp only [eq_self_iff_true, or_true, iff_true, (super_f d).critical_a],
  },
end

-- The multibrot set is all c's s.t. 0 doesn't reach ∞
lemma multibrot_basin' : c ∈ multibrot d ↔ (c,(c:𝕊)) ∉ (super_f d).basin :=
  by simp only [multibrot, mem_set_of, super.basin_iff_attracts, attracts]
lemma multibrot_basin : c ∈ multibrot d ↔ (c,(0:𝕊)) ∉ (super_f d).basin := begin
  set s := super_f d,
  simp only [multibrot_basin', not_iff_not, super.basin, mem_set_of],
  have e : ∀ n, (f d c^[n] c) = (f d c^[n+1] 0), {
    intros n, induction n with n h,
    simp only [function.iterate_zero_apply, zero_add, function.iterate_one, f_0],
   simp only [function.iterate_succ_apply', h],
  },
  simp only [e], constructor,
  rintros ⟨n,h⟩, use [n+1,h],
  rintros ⟨n,h⟩, use n, simp only [function.iterate_succ_apply'], exact s.stays_near h,
end

-- (c,c) is postcritical for c outside multibrot
lemma multibrot_p (m : c ∉ multibrot d) : (super_f d).p c = (super_f d).potential c 0 := begin
  set s := super_f d,
  have e : s.ps c = {1, s.potential c 0}, {
    apply set.ext, intro p, simp only [super.ps, mem_singleton_iff, mem_set_of, critical_f, ne.def,
      mem_insert_iff, mem_singleton_iff],
    constructor, {
      intro h, cases h, left, exact h, right, rcases h with ⟨p0,z,e,h⟩, cases h, rw h at e, exact e.symm,
      rw [h, s.potential_a] at e, exfalso, exact p0 e.symm,
    }, {
      intro h, cases h, left, exact h, right, constructor, {
        simp only [h, ←ne.def, s.potential_ne_zero], exact inf_ne_zero.symm,
      }, {
        use [0, h.symm, or.inl rfl],
      },
    },
  },
  simp only [super.p, e, cInf_pair], exact inf_of_le_right s.potential_le_one,
end
lemma multibrot_post (m : c ∉ multibrot d) : postcritical (super_f d) c c := begin
  set s := super_f d,
  simp only [postcritical, multibrot_p m, ←f_0 d, s.potential_eqn],
  simp only [multibrot_basin, not_not] at m,
  exact pow_lt_self_of_lt_one ((s.potential_pos c).mpr inf_ne_zero.symm) (s.potential_lt_one m) d_gt_one,
end

-- The multibrot bottcher map
def bottcher' (d : ℕ) [fact (2 ≤ d)] (c : ℂ) : ℂ := (super_f d).bottcher c c
def bottcher (d : ℕ) [fact (2 ≤ d)] : 𝕊 → ℂ := fill (bottcher' d) 0

-- bottcher at ℂ and ∞ 
lemma bottcher_coe {c : ℂ} : bottcher d c = bottcher' d c := rfl
lemma bottcher_inf : bottcher d ∞ = 0 := rfl

-- Multibrot membership in terms of f', not f
lemma f_f'_iter (n : ℕ) {z : ℂ} : (f d c^[n] ↑z) = ↑(f' d c^[n] z) := begin
  induction n with n h, simp only [function.iterate_zero, id],
  simp only [h, function.iterate_succ_apply'],
  generalize hx : f' d c^[n] c = x,
  simp only [f, lift', rec_coe],
end
lemma multibrot_coe : c ∈ multibrot d ↔ ¬tendsto (λ n, (f' d c)^[n] c) at_top at_inf :=
  by simp only [multibrot, mem_set_of, f_f'_iter, not_iff_not, tendsto_inf_iff_tendsto_at_inf]

-- The multibrot set is inside radius 2
lemma multibrot_le_two (m : c ∈ multibrot d) : abs c ≤ 2 := begin
  set s := abs c,
  contrapose m,
  simp only [multibrot_coe, not_le, not_not] at m ⊢,
  have s1 : 1 ≤ s := trans (by norm_num) (le_of_lt m),
  have s1' : 1 ≤ s-1 := by linarith, 
  have a : ∀ z : ℂ, 1 ≤ abs z → abs z^2 - s ≤ abs (f' d c z), {
    intros z z1, simp only [f'], refine trans (sub_le_sub_right _ _) (complex.abs.le_add _ _),
    simp only [complex.abs.map_pow], exact pow_le_pow z1 two_le_d,
  },
  have b : ∀ n, s*(s-1)^n ≤ abs (f' d c^[n] c), {
    intro n, induction n with n h, simp only [pow_zero, mul_one, function.iterate_zero_apply],
    simp only [function.iterate_succ_apply'], refine trans _ (a _ _), {
      transitivity (s * (s-1)^n)^2 - s, swap, bound,
      calc (s * (s-1)^n)^2 - s = s^2 * ((s-1)^n)^2 - s : by ring
      ... = s^2 * (s-1)^(n*2) - s : by rw pow_mul
      ... ≥ s^2 * (s-1)^(n*2) - s * (s-1)^(n*2) : by bound [le_mul_of_one_le_right, one_le_pow_of_one_le s1']
      ... = s * ((s-1)^1 * (s-1)^(n*2)) : by ring
      ... = s * (s-1)^(1+n*2) : by rw pow_add
      ... ≥ s * (s-1)^(1+n*1) : by bound [pow_le_pow]
      ... = s * (s-1)^(n+1) : by ring_nf,
    }, {
      exact trans (left.one_le_mul_of_le_of_le s1 (one_le_pow_of_one_le s1' _) (by bound)) h,
    },
  },
  simp only [tendsto_at_inf_iff_norm_tendsto_at_top, complex.norm_eq_abs],
  apply filter.tendsto_at_top_mono b, refine filter.tendsto.mul_at_top (by bound) tendsto_const_nhds _,
  apply tendsto_pow_at_top_at_top_of_one_lt, linarith,
end
lemma multibrot_subset_closed_ball : multibrot d ⊆ closed_ball 0 2 := begin
  intros c m, simp only [mem_closed_ball, complex.dist_eq, sub_zero], exact multibrot_le_two m,
end
lemma multibrot_two_lt (a : 2 < abs c) : c ∉ multibrot d := begin
  contrapose a, simp only [not_lt, not_not] at a ⊢, exact multibrot_le_two a,
end

-- If we repeat, we're in the multibrot set
lemma multibrot_of_repeat {a b : ℕ} (ab : a < b) (h : (f d c^[a] c) = (f d c^[b] c)) : c ∈ multibrot d := begin
  generalize hg : (λ n, f' d c^[n] c) = g,
  replace hg : ∀ n, f' d c^[n] c = g n := λ n, by rw ←hg,
  simp only [f_f'_iter, ←coe_zero, coe_eq_coe, hg] at h,
  have lo : ∀ n : ℕ, ∃ k, k ≤ b ∧ g n = g k, {
    intro n, induction n with n h, use [0, nat.zero_le _],
    rcases h with ⟨k,kb,nk⟩,
    by_cases e : k = b, use [a+1, nat.succ_le_iff.mpr ab],
    rw [←hg, ←hg, function.iterate_succ_apply', function.iterate_succ_apply', hg, hg, nk, e, h],
    use [k+1, nat.succ_le_iff.mpr (ne.lt_of_le e kb)],
    rw [←hg, ←hg, function.iterate_succ_apply', function.iterate_succ_apply', hg, hg, nk],
  },
  simp only [multibrot_coe, at_inf_basis.tendsto_right_iff, true_implies_iff, not_forall, filter.not_eventually,
    mem_set_of, not_lt, complex.norm_eq_abs, hg],
  use partial_sups (λ k, complex.abs (g k)) b,
  apply filter.frequently_of_forall, intro k, rcases lo k with ⟨l,lb,kl⟩,
  rw kl, exact le_partial_sups_of_le _ lb,
end

-- If we hit zero, we're in the multibrot set 
lemma multibrot_of_zero {n : ℕ} (h : f d c^[n] c = 0) : c ∈ multibrot d := begin
  have i0 : (f d c^[0] c) = c := by rw [function.iterate_zero_apply],
  have i1 : (f d c^[n+1] c) = c := by simp only [function.iterate_succ_apply', h, f_0],
  exact multibrot_of_repeat (nat.zero_lt_succ _) (trans i0 i1.symm),
end
lemma multibrot_zero : (0 : ℂ) ∈ multibrot d := begin
  apply multibrot_of_zero, rw [function.iterate_zero_apply, coe_zero],
end

-- multibrot d is compact
lemma not_multibrot_of_two_lt {n : ℕ} (h : 2 < abs (f' d c^[n] c)) : c ∉ multibrot d := begin
  by_cases c2 : 2 < abs c, exact multibrot_two_lt c2,
  simp only [multibrot_coe, not_not], simp only [not_lt] at c2,
  generalize hs : abs (f' d c^[n] c) = s, rw hs at h,
  have s1 : 1 ≤ s := by linarith,
  have s1' : 1 ≤ s-1 := by linarith,
  have b : ∀ k, s*(s-1)^k ≤ abs (f' d c^[k+n] c), {
    intro k, induction k with k p, simp only [pow_zero, mul_one, zero_add, ←hs],
    simp only [nat.succ_add, function.iterate_succ_apply'],
    generalize hz : f' d c^[k + n] c = z, rw hz at p, clear hz hs n,
    have ss1 : 1 ≤ s*(s-1)^k := by bound [one_le_mul_of_one_le_of_one_le, one_le_pow_of_one_le],
    have k2 : k ≤ k*2 := by linarith, 
    calc abs (f' d c z) = abs (z^d + c) : rfl
    ... ≥ abs (z^d) - abs c : by bound
    ... = abs z^d - abs c : by rw complex.abs.map_pow
    ... ≥ (s*(s-1)^k)^d - 2 : by bound [pow_le_pow_of_le_left]
    ... ≥ (s*(s-1)^k)^2 - 2 : by bound [pow_le_pow, two_le_d]
    ... = s^2*(s-1)^(k*2) - 2*1 : by rw [mul_pow, pow_mul, mul_one]
    ... ≥ s^2*(s-1)^k - s*(s-1)^k : by bound [pow_le_pow, one_le_pow_of_one_le]
    ... = s*((s-1)^k*(s-1)) : by ring
    ... = s * (s-1)^(k+1) : by rw pow_succ',
  },
  simp only [tendsto_at_inf_iff_norm_tendsto_at_top, complex.norm_eq_abs],
  rw [←filter.tendsto_add_at_top_iff_nat n], apply filter.tendsto_at_top_mono b,
  refine filter.tendsto.mul_at_top (by bound) tendsto_const_nhds _,
  apply tendsto_pow_at_top_at_top_of_one_lt, linarith,
end
lemma multibrot_eq_le_two : multibrot d = ⋂ n : ℕ, (λ c : ℂ, f' d c^[n] c) ⁻¹' closed_ball 0 2 := begin
  apply set.ext, intro c,
  simp only [mem_Inter, mem_preimage, mem_closed_ball, complex.dist_eq, sub_zero],
  constructor, {
    intros m n, contrapose m, simp only [not_le] at m, exact not_multibrot_of_two_lt m,
  }, {
    intros h, contrapose h,
    simp only [multibrot_coe, tendsto_at_inf_iff_norm_tendsto_at_top, complex.norm_eq_abs,
      not_not, not_forall, not_le, filter.tendsto_at_top, not_exists] at h ⊢,
      rcases (h 3).exists with ⟨n,h⟩, use n, linarith,
  },
end
lemma is_compact_multibrot : is_compact (multibrot d) := begin
  refine is_compact_of_is_closed_subset (is_compact_closed_ball _ _) _ multibrot_subset_closed_ball,
  rw multibrot_eq_le_two, apply is_closed_Inter, intros n,
  refine is_closed.preimage _ metric.is_closed_ball,
  induction n with n h, simp only [function.iterate_zero_apply], exact continuous_id,
  simp only [function.iterate_succ_apply'], rw continuous_iff_continuous_at, intro c,
  exact (analytic_f' _ (mem_univ _)).continuous_at.curry_comp continuous_at_id h.continuous_at,
end

-- The exterior is open
lemma is_open_multibrot_ext : is_open (multibrot_ext d) := begin
  rw alexandroff.is_open_iff_of_mem',
  simp only [coe_preimage_multibrot_ext, compl_compl],
  use [is_compact_multibrot, is_compact_multibrot.is_closed.is_open_compl],
  exact multibrot_ext_inf,
end

-- bottcher' d c is small for large c
lemma bottcher_bound {c : ℂ} (lo : 16 < abs c) : abs (bottcher' d c) ≤ 3 * abs c⁻¹ := begin
  set s := super_f d,
  generalize hg : fl (f d) ∞ c = g,
  -- Facts about c and f
  have ct : c⁻¹ ∈ {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹}, {
    simp only [mem_set_of, map_inv₀],
    apply inv_lt_inv_of_lt, bound, refine max_lt lo (half_lt_self (trans (by norm_num) lo)),
  },
  have mem : c ∉ multibrot d := multibrot_two_lt (trans (by norm_num) lo),
  have nz : ∀ n, f d c^[n] c ≠ 0, {
    intro n, contrapose mem, simp only [not_not] at mem ⊢, exact multibrot_of_zero mem,
  },
  have iter : ∀ n, (f d c^[n] ↑c)⁻¹ = ↑(g^[n] c⁻¹), {
    intro n, induction n with n h,
    have cp : c ≠ 0 := complex.abs.ne_zero_iff.mp (ne_of_gt (trans (by norm_num) lo)),
    simp only [function.iterate_zero_apply, inv_coe cp, to_complex_coe],
    have e : (f d c^[n] ↑c) = ((g^[n] c⁻¹ : ℂ) : 𝕊)⁻¹ := by rw [←h, inv_inv],
    simp only [function.iterate_succ_apply', e],
    generalize hz : g^[n] c⁻¹ = z,
    simp only [←hg, fl, ext_chart_at_inf, local_equiv.trans_apply, equiv.to_local_equiv_apply, inv_equiv_apply,
      inv_inf, coe_local_equiv_symm_apply, to_complex_zero, sub_zero, function.comp, add_zero, local_equiv.coe_trans_symm,
      local_equiv.symm_symm, coe_local_equiv_apply, equiv.to_local_equiv_symm_apply, inv_equiv_symm],
    rw coe_to_complex,
    simp only [ne.def, inv_eq_inf, ←hz, ←h, inv_inv, ←function.iterate_succ_apply' (f d c)],
    apply nz,
  },
  -- Find an n that gets us close enough to ∞ for s.bottcher = bottcher_near
  have b := mem, simp only [multibrot_basin', not_not] at b,
  have attracts := (s.basin_attracts b).eventually (s.bottcher_eq_bottcher_near c),
  rcases (attracts.and (s.basin_stays b)).exists with ⟨n,eq,near⟩, clear attracts b,
  simp only [super.bottcher_near, ext_chart_at_inf, local_equiv.trans_apply, coe_local_equiv_symm_apply,
    equiv.to_local_equiv_apply, inv_equiv_apply, inv_inf, to_complex_zero, sub_zero, super.fl, hg, iter,
    to_complex_coe] at eq,
  -- Translate our bound across n iterations
  have e0 : s.bottcher c (f d c^[n] ↑c) = bottcher' d c ^ d^n := s.bottcher_eqn_iter n,
  have e1 : bottcher_near g d (g^[n] c⁻¹) = bottcher_near g d c⁻¹ ^ d^n, {
    rw ←hg, exact bottcher_near_eqn_iter (super_near_f d c) ct n,
  },
  rw [e0,e1] at eq, clear e0 e1 iter,
  have ae : abs (bottcher' d c) = abs (bottcher_near g d c⁻¹), {
    apply (pow_left_inj (complex.abs.nonneg _) (complex.abs.nonneg _) (pow_pos d_pos n : 0 < d^n)).mp,
    simp only [←complex.abs.map_pow, eq],
  },
  rw [ae, ←hg], exact bottcher_near_le (super_near_f d c) ct,
end

-- bottcher' d c → 0 as c → ∞
lemma bottcher_tendsto_zero : tendsto (bottcher' d) at_inf (𝓝 0) := begin
  rw metric.tendsto_nhds, intros r rp, rw at_inf_basis.eventually_iff,
  use max 16 (3 / r),
  simp only [true_and, mem_set_of, complex.dist_eq, sub_zero, complex.norm_eq_abs, max_lt_iff],
  rintros z ⟨lo,rz⟩, apply lt_of_le_of_lt (bottcher_bound lo),
  rw div_lt_iff rp at rz, rw [map_inv₀, mul_inv_lt_iff (trans (by norm_num) lo)], exact rz,
end

-- bottcher is holomorphic on the outside
lemma bottcher_analytic : analytic_on ℂ (bottcher' d) (multibrot d)ᶜ := begin
  set s := super_f d, intros c m, apply holomorphic_at.analytic_at I I,
  exact (s.bottcher_holomorphic_on (c,c) (multibrot_post m)).curry_comp_of_eq holomorphic_at_id (holomorphic_coe _) rfl,
end
lemma bottcher_holomorphic (d : ℕ) [fact (2 ≤ d)] : holomorphic_on I I (bottcher d) (multibrot_ext d) := begin
  intros c m, induction c using riemann_sphere.rec, {
    simp only [multibrot_ext_coe] at m,
    exact holomorphic_at_fill_coe ((bottcher_analytic _ m).holomorphic_at I I),
  }, {
    refine holomorphic_at_fill_inf _ bottcher_tendsto_zero,
    rw at_inf_basis.eventually_iff, use 2,
    simp only [true_and, mem_set_of, complex.norm_eq_abs],
    exact λ z a, (bottcher_analytic _ (multibrot_two_lt a)).holomorphic_at I I,
  },
end

-- potential on 𝕊
def potential (d : ℕ) [fact (2 ≤ d)] : 𝕊 → ℝ := fill (λ c, (super_f d).potential c c) 0
lemma abs_bottcher {c : 𝕊} : abs (bottcher d c) = potential d c := begin
  set s := super_f d,
  induction c using riemann_sphere.rec,
  simp only [bottcher, potential, fill_coe], exact s.abs_bottcher,
  simp only [bottcher, potential, fill_inf, complex.abs.map_zero],
end
lemma potential_continuous : continuous (potential d) := begin
  set s := super_f d, rw continuous_iff_continuous_at, intro c, induction c using riemann_sphere.rec,
  exact continuous_at_fill_coe ((continuous.potential s).curry_comp continuous_id continuous_coe).continuous_at,
  have e : potential d =ᶠ[𝓝 ∞] (λ c, abs (bottcher d c)), { refine eventually_of_forall (λ c, _), rw ←abs_bottcher },
  rw continuous_at_congr e,
  exact complex.continuous_abs.continuous_at.comp (bottcher_holomorphic d _ multibrot_ext_inf).continuous_at,
end
lemma potential_lt_one {c : 𝕊} : potential d c < 1 ↔ c ∈ multibrot_ext d := begin
  set s := super_f d,
  induction c using riemann_sphere.rec, {
    constructor, {
      intro h, contrapose h,
      simp only [not_not, not_lt, multibrot_basin', potential, fill_coe, super.basin, mem_set_of, not_exists,
        multibrot_ext_coe] at h ⊢,
      rw s.potential_eq_one, exact h,
    }, {
      intro m, rw ←abs_bottcher, simp only [bottcher, fill_coe], simp only [multibrot_ext_coe] at m,
      exact s.bottcher_lt_one (multibrot_post m),
    },
  }, {  
    simp only [potential, bottcher, fill_inf, zero_lt_one, multibrot_ext_inf],
  },
end
lemma potential_nonneg {c : 𝕊} : 0 ≤ potential d c := begin
  induction c using riemann_sphere.rec, simp only [potential, fill_coe], exact (super_f d).potential_nonneg,
  simp only [potential, fill_inf],
end 
lemma potential_eq_zero {c : 𝕊} : potential d c = 0 ↔ c = ∞ := begin
  induction c using riemann_sphere.rec,
  simp only [potential, fill_coe, (super_f d).potential_eq_zero_of_one_preimage],
  simp only [potential, fill_inf, eq_self_iff_true],
end

-- bottcher is nontrivial everywhere in multibrot_ext, as otherwise trivality spreads throughout 𝕊
lemma bottcher_nontrivial {c : 𝕊} (m : c ∈ multibrot_ext d) : nontrivial_holomorphic_at (bottcher d) c := begin
  by_cases h : ∃ᶠ e in 𝓝 c, bottcher d e ≠ bottcher d c,
  exact {holomorphic_at := bottcher_holomorphic d _ m, nonconst := h },
  exfalso, simp only [filter.not_frequently, not_not] at h,
  set b := bottcher d c,
  have b1 : abs b < 1 := by simp only [abs_bottcher, potential_lt_one, m],
  -- From bottcher d c = y near a point, show that bottcher d c = y everywhere in 𝕊
  set t := {c | c ∈ multibrot_ext d ∧ ∀ᶠ e in 𝓝 c, bottcher d e = b},
  have tu : t = univ, {
    refine is_clopen.eq_univ _ ⟨c,m,h⟩, constructor, {
      rw is_open_iff_eventually, rintros e ⟨m,h⟩,
      apply (is_open_multibrot_ext.eventually_mem m).mp,
      apply (eventually_eventually_nhds.mpr h).mp,
      exact eventually_of_forall (λ f h m, ⟨m,h⟩),
    }, {
      rw is_closed_iff_frequently, intros x e, by_contradiction xt,
      have pb : potential d x = abs b, {
        apply tendsto_nhds_unique_of_frequently_eq potential_continuous.continuous_at continuous_at_const,
        refine e.mp (eventually_of_forall _), rintros z ⟨m,h⟩, rw [←h.self, abs_bottcher],
      },
      rw [←pb, potential_lt_one] at b1,
      have e' : ∃ᶠ y in 𝓝[{x}ᶜ] x, y ∈ t, {
        simp only [frequently_nhds_within_iff, mem_compl_singleton_iff],
        refine e.mp (eventually_of_forall (λ z zt, ⟨zt,_⟩)),
        contrapose xt, simp only [not_not] at xt ⊢, rwa ←xt,
      },
      contrapose xt, simp only [not_not], use b1,
      cases holomorphic_at.eventually_eq_or_eventually_ne (bottcher_holomorphic d _ b1) holomorphic_at_const with h h,
      use h, contrapose h, simp only [filter.not_eventually, not_not] at ⊢ h,
      exact e'.mp (eventually_of_forall (λ y yt, yt.2.self)),
    },
  },
  -- Contradiction!
  have m0 : (0 : 𝕊) ∈ multibrot_ext d, { have m : (0 : 𝕊) ∈ t := by simp only [tu, mem_univ], exact m.1 },
  simp only [←coe_zero, multibrot_ext_coe, multibrot_zero, not_true] at m0, exact m0,
end

-- bottcher surjects onto ball 0 1
lemma bottcher_surj (d : ℕ) [fact (2 ≤ d)] : bottcher d '' multibrot_ext d = ball 0 1 := begin
  set s := super_f d,
  apply subset_antisymm, {
    intros w, simp only [mem_image], rintros ⟨c,m,e⟩, rw ←e, clear e w,
    induction c using riemann_sphere.rec, {
      simp only [multibrot_ext_coe] at m,
      simp only [bottcher, fill_coe, bottcher', mem_ball, complex.dist_eq, sub_zero],
      exact s.bottcher_lt_one (multibrot_post m),
    }, {
      simp only [bottcher, fill_inf], exact mem_ball_self one_pos,
    },
  }, {
    refine trans _ interior_subset,
    refine is_preconnected.relative_clopen (convex_ball _ _).is_preconnected _ _ _, {
      use [0, mem_ball_self one_pos, ∞], simp only [multibrot_ext_inf, bottcher, fill_inf, true_and],
    }, {
      -- Relative openness
      rw is_open.interior_eq, exact inter_subset_right _ _,
      rw is_open_iff_eventually, rintros z ⟨c,m,e⟩,
      rw [←e, (bottcher_nontrivial m).nhds_eq_map_nhds, filter.eventually_map],
      exact (is_open_multibrot_ext.eventually_mem m).mp (eventually_of_forall (λ e m, by use [e,m])),
    }, {
      -- Relative closedness
      rintro x ⟨x1,m⟩, simp only [mem_ball, complex.dist_eq, sub_zero] at x1,
      rcases exists_between x1 with ⟨b,xb,b1⟩,
      set t := {e | potential d e ≤ b},
      have ct : is_compact t := (is_closed_le potential_continuous continuous_const).is_compact,
      have ts : t ⊆ multibrot_ext d, {
        intros c m, rw ←potential_lt_one, exact lt_of_le_of_lt m b1,
      },
      have mt : x ∈ closure (bottcher d '' t), {
        rw mem_closure_iff_frequently at m ⊢, apply m.mp,
        have lt : ∀ᶠ y : ℂ in 𝓝 x, abs y < b := complex.continuous_abs.continuous_at.eventually_lt continuous_at_const xb,
        refine lt.mp (eventually_of_forall (λ y lt m, _)),
        rcases m with ⟨c,m,cy⟩, rw ←cy, rw [←cy, abs_bottcher] at lt, exact ⟨c, le_of_lt lt, rfl⟩,
      },
      apply image_subset _ ts, rw is_closed.closure_eq at mt, exact mt,
      apply is_compact.is_closed, apply is_compact.image_of_continuous_on ct,
      refine continuous_on.mono _ ts, exact (bottcher_holomorphic d).continuous_on,
    },
  },
end

-- A warmup exponential lower bound on iterates
lemma iter_large (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (cb : 3 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ)
    : 2^n * abs z ≤ abs (f' d c^[n] z) := begin
  induction n with n h, simp only [pow_zero, one_mul, function.iterate_zero_apply],
  simp only [function.iterate_succ_apply'],
  generalize hw : f' d c^[n] z = w, rw hw at h, clear hw,
  have z4 : 3 ≤ abs z := trans cb cz,
  have z1 : 1 ≤ abs z := trans (by norm_num) z4,
  have nd : n+1 ≤ n*d+1 := by bound [le_mul_of_one_le_right, d_ge_one],
  calc abs (w^d + c) ≥ abs (w^d) - abs c : by bound
  ... = abs w^d - abs c : by rw complex.abs.map_pow
  ... ≥ (2^n * abs z)^d - abs c : by bound
  ... = 2^(n*d) * abs z^d - abs c : by rw [mul_pow, pow_mul]
  ... ≥ 2^(n*d) * abs z^2 - abs c : by bound [pow_le_pow z1 two_le_d]
  ... = 2^(n*d) * (abs z * abs z) - abs c : by rw pow_two
  ... ≥ 2^(n*d) * (3 * abs z) - abs c : by bound
  ... = 2^(n*d) * 2 * abs z + (2^(n*d) * abs z - abs c) : by ring
  ... = 2^(n*d+1) * abs z + (2^(n*d) * abs z - abs c) : by rw pow_succ'
  ... ≥ 2^(n+1) * abs z + (1 * abs z - abs c) : by bound [one_le_pow_of_one_le, pow_le_pow]
  ... = 2^(n+1) * abs z + (abs z - abs c) : by rw one_mul
  ... ≥ 2^(n+1) * abs z : by linarith,
end

-- Iterates tend to infinity for large c, z
lemma tendsto_iter_at_inf (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z)
    : tendsto (λ n, f' d c^[n] z) at_top at_inf := begin
  simp only [tendsto_at_inf_iff_norm_tendsto_at_top, complex.norm_eq_abs],
  refine filter.tendsto_at_top_mono (iter_large d c3 cz) _,
  exact filter.tendsto.at_top_mul_const (by linarith) (tendsto_pow_at_top_at_top_of_one_lt one_lt_two),
end

-- Approximate change of log log abs z across one iterate
lemma f_approx {c z : ℂ} (cb : 3 ≤ abs c) (cz : abs c ≤ abs z)
    : |log (log (abs (z^d + c))) - log (log (abs z)) - log d| ≤ 4 / ↑d / abs z^(d-1) := begin
  have d0 : (d : ℝ) ≠ 0 := nat.cast_ne_zero.mpr d_ne_zero,
  have d2 : 2 ≤ (d : ℝ) := trans (by norm_num) (nat.cast_le.mpr two_le_d),
  have z3 : 3 ≤ abs z := trans cb cz, 
  have z1 : 1 ≤ abs z := trans (by norm_num) z3, 
  have z0' : 0 < abs z := lt_of_lt_of_le (by norm_num) z3,
  have zd : 3 ≤ abs z^(d-1), {
    calc abs z^(d-1) ≥ 3^(d-1) : by bound [pow_mono z1]
    ... ≥ 3^1 : by bound [pow_le_pow _ d_minus_one_ge_one]
    ... = 3 : by norm_num,
  },
  have z0 : z ≠ 0 := complex.abs.ne_zero_iff.mp (ne_of_gt z0'),
  have zd0 : z^d ≠ 0 := pow_ne_zero _ z0,
  have zc0 : z^d + c ≠ 0, {
    rw ←complex.abs.ne_zero_iff, apply ne_of_gt,
    calc abs (z^d + c) ≥ abs (z^d) - abs c : by bound
    ... = abs z^d - abs c : by rw complex.abs.map_pow
    ... ≥ abs z^2 - abs z : by bound [pow_le_pow _ two_le_d]
    ... = abs z * (abs z - 1) : by ring
    ... ≥ 3 * (3 - 1) : by bound
    ... > 0 : by norm_num,
  },
  have cz : abs (c/z^d) ≤ 1/abs z^(d-1), {
    have d1 : d-1+1 = d := nat.sub_add_cancel d_ge_one, nth_rewrite 0 ←d1,
    simp only [map_div₀, complex.abs.map_pow, pow_succ, complex.abs.map_mul, div_mul_eq_div_div],
    bound,
  },
  have czs : abs (c/z^d) ≤ 1/2, {
    apply trans cz,
    calc 1 / abs z^(d-1) ≤ 1/3 : by bound
    ... ≤ 1/2 : by norm_num,
  },
  have l0s : 1 ≤ log (abs z), { rw real.le_log_iff_exp_le z0', exact trans (le_of_lt real.exp_one_lt_3) z3 },
  have l0 : 0 < log (abs z) := lt_of_lt_of_le (by norm_num) l0s,
  have l1 : 0 < ↑d * log (abs z) := by bound,
  have l2 : |log (abs (1 + c/z^d))| ≤ 2/abs z^(d-1), {
    nth_rewrite 0 ←complex.log_re, refine trans (complex.abs_re_le_abs _) (trans (log1p_small czs) _),
    calc 2 * abs (c/z^d) ≤ 2 * (1 / abs z^(d-1)) : by bound
    ... = 2 / abs z^(d-1) : by rw [←mul_div_assoc, mul_one],
  },
  have l3 : 0 < ↑d * log (abs z) + log (abs (1 + c/z^d)), {
    suffices h : -log (abs (1 + c/z^d)) < ↑d * log (abs z), linarith,
    apply lt_of_le_of_lt (neg_le_neg_iff.mpr (abs_le.mp l2).1), simp only [neg_neg],
    transitivity (1:ℝ),
    calc 2/abs z^(d-1) ≤ 2/3 : by bound
    ... < 1 : by norm_num,
    calc ↑d * log (abs z) ≥ 2 * 1 : by bound 
    ... > 1 : by norm_num,
  },
  rw [log_abs_add (z^d) c zd0 zc0, complex.abs.map_pow, real.log_pow, log_add _ _ l1 l3,
    real.log_mul (nat.cast_ne_zero.mpr d_ne_zero) (ne_of_gt l0)], swap, apply_instance,
  generalize hw : log (1 + log (abs (1 + c/z^d)) / (d * log (abs z))) = w,
  ring_nf, rw ←hw, clear hw w,
  have inner : |log (abs (1 + c/z^d)) / (d * log (abs z))| ≤ 2/d/abs z^(d-1), {
    simp only [abs_div, abs_of_pos l1, div_le_iff l1], apply trans l2,
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ←mul_assoc, mul_comm _ ↑d, mul_comm _ (↑d)⁻¹,
      ←mul_assoc, ←mul_assoc, mul_inv_cancel d0, one_mul],
    exact le_mul_of_one_le_right (by bound) l0s,
  },
  have weak : 2/↑d/abs z^(d-1) ≤ 1/2, {
    calc 2/↑d/abs z^(d-1) ≤ 2/2/3 : by bound
    ... ≤ 1/2 : by norm_num,
  },
  apply trans (real.log1p_small (trans inner weak)),
  simp only [(by norm_num : (4:ℝ) = 2*2), mul_assoc (2:ℝ) _ _],
  refine mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2),
  simp only [←mul_assoc, ←mul_div_assoc, ←div_eq_mul_inv, div_right_comm _ _ ↑d, inner],
end
 
-- Absolute values of iterates grow roughly as z^d^n for large c,z
lemma iter_approx (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ) 
    : |log (log (abs (f' d c^[n] z))) - log (log (abs z)) - n * log d| ≤ 8 / (d * abs z ^ (d-1)) := begin
  have z3 : 3 ≤ abs z := trans c3 cz,
  have z0 : 0 < abs z := lt_of_lt_of_le (by bound) z3,
  have d0 : 0 < d := d_pos,
  have d1 : 1 < d := d_gt_one,
  -- Strengthen to get something we can prove by induction
  suffices h : |log (log (abs (f' d c^[n] z))) - log (log (abs z)) - n * log d| ≤ 8 * (1 - (1/2)^n) / (d * abs z^(d-1)), {
    apply trans h, rw div_le_div_right, swap, bound, apply mul_le_of_le_one_right, norm_num, bound,
  },
  induction n with n h, {
    simp only [function.iterate_zero_apply, sub_self, nat.cast_zero, zero_mul, abs_zero, pow_zero, zero_div, mul_zero],
  },
  -- Generalize away the iteration
  simp only [function.iterate_succ_apply', nat.cast_succ, right_distrib, one_mul, sub_add_eq_sub_sub _ _ (log d),
    ←sub_add_eq_sub_sub _ _ (↑n * log d)],
  generalize hw : f' d c^[n] z = w,
  generalize hb : log (log (abs z)) + n * log d = b,
  have rw : 2^n * abs z ≤ abs w, { transitivity 2^n * abs z, bound, rw ←hw, exact iter_large d c3 cz n },
  rw [←sub_add_eq_sub_sub, hw, hb] at h, clear hw hb,
  have cw : abs c ≤ abs w, { refine trans cz (trans _ rw), bound [le_mul_of_one_le_left, one_le_pow_of_one_le] },
  -- Do the main calculation
  have e : log (log (abs (w^d + c))) - b - log d =
      (log (log (abs (w^d + c))) - log (log (abs w)) - log d) + (log (log (abs w)) - b) := by abel,
  rw [f', e], refine trans (abs_add _ _) (trans (add_le_add (f_approx c3 cw) h) _), clear e h,
  rw [←div_mul_eq_div_div, ←le_sub_iff_add_le, ←sub_div, ←mul_sub, ←sub_add, sub_sub_cancel_left, neg_add_eq_sub,
    pow_succ, ←one_sub_mul, sub_half, ←mul_assoc, (by norm_num : (8:ℝ) * (1/2) = 4), div_pow, one_pow, ←mul_div_assoc,
    mul_one, ←div_mul_eq_div_div, ←mul_assoc, mul_comm _ ↑d, mul_assoc ↑d _ _],
  refine div_le_div_of_le_left (by norm_num) (by bound) _,
  refine mul_le_mul_of_nonneg_left _ (by bound),
  calc abs w^(d-1) ≥ (2^n * abs z)^(d-1) : by bound
  ... = (2^n)^(d-1) * abs z^(d-1) : by rw mul_pow
  ... ≥ 2^n * abs z^(d-1) : by bound [le_self_pow, one_le_pow_of_one_le],
end

-- One-sided non-log versions of iter_approx
lemma iter_bounds (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ) 
    : abs z ^ (↑d^n / exp (8 / (d * abs z ^ (d-1)))) ≤ abs (f' d c^[n] z) ∧
      abs (f' d c^[n] z) ≤ abs z ^ (↑d^n * exp (8 / (d * abs z ^ (d-1)))) := begin
  have z1 : 1 < abs z := lt_of_lt_of_le (by norm_num) (trans c3 cz),
  have z0 : 0 < abs z := trans (by norm_num) z1,
  have d0 : 0 < (d : ℝ) := nat.cast_pos.mpr d_pos,
  have f1 : 1 < abs (f' d c^[n] z) :=
    lt_of_lt_of_le (one_lt_mul (one_le_pow_of_one_le one_le_two _) z1) (iter_large d c3 cz n),
  have f0 : 0 < abs (f' d c^[n] z) := trans zero_lt_one f1,
  have l0 : 0 < log (abs (f' d c^[n] z)) := real.log_pos f1,
  rcases abs_le.mp (iter_approx d c3 cz n) with ⟨lo,hi⟩,
  simp only [sub_le_iff_le_add', le_sub_iff_add_le] at lo hi,
  simp only [neg_add_eq_sub, sub_add_eq_add_sub, real.log_le_iff_le_exp l0, real.le_log_iff_exp_le l0,
    real.log_le_iff_le_exp f0, real.le_log_iff_exp_le f0, real.exp_add, real.exp_sub, real.exp_log (real.log_pos z1),
    real.exp_mul, real.exp_log z0, mul_comm _ (log (abs z)), mul_div_assoc] at lo hi,
  rw [←real.exp_mul ↑n (log ↑d), mul_comm ↑n _, real.exp_mul (log ↑d) ↑n, real.exp_log d0, real.rpow_nat_cast] at lo hi,
  use [lo,hi],
end
 
-- s.bottcher c z ~ 1/z for large z
lemma bottcher_large_approx (d : ℕ) [fact (2 ≤ d)] (c : ℂ)
    : tendsto (λ z : ℂ, (super_f d).bottcher c z * z) at_inf (𝓝 1) := begin
  set s := super_f d,
  have e : ∀ᶠ z : ℂ in at_inf, s.bottcher c z * z = s.bottcher_near c z * z, {
    suffices e : ∀ᶠ z : ℂ in at_inf, s.bottcher c z = s.bottcher_near c z,
    exact e.mp (eventually_of_forall (λ z e, by rw e)),
    refine @filter.tendsto.eventually _ _ _ _ _ (λ z, s.bottcher c z = s.bottcher_near c z) coe_tendsto_inf _,
    apply s.bottcher_eq_bottcher_near,
  },
  rw filter.tendsto_congr' e, clear e,
  have m := bottcher_near_monic (s.super_near_c.s (mem_univ c)),
  simp only [has_deriv_at_iff_tendsto, sub_zero, bottcher_near_zero, smul_eq_mul, mul_one, metric.tendsto_nhds_nhds,
    real.dist_eq, complex.norm_eq_abs, complex.dist_eq, abs_mul, abs_of_nonneg (complex.abs.nonneg _), abs_inv] at m,
  simp only [metric.tendsto_nhds, at_inf_basis.eventually_iff, true_and, mem_set_of, complex.dist_eq,
    complex.norm_eq_abs],
  intros e ep, rcases m e ep with ⟨r,rp,h⟩, use 1/r, intros z zr,
  have az0 : abs z ≠ 0 := ne_of_gt (trans (one_div_pos.mpr rp) zr),
  have z0 : z ≠ 0 := complex.abs.ne_zero_iff.mp az0,
  specialize @h (z⁻¹) _, simp only [one_div, map_inv₀] at zr ⊢, exact inv_lt_of_inv_lt rp zr,
  simp only [map_inv₀, inv_inv, ←complex.abs.map_mul, sub_mul, inv_mul_cancel z0, mul_comm z _] at h,
  simp only [super.bottcher_near, ext_chart_at_inf, local_equiv.trans_apply, coe_local_equiv_symm_apply,
    equiv.to_local_equiv_apply, inv_equiv_apply, inv_inf, to_complex_zero, sub_zero, inv_coe z0, to_complex_coe],
  exact h,
end

-- s.potential c z ~ 1/abs z for large z
lemma potential_tendsto (d : ℕ) [fact (2 ≤ d)] (c : ℂ)
    : tendsto (λ z : ℂ, (super_f d).potential c z * abs z) at_inf (𝓝 1) := begin
  set s := super_f d,
  simp only [←s.abs_bottcher, ←complex.abs.map_mul, ←complex.abs.map_one],
  exact complex.continuous_abs.continuous_at.tendsto.comp (bottcher_large_approx d c),
end
 
-- The derivative of x → exp (-exp x), for use in approximating potential
lemma has_deriv_at_exp_neg_exp (x : ℝ) : has_deriv_at (λ x, exp (-exp x)) (-exp (x - exp x)) x := begin
  have h : has_deriv_at (λ x, exp (-exp x)) (exp (-exp x) * -exp x) x := has_deriv_at.exp (real.has_deriv_at_exp x).neg,
  simp only [mul_neg, ←real.exp_add, neg_add_eq_sub] at h, exact h,
end
lemma deriv_exp_neg_exp (x : ℝ) : deriv (λ x, exp (-exp x)) x = -exp (x - exp x) := (has_deriv_at_exp_neg_exp x).deriv

-- This is a weak bound, but it's all we use below
lemma deriv_exp_neg_exp_le (x : ℝ) : ‖deriv (λ x, exp (-exp x)) x‖ ≤ exp (-x) := begin
  rw deriv_exp_neg_exp,
  simp only [real.norm_eq_abs, abs_le], constructor, {
    rw [neg_le_neg_iff, real.exp_le_exp],
    suffices h : 2*x ≤ exp x, linarith,
    by_cases x1 : x ≤ 1,
    exact trans (by linarith) (real.add_one_le_exp _),
    exact trans (by nlinarith) (real.quadratic_le_exp_of_nonneg (by linarith)),
  }, {
    rw neg_le, refine le_of_lt (trans _ (real.exp_pos _)), rw neg_lt_zero, exact real.exp_pos _,
  },
end

-- potential is given by the expected limit
lemma tendsto_potential (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z)
    : tendsto (λ n, abs (f' d c^[n] z) ^ -((d^n:ℕ):ℝ)⁻¹) at_top (𝓝 ((super_f d).potential c z)) := begin
  set s := super_f d,
  have p0 : s.potential c z ≠ 0, { rw s.potential_ne_zero, exact coe_ne_inf },
  suffices h : tendsto (λ n, (abs (f' d c^[n] z) * s.potential c ↑(f' d c^[n] z)) ^ -((d^n:ℕ):ℝ)⁻¹) at_top (𝓝 1), {
    replace h := h.mul_const (s.potential c z),
    simp only [div_mul_cancel _ p0, one_mul, ←f_f'_iter, s.potential_eqn_iter,
      real.mul_rpow (complex.abs.nonneg _) (pow_nonneg s.potential_nonneg _),
      real.pow_nat_rpow_nat_inv s.potential_nonneg (pow_ne_zero _ d_ne_zero),
      real.rpow_neg (pow_nonneg s.potential_nonneg _), ←div_eq_mul_inv] at h,
    exact h,
  },
  simp only [←s.abs_bottcher, ←complex.abs.map_mul, mul_comm _ (s.bottcher _ _)],
  rw metric.tendsto_at_top, intros r rp,
  rcases metric.tendsto_at_top.mp ((bottcher_large_approx d c).comp (tendsto_iter_at_inf d c3 cz))
    (min (1/2) (r/4)) (by bound) with ⟨n,h⟩,
  use n, intros k nk, specialize h k nk,
  generalize hw : f' d c^[k] z = w, generalize hp : s.bottcher c w * w = p,
  simp only [hw, hp, function.comp, complex.dist_eq, real.dist_eq] at h ⊢,
  clear' hp w hw nk n p0 s cz c3 z c,
  generalize ha : abs p = a,
  generalize hb : ((d^k:ℕ):ℝ)⁻¹ = b,
  have a1 : |a-1| < min (1/2) (r/4), {
    rw ←ha, refine lt_of_le_of_lt _ h, rw ←complex.abs.map_one, apply complex.abs.abs_abv_sub_le_abv_sub,
  },
  have am : a ∈ ball (1:ℝ) (1/2), { simp only [mem_ball, real.dist_eq], exact (lt_min_iff.mp a1).1 },
  have b0 : 0 ≤ b, { rw ←hb, bound },
  have b1 : b ≤ 1, { rw ←hb, exact inv_le_one (nat.one_le_cast.mpr (one_le_pow_of_one_le d_ge_one _)) },
  have hd : ∀ x, x ∈ ball (1:ℝ) (1/2) → has_deriv_at (λ x, x^-b) (1 * (-b) * x^(-b-1) + 0 * x^-b * log x) x, {
    intros x m, apply has_deriv_at.rpow (has_deriv_at_id _) (has_deriv_at_const _ _),
    simp only [mem_ball, real.dist_eq, id] at m ⊢, linarith [abs_lt.mp m],
  },
  simp only [zero_mul, add_zero, one_mul] at hd,
  have bound : ∀ x, x ∈ ball (1:ℝ) (1/2) → ‖deriv (λ x, x^-b) x‖ ≤ 4, {
    intros x m,
    simp only [(hd x m).deriv, real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg b0],
    simp only [mem_ball, real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add] at m, norm_num at m,
    have x0 : 0 < x := by linarith,
    calc b * |x ^ (-b-1)| ≤ 1 * |x|^(-b-1) : by bound [real.abs_rpow_le_abs_rpow]
    ... = (x^(b+1))⁻¹ : by rw [←real.rpow_neg (le_of_lt x0), neg_add', one_mul, abs_of_pos x0]
    ... ≤ ((1/2)^(b+1))⁻¹ : by bound [m.1, real.rpow_le_rpow]
    ... = 2^(b+1) : by rw [one_div, real.inv_rpow zero_le_two, inv_inv]
    ... ≤ 2^(1+1:ℝ) : by bound [real.rpow_le_rpow_of_exponent_le]
    ... ≤ 4 : by norm_num,
  },
  have le := convex.norm_image_sub_le_of_norm_deriv_le (λ x m, (hd x m).differentiable_at) bound (convex_ball _ _)
    (mem_ball_self (by norm_num)) am,
  simp only [real.norm_eq_abs, real.one_rpow] at le,
  calc |a ^ -b - 1| ≤ 4 * |a-1| : le
  ... < 4 * (r/4) : by bound [(lt_min_iff.mp a1).2]
  ... = r : by ring,
end

-- For large c and z, s.potential = 1/abs z + o(1/abs z)
lemma potential_approx (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (c4 : 4 ≤ abs c) (cz : abs c ≤ abs z)
    : |(super_f d).potential c z - 1/abs z| ≤ 24 / (↑d * abs z ^ (d-1) * log (abs z)) := begin
  have d2 : 2 ≤ (d:ℝ) := trans (by norm_num) (nat.cast_le.mpr two_le_d),
  have z4 : 4 ≤ abs z := (trans c4 cz),
  have z0 : 0 < abs z := lt_of_lt_of_le (by norm_num) z4,
  have z1 : 1 < abs z := lt_of_lt_of_le (by norm_num) z4,
  have c3 : 3 ≤ abs c := trans (by norm_num) c4,
  have c0 : 0 < abs c := lt_of_lt_of_le (by norm_num) c4,
  have l2 : 0 < log (abs z) := real.log_pos (by linarith),
  set s := super_f d,
  generalize hb : 24 / (↑d * abs z ^ (d-1) * log (abs z)) = b,
  -- Swap out potential for an iterate approximate
  suffices h : ∀ᶠ n in at_top, |abs (f' d c^[n] z) ^ -((d^n:ℕ):ℝ)⁻¹ - 1/abs z| ≤ b, {
    apply le_of_forall_pos_lt_add, intros e ep,
    rcases (h.and (metric.tendsto_nhds.mp (tendsto_potential d c3 cz) e ep)).exists with ⟨n,h,t⟩,
    generalize hw : abs (f' d c^[n] z) ^ -((d^n:ℕ):ℝ)⁻¹ = w, rw hw at h t,
    rw [real.dist_eq, abs_sub_comm] at t, rw add_comm,
    calc |s.potential c z - 1/abs z|
        ≤ |s.potential c z - w| + |w - 1/abs z| : abs_sub_le _ _ _
    ... < e + _ : add_lt_add_of_lt_of_le t h,
  },
  -- iter_approx does the rest
  apply eventually_of_forall, intro n,
  generalize hi : ((d^n:ℕ):ℝ)⁻¹ = i,
  have dn0 : 0 < ((d^n:ℕ):ℝ) := nat.cast_pos.mpr (pow_pos d_pos n),
  have i0 : 0 < i, { rw ←hi, exact inv_pos.mpr dn0 },
  have f1 : 1 < abs (f' d c^[n] z) :=
    lt_of_lt_of_le (one_lt_mul (one_le_pow_of_one_le one_le_two _) z1) (iter_large d c3 cz n),
  have f0 : 0 < abs (f' d c^[n] z) := trans zero_lt_one f1,
  have l0 : 0 < log (abs (f' d c^[n] z)) := real.log_pos f1,
  have l1 : 0 < log (abs (f' d c^[n] z) ^ i), { rw real.log_rpow f0, bound },
  have f1 : 0 < abs (f' d c^[n] z) ^ i := real.rpow_pos_of_pos f0 i,
  have h := iter_approx d c3 cz n,
  rw [sub_sub, add_comm, ←sub_sub, ←real.log_pow _ n, ←nat.cast_pow, ←real.log_div (ne_of_gt l0) (ne_of_gt dn0),
    div_eq_mul_inv, mul_comm, ←real.log_rpow f0, hi] at h,
  generalize hr : 8 / (↑d * abs z^(d-1)) = r, rw hr at h,
  have r0 : 0 < r, { rw ←hr, bound },
  have r1 : r ≤ 1, {
    rw [←hr, div_le_one], swap, bound,
    calc ↑d * abs z^(d-1) ≥ 2 * 4^(d-1) : by bound
    ... ≥ 2 * 4 : by bound [le_self_pow _ (ne_of_gt (d_minus_one_pos : 0 < d-1))]
    ... = 8 : by norm_num,
  },
  set t := closed_ball (log (log (abs z))) r,
  have yt : log (log (abs (f' d c^[n] z) ^ i)) ∈ t := by simp only [mem_closed_ball, real.dist_eq, h],
  have bound : ∀ x, x ∈ t → ‖deriv (λ x, exp (-exp x)) x‖ ≤ 3 / log (abs z), {
    intros x m, simp only [mem_closed_ball, real.dist_eq] at m,
    replace m : -x ≤ 1 - log (log (abs z)) := by linarith [(abs_le.mp m).1],
    refine trans (deriv_exp_neg_exp_le _) (trans (real.exp_le_exp.mpr m) _),
    simp only [real.exp_sub, real.exp_log l2], bound [real.exp_one_lt_3, l2],
  },
  have m := convex.norm_image_sub_le_of_norm_deriv_le (λ x _, (has_deriv_at_exp_neg_exp x).differentiable_at)
    bound (convex_closed_ball _ _) (mem_closed_ball_self (le_of_lt r0)) yt,
  simp only [real.norm_eq_abs] at m,
  replace m := trans m (mul_le_mul_of_nonneg_left h (by bound)),
  simp only [real.exp_log l1, real.exp_log l2, real.exp_neg, real.exp_log z0, real.exp_log f1,
    ←real.rpow_neg (le_of_lt f0)] at m,
  rw one_div, refine trans m (le_of_eq _),
  rw [←hr, ←hb], field_simp [ne_of_gt l2, ne_of_gt z0], ring_nf,
end

-- For large c, large z's are postcritical
lemma large_post {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z) : postcritical (super_f d) c z := begin
  have d0 : 0 < d := d_pos,
  have d2 : 2 ≤ (d:ℝ) := trans (by norm_num) (nat.cast_le.mpr two_le_d),
  have c10 : 10 ≤ abs c := trans (by norm_num) (trans (real.add_one_le_exp _) cb),
  have c4 : 4 ≤ abs c := trans (by norm_num) c10,
  have c0 : 0 < abs c := by linarith,
  have lcb : 48 ≤ log (abs c) := (real.le_log_iff_exp_le c0).mpr cb,
  have lc : 0 < log (abs c) := lt_of_lt_of_le (by norm_num) lcb,
  have z0 : 0 < abs z := lt_of_lt_of_le (by norm_num) (trans c10 cz),
  have m : c ∉ multibrot d := multibrot_two_lt (lt_of_lt_of_le (by norm_num) c4),
  simp only [postcritical, multibrot_p m],
  set s := super_f d,
  rw [←real.pow_nat_rpow_nat_inv s.potential_nonneg (ne_of_gt d0),
    ←real.pow_nat_rpow_nat_inv (s.potential_nonneg : 0 ≤ s.potential c 0) (ne_of_gt d0)],
  simp only [←s.potential_eqn], refine real.rpow_lt_rpow s.potential_nonneg _ (by bound),
  generalize hw : f' d c z = w,
  have e : f d c z = w := by rw [f, lift_coe', hw],
  simp only [f_0, e], clear e,
  have cw2 : 4 * abs c ≤ abs w, {
    simp only [←hw,f'],
    have z1 : 1 ≤ abs z := by linarith,
    calc abs (z^d + c) ≥ abs (z^d) - abs c : by bound
    ... = abs z^d - abs c : by rw complex.abs.map_pow
    ... ≥ abs z^2 - abs c : by bound [pow_le_pow z1 two_le_d]
    ... ≥ abs c^2 - abs c : by bound
    ... = abs c * abs c - abs c : by rw pow_two
    ... ≥ 5 * abs c - abs c : by bound [(by linarith : 5 ≤ abs c)]
    ... = 4 * abs c : by ring,
  },
  have cw : abs c ≤ abs w := trans (by linarith) cw2,
  have lcw : log (abs c) ≤ log (abs w) := (real.log_le_log c0 (lt_of_lt_of_le c0 cw)).mpr cw,
  have lw : 0 < log (abs w) := lt_of_lt_of_le lc lcw,
  have pw := sub_le_iff_le_add.mp (abs_le.mp (potential_approx d c4 cw)).2,
  have pc := le_sub_iff_add_le.mp (abs_le.mp (potential_approx d c4 (le_refl _))).1,
  refine lt_of_le_of_lt pw (lt_of_lt_of_le _ pc),
  generalize hkc : 24 / (↑d * abs c^(d-1) * log (abs c)) = kc,
  generalize hkw : 24 / (↑d * abs w^(d-1) * log (abs w)) = kw,
  rw [neg_add_eq_sub, lt_sub_iff_add_lt, add_comm _ kc, ←add_assoc],
  have kcw : kw ≤ kc, { rw [←hkc,←hkw], bound },
  have kcc : kc ≤ 1 / (4 * abs c), {
    rw ←hkc,
    have c1 : 1 ≤ abs c := trans (by norm_num) cb,
    have lc1 : 1 ≤ log (abs c) := trans (by norm_num) lcb,
    calc 24 / (↑d * abs c^(d-1) * log (abs c)) ≤ 24 / (2 * abs c * 48) : by bound [le_self_pow, (d_gt_one : 1 < d)]
    ... = 24 / (48 * 2) / abs c : by rw [mul_comm _ (48:ℝ), ←mul_assoc, ←div_div]
    ... = 1 / 4 / abs c : by norm_num
    ... = 1 / (4 * abs c) : by rw div_div,
  },
  calc kc + kw + 1/abs w ≤ kc + kc + 1/(4*abs c) : by bound
  ... = 2*kc + 1/(4*abs c) : by ring
  ... ≤ 2*(1/(4*abs c)) + 1/(4*abs c) : by bound
  ... = (2/4)/abs c + (1/4)/(abs c) : by field_simp
  ... = (3/4)/abs c : by ring
  ... < 1/abs c : (div_lt_div_right c0).mpr (by norm_num),
end

-- s.bottcher = bottcher_near for large c,z
lemma bottcher_eq_bottcher_near_z {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z)
    : (super_f d).bottcher c z = bottcher_near (fl (f d) ∞ c) d z⁻¹ := begin
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (trans (real.add_one_le_exp _) cb),
  have c0 : 0 < abs c := trans (by norm_num) c16,
  have z0 : 0 < abs z := lt_of_lt_of_le c0 cz,
  set s := super_f d,
  set t := closed_ball (0:ℂ) (abs c)⁻¹,
  suffices e : eq_on (λ z : ℂ, s.bottcher c (z:𝕊)⁻¹) (bottcher_near (fl (f d) ∞ c) d) t, {
    have z0' : z ≠ 0 := complex.abs.ne_zero_iff.mp (ne_of_gt z0),
    convert @e z⁻¹ _, rw [inv_coe (inv_ne_zero z0'), inv_inv],
    simp only [mem_closed_ball, complex.dist_eq, sub_zero, map_inv₀, inv_le_inv z0 c0, cz],
  },
  have a0 : holomorphic_on I I (λ z : ℂ, s.bottcher c (z:𝕊)⁻¹) t, {
    intros z m, refine (s.bottcher_holomorphic_on _ _).in2.comp (holomorphic_inv.comp holomorphic_coe _),
    simp only [mem_closed_ball, complex.dist_eq, sub_zero] at m,
    by_cases z0 : z = 0, simp only [z0, coe_zero, inv_zero'], exact s.post_a c,
    rw inv_coe z0, apply large_post cb,
    rwa [map_inv₀, le_inv c0], exact complex.abs.pos z0,
  },
  have a1 : holomorphic_on I I (bottcher_near (fl (f d) ∞ c) d) t, {
    intros z m, apply analytic_at.holomorphic_at,
    apply bottcher_near_analytic_z (super_near_f d c),
    simp only [mem_set_of, mem_closed_ball, complex.dist_eq, sub_zero] at ⊢ m,
    refine lt_of_le_of_lt m _,
    refine inv_lt_inv_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _,
    exact max_lt c16 (half_lt_self (trans (by norm_num) c16)),
  },
  refine (a0.eq_of_locally_eq a1 (convex_closed_ball _ _).is_preconnected _).self_set,
  use [0, mem_closed_ball_self (by bound)],
  have e : ∀ᶠ z in 𝓝 0, bottcher_near (fl (f d) ∞ c) d z = s.bottcher_near c (z:𝕊)⁻¹ :=
    by simp only [super.bottcher_near, ext_chart_at_inf_apply, inv_inv, to_complex_coe, inv_inf, to_complex_zero,
      sub_zero, super.fl, eq_self_iff_true, filter.eventually_true],
  refine filter.eventually_eq.trans _ (filter.eventually_eq.symm e),
  have i : tendsto (λ z : ℂ, (z:𝕊)⁻¹) (𝓝 0) (𝓝 ∞), {
    have h : continuous_at (λ z : ℂ, (z:𝕊)⁻¹) 0 := (riemann_sphere.continuous_inv.comp continuous_coe).continuous_at,
    simp only [continuous_at, coe_zero, inv_zero'] at h, exact h,
  },
  exact i.eventually (s.bottcher_eq_bottcher_near c),
end

-- bottcher' = bottcher_near for large c
lemma bottcher_eq_bottcher_near {c : ℂ} (cb : exp 48 ≤ abs c)
    : bottcher' d c = bottcher_near (fl (f d) ∞ c) d c⁻¹ := bottcher_eq_bottcher_near_z cb (le_refl _)

-- z⁻¹ is in the super_near_c region for large c,z
lemma inv_mem_t {c z : ℂ} (c16 : 16 < abs c) (cz : abs c ≤ abs z)
    : z⁻¹ ∈ {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹} := begin
  simp only [mem_set_of, map_inv₀],
  refine inv_lt_inv_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _,
  exact lt_of_lt_of_le (max_lt c16 (half_lt_self (trans (by norm_num) c16))) cz,
end

-- Terms in the bottcher_near product are close to 1
lemma term_approx (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ)
    : abs (term (fl (f d) ∞ c) d n z⁻¹ - 1) ≤ 2 * (1/2)^n * (abs z)⁻¹ := begin
  set s := super_f d,
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (trans (real.add_one_le_exp _) cb),
  have d2 : 2 ≤ (d:ℝ) := trans (by norm_num) (nat.cast_le.mpr two_le_d),
  have z0 : abs z ≠ 0 := ne_of_gt (lt_of_lt_of_le (trans (by norm_num) c16) cz),
  have i8 : (abs z)⁻¹ ≤ 1/8, {
    rw one_div, apply inv_le_inv_of_le, norm_num, exact trans (by norm_num) (trans (le_of_lt c16) cz),
  },
  have i1 : (abs z)⁻¹ ≤ 1 := trans i8 (by norm_num),
  simp only [term],
  have wc := iterates_converge (super_near_f d c) n (inv_mem_t c16 cz),
  generalize hw : fl (f d) ∞ c^[n] z⁻¹ = w, rw hw at wc,
  replace wc : abs w ≤ (abs z)⁻¹, {
    rw map_inv₀ at wc,
    exact trans wc (mul_le_of_le_one_left (inv_nonneg.mpr (complex.abs.nonneg _)) (by bound)),
  },
  have cw : abs (c * w^d) ≤ (abs z)⁻¹, {
    simp only [complex.abs.map_mul, complex.abs.map_pow],
    calc abs c * abs w^d ≤ abs z * (abs z)⁻¹^d : by bound
    ... ≤ abs z * (abs z)⁻¹^2 : by bound [pow_le_pow_of_le_one, (two_le_d : 2 ≤ d)]
    ... = (abs z)⁻¹ : by { rw pow_two, field_simp [z0] },
  },
  have cw2 : abs (c * w^d) ≤ 1/2 := trans cw (trans i8 (by norm_num)),
  simp only [gl_f, gl], rw [complex.inv_cpow, ←complex.cpow_neg], swap, {
    refine ne_of_lt (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt _ (half_lt_self real.pi_pos))),
    rw [complex.abs_arg_le_pi_div_two_iff, complex.add_re, complex.one_re],
    calc 1 + (c * w^d).re ≥ 1 + -|(c * w^d).re| : by bound [neg_abs_le_self]
    ... = 1 - |(c * w^d).re| : by ring
    ... ≥ 1 - abs (c * w^d) : by bound [complex.abs_re_le_abs]
    ... ≥ 1 - 1/2 : by bound
    ... ≥ 0 : by norm_num,
  }, {
    have dn : abs (-(1 / (d:ℂ)^(n+1))) ≤ (1/2)^(n+1), {
      simp only [one_div, complex.abs.map_neg, map_inv₀, ←nat.cast_pow, complex.abs_of_nat, inv_pow], bound,
    },
    have d1 : abs (-(1 / (d:ℂ)^(n+1))) ≤ 1 := trans dn (by bound),
    refine trans (pow_small _ d1) _,
    ring_nf, rw mul_comm, exact cw2,
    rw add_sub_cancel',
    calc 4 * abs (c * w^d) * abs (-(1 / (d:ℂ)^(n+1))) ≤ 4 * (abs z)⁻¹ * (1/2)^(n+1) : by bound
    ... ≤ 2 * (1/2)^n * (abs z)⁻¹ : by { rw pow_succ, ring_nf },
  },
end

-- Linear approximation for s.bottcher c z
lemma bottcher_approx_z (d : ℕ) [fact (2 ≤ d)] {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z)
    : abs ((super_f d).bottcher c z - z⁻¹) ≤ 16 * (abs z)⁻¹^2 := begin
  set s := super_f d,
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (trans (real.add_one_le_exp _) cb),
  have z0 : abs z ≠ 0 := ne_of_gt (lt_of_lt_of_le (trans (by norm_num) c16) cz),
  have i8 : (abs z)⁻¹ ≤ 1/8, {
    rw one_div, apply inv_le_inv_of_le, norm_num, exact trans (by norm_num) (trans (le_of_lt c16) cz),
  },
  nth_rewrite 0 ←mul_one z⁻¹,
  simp only [bottcher_eq_bottcher_near_z cb cz, bottcher_near, complex.abs.map_mul, ←mul_sub,
    pow_two, ←mul_assoc, map_inv₀, mul_comm (abs z)⁻¹],
  refine mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (complex.abs.nonneg _)),
  rcases term_prod_exists (super_near_f d c) _ (inv_mem_t c16 cz) with ⟨p,h⟩,
  rw h.tprod_eq, simp only [has_prod] at h,
  apply le_of_tendsto' (filter.tendsto.comp complex.continuous_abs.continuous_at (h.sub_const 1)),
  clear h, intro A, simp only [function.comp],
  rw [(by norm_num : (16:ℝ) = 4 * 4), mul_assoc],
  refine dist_prod_one_le_abs_sum _ (by linarith),
  refine trans (finset.sum_le_sum (λ n _, term_approx d cb cz n)) _,
  simp only [mul_comm _ _⁻¹, ←mul_assoc, ←finset.mul_sum],
  calc (abs z)⁻¹ * 2 * A.sum (pow (1/2)) ≤ (abs z)⁻¹ * 2 * (1-1/2)⁻¹ : by bound [partial_geometric_bound]
  ... = (abs z)⁻¹ * 4 : by ring,
end

-- Linear approximation for bottcher d c
lemma bottcher_approx (d : ℕ) [fact (2 ≤ d)] {c : ℂ} (cb : exp 48 ≤ abs c)
    : abs (bottcher' d c - c⁻¹) ≤ 16 * (abs c)⁻¹^2 := bottcher_approx_z d cb (le_refl _)

-- bottcher is monic at ∞
lemma bottcher_has_deriv_at_one : has_deriv_at (λ z : ℂ, bottcher d (↑z)⁻¹) 1 0 := begin
  simp only [has_deriv_at, has_deriv_at_filter, bottcher, has_fderiv_at_filter, coe_zero, inv_zero',
    fill_inf, sub_zero, continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply, smul_eq_mul,
    mul_one, asymptotics.is_o_iff],
  intros k k0, rw metric.eventually_nhds_iff,
  refine ⟨min (exp 48)⁻¹ (k/16), by bound, _⟩, intros z le,
  simp only [complex.dist_eq, sub_zero, lt_min_iff] at le, simp only [complex.norm_eq_abs],
  by_cases z0 : z = 0, simp only [z0, coe_zero, inv_zero', fill_inf, sub_zero, complex.abs.map_zero, mul_zero],
  simp only [inv_coe z0, fill_coe],
  have b : abs (bottcher' d z⁻¹ - z⁻¹⁻¹) ≤ 16 * (abs z⁻¹)⁻¹^2 := bottcher_approx d _, {
    simp only [inv_inv] at b, apply trans b,
    simp only [map_inv₀, inv_inv, pow_two, ←mul_assoc],
    refine mul_le_mul_of_nonneg_right _ (complex.abs.nonneg _),
    calc 16 * abs z ≤ 16 * (k / 16) : by bound [le.2]
    ... = k : by ring,
  }, {
    rw [map_inv₀, le_inv (real.exp_pos _) (complex.abs.pos z0)], exact le_of_lt le.1,
  },
end

-- bottcher is nonsingular at ∞
lemma bottcher_mfderiv_inf_ne_zero : mfderiv I I (bottcher d) ∞ ≠ 0 := begin
  simp only [mfderiv, (bottcher_holomorphic d _ multibrot_ext_inf).mdifferentiable_at, if_pos, written_in_ext_chart_at,
    bottcher_inf, ext_chart_at_inf, ext_chart_at_eq_refl, function.comp, local_equiv.refl_coe, id,
    local_equiv.trans_apply, equiv.to_local_equiv_apply, inv_equiv_apply, inv_inf, coe_local_equiv_symm_apply,
    to_complex_zero, local_equiv.coe_trans_symm, local_equiv.symm_symm, coe_local_equiv_apply,
    equiv.to_local_equiv_symm_apply, inv_equiv_symm, model_with_corners.boundaryless.range_eq_univ,
    fderiv_within_univ],
  rw bottcher_has_deriv_at_one.has_fderiv_at.fderiv,
  rw [ne.def, continuous_linear_map.ext_iff, not_forall], use 1,
  simp only [continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply, algebra.id.smul_eq_mul, mul_one,
    continuous_linear_map.zero_apply, one_ne_zero, not_false_iff],
end
 
-- bottcher is injective
lemma bottcher_inj : inj_on (bottcher d) (multibrot_ext d) := begin
  -- We operate by induction on potential down to 0, expressed using closed sets of pairs.  Preliminaries first:
  by_contradiction bad, simp only [inj_on, not_forall, ←ne.def] at bad,
  rcases bad with ⟨x,xm,y,ym,bxy,xy⟩,
  generalize hb : potential d x = b,
  have b1 : b < 1 := by rwa [←hb, potential_lt_one],
  set u := {c | potential d c ≤ b},
  set t0 := u ×ˢ u,
  set t1 := {q : 𝕊 × 𝕊 | bottcher d q.1 = bottcher d q.2 ∧ q ∈ t0},
  set t2  := {q : 𝕊 × 𝕊 | q.1 ≠ q.2 ∧ q ∈ t1},
  have t2ne : t2.nonempty, {
    refine ⟨⟨x,y⟩,xy,bxy,_,_⟩, simp only [mem_set_of, ←hb], simp only [mem_set_of, ←hb, ←abs_bottcher, bxy],
  },
  clear' x xm y ym bxy xy hb,
  have ue : u ⊆ multibrot_ext d, { intros c m, rw ←potential_lt_one, exact lt_of_le_of_lt m b1 },
  have t01 : t1 ⊆ t0 := inter_subset_right _ _,
  have t12 : t2 ⊆ t1 := inter_subset_right _ _,
  have uc : is_closed u := is_closed_le potential_continuous continuous_const,
  have t0c : is_closed t0 := uc.prod uc,
  have t1c : is_closed t1, {
    rw is_closed_iff_frequently, rintros ⟨x,y⟩ f,
    have m0 : (x,y) ∈ t0 := filter.frequently.mem_of_closed (f.mp (eventually_of_forall (λ _ m, t01 m))) t0c,
    refine ⟨tendsto_nhds_unique_of_frequently_eq _ _ (f.mp (eventually_of_forall (λ _ m, m.1))), m0⟩,
    exact (bottcher_holomorphic d _ (ue m0.1)).continuous_at.comp continuous_at_fst,
    exact (bottcher_holomorphic d _ (ue m0.2)).continuous_at.comp continuous_at_snd,
  },
  have t12' : closure t2 ⊆ t1, { rw ←t1c.closure_eq, exact closure_mono t12 }, 
  have t2c' : is_compact (closure t2) := is_closed_closure.is_compact,
  have t2ne' : (closure t2).nonempty := t2ne.closure,
  -- Find the smallest potential which (almost) violates injectivity, and a pair (x,y) which realizes it
  have pc : continuous (λ q : 𝕊 × 𝕊, potential d q.1) := potential_continuous.comp continuous_fst,
  rcases pc.continuous_on.compact_min t2c' t2ne' with ⟨⟨x,y⟩,m2,min⟩,
  simp only [is_min_on_iff] at min,
  generalize xp : potential d x = p, rw xp at min,
  have m1 := t12' m2,
  have pb : p ≤ b, { rw ←xp, exact m1.2.1 },
  have xm : x ∈ multibrot_ext d := ue m1.2.1,
  have ym : y ∈ multibrot_ext d := ue m1.2.2,
  have yp : potential d y = p := by rw [←abs_bottcher, ←m1.1, abs_bottcher, xp],
  have p0i : p = 0 → x = ∞ ∧ y = ∞, { intro p0, rw [p0, potential_eq_zero] at xp yp, use [xp, yp], },
   -- Split into three cases to find a contradiction
  by_cases xy : x ≠ y, {
    -- Case 1: If x ≠ y, we can move a bit downwards in potential
    have p0 : p ≠ 0, { contrapose xy, simp only [not_not] at xy ⊢, rcases p0i xy with ⟨xi,yi⟩, rw [xi,yi] },
    have f : ∃ᶠ q : ℂ × ℂ in filter.map (λ q : 𝕊 × 𝕊, (bottcher d q.1, bottcher d q.2)) (𝓝 (x,y)),
        q.1 = q.2 ∧ abs q.1 < p, {
      rw [nhds_prod_eq, ←filter.prod_map_map_eq, ←(bottcher_nontrivial xm).nhds_eq_map_nhds,
        ←(bottcher_nontrivial ym).nhds_eq_map_nhds, m1.1, ←nhds_prod_eq],
      apply (continuous_id.prod continuous_id).continuous_at.frequently,
      simp only [eq_self_iff_true, true_and, ←yp, ←abs_bottcher], apply frequently_smaller,
      rw [←complex.abs.ne_zero_iff, abs_bottcher, yp], exact p0,
    },
    simp only [filter.frequently_map] at f,
    rcases (f.and_eventually (ne.eventually_ne xy)).exists with ⟨⟨v,w⟩,⟨bvw,pv⟩,vw⟩,
    simp only [not_lt, abs_bottcher] at vw bvw pv ⊢,
    have pw : potential d w < p := by rwa [←abs_bottcher, ←bvw, abs_bottcher],
    have m : (v,w) ∈ t2 := ⟨vw, bvw, trans (le_of_lt pv) pb, trans (le_of_lt pw) pb⟩,
    contrapose pv, simp only [not_lt], exact min ⟨v,w⟩ (subset_closure m),
  },
  -- x = y, so we're at a singular point
  simp only [not_not] at xy, rw ←xy at m1 m2 p0i, clear xy ym yp y,
  have db : mfderiv I I (bottcher d) x = 0, {
    contrapose m2, simp only [mem_closure_iff_frequently, filter.not_frequently],
    refine ((bottcher_holomorphic d _ xm).local_inj m2).mp (eventually_of_forall _),
    rintros ⟨x,y⟩ inj ⟨xy,e,h⟩, simp only at xy e inj, exact xy (inj e),
  },
  by_cases p0 : p ≠ 0, {
    -- Case 2: At a singular point we're not locally injective, so we can find a smaller potential value
    rcases not_local_inj_of_mfderiv_zero (bottcher_holomorphic d _ xm) db with ⟨r,ra,rx,e⟩,
    simp only [eventually_nhds_within_iff, mem_compl_singleton_iff] at e,
    rw [←xp, ←abs_bottcher, complex.abs.ne_zero_iff] at p0,
    have h := frequently_smaller p0,
    rw [(bottcher_nontrivial xm).nhds_eq_map_nhds, filter.frequently_map] at h,
    have m : ∃ᶠ z in 𝓝 x, potential d z < p ∧ (z, r z) ∈ t2, {
      refine h.mp (e.mp (eventually_of_forall (λ z e lt, _))),
      have zx : z ≠ x, { contrapose lt, simp only [not_not, not_lt] at lt ⊢, simp only [lt] },
      rw [abs_bottcher, abs_bottcher, xp] at lt,
      rcases e zx with ⟨rz,e⟩,
      refine ⟨lt, rz.symm, e.symm, trans (le_of_lt lt) pb, _⟩,
      rw [←abs_bottcher, ←e, abs_bottcher] at lt, exact trans (le_of_lt lt) pb,
    },
    rcases m.exists with ⟨y,yp,m⟩,
    linarith [min _ (subset_closure m)],
  }, {
    -- Case 1: x = ∞, which we know is nonsingular
    simp only [not_not] at p0, rw (p0i p0).1 at db,
    exact bottcher_mfderiv_inf_ne_zero db,
  },
end

-- The inverse to bottcher d
def ray_exists (d : ℕ) [fact (2 ≤ d)] :=
  global_complex_inverse_fun_open'' (bottcher_holomorphic d) bottcher_inj is_open_multibrot_ext
def ray (d : ℕ) [fact (2 ≤ d)] : ℂ → 𝕊 := classical.some (ray_exists d)
lemma ray_holomorphic (d : ℕ) [fact (2 ≤ d)] : holomorphic_on I I (ray d) (ball 0 1) := begin
  rw ←bottcher_surj d, exact (classical.some_spec (ray_exists d)).1,
end
lemma ray_bottcher {c : 𝕊} (m : c ∈ multibrot_ext d) : ray d (bottcher d c) = c :=
  (classical.some_spec (ray_exists d)).2 _ m
lemma bottcher_ray {z : ℂ} (m : z ∈ ball (0:ℂ) 1) : bottcher d (ray d z) = z := begin
  rw ←bottcher_surj d at m, rcases m with ⟨c,m,cz⟩,
  nth_rewrite 0 ←cz, rw ray_bottcher m, exact cz,
end
lemma ray_surj (d : ℕ) [fact (2 ≤ d)] : ray d '' ball 0 1 = multibrot_ext d := begin
  rw ←bottcher_surj d, apply set.ext, intros c, simp only [←image_comp, mem_image], constructor, {
    rintros ⟨e,m,ec⟩, simp only [function.comp, ray_bottcher m] at ec, rwa ←ec, 
  }, {
    intros m, use [c, m, ray_bottcher m],
  },
end

-- bottcher d is a local homeomorphism from multibrot_ext d to ball 0 1
def bottcher_homeomorph (d : ℕ) [fact (2 ≤ d)] : local_homeomorph 𝕊 ℂ := {
  to_fun := bottcher d,
  inv_fun := ray d,
  source := multibrot_ext d,
  target := ball 0 1,
  map_source' := begin intros c m, simp only [←bottcher_surj d], exact mem_image_of_mem _ m end,
  map_target' := begin intros z m, simp only [←ray_surj d], exact mem_image_of_mem _ m end,
  left_inv' := λ c m, ray_bottcher m,
  right_inv' := λ z m, bottcher_ray m,
  open_source := is_open_multibrot_ext,
  open_target := is_open_ball,
  continuous_to_fun := (bottcher_holomorphic d).continuous_on,
  continuous_inv_fun := (ray_holomorphic d).continuous_on,
}