-- Bottcher map near a superattracting fixpoint

import data.complex.basic
import data.complex.exponential
import analysis.complex.removable_singularity
import analysis.special_functions.complex.log
import tactic.monotonicity
import topology.basic

import analytic
import hartogs
import osgood
import pow
import products
import zeros

open complex (exp log abs cpow)
open filter (tendsto at_top)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball ball_mem_nhds mem_ball_self nonempty_ball)
open nat (iterate)
open set (maps_to univ)
open_locale nnreal topology
noncomputable theory

section bottcher

-- All information for a monic superattracting fixed point at the origin
variables {f : ℂ → ℂ}
variables {d : ℕ}
variables {z : ℂ}
variables {t : set ℂ}

-- f has a monic, superattracting fixed point of order d at the origin.
-- Simplified version of super_near with no smallest requirements
structure super_at (f : ℂ → ℂ) (d : ℕ) : Prop :=
  (d2 : 2 ≤ d)
  (fa0 : analytic_at ℂ f 0)
  (fd : order_at f 0 = d)
  (fc : leading_coeff f 0 = 1)

-- f has a monic, superattracting fixed point of order d at the origin.
-- We impose some smallness requirements to make bounds easier later.
structure super_near (f : ℂ → ℂ) (d : ℕ) (t : set ℂ) extends super_at f d : Prop :=
  (o : is_open t)
  (t0 : (0 : ℂ) ∈ t)
  (t2 : ∀ {z}, z ∈ t → abs z ≤ 1/2)
  (fa : analytic_on ℂ f t)
  (ft : maps_to f t t)
  (gs' : ∀ {z : ℂ}, z ≠ 0 → z ∈ t → abs (f z / z^d - 1) ≤ 1/4)

-- Facts about d
lemma super_at.dp (s : super_at f d) : d > 0 := lt_of_lt_of_le two_pos s.d2
lemma super_at.drp (s : super_at f d) : (d : ℝ) > 0 := nat.cast_pos.mpr s.dp
lemma super_at.drz (s : super_at f d) : (d : ℝ) ≠ 0 := ne_of_gt s.drp
lemma super_at.dz (s : super_at f d) : (d : ℂ) ≠ 0 := nat.cast_ne_zero.mpr (ne_of_gt s.dp)
lemma super_at.dr2 (s : super_at f d) : (d : ℝ) ≥ 2 := trans (nat.cast_le.mpr s.d2) (by norm_num)

-- f z = z^d * g z
def g (f : ℂ → ℂ) (d : ℕ) : ℂ → ℂ := λ z, if z = 0 then 1 else f z / z^d

-- g 0 = 1
lemma g0 {f : ℂ → ℂ} {d : ℕ} : g f d 0 = 1 := by simp only [g, eq_self_iff_true, if_true]

-- Asymptotic bound on f
lemma super_at.approx (s : super_at f d) : (λ z, f z - z^d) =o[𝓝 0] (λ z, z^d) := begin
  have a := s.fa0.leading_approx,
  simp only [s.fd, s.fc, sub_zero, pi.one_apply, algebra.id.smul_eq_mul, mul_one] at a,
  exact a,
end

-- f 0 = 0
lemma super_at.f0 (s : super_at f d) : f 0 = 0 := begin
  have p : order_at f 0 > 0 := by simp [s.fd, s.dp],
  exact s.fa0.zero_of_order_pos p,
end

-- f = z^d g
lemma super_at.fg (s : super_at f d) (z : ℂ) : f z = z^d * g f d z := begin
  by_cases z0 : z = 0, {
    simp only [z0, zero_pow s.dp, s.f0, zero_mul],
  }, {
    simp only [g, z0, if_false], field_simp [z0], rw mul_comm,
  },
end

-- g is analytic where f is
lemma super_at.ga_of_fa (s : super_at f d) {c : ℂ} (fa : analytic_at ℂ f c) : analytic_at ℂ (g f d) c := begin
  rcases fa.ball with ⟨r,rp,fa⟩,
  have o : is_open (ball c r) := is_open_ball,
  generalize ht : ball c r = t,
  rw ht at fa o,
  suffices h : analytic_on ℂ (g f d) t, { rw ←ht at h, exact h _ (mem_ball_self rp), },
  have ga : differentiable_on ℂ (g f d) (t \ {0}), {
    have e : ∀ z : ℂ, z ∈ t \ {0} → g f d z = f z / z^d, {
      intros z zs, simp only [set.mem_diff, set.mem_singleton_iff] at zs, simp only [g, zs.2, if_false],
    },
    rw differentiable_on_congr e,
    apply differentiable_on.div (fa.mono (set.diff_subset _ _)).differentiable_on,
    exact (differentiable.pow differentiable_id _).differentiable_on,
    intros z zs, exact pow_ne_zero _ (set.mem_diff_singleton.mp zs).2,
  },
  rw ←differentiable_iff_analytic o, swap, apply_instance,
  by_cases t0 : (0 : ℂ) ∉ t, {
    rw set.diff_singleton_eq_self t0 at ga, exact ga,
  },
  simp only [set.not_not_mem] at t0,
  have gc : continuous_at (g f d) 0, {
    rw metric.continuous_at_iff, intros e ep,
    rcases metric.eventually_nhds_iff.mp (asymptotics.is_O_with_iff.mp
      (s.approx.forall_is_O_with (by bound : e/2 > 0))) with ⟨t,tp,h⟩,
    use [t,tp], intros z zs, specialize h zs,
    simp only [complex.norm_eq_abs] at h,
    simp only [g, complex.dist_eq],
    by_cases z0 : z = 0, { simp only [z0, sub_self, absolute_value.map_zero], exact ep },
    simp only [z0, if_false, eq_self_iff_true, if_true],
    calc abs (f z / z^d - 1) = abs (f z * (z^d)⁻¹ - 1) : by rw div_eq_mul_inv
    ... = abs ((f z - z^d) * (z^d)⁻¹) : by rw [mul_sub_right_distrib, mul_inv_cancel (pow_ne_zero d z0)]
    ... = abs (f z - z^d) * abs (z^d)⁻¹ : by rw absolute_value.map_mul
    ... ≤ e/2 * abs (z^d) * abs (z^d)⁻¹ : by bound
    ... = e/2 * (abs (z^d) * abs (z^d)⁻¹) : by ring
    ... ≤ e/2 * 1 : by bound
    ... = e/2 : by ring
    ... < e : half_lt_self ep,
  },
  exact (complex.differentiable_on_compl_singleton_and_continuous_at_iff (o.mem_nhds t0)).mp ⟨ga,gc⟩,
end

-- g is analytic
lemma super_near.ga (s : super_near f d t) : analytic_on ℂ (g f d) t := λ z m, s.ga_of_fa (s.fa z m)

-- super_at → super_near, manual radius version
lemma super_at.super_on_ball (s : super_at f d) {r : ℝ} (rp : 0 < r) (r2 : r ≤ 1/2)
    (fa : analytic_on ℂ f (ball 0 r)) (gs : ∀ {z : ℂ}, abs z < r → abs (g f d z - 1) < 1/4)
    : super_near f d (ball 0 r) := begin
  have gs : ∀ {z : ℂ}, z ≠ 0 → z ∈ ball (0 : ℂ) r → abs (f z / z^d - 1) ≤ 1/4, {
    intros z z0 zs, simp only [mem_ball_zero_iff, complex.norm_eq_abs, lt_min_iff] at zs,
    specialize gs zs, simp only [g, z0, if_false, eq_self_iff_true, if_true] at gs, exact le_of_lt gs,
  },
  exact {
    d2 := s.d2, fa0 := s.fa0, fd := s.fd, fc := s.fc, o := is_open_ball, t0 := mem_ball_self rp, gs' := λ _, gs, fa := fa,
    t2 := begin intros z zs, simp only [mem_ball_zero_iff, complex.norm_eq_abs] at zs, exact trans (le_of_lt zs) r2 end,
    ft := begin
      intros z zs, simp only [mem_ball_zero_iff, complex.norm_eq_abs] at ⊢ zs gs,
      by_cases z0 : z = 0, { simp only [z0, s.f0, rp, absolute_value.map_zero] },
      calc abs (f z) = abs (f z / z^d * z^d) : by rw div_mul_cancel _ (pow_ne_zero d z0)
      ... = abs (f z / z^d - 1 + 1) * (abs z)^d : by simp only [absolute_value.map_mul, complex.abs_pow, sub_add_cancel]
      ... ≤ (abs (f z / z^d - 1) + abs (1 : ℂ)) * r^d : by bound
      ... ≤ (1/4 + abs (1 : ℂ)) * r^d : by bound [gs z0 zs]
      ... ≤ 5/4 * r^(d-1) * r : by { rw [mul_assoc, ←pow_succ', nat.sub_add_cancel (trans one_le_two s.d2)], norm_num }
      ... ≤ 5/4 * (1/2)^(d-1) * r : by bound
      ... ≤ 5/4 * (1/2)^(2-1) * r : by bound [pow_le_pow_of_le_one, nat.sub_le_sub_right s.d2 1]
      ... = 5/8 * r : by norm_num
      ... < r : by bound [mul_lt_of_lt_one_left],
    end,
  },
end

-- super_at → super_near, automatic radius version
lemma super_at.super_near (s : super_at f d) : ∃ t, super_near f d t := begin
  rcases s.fa0.ball with ⟨r0,r0p,fa⟩,
  rcases metric.continuous_at_iff.mp (s.ga_of_fa (fa 0 (mem_ball_self r0p))).continuous_at (1/4) (by norm_num)
    with ⟨r1,r1p,gs⟩,
  set r := min r0 (min r1 (1/2)),
  use ball 0 r,
  have rp : 0 < r := by bound,
  have r2 : r ≤ 1/2 := trans (min_le_right _ _) (min_le_right _ _),
  have rr1 : r ≤ r1 := trans (min_le_right r0 _) (min_le_left r1 _),
  simp only [g0, dist_zero_right, complex.norm_eq_abs, complex.dist_eq, sub_zero] at gs,
  exact s.super_on_ball rp r2 (fa.mono (metric.ball_subset_ball (min_le_left r0 _))) (λ z zr, gs (lt_of_lt_of_le zr rr1)),
end

-- g is small near 0
lemma super_near.gs (s : super_near f d t) {z : ℂ} (zt : z ∈ t) : abs (g f d z - 1) ≤ 1/4 := begin
  by_cases z0 : z = 0, {
    simp only [z0, g0, sub_self, absolute_value.map_zero, one_div, inv_nonneg, zero_le_bit0, zero_le_one],
  }, {
    simp only [g, z0, if_false, s.gs' z0 zt],
  },
end

-- g is nonzero
lemma super_near.g_ne_zero (s : super_near f d t) {z : ℂ} (zt : z ∈ t) : g f d z ≠ 0 := begin
  have h := s.gs zt, contrapose h, simp only [not_not] at h, simp only [h], norm_num,
end

-- f is zero only at zero
lemma super_near.f_ne_zero (s : super_near f d t) {z : ℂ} (zt : z ∈ t) (z0 : z ≠ 0) : f z ≠ 0 :=
  by simp only [s.fg, mul_ne_zero (pow_ne_zero _ z0) (s.g_ne_zero zt), ne.def, not_false_iff]

-- First, we prove Bottcher's theorem for a monic, superattracting fixed point at 0.  We have
--   f z = z^d * g z
--   g 0 = 1
-- Ignoring multiple values, we want
--   (E n z)^(d^n) = f^[n] z
--   E n z = (f^[n] z)^(1/d^n)
--   E n z = (f (f^[n-1] z))^(1/d^n)
--   E n z = (f ((E (n-1) z)^(d^(n-1))))^(1/d^n)
--   E n z = ((E (n-1) z)^(d^n) * g ((E (n-1) z)^(d^(n-1))))^(1/d^n)
--   E n z = E (n-1) z * (g ((E (n-1) z)^(d^(n-1))))^(1/d^n)
--   E n z = E (n-1) z * (g (f^[n-1] z))^(1/d^n)
--   E n z = z * prod_{1 < k ≤ n} (g (f^[k-1] z))^(1/d^k)
-- Terms in our infinite product
def term (f : ℂ → ℂ) (d n : ℕ) (z : ℂ) := g f d (f^[n] z) ^ (1/d^(n+1) : ℂ)

-- With term in hand, we can define Böttcher coordinates
def bottcher_near (f : ℂ → ℂ) (d : ℕ) (z : ℂ) := z * tprod (λ n, term f d n z)

-- ^d shifts term (n+1) to term n:
--   (term n z)^d = (g (f^[n] z) ^ 1/d^(n+1))^d
--                = (g (f^[n-1] (f z)) ^ 1/d^n)
--                = term (n-1) (f z)
lemma term_eqn (s : super_near f d t) : ∀ n, z ∈ t → term f d n (f z) = (term f d (n+1) z)^d :=
  λ n zr, by simp only [term, ←function.iterate_succ_apply, pow_mul_nat, div_mul, pow_succ _ (n+1),
    mul_div_cancel_left _ s.dz]

-- The analogue of term_eqn (-1):
--   (z * term 0 z)^d = (z * g z ^ 1/d)^d
--                    = z^d * g z
--                    = f z
lemma term_base (s : super_near f d t) : z ∈ t → f z = (z * term f d 0 z)^d := begin
  intro zr, rw term, simp only [function.iterate_zero, id.def, pow_one, one_div],
  rw [mul_pow, pow_mul_nat, inv_mul_cancel _], {
    rw s.fg, simp only [complex.cpow_one],
  }, {
    simp only [ne.def, nat.cast_eq_zero],
    exact ne_of_gt (gt_of_ge_of_gt s.d2 (by norm_num)),
  },
end

-- How fast do we converge?  Within r, we (very loosely) have
--   abs (f z) = abs (z^d * g z) ≤ 5/4 * (abs z)^d ≤ 5/8 * abs z
--   abs (f^(n) z) ≤ (5/8)^n * abs z ≤ 1/2 * (5/8)^n
--   abs (term s n z - 1) ≤ 4 * 1/d^(n+1) * 1/4 ≤ 1/2 * (1/d)^n

-- abs (f z) ≤ 5/8 * abs z within t
lemma f_converges (s : super_near f d t) : z ∈ t → abs (f z) ≤ 5/8 * abs z := begin
  intro zt,
  rw s.fg, simp,
  have gs : abs (g f d z) ≤ 5/4, {
    calc abs (g f d z) = abs (g f d z - 1 + 1) : by ring_nf
    ... ≤ abs (g f d z - 1) + abs (1 : ℂ) : by bound
    ... ≤ 1/4 + abs (1 : ℂ) : by bound [s.gs zt]
    ... ≤ 5/4 : by norm_num,
  },
  have az1 : abs z ≤ 1 := trans (s.t2 zt) (by norm_num),
  calc abs z ^ d * abs (g f d z) ≤ abs z ^ 2 * (5/4)
      : by bound [pow_le_pow_of_le_one (by bound) az1 s.d2]
  ... = abs z * abs z * (5/4) : by ring_nf
  ... ≤ 1/2 * abs z * (5/4) : by bound [s.t2 zt]
  ... = 5/8 * abs z : by ring,
end

lemma five_eights_pow_le {n : ℕ} {r : ℝ} : r > 0 → (5/8)^n * r ≤ r := begin
  intro rp, transitivity 1^n * r, bound, simp only [one_pow, one_mul],
end

lemma five_eights_pow_lt {n : ℕ} {r : ℝ} : r > 0 → n ≠ 0 → (5/8)^n * r < r := begin
  intros rp np,
  have h : (5/8 : ℝ)^n < 1 := pow_lt_one (by norm_num) (by norm_num) np,
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h rp) (by simp only [one_mul]),
end

-- Iterating f remains in t
lemma super_near.maps_to (s : super_near f d t) (n : ℕ) : maps_to (f^[n]) t t := begin
  induction n with n h, simp only [set.maps_to_id, function.iterate_zero],
  rw function.iterate_succ', exact s.ft.comp h,
end

-- abs (f^[n] z) ≤ (5/8)^n * abs z
lemma iterates_converge (s : super_near f d t) : ∀ n, z ∈ t → abs (f^[n] z) ≤ (5/8)^n * abs z := begin
  intros n zt,
  induction n with n nh, { simp only [function.iterate_zero, id.def, pow_zero, one_mul], },
  rw function.iterate_succ',
  transitivity 5/8 * abs (f^[n] z), {
    exact f_converges s (s.maps_to n zt),
  }, {
    calc 5/8 * abs (f^[n] z) ≤ 5/8 * ((5/8)^n * abs z) : by bound
    ... = 5/8 * (5/8)^n * abs z : by ring
    ... = (5/8)^(n+1) * abs z : by rw ←pow_succ
    ... = (5/8)^(n.succ) * abs z : rfl,
  },
end

-- Iterates are analytic
lemma iterates_analytic (s : super_near f d t) : ∀ n, analytic_on ℂ (f^[n]) t := begin
  intro n, induction n with n h, {
    simp only [function.iterate_zero], exact analytic_on_id,
  }, {
    rw function.iterate_succ', intros z zt, exact (s.fa _ (s.maps_to n zt)).comp (h z zt),
  },
end

-- term is analytic close to 0
lemma term_analytic (s : super_near f d t) : ∀ n, analytic_on ℂ (term f d n) t := begin
  intros n z zt,
  refine analytic_at.cpow _ analytic_at_const _, {
    exact (s.ga _ (s.maps_to n zt)).comp (iterates_analytic s n z zt),
  }, {
    exact near_one_avoids_negative_reals (lt_of_le_of_lt (s.gs (s.maps_to n zt)) (by norm_num)),
  },
end

-- term converges to 1 exponentially, sufficiently close to 0
lemma term_converges (s : super_near f d t) : ∀ n, z ∈ t → abs (term f d n z - 1) ≤ 1/2 * (1/2)^n := begin
  intros n zt, rw term,
  transitivity 4 * abs (g f d (f^[n] z) - 1) * abs (1/d^(n+1) : ℂ), {
    apply pow_small, {
      exact trans (s.gs (s.maps_to n zt)) (by norm_num),
    }, {
      simp only [one_div, map_inv₀, complex.abs_pow, complex.abs_cast_nat],
      apply inv_le_one,
      have hd : 1 ≤ (d : ℝ) := trans (by norm_num) s.dr2,
      exact one_le_pow_of_one_le hd _,
    },
  }, {
    have gs : abs (g f d (f^[n] z) - 1) ≤ 1/4 := s.gs (s.maps_to n zt),
    have ps : abs (1/↑d^(n+1) : ℂ) ≤ 1/2 * (1/2)^n, {
      have nn : 1/2 * (1/2 : ℝ)^n = (1/2)^(n+1) := (pow_succ _ _).symm,
      rw nn, simp, apply inv_le_inv_of_le, bound, bound [s.dr2]
    },
    calc 4 * abs (g f d (f^[n] z) - 1) * abs (1/↑d^(n+1) : ℂ) ≤ 4 * (1/4) * (1/2 * (1/2)^n) : by bound
    ... = 1/2 * (1/2)^n : by ring,
  },
end

-- term is nonzero, sufficiently close to 0
lemma term_nonzero (s : super_near f d t) : ∀ n, z ∈ t → term f d n z ≠ 0 := begin
  intros n zt,
  have h := term_converges s n zt,
  have o : 1/2 * (1/2 : ℝ)^n < 1, {
    have p : (1/2 : ℝ)^n ≤ 1 := pow_le_one n (by norm_num) (by bound),
    calc 1/2 * (1/2 : ℝ)^n ≤ 1/2 * 1 : by bound
    ... < 1 : by norm_num,
  },
  exact near_one_avoids_zero (lt_of_le_of_lt h o),
end

-- The term product exists and is analytic
lemma term_prod (s : super_near f d t)
    : prod_exists_on (term f d) t ∧ analytic_on ℂ (tprod_on (term f d)) t ∧
        ∀ z, z ∈ t → tprod_on (term f d) z ≠ 0 := begin
  have c12 : (1/2 : ℝ) ≤ 1/2 := by norm_num,
  have a0 : 0 ≤ (1/2 : ℝ) := by norm_num,
  exact fast_products_converge' s.o c12 a0 (by bound) (term_analytic s) (λ n z, term_converges s n),
end
lemma term_prod_exists (s : super_near f d t) : prod_exists_on (term f d) t := (term_prod s).1
lemma term_prod_analytic_z (s : super_near f d t) : analytic_on ℂ (tprod_on (term f d)) t := (term_prod s).2.1
lemma term_prod_ne_zero (s : super_near f d t) (zt : z ∈ t) : tprod_on (term f d) z ≠ 0 := (term_prod s).2.2 _ zt

-- bottcher satisfies b (f z) = (b z)^d near 0
theorem bottcher_near_eqn (s : super_near f d t) (zt : z ∈ t)
    : bottcher_near f d (f z) = (bottcher_near f d z)^d := begin
  simp_rw [bottcher_near],
  have pe := (term_prod_exists s) z zt,
  simp only [mul_pow, product_pow' pe],
  have pe : prod_exists (λ n, term f d n z ^ d), { rcases pe with ⟨g,hg⟩, exact ⟨_,product_pow d hg⟩ },
  simp only [product_split pe, ←term_eqn s _ zt, ←mul_assoc, ←mul_pow, ←term_base s zt],
end

-- The same equation, iterated
theorem bottcher_near_eqn_iter (s : super_near f d t) (zt : z ∈ t) (n : ℕ)
    : bottcher_near f d (f^[n] z) = (bottcher_near f d z)^(d^n) := begin
  induction n with n h, simp only [function.iterate_zero, id.def, pow_zero, pow_one],
  simp only [function.iterate_succ', pow_succ', pow_mul, bottcher_near_eqn s (s.maps_to n zt), h],
end
 
-- f^[n] 0 = 0
lemma iterates_at_zero (s : super_near f d t) : ∀ n, f^[n] 0 = 0 := begin
  intro n, induction n with n h, simp only [function.iterate_zero, id.def],
  simp only [function.iterate_succ', function.comp_app, h, s.f0],
end

-- term s n 0 = 1
lemma term_at_zero (s : super_near f d t) (n : ℕ) : term f d n 0 = 1 :=
  by simp only [term, iterates_at_zero s, g0, complex.one_cpow]

-- prod (term s _ 0) = 1
lemma term_prod_at_zero (s : super_near f d t) : tprod_on (term f d) 0 = 1 :=
  by simp_rw [tprod_on, term_at_zero s, prod_ones']

-- b' 0 = 1, and in particular b is a local isomorphism
theorem bottcher_near_monic (s : super_near f d t) : has_deriv_at (bottcher_near f d) 1 0 := begin
  have dz : has_deriv_at (λ z : ℂ, z) 1 0 := has_deriv_at_id 0,
  have db := has_deriv_at.mul dz (term_prod_analytic_z s 0 s.t0).has_deriv_at,
  simp only [one_mul, zero_mul, add_zero] at db,
  rw term_prod_at_zero s at db, exact db,
end

-- b 0 = 0 
theorem bottcher_near_zero : bottcher_near f d 0 = 0 := by simp only [bottcher_near, zero_mul]

-- z ≠ 0 → b z ≠ 0 
theorem bottcher_near_ne_zero (s : super_near f d t) : z ∈ t → z ≠ 0 → bottcher_near f d z ≠ 0 :=
  λ zt z0, mul_ne_zero z0 (term_prod_ne_zero s zt)

-- bottcher is analytic in z
theorem bottcher_near_analytic_z (s : super_near f d t) : analytic_on ℂ (bottcher_near f d) t :=
  analytic_on_id.mul (term_prod_analytic_z s)

-- f^[n] z → 0 
lemma iterates_tendsto (s : super_near f d t) (zt : z ∈ t) : tendsto (λ n, f^[n] z) at_top (𝓝 0) := begin
  by_cases z0 : z = 0, simp only [z0, iterates_at_zero s, tendsto_const_nhds],
  rw metric.tendsto_at_top, intros e ep,
  simp only [complex.dist_eq, sub_zero],
  have xp : e / abs z > 0 := div_pos ep (complex.abs.pos z0),
  rcases exists_pow_lt_of_lt_one xp (by norm_num : (5/8 : ℝ) < 1) with ⟨N,Nb⟩,
  simp only [lt_div_iff (complex.abs.pos z0)] at Nb,
  use N, intros n nN,
  refine lt_of_le_of_lt (iterates_converge s n zt) (lt_of_le_of_lt _ Nb),
  bound [pow_le_pow_of_le_one],
end

 -- bottcher_near < 1
theorem bottcher_near_lt_one (s : super_near f d t) (zt : z ∈ t) : abs (bottcher_near f d z) < 1 := begin
  rcases metric.continuous_at_iff.mp (bottcher_near_analytic_z s _ s.t0).continuous_at 1 zero_lt_one
    with ⟨r,rp,rs⟩,
  simp only [complex.dist_eq, sub_zero, bottcher_near_zero] at rs,
  have b' : ∀ᶠ n in at_top, abs (bottcher_near f d (f^[n] z)) < 1, {
    refine (metric.tendsto_nhds.mp (iterates_tendsto s zt) r rp).mp (filter.eventually_of_forall (λ n h, _)),
    rw [complex.dist_eq, sub_zero] at h, exact rs h,
  },
  rcases b'.exists with ⟨n,b⟩,
  contrapose b, simp only [not_lt] at b ⊢,
  simp only [bottcher_near_eqn_iter s zt n, complex.abs.map_pow, one_le_pow_of_one_le b],
end

-- Linear bound on bottcher_near
theorem bottcher_near_le (s : super_near f d t) (zt : z ∈ t) : abs (bottcher_near f d z) ≤ 3 * abs z := begin
  simp only [bottcher_near, complex.abs.map_mul], rw mul_comm,
  refine mul_le_mul_of_nonneg_right _ (complex.abs.nonneg _),
  rcases term_prod_exists s _ zt with ⟨p,h⟩, rw h.tprod_eq, simp only [has_prod] at h,
  apply le_of_tendsto' (filter.tendsto.comp complex.continuous_abs.continuous_at h),
  intro A, clear h, simp only [function.comp, complex.abs.map_prod],
  have tb : ∀ n, abs (term f d n z) ≤ 1 + 1/2*(1/2)^n, {
    intros n,
    calc abs (term f d n z) = abs (1 + (term f d n z - 1)) : by ring_nf
    ... ≤ complex.abs 1 + abs (term f d n z - 1) : by bound
    ... = 1 + abs (term f d n z - 1) : by norm_num
    ... ≤ 1 + 1/2*(1/2)^n : by bound [term_converges s n zt],
  },
  have p : ∀ n : ℕ, 0 < (1:ℝ) + 1/2*(1/2)^n := λ _, by bound,
  have lb : ∀ n : ℕ, real.log ((1:ℝ) + 1/2*(1/2)^n) ≤ 1/2*(1/2)^n :=
    λ n, trans (real.log_le_sub_one_of_pos (p n)) (le_of_eq (by ring)),
  refine trans (finset.prod_le_prod (λ _ _, complex.abs.nonneg _) (λ n _, tb n)) _, clear tb,
  rw [←real.exp_log (finset.prod_pos (λ n _, p n)), real.log_prod _ _ (λ n _, ne_of_gt (p n))], clear p, simp only,
  refine trans (real.exp_le_exp.mpr (finset.sum_le_sum (λ n _, lb n))) _, clear lb zt s p t d f,
  refine trans (real.exp_le_exp.mpr _) (le_of_lt real.exp_one_lt_3),
  have geom := partial_scaled_geometric_bound (1/2) A (le_of_lt one_half_pos) one_half_lt_one,
  simp only [nnreal.coe_div, nnreal.coe_one, nnreal.coe_two] at geom,
  exact trans geom (by norm_num),
end

end bottcher

-- Next we prove that everything is analytic in an additional function parameter
section bottcher_c

variables {f : ℂ → ℂ → ℂ}
variables {d : ℕ}
variables {u : set ℂ}
variables {t : set (ℂ × ℂ)}

-- super_at everywhere on a parameter set, at z = 0
structure super_at_c (f : ℂ → ℂ → ℂ) (d : ℕ) (u : set ℂ) : Prop :=
  (o : is_open u)
  (s : ∀ {c}, c ∈ u → super_at (f c) d)
  (fa : ∀ {c}, c ∈ u → analytic_at ℂ (uncurry f) (c,0))

-- super_near everywhere on a parameter set
structure super_near_c (f : ℂ → ℂ → ℂ) (d : ℕ) (u : set ℂ) (t : set (ℂ × ℂ)) : Prop :=
  (o : is_open t)
  (tc : ∀ {p : ℂ × ℂ}, p ∈ t → p.1 ∈ u)
  (s : ∀ {c}, c ∈ u → super_near (f c) d {z | (c,z) ∈ t})
  (fa : analytic_on ℂ (uncurry f) t)

-- t → super_near
lemma super_near_c.ts (s : super_near_c f d u t) {p : ℂ × ℂ} (m : p ∈ t)
    : super_near (f p.1) d {z | (p.1,z) ∈ t} := s.s (s.tc m)

-- u is open
lemma super_near_c.ou (s : super_near_c f d u t) : is_open u := begin
  have e : u = prod.fst '' t, {
    ext c, simp only [set.mem_image, prod.exists, exists_and_distrib_right, exists_eq_right],
    exact ⟨(λ m, ⟨0,(s.s m).t0⟩), (λ h, exists.elim h (λ z m, s.tc m))⟩,
  },
  rw e, exact is_open_map_fst _ s.o,
end

-- super_at → super_at_c
lemma super_near_c.super_at_c (s : super_near_c f d u t) : super_at_c f d u := {
  o := s.ou,
  s := begin intros c m, have s := s.s m, exact {d2 := s.d2, fa0 := s.fa0, fd := s.fd, fc := s.fc} end,
  fa := λ c m, s.fa _ (s.s m).t0,
}

-- Two-parameter g
def g2 (f : ℂ → ℂ → ℂ) (d : ℕ) := λ p : ℂ × ℂ, g (f p.1) d p.2

-- g2 is jointly analytic where f is
lemma super_at_c.ga_of_fa (s : super_at_c f d u) {t : set (ℂ × ℂ)} (o : is_open t) (fa : analytic_on ℂ (uncurry f) t)
    (tc : ∀ {p : ℂ × ℂ}, p ∈ t → p.1 ∈ u) : analytic_on ℂ (g2 f d) t := begin
  refine pair.hartogs o _ _, {
    intros c z m,
    simp only [g2, g],
    by_cases zero : z = 0, {
      simp only [zero, eq_self_iff_true, if_true], exact analytic_at_const,
    }, {
      simp only [zero, if_false], refine analytic_at.div _ analytic_at_const (pow_ne_zero _ zero),
      refine (fa _ _).curry_comp analytic_at_id analytic_at_const, exact m,
    },
  }, {
    intros c z m, apply (s.s (tc m)).ga_of_fa,
    refine (fa _ _).curry_comp analytic_at_const analytic_at_id, exact m,
  },
end

-- g2 is jointly analytic
lemma super_near_c.ga (s : super_near_c f d u t) : analytic_on ℂ (g2 f d) t :=
  s.super_at_c.ga_of_fa s.o s.fa (λ p m, s.tc m)

-- super_near_c commutes with unions
lemma super_near_c.Union {I : Type} {u : I → set ℂ} {t : I → set (ℂ × ℂ)} (s : ∀ i, super_near_c f d (u i) (t i))
    : super_near_c f d (⋃ i, u i) (⋃ i, t i) := begin
  set tu := ⋃ i, t i,
  have o : is_open tu := is_open_Union (λ i, (s i).o),
  have sm : ∀ {c z : ℂ}, (c,z) ∈ tu → ∃ u, z ∈ u ∧ u ⊆ {z | (c,z) ∈ tu} ∧ super_near (f c) d u, {
    intros c z m, rcases set.mem_Union.mp m with ⟨i,m⟩, use {z | (c,z) ∈ t i},
    simp only [m, (s i).s ((s i).tc m), set.mem_set_of_eq, set.mem_Union, set.set_of_subset_set_of,
      and_true, true_and],
    exact λ z m, ⟨i,m⟩,
  },
  exact {
    o := o,
    tc := begin intros p m, rcases set.mem_Union.mp m with ⟨i,m⟩, exact set.subset_Union _ i ((s i).tc m), end,
    fa := begin intros p m, rcases set.mem_Union.mp m with ⟨i,m⟩, exact (s i).fa _ m, end,
    s := begin
      intros c m, rcases set.mem_Union.mp m with ⟨i,m⟩, have s := (s i).s m,
      exact {
        d2 := s.d2, fa0 := s.fa0, fd := s.fd, fc := s.fc,
        o := o.snd_preimage c,
        t0 := set.subset_Union _ i s.t0,
        t2 := begin intros z m, rcases sm m with ⟨u,m,us,s⟩, exact s.t2 m, end,
        fa := begin intros z m, rcases sm m with ⟨u,m,us,s⟩, exact s.fa _ m, end,
        ft := begin intros z m, rcases sm m with ⟨u,m,us,s⟩, exact us (s.ft m), end,
        gs' := begin intros z z0 m, rcases sm m with ⟨u,m,us,s⟩, exact s.gs' z0 m, end,
      },
    end,
  },
end

-- super_at_c → super_near_c, staying inside w
lemma super_at_c.super_near_c' (s : super_at_c f d u) {w : set (ℂ × ℂ)}
    (wo : is_open w) (wc : ∀ c, c ∈ u → (c,(0:ℂ)) ∈ w) : ∃ t, t ⊆ w ∧ super_near_c f d u t := begin
  have h : ∀ c, c ∈ u → ∃ r, r > 0 ∧ ball c r ⊆ u ∧ ball (c,0) r ⊆ w ∧ super_near_c f d (ball c r) (ball (c,0) r), {
    intros c m,
    rcases (s.fa m).ball with ⟨r0,r0p,fa⟩,
    rcases metric.is_open_iff.mp s.o c m with ⟨r1,r1p,rc⟩,
    set r2 := min r0 r1,
    have fa := fa.mono (metric.ball_subset_ball (min_le_left r0 r1)),
    have rc : ball c r2 ⊆ u := trans (metric.ball_subset_ball (by bound)) rc,
    have ga := s.ga_of_fa is_open_ball fa (begin
      intros p m, simp only [←ball_prod_same, set.mem_prod] at m, exact rc m.1,
    end),
    rcases metric.is_open_iff.mp wo (c,0) (wc c m) with ⟨r3,r3p,rw⟩,
    rcases metric.continuous_at_iff.mp (ga (c,0) (mem_ball_self (by bound))).continuous_at (1/4) (by norm_num)
      with ⟨r4,r4p,gs⟩,
    set r := min (min r2 r3) (min r4 (1/2)),
    have rp : 0 < r := by bound,
    have rh : r ≤ 1/2 := trans (min_le_right _ _) (min_le_right _ _),
    have rr4 : r ≤ r4 := trans (min_le_right _ _) (min_le_left r4 _),
    have rc : ball c r ⊆ u := trans (metric.ball_subset_ball (by bound)) rc,
    have rw : ball (c,0) r ⊆ w :=
      trans (metric.ball_subset_ball (trans (min_le_left _ _) (min_le_right _ _))) rw,
    use [r, rp, rc, rw],
    exact {
      o := is_open_ball,
      tc := begin intros p m, simp only [←ball_prod_same, set.mem_prod] at m, exact metric.ball_subset_ball (by bound) m.1 end,
      s := begin
        intros c' m, simp only [←ball_prod_same, set.mem_prod, m, true_and], apply (s.s (rc m)).super_on_ball rp rh, {
          apply fa.curry_comp analytic_on_const analytic_on_id,
          intros z zm, apply metric.ball_subset_ball (by bound : r ≤ r2),
          simp only [←ball_prod_same, set.mem_prod, m, true_and], exact zm,
        }, {
          simp only [complex.dist_eq, prod.dist_eq, sub_zero, max_lt_iff, and_imp, g2, g0] at gs,
          simp only [metric.mem_ball, complex.dist_eq] at m,
          intros z zr, exact @gs ⟨c',z⟩ (lt_of_lt_of_le m rr4) (lt_of_lt_of_le zr rr4),
        }
      end,
      fa := fa.mono (metric.ball_subset_ball (by bound)),
    },
  },
  set r := λ c : u, classical.some (h _ c.mem),
  set v := λ c : u, ball (c : ℂ) (r c),
  set t := λ c : u, ball ((c : ℂ), (0 : ℂ)) (r c),
  use ⋃ c : u, t c,
  have e : u = ⋃ c : u, v c, {
    apply set.ext, intro c, rw set.mem_Union, constructor, {
      intro m, use ⟨c,m⟩, rcases classical.some_spec (h c m) with ⟨rp,_,_⟩, exact mem_ball_self rp,
    }, {
      intro m, rcases m with ⟨i,m⟩, rcases classical.some_spec (h _ i.mem) with ⟨_,us,_⟩, exact us m,
    },
  },
  have tw : (⋃ c : u, t c) ⊆ w, {
    apply set.Union_subset, intro i, rcases classical.some_spec (h _ i.mem) with ⟨_,_,rw,_⟩, exact rw,
  },
  have si : ∀ c : u, super_near_c f d (v c) (t c), {
    intro i, rcases classical.some_spec (h _ i.mem) with ⟨_,_,_,s⟩, exact s,
  },
  have s := super_near_c.Union si, simp only at s, rw ←e at s,
  use [tw, s],
end

-- super_at_c → super_near_c
lemma super_at_c.super_near_c (s : super_at_c f d u) : ∃ t, super_near_c f d u t := begin
  rcases s.super_near_c' is_open_univ (λ _ _, set.mem_univ _) with ⟨t,_,s⟩, use [t,s],
end
 
lemma iterates_analytic_c (s : super_near_c f d u t) {c z : ℂ} (n : ℕ) (m : (c,z) ∈ t)
    : analytic_at ℂ (λ c, f c^[n] z) c := begin
  induction n with n nh, {
    simp only [function.iterate_zero, id.def], exact analytic_at_const,
  }, {
    simp_rw function.iterate_succ', simp only [function.comp_app],
    refine (s.fa _ _).comp (analytic_at_id.prod nh),
    exact (s.ts m).maps_to n m,
  },
end

lemma term_analytic_c (s : super_near_c f d u t) {c z : ℂ} (n : ℕ) (m : (c,z) ∈ t)
    : analytic_at ℂ (λ c, term (f c) d n z) c := begin
  refine analytic_at.cpow _ analytic_at_const _, {
    have e : (λ c, g (f c) d (f c^[n] z)) = (λ c, g2 f d (c, f c^[n] z)) := rfl,
    rw e, refine (s.ga _ _).comp _, exact (s.ts m).maps_to n m,
    apply analytic_at_id.prod (iterates_analytic_c s n m),
  }, {
    refine near_one_avoids_negative_reals _,
    exact lt_of_le_of_lt ((s.ts m).gs ((s.ts m).maps_to n m)) (by norm_num),
  },
end

-- term prod is analytic in c
theorem term_prod_analytic_c (s : super_near_c f d u t) {c z : ℂ} (m : (c,z) ∈ t)
    : analytic_at ℂ (λ c, tprod (λ n, term (f c) d n z)) c := begin
  rw ←tprod_on,
  have c12 : (1/2 : ℝ) ≤ 1/2 := by norm_num,
  have a0 : 0 ≤ (1/2 : ℝ) := by norm_num,
  set t' := {c | (c,z) ∈ t},
  have o' : is_open t' := s.o.preimage (by continuity),
  refine (fast_products_converge' o' c12 a0 (by bound) _ (λ n c m, term_converges (s.ts m) n m)).2.1 _ m,
  exact λ n c m, term_analytic_c s n m,
end

-- term prod is jointly analytic (using Hartogs's theorem for simplicity)
theorem term_prod_analytic (s : super_near_c f d u t)
    : analytic_on ℂ (λ p : ℂ × ℂ, tprod (λ n, term (f p.1) d n p.2)) t := begin
  refine pair.hartogs s.o _ _, {
    intros c z m, simp only, exact term_prod_analytic_c s m,
  }, {
    intros c z m, simp only, exact term_prod_analytic_z (s.ts m) _ m,
  },
end

-- bottcher is analytic in c
theorem bottcher_near_analytic_c (s : super_near_c f d u t) {c z : ℂ} (m : (c,z) ∈ t)
    : analytic_at ℂ (λ c, bottcher_near (f c) d z) c := analytic_at_const.mul (term_prod_analytic_c s m)

-- bottcher is jointly analytic (using Hartogs's theorem for simplicity)
theorem bottcher_near_analytic (s : super_near_c f d u t)
    : analytic_on ℂ (λ p : ℂ × ℂ, bottcher_near (f p.1) d p.2) t :=
  λ p m, analytic_at_snd.mul (term_prod_analytic s _ m)

-- deriv f is nonzero away from 0
lemma df_ne_zero (s : super_near_c f d u t) {c : ℂ}  (m : c ∈ u)
    : ∀ᶠ p : ℂ × ℂ in 𝓝 (c,0), deriv (f p.1) p.2 = 0 ↔ p.2 = 0 := begin
  have df : ∀ e z, (e,z) ∈ t → deriv (f e) z = ↑d * z^(d-1) * g (f e) d z + z^d * deriv (g (f e) d) z, {
    intros e z m, apply has_deriv_at.deriv,
    have fg : f e = λ z, z^d * g (f e) d z := by simp only [←(s.ts m).fg],
    nth_rewrite 0 fg,
    apply has_deriv_at.mul, apply has_deriv_at_pow,
    rw has_deriv_at_deriv_iff, exact ((s.ts m).ga _ m).differentiable_at,
  },
  have small : ∀ᶠ p : ℂ × ℂ in 𝓝 (c,0), abs (p.2 * deriv (g (f p.1) d) p.2) < abs (↑d * g (f p.1) d p.2), {
    have ga : analytic_at ℂ (uncurry (λ c z, g (f c) d z)) (c,0) := s.ga _ (s.s m).t0,
    apply continuous_at.eventually_lt, {
      exact complex.continuous_abs.continuous_at.comp (continuous_at_snd.mul ga.deriv2.continuous_at),
    }, {
      exact complex.continuous_abs.continuous_at.comp (continuous_at_const.mul ga.continuous_at),
    }, {
      simp only [g0, zero_mul, complex.abs.map_zero, complex.abs.map_mul, complex.abs_cast_nat,
        complex.abs.map_one, mul_one, nat.cast_pos],
      exact (s.s m).dp,
    },
  },
  apply small.mp,
  apply (s.o.eventually_mem (s.s m).t0).mp,
  apply filter.eventually_of_forall, clear small,
  rintros ⟨e,w⟩ m' small, simp only [df _ _ m'] at small ⊢,
  nth_rewrite 3 ←nat.sub_add_cancel (nat.succ_le_of_lt (s.s m).dp),
  simp only [pow_add, pow_one, mul_comm _ (w^(d-1)), mul_assoc (w^(d-1)) _ _, ←left_distrib, mul_eq_zero,
    pow_eq_zero_iff (nat.sub_pos_of_lt (s.s m).d2)],
  exact or_iff_left (add_ne_zero_of_abs_lt small),
end

end bottcher_c