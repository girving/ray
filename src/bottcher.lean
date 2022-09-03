-- Bottcher map for Julia sets

import data.complex.basic
import data.complex.exponential
import analysis.complex.removable_singularity
import analysis.special_functions.complex.log
import tactic.monotonicity
import topology.basic

import analytic
import hartogs
import if_p
import osgood
import products
import zeros

open complex (exp log abs cpow)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball)
open nat (iterate)
open set (univ)
open_locale nnreal
noncomputable theory

section bottcher

-- Information about a fixpoint.  Notes:
-- 1. Fixpoints are superattracting if d ≥ 2
-- 2. Monic fixpoints are those where a = 1
structure fixpoint (f : ℂ → ℂ) (c : ℂ) : Type :=
  (d : ℕ)  -- Order of the fixpoint
  (g : ℂ → ℂ)
  (a : ℂ)
  (a0 : a ≠ 0)
  (gc : g c = 1)
  (fc : f c = c)
  (fg : ∀ z, f z = c + a * (z - c)^d * g z)
  (fa : analytic_at ℂ f c)
  (ga : analytic_at ℂ g c)

-- All information for a superattracting fixed point
variables {f g : ℂ → ℂ}
variables {d : ℕ}
variables {c a z : ℂ}
variables {r : ℝ}

structure super (f g : ℂ → ℂ) (d : ℕ) (c a : ℂ) (r : ℝ) : Prop :=
  (d2 : d ≥ 2)
  (a0 : a ≠ 0)
  (gc : g c = 1)
  (fc : f c = c)
  (fg : ∀ z, f z = c + a * (z - c)^d * g z)
  (rp : r > 0)
  (r2 : r ≤ 1/2)
  (fa : analytic_on ℂ f (ball 0 r))
  (ga : analytic_on ℂ g (ball 0 r))
  (gs : ∀ {z : ℂ}, abs z ≤ r → abs (g z - 1) ≤ 1/4)

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
def term (s : super f g d 0 a r) (n : ℕ) (z : ℂ) := g (f^[n] z) ^ (1/d^(n+1) : ℂ)

-- With term in hand, we can define Böttcher coordinates
def bottcher (s : super f g d 0 1 r) (z : ℂ) := z * tprod (λ n, term s n z)

-- ^d shifts term (n+1) to term n:
--   (term n z)^d = (g (f^[n] z) ^ 1/d^(n+1))^d
--                = (g (f^[n-1] (f z)) ^ 1/d^n)
--                = term (n-1) (f z)
lemma term_eqn (s : super f g d 0 1 r) : ∀ n, abs z ≤ r → term s n (f z) = (term s (n+1) z)^d := begin
  intros n zr, rw term, rw term,
  rw ←function.iterate_succ_apply,
  rw [simple.pow_mul_nat, div_mul, simple.pow_div _],
  simp, exact ne_of_gt (gt_of_ge_of_gt s.d2 (by norm_num))
end

-- The analogue of term_eqn (-1):
--   (z * term 0 z)^d = (z * g z ^ 1/d)^d
--                    = z^d * g z
--                    = f z
lemma term_base (s : super f g d 0 1 r) : abs z ≤ r → f z = (z * term s 0 z)^d := begin
  intro zr, rw term, simp,
  rw [mul_pow, simple.pow_mul_nat, inv_mul_cancel _],
  rw s.fg, simp,
  simp, exact ne_of_gt (gt_of_ge_of_gt s.d2 (by norm_num))
end

-- How fast do we converge?  Within r, we (very loosely) have
--   abs (f z) = abs (z^d * g z) ≤ 5/4 * (abs z)^d ≤ 5/8 * abs z
--   abs (f^(n) z) ≤ (5/8)^n * abs z ≤ 1/2 * (5/8)^n
--   abs (term s n z - 1) ≤ 4 * 1/d^(n+1) * 1/4 ≤ 1/2 * (1/d)^n

-- We use this a few times, so make it a lemma
lemma super.dr2 (s : super f g d 0 1 r) : (d : ℝ) ≥ 2 := begin
  flip_ineq, transitivity ((2 : ℕ) : ℝ), norm_num,
  exact simple.nat_real_coe_le_coe s.d2
end

-- abs (f z) ≤ 5/8 * abs z within r
lemma f_converges (s : super f g d 0 1 r) : abs z ≤ r → abs (f z) ≤ 5/8 * abs z := begin
  intro zr,
  rw s.fg, simp,
  have gs : abs (g z) ≤ 5/4, {
    calc abs (g z) = abs (g z - 1 + 1) : by ring_nf
    ... ≤ abs (g z - 1) + abs (1 : ℂ) : complex.abs_add _ _
    ... ≤ 1/4 + abs (1 : ℂ) : by bound [s.gs zr]
    ... ≤ 5/4 : by norm_num
  },
  have az1 : abs z ≤ 1 := trans zr (trans s.r2 (by norm_num)),
  calc abs z ^ d * abs (g z) ≤ abs z ^ 2 * (5/4)
      : by bound [pow_le_pow_of_le_one (by bound) az1 s.d2]
  ... = abs z * abs z * (5/4) : by ring_nf
  ... ≤ 1/2 * abs z * (5/4) : by bound [trans zr s.r2]
  ... = 5/8 * abs z : by ring
end

-- abs (f z) ≤ abs z within r
lemma f_remains (s : super f g d 0 1 r) : abs z ≤ r → abs (f z) ≤ abs z := begin
  intro zs,
  transitivity 5/8 * abs z,
  exact f_converges s zs,
  transitivity 1 * abs z, bound, simp
end

lemma five_eights_pow_le {n : ℕ} {r : ℝ} : r > 0 → (5/8)^n * r ≤ r := begin
  intro rp, transitivity 1^n * r, bound, simp
end

lemma five_eights_pow_lt {n : ℕ} {r : ℝ} : r > 0 → n ≠ 0 → (5/8)^n * r < r := begin
  intros rp np,
  have h : (5/8 : ℝ)^n < 1 := pow_lt_one (by norm_num) (by norm_num) np,
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_right h rp) (by simp)
end

-- abs (f^[n] z) ≤ (5/8)^n * abs z
lemma iterates_converge (s : super f g d 0 1 r) : ∀ n, abs z ≤ r → abs (f^[n] z) ≤ (5/8)^n * r := begin
  intros n zr,
  induction n with n nh, { simpa },
  rw function.iterate_succ',
  transitivity 5/8 * abs (f^[n] z),
  apply f_converges s (trans nh (five_eights_pow_le s.rp)),
  calc 5/8 * abs (f^[n] z) ≤ 5/8 * ((5/8)^n * r) : by bound [s.rp]
  ... = 5/8 * (5/8)^n * r : by ring
  ... = (5/8)^(n+1) * r : by rw ←pow_succ
  ... = (5/8)^(n.succ) * r : rfl
end

-- Often, all we need is abs (f^[n] z) ≤ r
lemma iterates_remain (s : super f g d 0 1 r) : ∀ n, abs z ≤ r → abs (f^[n] z) ≤ r := begin
  intros n zr,
  exact trans (iterates_converge s n zr) (five_eights_pow_le s.rp)
end

-- iterates_remain as set.maps_to
lemma iterates_maps_to (s : super f g d 0 1 r) : ∀ n, set.maps_to (f^[n]) (ball 0 r) (ball 0 r) := begin
  intros n z zs, simp at ⊢ zs,
  by_cases np : n = 0, { rw np, simpa },
  exact lt_of_le_of_lt (iterates_converge s n (le_of_lt zs)) (five_eights_pow_lt s.rp np)
end

-- Iterates are analytic
lemma iterates_analytic (s : super f g d 0 1 r) : ∀ n, analytic_on ℂ (f^[n]) (ball 0 r) := begin
  intro n,
  rw ←differentiable_iff_analytic is_open_ball,
  induction n with n, {
    simp, exact λ _ _, differentiable_within_at_id
  }, {
    rw function.iterate_succ',
    refine differentiable_on.comp _ (by assumption) (iterates_maps_to s n),
    exact (differentiable_iff_analytic is_open_ball).mpr s.fa,
  },
  exact complete_of_proper
end

-- term is analytic close to 0
lemma term_analytic (s : super f g d 0 1 r) : ∀ n, analytic_on ℂ (term s n) (ball 0 r) := begin
  intro n,
  rw ←differentiable_iff_analytic is_open_ball,
  apply differentiable_on.cpow, {
    refine differentiable_on.comp _ _ (iterates_maps_to s n),
    exact (differentiable_iff_analytic is_open_ball).mpr s.ga,
    exact (differentiable_iff_analytic is_open_ball).mpr (iterates_analytic s n)
  }, {
    exact differentiable_on_const _
  }, {
    intros z zr, simp at zr,
    refine near_one_avoids_negative_reals _,
    exact lt_of_le_of_lt (s.gs (iterates_remain s n (le_of_lt zr))) (by norm_num),
  },
  exact complete_of_proper
end

-- term converges to 1 exponentially, sufficiently close to 0
lemma term_converges (s : super f g d 0 1 r) : ∀ n, abs z ≤ r → abs (term s n z - 1) ≤ 1/2 * (1/2)^n := begin
  intros n zr,
  rw term,
  transitivity 4 * abs (g (f^[n] z) - 1) * abs (1/d^(n+1) : ℂ), {
    apply pow_small, {
      transitivity (1/4 : ℝ),
      exact s.gs (iterates_remain s n zr),
      norm_num
    }, {
      simp, apply inv_le_one,
      have hd : 1 ≤ (d : ℝ) := trans (by norm_num) s.dr2,
      exact one_le_pow_of_one_le hd _
    }
  }, {
    have fns : abs (f^[n] z) ≤ r := iterates_remain s n zr,
    have gs : abs (g (f^[n] z) - 1) ≤ 1/4 := s.gs fns,
    have ps : abs (1/↑d^(n+1) : ℂ) ≤ 1/2 * (1/2)^n, {
      have nn : 1/2 * (1/2 : ℝ)^n = (1/2)^(n+1) := (pow_succ _ _).symm,
      rw nn, simp, apply inv_le_inv_of_le, bound, bound [s.dr2]
    },
    calc 4 * abs (g (f^[n] z) - 1) * abs (1/↑d^(n+1) : ℂ) ≤ 4 * (1/4) * (1/2 * (1/2)^n) : by bound
    ... = 1/2 * (1/2)^n : by ring
  }
end

-- term is nonzero, sufficiently close to 0
lemma term_nonzero (s : super f g d 0 1 r) : ∀ n, abs z ≤ r → term s n z ≠ 0 := begin
  intros n zr,
  have h := term_converges s n zr,
  have o : 1/2 * (1/2 : ℝ)^n < 1, {
    have p : (1/2 : ℝ)^n ≤ 1 := pow_le_one n (by norm_num) (by bound),
    calc 1/2 * (1/2 : ℝ)^n ≤ 1/2 * 1 : by bound
    ... < 1 : by norm_num
  },
  exact near_one_avoids_zero (lt_of_le_of_lt h o)
end

-- The term product exists and is analytic
lemma term_prod (s : super f g d 0 1 r)
    : prod_exists_on (term s) (ball 0 r) ∧ analytic_on ℂ (tprod_on (term s)) (ball 0 r) := begin
  have c12 : (1/2 : ℝ) ≤ 1/2 := by norm_num,
  have a0 : 0 ≤ (1/2 : ℝ) := by norm_num,
  have a1 : (1/2 : ℝ) < 1 := by norm_num,
  apply fast_products_converge' is_open_ball c12 a0 a1, {
    exact term_analytic s
  }, {
    intros n z zr, simp at zr, exact term_converges s n (le_of_lt zr)
  }
end

-- bottcher satisfies b (f z) = (b z)^d near 0
theorem bottcher_eqn (s : super f g d 0 1 r) : abs z < r → bottcher s (f z) = (bottcher s z)^d := begin
  intro zr,
  rw bottcher, rw bottcher,
  have zs : z ∈ ball (0 : ℂ) r := by simpa,
  have zr' := le_of_lt zr,
  have pe := (term_prod s).left z zs,
  rw mul_pow,
  rw product_pow' pe, simp,
  have pe : prod_exists (λ n, term s n z ^ d), { rcases pe with ⟨g,hg⟩, exact ⟨_,product_pow d hg⟩ },
  rw product_split pe, simp,
  simp_rw ←term_eqn s _ zr',
  rw ←mul_assoc, rw ←mul_pow, rw ←term_base s zr'
end

-- f^[n] 0 = 0
lemma iterates_at_zero (s : super f g d 0 1 r) : ∀ n, f^[n] 0 = 0 := begin
  intro n, induction n with n h, simp,
  rw function.iterate_succ', simp, rw [h, s.fc]
end

-- term s n 0 = 1
lemma term_at_zero (s : super f g d 0 1 r) : ∀ n, term s n 0 = 1 := begin
  intro n, rw [term, iterates_at_zero s, s.gc], simp
end

-- prod (term s _ 0) = 1
lemma term_prod_at_zero (s : super f g d 0 1 r) : tprod_on (term s) 0 = 1 := begin
  simp_rw [tprod_on, term_at_zero s], exact prod_ones'
end

-- b' 0 = 1, and in particular b is a local isomorphism
theorem bottcher_monic (s : super f g d 0 1 r) : has_deriv_at (bottcher s) 1 0 := begin
  have p := term_prod s,
  have dp := (p.right 0 (metric.mem_ball_self s.rp)).has_deriv_at,
  have dz : has_deriv_at (λ z : ℂ, z) 1 0 := has_deriv_at_id 0,
  have db := has_deriv_at.mul dz dp, simp at db,
  rw term_prod_at_zero at db, exact db
end

-- bottcher is analytic in z
theorem bottcher_analytic_z (s : super f g d 0 1 r) : analytic_on ℂ (bottcher s) (ball 0 r) := begin
  rw ←differentiable_iff_analytic is_open_ball,
  exact differentiable_on.mul differentiable_on_id (term_prod s).right.differentiable_on,
  exact complete_of_proper
end

end bottcher

-- Next we prove that everything is analytic in an additional function parameter
section bottcher_c

variables {f g : ℂ → ℂ → ℂ}
variables {cs : set ℂ}
variables {d : ℕ}
variables {r : ℝ}

-- super everywhere on a parameter set
structure super_c (f g : ℂ → ℂ → ℂ) (cs : set ℂ) (d : ℕ) (r : ℝ) :=
(rp : r > 0)
(o : is_open cs)
(s : Π c, c ∈ cs → super (f c) (g c) d 0 1 r)
(fa : analytic_on ℂ (uncurry f) (cs ×ˢ (ball (0 : ℂ) r)))
(ga : analytic_on ℂ (uncurry g) (cs ×ˢ (ball (0 : ℂ) r)))

-- The set on which everything is defined is open
lemma super_c.o2 (s : super_c f g cs d r) : is_open (cs ×ˢ (ball (0 : ℂ) r)) := is_open.prod s.o is_open_ball

-- Differentiability of f and g
lemma super_c.fd (s : super_c f g cs d r) : differentiable_on ℂ (uncurry f) (cs ×ˢ (ball (0 : ℂ) r)) :=
  (differentiable_iff_analytic2 s.o2).mpr s.fa
lemma super_c.gd (s : super_c f g cs d r) : differentiable_on ℂ (uncurry g) (cs ×ˢ (ball (0 : ℂ) r)) :=
  (differentiable_iff_analytic2 s.o2).mpr s.ga

-- Parameterized version of bottcher
def bottcher_c (s : super_c f g cs d r) (c z : ℂ) : ℂ :=
  if_p (c ∈ cs) (λ m, bottcher (s.s c m) z)

-- bottcher_c factors as expected
lemma bottcher_c_def (s : super_c f g cs d r) (c z : ℂ)
    : bottcher_c s c z = z * tprod (λ n, if_p (c ∈ cs) (λ m, term (s.s c m) n z)) := begin
  simp_rw [bottcher_c, bottcher],
  by_cases m : c ∈ cs, {
    simp_rw if_p_true m
  }, {
    simp_rw [if_p_false m, has_prod.zero.tprod_eq], simp
  }
end

--lemma term_prod_fast_c
-- tprod_on (λ n c, if_p (c ∈ cs) (λ m, term (s.s c m) n z))

    --(o : is_open s) (c12 : c ≤ 1/2) (a0 : 0 ≤ a) (a1 : a < 1)
    --(h : ∀ n, analytic_on ℂ (f n) s) (hf : ∀ n z, z ∈ s → abs (f n z - 1) ≤ c * a^n)

lemma iterates_maps_to_c (s : super_c f g cs d r) {z : ℂ}
    (n : ℕ) (zm : z ∈ ball (0 : ℂ) r)
    : set.maps_to (λ (c : ℂ), (c, f c^[n] z)) cs (cs ×ˢ ball 0 r) := begin
  intros c cm, simp at ⊢ zm, refine ⟨cm,_⟩,
  by_cases n0 : n = 0, { rw n0, simpa },
  exact lt_of_le_of_lt (iterates_converge (s.s c cm) n (le_of_lt zm)) (five_eights_pow_lt s.rp n0)
end

lemma iterates_differentiable_c (s : super_c f g cs d r) {z : ℂ}
    (n : ℕ) (zm : z ∈ ball (0 : ℂ) r)
    : differentiable_on ℂ (λ c, f c^[n] z) cs := begin
  induction n with n nh, {
    simp, exact differentiable_on_const _
  }, {
    simp_rw function.iterate_succ', simp,
    have e : (λ c, f c (f c^[n] z)) = (uncurry f) ∘ (λ c, (c, f c^[n] z)) := rfl,
    rw e, clear e, apply differentiable_on.comp s.fd,
    exact differentiable_on.prod differentiable_on_id nh,
    exact iterates_maps_to_c s n zm
  }
end

lemma term_analytic_c (s : super_c f g cs d r) {z : ℂ}
    (n : ℕ) (zm : z ∈ ball (0 : ℂ) r)
    : analytic_on ℂ (λ c, if_p (c ∈ cs) (λ m, term (s.s c m) n z)) cs := begin
  simp_rw term,
  rw analytic_on_congr s.o (if_p_const cs),
  rw ←differentiable_iff_analytic s.o,
  apply differentiable_on.cpow, {
    have e : (λ c, g c (f c^[n] z)) = (uncurry g) ∘ (λ c, (c, f c^[n] z)) := rfl,
    rw e, apply differentiable_on.comp s.gd,
    apply differentiable_on.prod differentiable_on_id,
    exact iterates_differentiable_c s n zm,
    exact iterates_maps_to_c s n zm
  }, {
    exact differentiable_on_const _
  }, {
    intros c cm, simp at zm,
    refine near_one_avoids_negative_reals _,
    exact lt_of_le_of_lt ((s.s c cm).gs (iterates_remain (s.s c cm) n (le_of_lt zm))) (by norm_num)
  },
  repeat { exact complete_of_proper },
end

-- bottcher is analytic in c
theorem bottcher_analytic_c (s : super_c f g cs d r) {z : ℂ} (zm : z ∈ ball (0 : ℂ) r)
    : analytic_on ℂ (λ c, bottcher_c s c z) cs := begin
  simp_rw bottcher_c_def s,
  rw ←differentiable_iff_analytic s.o,
  apply differentiable_on.mul (differentiable_on_const _),
  rw differentiable_iff_analytic s.o,
  rw ←tprod_on,
  have c12 : (1/2 : ℝ) ≤ 1/2 := by norm_num,
  have a0 : 0 ≤ (1/2 : ℝ) := by norm_num,
  have a1 : (1/2 : ℝ) < 1 := by norm_num,
  refine (fast_products_converge' s.o c12 a0 a1 _ _).right, {
    exact λ n, term_analytic_c s n zm
  }, {
    intros n c cm, rw if_p_true cm, simp at zm,
    exact term_converges (s.s c cm) n (le_of_lt zm)
  },
  repeat { exact complete_of_proper }
end

-- bottcher is jointly analytic (using Hartog's theorem for simplicity)
theorem bottcher_analytic2 (s : super_c f g cs d r)
    : analytic_on ℂ (uncurry (bottcher_c s)) (cs ×ˢ (ball (0 : ℂ) r)) := begin
  apply pair.hartogs (s.o.prod metric.is_open_ball), {
    simp, intros c0 c1 c0s c1s, exact bottcher_analytic_c s (by simpa) _ c0s,
  }, {
    simp, intros c0 c1 c0s c1s,
    have e : bottcher_c s c0 = bottcher (s.s c0 c0s), { funext, rw [bottcher_c, if_p_true c0s] },
    rw e, apply bottcher_analytic_z, simpa,
  },
  apply_instance, apply_instance,
end

end bottcher_c