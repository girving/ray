import Ray.Dynamics.Multibrot.Basic

/-!
## Effective bounds on `bottcher` and `potential` for Multibrot sets

We derive effective bounds and estimates for the Böttcher coordinates of the Multibrot sets.  These
are used in `Isomorphism.lean` and `Connected.lean` to prove our main theoretical results, and by
`Render/Potential.lean` for rigorous numerical calculations.

For the theory, we mainly need that our diagonal Böttcher `bottcher d c` is holomorphic with
derivative 1 at `∞`, by showing that the analytically continued map is given by the infinite product
for large `c`.  This does not follow immediately from our dynamical work, which covers only finite
`c : ℂ`.  I'm uneasy that I've missed some basic conceptual arguments that would make these
calculations unnecessary.

However, for numerical results the intermediate bounds have independent use, in particular
`potential_approx`.  Here we want the bounds to be as tight as possible to break out of loops as
soon as we can, and improve numerical precision.

Here are the main effective results that we prove:

1. The Multibrot set is inside radius 2.
2. For `16 < abs c`, `abs (bottcher' d c) ≤ 3 * abs c⁻¹`.
   In particular, `bottcher' c d → 0` as `c → ∞`
3. Iterates escape exponentially fast: if `max 3 (abs c) ≤ abs z`, `2^n * abs z ≤ abs (f c^[n] z)`
4. Iterates grow roughly as `z^d^n` for large `z`: if `max 3 (abs c) ≤ abs z`, then
   `|log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤ 4 / (d * abs z ^ (d - 1))`
5. `s.potential c z = 1/abs z + o(1/abs z)`: if `max 3 (abs c) ≤ abs z`, then
   `|s.potential c z - 1 / abs z| ≤ 12 / (d * abs z ^ (d - 1) * log (abs z))`
6. If `exp 9 ≤ abs c ≤ abs z`, then `z` is postcritical (`(c,z) ∈ s.post`)
7. If `exp 9 ≤ abs c ≤ abs z`, `s.bottcher = bottcherNear`, and thus the infinite produce holds
8. If `exp 9 ≤ abs c ≤ abs z`, `abs (s.bottcher c z - z⁻¹) ≤ 16 * (abs z)⁻¹^2`
9. `bottcher d` is monic at `∞` (has derivative 1 there)
-/

open Complex (abs)
open Filter (eventually_of_forall Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall mem_ball_self mem_ball mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
## Bounds about `exp` and such
-/

/-- `exp (2/3) ≤ 2` -/
lemma exp_two_thirds_le : exp (2/3) ≤ 2 := by
  have e : (2/3 : ℝ) = 1 * (2/3) := by norm_num
  rw [e, Real.exp_mul, ←pow_le_pow_iff_left (n := 3) (by bound) (by norm_num) (by norm_num),
    ←Real.rpow_mul_natCast (by bound), Nat.cast_ofNat, div_mul_cancel _ (by norm_num),
    Real.rpow_two]
  exact le_trans (pow_le_pow_left (by bound) Real.exp_one_lt_d9.le 2) (by norm_num)

/-- `exp 9` is very big -/
lemma le_exp_9 : 1000 ≤ exp 9 := by
  have e : (9 : ℝ) = ↑(9 : ℕ) := by norm_num
  rw [e, ←Real.exp_one_pow]
  exact le_trans (by norm_num) (pow_le_pow_left (by norm_num) Real.exp_one_gt_d9.le _)

/-- We will use this function below to produce bounds on `s.potential` approximates -/
def ene (x : ℝ) : ℝ := exp (-exp x)

/-- The derivative of `ene` -/
def dene (x : ℝ) : ℝ := -exp (x - exp x)

/-- `d ene / dx = dene` -/
lemma hasDerivAt_ene (x : ℝ) : HasDerivAt ene (dene x) x := by
  have h : HasDerivAt (fun x ↦ exp (-exp x)) (exp (-exp x) * -exp x) x :=
    HasDerivAt.exp (Real.hasDerivAt_exp x).neg
  simp only [mul_neg, ← Real.exp_add, neg_add_eq_sub] at h; exact h

/-- `d ene / dx = dene` -/
lemma deriv_ene (x : ℝ) : deriv ene x = dene x := (hasDerivAt_ene x).deriv

/-- Below we evaluate `dene x = exp (-exp x)` at a point of the form `log (log (abs z)) - k`.
    The derivative simplifies in this case. -/
lemma dene_eq (k : ℝ) {z : ℝ} (z1 : 1 < z) :
    dene (log (log z) - k) = -exp (-k) * log z * z ^ (-exp (-k)) := by
  have l0 : 0 < log z := Real.log_pos z1
  simp only [dene, sub_eq_add_neg, Real.exp_add, Real.exp_log l0, mul_comm _ (exp (-k)), ←neg_mul]
  apply congr_arg₂ _ rfl
  rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity)]

/-- This is a weak bound, but it's all we use below -/
lemma deriv_ene_le (x : ℝ) : ‖deriv ene x‖ ≤ exp (-x) := by
  rw [deriv_ene]
  simp only [Real.norm_eq_abs, abs_le]; constructor
  · rw [dene, neg_le_neg_iff, Real.exp_le_exp]
    suffices h : 2 * x ≤ exp x; linarith
    by_cases x1 : x ≤ 1
    exact le_trans (by linarith) (Real.add_one_le_exp _)
    exact le_trans (by nlinarith) (Real.quadratic_le_exp_of_nonneg (by linarith))
  · rw [dene, neg_le]
    refine (lt_trans ?_ (Real.exp_pos _)).le
    rw [neg_lt_zero]
    apply Real.exp_pos

/-!
## Effective bounds on iterates and Böttcher coordinates
-/

/-- A warmup exponential lower bound on iterates -/
theorem iter_large (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ abs z) (cz : abs c ≤ abs z) (n : ℕ) :
   2^n * abs z ≤ abs ((f' d c)^[n] z) := by
  induction' n with n h
  · simp only [Nat.zero_eq, pow_zero, one_mul, Function.iterate_zero_apply, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (f' d c)^[n] z = w; rw [hw] at h; clear hw
    have z1 : 1 ≤ abs z := le_trans (by norm_num) z3
    have d1 : 1 ≤ d := d_ge_one
    have nd : n + 1 ≤ n * d + 1 := by bound [le_mul_of_one_le_right]
    calc abs (w ^ d + c)
      _ ≥ abs (w ^ d) - abs c := by bound
      _ = abs w ^ d - abs c := by rw [Complex.abs.map_pow]
      _ ≥ (2 ^ n * abs z) ^ d - abs c := by bound
      _ = 2 ^ (n*d) * abs z ^ d - abs c := by rw [mul_pow, pow_mul]
      _ ≥ 2 ^ (n*d) * abs z ^ 2 - abs c := by bound [pow_le_pow_right z1 two_le_d]
      _ = 2 ^ (n*d) * (abs z * abs z) - abs c := by rw [pow_two]
      _ ≥ 2 ^ (n*d) * (3 * abs z) - abs c := by bound
      _ = 2 ^ (n*d) * 2 * abs z + (2 ^ (n * d) * abs z - abs c) := by ring
      _ = 2 ^ (n*d + 1) * abs z + (2 ^ (n * d) * abs z - abs c) := by rw [pow_succ']
      _ ≥ 2 ^ (n + 1) * abs z + (1 * abs z - abs c) := by bound [pow_le_pow_right]
      _ = 2 ^ (n + 1) * abs z + (abs z - abs c) := by rw [one_mul]
      _ ≥ 2 ^ (n + 1) * abs z := by bound

/-- Iterates tend to infinity for large `z` -/
theorem tendsto_iter_atInf (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ abs z) (cz : abs c ≤ abs z) :
    Tendsto (fun n ↦ (f' d c)^[n] z) atTop atInf := by
  simp only [tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs]
  refine' Filter.tendsto_atTop_mono (iter_large d z3 cz) _
  exact Filter.Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Large iterates are `≠ 0` -/
lemma f_ne_zero {c z : ℂ} (cz : abs c ≤ abs z) (z3 : 3 ≤ abs z) : z^d + c ≠ 0 := by
  rw [← Complex.abs.ne_zero_iff]; apply ne_of_gt
  have z1 : 1 ≤ abs z := le_trans (by norm_num) z3
  calc abs (z ^ d + c)
    _ ≥ abs (z ^ d) - abs c := by bound
    _ = abs z ^ d - abs c := by rw [Complex.abs.map_pow]
    _ ≥ abs z ^ 2 - abs z := by bound [pow_le_pow_right _ two_le_d]
    _ = abs z * (abs z - 1) := by ring
    _ ≥ 3 * (3 - 1) := by bound
    _ > 0 := by norm_num

/-- The approximate change of `log (log (abs z))` across one iterate -/
theorem f_approx {c z : ℂ} (z3 : 3 ≤ abs z) (cz : abs c ≤ abs z) :
    |log (log (abs (z ^ d + c))) - log (log (abs z)) - log d| ≤ 2 / ↑d / abs z ^ (d - 1) := by
  have dp : 0 < d := d_pos
  have d0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr d_ne_zero
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have z1 : 1 ≤ abs z := le_trans (by norm_num) z3
  have z0' : 0 < abs z := lt_of_lt_of_le (by norm_num) z3
  have zd : 3 ≤ abs z ^ (d - 1) := by
    calc abs z ^ (d - 1)
      _ ≥ 3 ^ (d - 1) := by bound [pow_right_mono z1]
      _ ≥ 3 ^ 1 := by bound [pow_le_pow_right _ d_minus_one_ge_one]
      _ = 3 := by norm_num
  have z0 : z ≠ 0 := Complex.abs.ne_zero_iff.mp (z0'.ne')
  have zd0 : z ^ d ≠ 0 := pow_ne_zero _ z0
  have zc0 : z ^ d + c ≠ 0 := f_ne_zero cz z3
  have cz : abs (c / z ^ d) ≤ 1 / abs z ^ (d - 1) := by
    have d1 : z^d = z^(d - 1 + 1) := by rw [Nat.sub_add_cancel d_ge_one]
    simp only [d1, map_div₀, Complex.abs.map_pow, pow_succ, Complex.abs.map_mul, div_mul_eq_div_div]
    bound
  have czs : abs (c / z ^ d) ≤ 1 / 3 := le_trans cz (by bound)
  have l0s : 1 ≤ log (abs z) := by
    rw [Real.le_log_iff_exp_le z0']; exact le_trans Real.exp_one_lt_3.le z3
  have l0 : 0 < log (abs z) := by positivity
  have l1 : 0 < ↑d * log (abs z) := by bound
  have l2 : |log (abs (1 + c / z ^ d))| ≤ 3/2 / abs z ^ (d - 1) := by
    nth_rw 1 [← Complex.log_re]
    refine le_trans (Complex.abs_re_le_abs _) (le_trans (log1p_small' (by norm_num) czs) ?_)
    calc 1 / (1 - 1/3) * abs (c / z ^ d)
      _ = 3/2 * abs (c / z ^ d) := by norm_num
      _ ≤ 3/2 * (1 / abs z ^ (d - 1)) := by gcongr
      _ = 3/2 / abs z ^ (d - 1) := by rw [← mul_div_assoc, mul_one]
  have l3 : 0 < ↑d * log (abs z) + log (abs (1 + c / z ^ d)) := by
    suffices h : -log (abs (1 + c / z ^ d)) < ↑d * log (abs z); linarith
    apply lt_of_le_of_lt (neg_le_neg_iff.mpr (abs_le.mp l2).1); simp only [neg_neg]
    trans (1 : ℝ)
    · calc 3/2 / abs z ^ (d - 1)
        _ ≤ 3/2 / 3 := by bound
        _ < 1 := by norm_num
    · calc ↑d * log (abs z)
        _ ≥ 2 * 1 := by bound
        _ > 1 := by norm_num
  rw [log_abs_add (z ^ d) c zd0 zc0, Complex.abs.map_pow, Real.log_pow, log_add _ _ l1 l3,
    Real.log_mul (Nat.cast_ne_zero.mpr d_ne_zero) l0.ne']
  generalize hw : log (1 + log (abs (1 + c / z ^ d)) / (d * log (abs z))) = w
  ring_nf; rw [← hw]; clear hw w
  have inner : |log (abs (1 + c / z ^ d)) / (d * log (abs z))| ≤ 3/2 / d / abs z ^ (d - 1) := by
    simp only [abs_div, abs_of_pos l1, div_le_iff l1]; apply le_trans l2
    generalize ht : (3/2 : ℝ) = t
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm _ (d:ℝ),
      mul_comm _ (d:ℝ)⁻¹, ← mul_assoc, ← mul_assoc, mul_inv_cancel d0, one_mul]
    refine le_mul_of_one_le_right ?_ l0s
    rw [←ht]; bound
  have weak : 3/2 / ↑d / abs z ^ (d - 1) ≤ 1 / 4 := by
    calc 3/2 / ↑d / abs z ^ (d - 1)
      _ ≤ 3/2 / 2 / 3 := by bound
      _ = 1 / 4 := by norm_num
  apply le_trans (Real.log1p_small' (by norm_num) (le_trans inner weak))
  generalize log (abs (1 + c / z^d)) / (d * log (abs z)) = w at inner
  simp only [div_eq_mul_inv, ←inv_pow, mul_assoc] at inner
  simp only [mul_comm _ (2 : ℝ)]
  generalize (d : ℝ)⁻¹ * (abs z)⁻¹ ^ (d-1) = u at inner
  simp only [←mul_assoc] at inner
  norm_num at inner ⊢
  linarith

/-- Absolute values of iterates grow roughly as `z^d^n` for large `z` -/
theorem iter_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ abs z) (cz : abs c ≤ abs z) (n : ℕ) :
    |log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤
      4 / (d * abs z ^ (d - 1)) := by
  have z0 : 0 < abs z := lt_of_lt_of_le (by linarith) z3
  have d0 : 0 < d := d_pos
  have d1' : 0 < d-1 := d_minus_one_pos
  -- Strengthen to get something we can prove by induction
  suffices h : |log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤
      4 * (1 - (1 / 2 : ℝ) ^ n) / (d * abs z ^ (d - 1)) by
    apply le_trans h; rw [div_le_div_right]
    · bound
    · bound
  induction' n with n h
  · simp only [Function.iterate_zero_apply, sub_self, Nat.cast_zero, MulZeroClass.zero_mul,
      abs_zero, pow_zero, zero_div, MulZeroClass.mul_zero, le_refl]
  -- Generalize away the iteration
  simp only [Function.iterate_succ_apply', Nat.cast_succ, right_distrib, one_mul,
    sub_add_eq_sub_sub _ _ (log d), ← sub_add_eq_sub_sub _ _ (↑n * log d)]
  generalize hw : (f' d c)^[n] z = w
  generalize hb : log (log (abs z)) + n * log d = b
  have rw : 2 ^ n * abs z ≤ abs w := by
    trans 2 ^ n * abs z; bound; rw [← hw]; exact iter_large d z3 cz n
  rw [← sub_add_eq_sub_sub, hw, hb] at h; clear hw hb
  have zw : abs z ≤ abs w := by
    refine le_trans ?_ rw; bound [le_mul_of_one_le_left, one_le_pow_of_one_le]
  have cw : abs c ≤ abs w := le_trans cz zw
  -- Do the main calculation
  have e : log (log (abs (w ^ d + c))) - b - log d =
      log (log (abs (w ^ d + c))) - log (log (abs w)) - log d + (log (log (abs w)) - b) := by abel
  rw [f', e]
  refine le_trans (abs_add _ _) (le_trans (add_le_add (f_approx (le_trans z3 zw) cw) h) ?_)
  clear e h
  rw [← div_mul_eq_div_div, ← le_sub_iff_add_le, ← sub_div, ← mul_sub, ← sub_add,
    sub_sub_cancel_left, neg_add_eq_sub, pow_succ, ← one_sub_mul, sub_half, ← mul_assoc,
    (by norm_num : (4 : ℝ) * (1 / 2) = 2), div_pow, one_pow, ← mul_div_assoc, mul_one, ←
    div_mul_eq_div_div, ← mul_assoc, mul_comm _ (d:ℝ), mul_assoc (d:ℝ) _ _]
  refine div_le_div_of_le_left (by norm_num) (by bound) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by bound)
  calc abs w ^ (d - 1)
    _ ≥ (2 ^ n * abs z) ^ (d - 1) := by bound
    _ = (2 ^ n) ^ (d - 1) * abs z ^ (d - 1) := by rw [mul_pow]
    _ ≥ 2 ^ n * abs z ^ (d - 1) := by bound [one_le_pow_of_one_le]

/-- `s.bottcher c z ~ 1/z` for large `z` -/
theorem bottcher_large_approx (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).bottcher c z * z) atInf (𝓝 1) := by
  set s := superF d
  have e : ∀ᶠ z : ℂ in atInf, s.bottcher c z * z = s.bottcherNear c z * z := by
    suffices e : ∀ᶠ z : ℂ in atInf, s.bottcher c z = s.bottcherNear c z
    exact e.mp (eventually_of_forall fun z e ↦ by rw [e])
    refine coe_tendsto_inf.eventually (p := fun z ↦ s.bottcher c z = s.bottcherNear c z) ?_
    apply s.bottcher_eq_bottcherNear
  rw [Filter.tendsto_congr' e]; clear e
  have m := bottcherNear_monic (s.superNearC.s (mem_univ c))
  simp only [hasDerivAt_iff_tendsto, sub_zero, bottcherNear_zero, smul_eq_mul, mul_one,
    Metric.tendsto_nhds_nhds, Real.dist_eq, Complex.norm_eq_abs, Complex.dist_eq, abs_mul,
    abs_of_nonneg (Complex.abs.nonneg _), abs_inv] at m
  simp only [Metric.tendsto_nhds, atInf_basis.eventually_iff, true_and_iff, mem_setOf,
    Complex.dist_eq, Complex.norm_eq_abs]
  intro e ep; rcases m e ep with ⟨r, rp, h⟩; use 1 / r; intro z zr
  have az0 : abs z ≠ 0 := (lt_trans (one_div_pos.mpr rp) zr).ne'
  have z0 : z ≠ 0 := Complex.abs.ne_zero_iff.mp az0
  have zir : abs (z⁻¹) < r := by
    simp only [one_div, map_inv₀] at zr ⊢; exact inv_lt_of_inv_lt rp zr
  specialize @h z⁻¹ zir
  simp only [map_inv₀, inv_inv, ← Complex.abs.map_mul, sub_mul, inv_mul_cancel z0,
    mul_comm z _] at h
  simp only [Super.bottcherNear, extChartAt_inf, PartialEquiv.trans_apply,
    coePartialEquiv_symm_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, RiemannSphere.inv_inf,
    toComplex_zero, sub_zero, inv_coe z0, toComplex_coe]
  exact h

/-- `s.potential c z ~ 1/abs z` for large `z` -/
theorem potential_tendsto (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).potential c z * abs z) atInf (𝓝 1) := by
  set s := superF d
  simp only [← s.abs_bottcher, ← Complex.abs.map_mul, ← Complex.abs.map_one]
  exact Complex.continuous_abs.continuousAt.tendsto.comp (bottcher_large_approx d c)

/-- `potential` is the limit of roots of iterates -/
theorem tendsto_potential (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ abs z) (cz : abs c ≤ abs z) :
    Tendsto (fun n ↦ abs ((f' d c)^[n] z) ^ (-((d ^ n : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 ((superF d).potential c z)) := by
  set s := superF d
  have p0 : s.potential c z ≠ 0 := by rw [s.potential_ne_zero]; exact coe_ne_inf
  suffices h : Tendsto (fun n ↦ (abs ((f' d c)^[n] z) *
      s.potential c ↑((f' d c)^[n] z)) ^ (-((d ^ n : ℕ) : ℝ)⁻¹))
      atTop (𝓝 1) by
    replace h := h.mul_const (s.potential c z)
    simp only [div_mul_cancel _ p0, one_mul, ← f_f'_iter, s.potential_eqn_iter,
      Real.mul_rpow (Complex.abs.nonneg _) (pow_nonneg s.potential_nonneg _),
      Real.pow_rpow_inv_natCast s.potential_nonneg (pow_ne_zero _ d_ne_zero),
      Real.rpow_neg (pow_nonneg s.potential_nonneg _), ← div_eq_mul_inv] at h
    exact h
  simp only [← s.abs_bottcher, ← Complex.abs.map_mul, mul_comm _ (s.bottcher _ _)]
  rw [Metric.tendsto_atTop]; intro r rp
  rcases Metric.tendsto_atTop.mp ((bottcher_large_approx d c).comp (tendsto_iter_atInf d z3 cz))
      (min (1 / 2) (r / 4)) (by bound) with ⟨n, h⟩
  use n; intro k nk; specialize h k nk
  generalize hw : (f' d c)^[k] z = w; generalize hp : s.bottcher c w * w = p
  simp only [hw, hp, Function.comp, Complex.dist_eq, Real.dist_eq] at h ⊢
  clear hp w hw nk n p0 s cz z3 z c
  generalize ha : abs p = a
  generalize hb : ((d ^ k : ℕ) : ℝ)⁻¹ = b
  have a1 : |a - 1| < min (1 / 2) (r / 4) := by
    rw [← ha]; refine lt_of_le_of_lt ?_ h
    rw [← Complex.abs.map_one]; apply Complex.abs.abs_abv_sub_le_abv_sub
  have am : a ∈ ball (1 : ℝ) (1 / 2) := by
    simp only [mem_ball, Real.dist_eq]; exact (lt_min_iff.mp a1).1
  have b0 : 0 ≤ b := by rw [← hb]; bound
  have b1 : b ≤ 1 := by
    rw [← hb]; exact inv_le_one (Nat.one_le_cast.mpr (one_le_pow_of_one_le d_ge_one _))
  have hd : ∀ x, x ∈ ball (1 : ℝ) (1 / 2) →
      HasDerivAt (fun x ↦ x ^ (-b)) (1 * -b * x ^ (-b - 1) + 0 * x ^ (-b) * log x) x := by
    intro x m; apply HasDerivAt.rpow (hasDerivAt_id _) (hasDerivAt_const _ _)
    simp only [mem_ball, Real.dist_eq, id] at m ⊢; linarith [abs_lt.mp m]
  simp only [MulZeroClass.zero_mul, add_zero, one_mul] at hd
  have bound : ∀ x, x ∈ ball (1 : ℝ) (1 / 2) → ‖deriv (fun x ↦ x ^ (-b)) x‖ ≤ 4 := by
    intro x m
    simp only [(hd x m).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg b0]
    simp only [mem_ball, Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add] at m
    norm_num at m
    have x0 : 0 < x := by linarith
    calc b * |x ^ (-b - 1)|
      _ ≤ 1 * |x| ^ (-b - 1) := by bound [Real.abs_rpow_le_abs_rpow]
      _ = (x ^ (b + 1))⁻¹ := by rw [← Real.rpow_neg x0.le, neg_add', one_mul, abs_of_pos x0]
      _ ≤ ((1 / 2 : ℝ) ^ (b + 1))⁻¹ := by bound [m.1.le]
      _ = 2 ^ (b + 1) := by rw [one_div, Real.inv_rpow zero_le_two, inv_inv]
      _ ≤ 2 ^ (1 + 1 : ℝ) := by bound [Real.rpow_le_rpow_of_exponent_le]
      _ ≤ 4 := by norm_num
  have le := Convex.norm_image_sub_le_of_norm_deriv_le (fun x m ↦ (hd x m).differentiableAt) bound
      (convex_ball _ _) (mem_ball_self (by norm_num)) am
  simp only [Real.norm_eq_abs, Real.one_rpow] at le
  calc |a ^ (-b) - 1|
    _ ≤ 4 * |a - 1| := le
    _ < 4 * (r / 4) := by linarith [(lt_min_iff.mp a1).2]
    _ = r := by ring

/-- `s.potential = 1/abs z + o(1/abs z)` -/
theorem potential_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ abs z) (cz : abs c ≤ abs z) :
    |(superF d).potential c z - 1 / abs z| ≤ 8 / (↑d * abs z ^ (d - 1) * log (abs z)) := by
  have d0 : 0 < d := d_pos
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have z0 : 0 < abs z := lt_of_lt_of_le (by norm_num) z3
  have z1 : 1 < abs z := lt_of_lt_of_le (by norm_num) z3
  have l2 : 0 < log (abs z) := Real.log_pos (by linarith)
  set s := superF d
  generalize hb : 8 / (↑d * abs z ^ (d - 1) * log (abs z)) = b
  -- Swap out potential for an iterate approximate
  suffices h : ∀ᶠ n in atTop, |abs ((f' d c)^[n] z) ^ (-((d ^ n : ℕ) : ℝ)⁻¹) - 1 / abs z| ≤ b
  · apply le_of_forall_pos_lt_add; intro e ep
    rcases(h.and (Metric.tendsto_nhds.mp (tendsto_potential d z3 cz) e ep)).exists with ⟨n, h, t⟩
    generalize hw : abs ((f' d c)^[n] z) ^ (-((d ^ n : ℕ) : ℝ)⁻¹) = w; rw [hw] at h t
    rw [Real.dist_eq, abs_sub_comm] at t; rw [add_comm]
    calc |s.potential c z - 1 / abs z|
      _ ≤ |s.potential c z - w| + |w - 1 / abs z| := abs_sub_le _ _ _
      _ < e + _ := add_lt_add_of_lt_of_le t h
  -- iter_approx does the rest
  apply eventually_of_forall
  intro n
  generalize hi : ((d ^ n : ℕ) : ℝ)⁻¹ = i
  have dn0 : 0 < ((d ^ n : ℕ) : ℝ) := Nat.cast_pos.mpr (pow_pos d_pos n)
  have i0 : 0 < i := by rw [← hi]; exact inv_pos.mpr dn0
  have f1 : 1 < abs ((f' d c)^[n] z) :=
    lt_of_lt_of_le (one_lt_mul (one_le_pow_of_one_le one_le_two _) z1) (iter_large d z3 cz n)
  have f0 : 0 < abs ((f' d c)^[n] z) := lt_trans zero_lt_one f1
  have l0 : 0 < log (abs ((f' d c)^[n] z)) := Real.log_pos f1
  have l1 : 0 < log (abs ((f' d c)^[n] z) ^ i) := by rw [Real.log_rpow f0]; bound
  have f1 : 0 < abs ((f' d c)^[n] z) ^ i := Real.rpow_pos_of_pos f0 i
  have h := iter_approx d z3 cz n
  rw [sub_sub, add_comm, ← sub_sub, ← Real.log_pow _ n, ← Nat.cast_pow, ←
    Real.log_div l0.ne' dn0.ne', div_eq_mul_inv, mul_comm, ← Real.log_rpow f0, hi] at h
  generalize hr : 4 / (↑d * abs z ^ (d - 1)) = r; rw [hr] at h
  have r0 : 0 < r := by rw [← hr]; bound
  have r1 : r ≤ 2/3 := by
    rw [← hr, div_le_iff]; swap; bound
    calc 2/3 * (↑d * abs z ^ (d - 1))
      _ ≥ 2/3 * (2 * 3 ^ (d - 1)) := by bound
      _ ≥ 2/3 * (2 * 3) := by bound [le_self_pow _ (d_minus_one_pos : 0 < d - 1).ne']
      _ = 4 := by norm_num
  set t := closedBall (log (log (abs z))) r
  have yt : log (log (abs ((f' d c)^[n] z) ^ i)) ∈ t := by
    simp only [mem_closedBall, Real.dist_eq, h]
  have bound : ∀ x, x ∈ t → ‖deriv ene x‖ ≤ 2 / log (abs z) := by
    intro x m; simp only [mem_closedBall, Real.dist_eq] at m
    replace m : -x ≤ 2/3 - log (log (abs z)) := by linarith [(abs_le.mp m).1]
    refine le_trans (deriv_ene_le _) (le_trans (Real.exp_le_exp.mpr m) ?_)
    simp only [Real.exp_sub, Real.exp_log l2]; bound [exp_two_thirds_le, l2]
  have m :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ ↦ (hasDerivAt_ene x).differentiableAt) bound (convex_closedBall _ _)
      (mem_closedBall_self r0.le) yt
  simp only [Real.norm_eq_abs] at m
  replace m := le_trans m (mul_le_mul_of_nonneg_left h (by bound))
  simp only [ene, Real.exp_log l1, Real.exp_log l2, Real.exp_neg, Real.exp_log z0, Real.exp_log f1,
    ←Real.rpow_neg f0.le] at m
  rw [one_div]; refine le_trans m (le_of_eq ?_)
  rw [← hr, ← hb]; field_simp [l2.ne', z0.ne']; ring_nf

/-- For large `c`, large `z`'s are postcritical -/
theorem largePost {c z : ℂ} (c9 : exp 9 ≤ abs c) (cz : abs c ≤ abs z) :
    Postcritical (superF d) c z := by
  have d0 : 0 < d := d_pos
  have d1 : 0 < d-1 := d_minus_one_pos
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have c1000 : 1000 ≤ abs c := le_trans le_exp_9 c9
  have c3 : 3 ≤ abs c := le_trans (by norm_num) c1000
  have c4 : 4 ≤ abs c := le_trans (by norm_num) c1000
  have c0 : 0 < abs c := by linarith
  have z3 : 3 ≤ abs z := le_trans (by norm_num) (le_trans c4 cz)
  have lc9 : 9 ≤ log (abs c) := (Real.le_log_iff_exp_le c0).mpr c9
  have lc : 0 < log (abs c) := lt_of_lt_of_le (by norm_num) lc9
  simp only [Postcritical, multibrot_p]
  set s := superF d
  rw [← Real.pow_rpow_inv_natCast s.potential_nonneg d0.ne', ←
    Real.pow_rpow_inv_natCast (s.potential_nonneg : 0 ≤ s.potential c 0) d0.ne']
  simp only [← s.potential_eqn]
  refine Real.rpow_lt_rpow s.potential_nonneg ?_ (by bound)
  generalize hw : f' d c z = w
  have e : f d c z = w := by rw [f, lift_coe', hw]
  simp only [f_0, e]; clear e
  have zw2 : 999 * abs z ≤ abs w := by
    simp only [← hw, f']
    have z1 : 1 ≤ abs z := by linarith
    calc abs (z ^ d + c)
      _ ≥ abs (z ^ d) - abs c := by bound
      _ = abs z ^ d - abs c := by rw [Complex.abs.map_pow]
      _ ≥ abs z ^ 2 - abs c := by bound [pow_le_pow_right z1 two_le_d]
      _ ≥ abs z ^ 2 - abs z := by bound
      _ = abs z * abs z - abs z := by rw [pow_two]
      _ ≥ 1000 * abs z - abs z := by bound [le_trans c1000 cz]
      _ = 999 * abs z := by ring
  have cw2 : 999 * abs c ≤ abs w := le_trans (mul_le_mul_of_nonneg_left cz (by norm_num)) zw2
  have zw : abs z ≤ abs w := le_trans (by linarith) zw2
  have cw : abs c ≤ abs w := le_trans cz zw
  have w3 : 3 ≤ abs w := le_trans z3 zw
  have lcw : log (abs c) ≤ log (abs w) := (Real.log_le_log_iff c0 (lt_of_lt_of_le c0 cw)).mpr cw
  have pw := sub_le_iff_le_add.mp (abs_le.mp (potential_approx d w3 cw)).2
  have pc := le_sub_iff_add_le.mp (abs_le.mp (potential_approx d c3 (le_refl _))).1
  refine lt_of_le_of_lt pw (lt_of_lt_of_le ?_ pc)
  generalize hkc : 8 / (↑d * abs c ^ (d - 1) * log (abs c)) = kc
  generalize hkw : 8 / (↑d * abs w ^ (d - 1) * log (abs w)) = kw
  rw [neg_add_eq_sub, lt_sub_iff_add_lt, add_comm _ kc, ← add_assoc]
  have kcw : kw ≤ kc := by rw [← hkc, ← hkw]; bound
  have kcc : kc ≤ 1 / (9 / 4 * abs c) := by
    rw [← hkc]
    have c1 : 1 ≤ abs c := le_trans (by norm_num) c3
    calc 8 / (↑d * abs c ^ (d - 1) * log (abs c))
      _ ≤ 8 / (2 * abs c * 9) := by bound
      _ = 8 / (9 * 2) / abs c := by rw [mul_comm _ (9 : ℝ), ← mul_assoc, ← div_div]
      _ = 1 / (9 / 4) / abs c := by norm_num
      _ = 1 / (9 / 4 * abs c) := by rw [div_div]
  calc kc + kw + 1 / abs w
    _ ≤ kc + kc + 1 / (999 * abs c) := by bound
    _ = 2 * kc + 1 / (999 * abs c) := by ring
    _ ≤ 2 * (1 / (9 / 4 * abs c)) + 1 / (999 * abs c) := by linarith
    _ = 2 / (9 / 4) / abs c + 1 / 999 / abs c := by field_simp
    _ = (2 / (9 / 4) + 1 / 999) / abs c := by ring
    _ < 1 / abs c := (div_lt_div_right c0).mpr (by norm_num)

/-- `s.bottcher = bottcherNear` for large `c,z`.
    This means that `s.bottcher` is given by the infinite product formula from `BottcherNear.lean`
    for large `c,z`. -/
theorem bottcher_eq_bottcherNear_z {c z : ℂ} (c9 : exp 9 ≤ abs c) (cz : abs c ≤ abs z) :
    (superF d).bottcher c z = bottcherNear (fl (f d) ∞ c) d z⁻¹ := by
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (le_trans le_exp_9 c9)
  have c0 : 0 < abs c := lt_trans (by norm_num) c16
  have z0 : 0 < abs z := lt_of_lt_of_le c0 cz
  set s := superF d
  set t := closedBall (0 : ℂ) (abs c)⁻¹
  suffices e : EqOn (fun z : ℂ ↦ s.bottcher c (z : 𝕊)⁻¹) (bottcherNear (fl (f d) ∞ c) d) t
  · have z0' : z ≠ 0 := Complex.abs.ne_zero_iff.mp z0.ne'
    convert @e z⁻¹ _; rw [inv_coe (inv_ne_zero z0'), inv_inv]
    simp only [mem_closedBall, Complex.dist_eq, sub_zero, map_inv₀, inv_le_inv z0 c0, cz]
  have a0 : HolomorphicOn I I (fun z : ℂ ↦ s.bottcher c (z : 𝕊)⁻¹) t := by
    intro z m
    refine' (s.bottcher_holomorphicOn _ _).along_snd.comp (holomorphic_inv.comp holomorphic_coe _)
    simp only [mem_closedBall, Complex.dist_eq, sub_zero] at m
    by_cases z0 : z = 0; simp only [z0, coe_zero, inv_zero']; exact s.post_a c
    rw [inv_coe z0]; apply largePost c9
    rwa [map_inv₀, le_inv c0]; exact Complex.abs.pos z0
  have a1 : HolomorphicOn I I (bottcherNear (fl (f d) ∞ c) d) t := by
    intro z m; apply AnalyticAt.holomorphicAt
    apply bottcherNear_analytic_z (superNearF d c)
    simp only [mem_setOf, mem_closedBall, Complex.dist_eq, sub_zero] at m ⊢
    refine' lt_of_le_of_lt m _
    refine' inv_lt_inv_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _
    exact max_lt c16 (half_lt_self (lt_trans (by norm_num) c16))
  refine' (a0.eq_of_locally_eq a1 (convex_closedBall _ _).isPreconnected _).self_of_nhdsSet
  use 0, mem_closedBall_self (by bound)
  have e : ∀ᶠ z in 𝓝 0, bottcherNear (fl (f d) ∞ c) d z = s.bottcherNear c (z : 𝕊)⁻¹ := by
    simp only [Super.bottcherNear, extChartAt_inf_apply, inv_inv, toComplex_coe,
      RiemannSphere.inv_inf, toComplex_zero, sub_zero, Super.fl, eq_self_iff_true,
      Filter.eventually_true]
  refine' Filter.EventuallyEq.trans _ (Filter.EventuallyEq.symm e)
  have i : Tendsto (fun z : ℂ ↦ (z : 𝕊)⁻¹) (𝓝 0) (𝓝 ∞) := by
    have h : ContinuousAt (fun z : ℂ ↦ (z : 𝕊)⁻¹) 0 :=
      (RiemannSphere.continuous_inv.comp continuous_coe).continuousAt
    simp only [ContinuousAt, coe_zero, inv_zero'] at h; exact h
  exact i.eventually (s.bottcher_eq_bottcherNear c)

/-- `bottcher' = bottcherNear` for large `c` -/
theorem bottcher_eq_bottcherNear {c : ℂ} (c9 : exp 9 ≤ abs c) :
    bottcher' d c = bottcherNear (fl (f d) ∞ c) d c⁻¹ :=
  bottcher_eq_bottcherNear_z c9 (le_refl _)

/-- `z⁻¹` is in the `superNearC` region for large `c,z` -/
theorem inv_mem_t {c z : ℂ} (c16 : 16 < abs c) (cz : abs c ≤ abs z) :
    z⁻¹ ∈ {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹} := by
  simp only [mem_setOf, map_inv₀]
  refine' inv_lt_inv_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _
  exact lt_of_lt_of_le (max_lt c16 (half_lt_self (lt_trans (by norm_num) c16))) cz

/-- Terms in the `bottcherNear` product are close to 1 -/
theorem term_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c9 : exp 9 ≤ abs c) (cz : abs c ≤ abs z)
    (n : ℕ) : abs (term (fl (f d) ∞ c) d n z⁻¹ - 1) ≤ 2 * (1 / 2 : ℝ) ^ n * (abs z)⁻¹ := by
  set s := superF d
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (le_trans le_exp_9 c9)
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have z0 : abs z ≠ 0 := (lt_of_lt_of_le (lt_trans (by norm_num) c16) cz).ne'
  have i8 : (abs z)⁻¹ ≤ 1 / 8 := by
    rw [one_div]; apply inv_le_inv_of_le; norm_num
    exact le_trans (by norm_num) (le_trans c16.le cz)
  have i1 : (abs z)⁻¹ ≤ 1 := le_trans i8 (by norm_num)
  simp only [term]
  have wc := iterates_converge (superNearF d c) n (inv_mem_t c16 cz)
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w; rw [hw] at wc
  replace wc : abs w ≤ (abs z)⁻¹
  · rw [map_inv₀] at wc
    exact le_trans wc (mul_le_of_le_one_left (inv_nonneg.mpr (Complex.abs.nonneg _)) (by bound))
  have cw : abs (c * w ^ d) ≤ (abs z)⁻¹ := by
    simp only [Complex.abs.map_mul, Complex.abs.map_pow]
    calc abs c * abs w ^ d
      _ ≤ abs z * (abs z)⁻¹ ^ d := by bound
      _ ≤ abs z * (abs z)⁻¹ ^ 2 := by bound [pow_le_pow_of_le_one, (two_le_d : 2 ≤ d)]
      _ = (abs z)⁻¹ := by rw [pow_two]; field_simp [z0]
  have cw2 : abs (c * w ^ d) ≤ 1 / 2 := le_trans cw (le_trans i8 (by norm_num))
  simp only [gl_f, gl]; rw [Complex.inv_cpow, ← Complex.cpow_neg]; swap
  · refine (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt ?_ (half_lt_self Real.pi_pos))).ne
    rw [Complex.abs_arg_le_pi_div_two_iff, Complex.add_re, Complex.one_re]
    calc 1 + (c * w ^ d).re
      _ ≥ 1 + -|(c * w ^ d).re| := by bound [neg_abs_le_self]
      _ = 1 - |(c * w ^ d).re| := by ring
      _ ≥ 1 - abs (c * w ^ d) := by bound [Complex.abs_re_le_abs]
      _ ≥ 1 - 1 / 2 := by linarith
      _ ≥ 0 := by norm_num
  · have dn : abs (-(1 / ((d ^ (n + 1) : ℕ) : ℂ))) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      simp only [Nat.cast_pow, one_div, map_neg_eq_map, map_inv₀, map_pow, Complex.abs_natCast,
        inv_pow]
      bound
    have d1 : abs (-(1 / ((d ^ (n + 1) : ℕ) : ℂ))) ≤ 1 := le_trans dn (by bound)
    refine le_trans (pow_small ?_ d1) ?_
    · rw [add_sub_cancel']; exact cw2
    · rw [add_sub_cancel']
      calc 4 * abs (c * w ^ d) * abs (-(1 / ((d ^ (n + 1) : ℕ) : ℂ)))
        _ ≤ 4 * (abs z)⁻¹ * (1/2 : ℝ) ^ (n + 1) := by bound
        _ ≤ 2 * (1/2 : ℝ) ^ n * (abs z)⁻¹ := by
          simp only [pow_succ, ←mul_assoc, mul_comm _ (1/2:ℝ)]; norm_num
          simp only [mul_comm _ ((2:ℝ)^n)⁻¹, ←mul_assoc, le_refl]

/-- `s.bottcher c z = z⁻¹ + O(z⁻¹^2)` -/
theorem bottcher_approx_z (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c9 : exp 9 ≤ abs c)
    (cz : abs c ≤ abs z) : abs ((superF d).bottcher c z - z⁻¹) ≤ (16:ℝ) * (abs z)⁻¹ ^ 2 := by
  set s := superF d
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (le_trans le_exp_9 c9)
  have i8 : (abs z)⁻¹ ≤ 1 / 8 := by
    rw [one_div]; apply inv_le_inv_of_le; norm_num
    exact le_trans (by norm_num) (le_trans c16.le cz)
  simp only [bottcher_eq_bottcherNear_z c9 cz, bottcherNear, Complex.abs.map_mul, ← mul_sub_one,
    pow_two, ← mul_assoc, map_inv₀, mul_comm (abs z)⁻¹]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Complex.abs.nonneg _))
  rcases term_prod_exists (superNearF d c) _ (inv_mem_t c16 cz) with ⟨p, h⟩
  rw [h.tprod_eq]; simp only [HasProd] at h
  apply le_of_tendsto' (Filter.Tendsto.comp Complex.continuous_abs.continuousAt (h.sub_const 1))
  clear h; intro A; simp only [Function.comp]
  rw [(by norm_num : (16 : ℝ) = 4 * 4), mul_assoc]
  refine dist_prod_one_le_abs_sum ?_ (by linarith)
  refine le_trans (Finset.sum_le_sum fun n _ ↦ term_approx d c9 cz n) ?_
  simp only [mul_comm _ _⁻¹, ← mul_assoc, ← Finset.mul_sum]
  calc (abs z)⁻¹ * 2 * A.sum (fun n ↦ (1/2:ℝ)^n)
    _ ≤ (abs z)⁻¹ * 2 * (1 - 1 / 2)⁻¹ := by bound [partial_geometric_bound]
    _ = (abs z)⁻¹ * 4 := by ring

/-- `bottcher' d c = c⁻¹ + O(c⁻¹^2)` -/
theorem bottcher_approx (d : ℕ) [Fact (2 ≤ d)] {c : ℂ} (c9 : exp 9 ≤ abs c) :
    abs (bottcher' d c - c⁻¹) ≤ 16 * (abs c)⁻¹ ^ 2 :=
  bottcher_approx_z d c9 (le_refl _)

/-- bottcher is monic at `∞` (has derivative 1) -/
theorem bottcher_hasDerivAt_one : HasDerivAt (fun z : ℂ ↦ bottcher d (↑z)⁻¹) 1 0 := by
  rw [HasDerivAt, HasDerivAtFilter, bottcher, hasFDerivAtFilter_iff_isLittleO, coe_zero, inv_zero',
    fill_inf]
  simp only [sub_zero, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, mul_one]
  rw [Asymptotics.isLittleO_iff]
  intro k k0; rw [Metric.eventually_nhds_iff]
  refine ⟨min (exp 9)⁻¹ (k / 16), by bound, ?_⟩; intro z le
  simp only [Complex.dist_eq, sub_zero, lt_min_iff] at le; simp only [Complex.norm_eq_abs]
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', fill_inf, sub_zero, Complex.abs.map_zero,
      MulZeroClass.mul_zero, le_refl]
  simp only [inv_coe z0, fill_coe]
  have b : abs (bottcher' d z⁻¹ - z⁻¹⁻¹) ≤ (16:ℝ) * (abs z⁻¹)⁻¹ ^ 2 := bottcher_approx d ?_
  · simp only [inv_inv] at b; apply le_trans b
    simp only [map_inv₀, inv_inv, pow_two, ← mul_assoc]
    refine' mul_le_mul_of_nonneg_right _ (Complex.abs.nonneg _)
    calc 16 * abs z
      _ ≤ 16 * (k / 16) := by linarith [le.2]
      _ = k := by ring
  · rw [map_inv₀, le_inv (Real.exp_pos _) (Complex.abs.pos z0)]; exact le.1.le

/-- bottcher is nonsingular at `∞` -/
theorem bottcher_mfderiv_inf_ne_zero : mfderiv I I (bottcher d) ∞ ≠ 0 := by
  simp only [mfderiv, (bottcherHolomorphic d _ multibrotExt_inf).mdifferentiableAt, if_pos,
    writtenInExtChartAt, bottcher_inf, extChartAt_inf, extChartAt_eq_refl, Function.comp,
    PartialEquiv.refl_coe, id, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, invEquiv_apply,
    RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, PartialEquiv.coe_trans_symm,
    PartialEquiv.symm_symm, coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm,
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  rw [bottcher_hasDerivAt_one.hasFDerivAt.fderiv]
  rw [Ne.def, ContinuousLinearMap.ext_iff, not_forall]; use 1
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    Algebra.id.smul_eq_mul, mul_one, ContinuousLinearMap.zero_apply]
  convert one_ne_zero; exact NeZero.one
