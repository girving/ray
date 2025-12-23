module
public import Ray.Multibrot.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Ray.Dynamics.Potential
import Ray.Multibrot.Basic
import Ray.Multibrot.Iterates
import Ray.Multibrot.Specific

/-!
## Effective bounds on the Multibrot `potential` function

We derive effective estimates for `log (-log potential)` and `potential`, building only
the iterate growth rate estimates in `Iterates.lean`:

1. `log (-log (s.potential c z)) = log (log (abs z)) + O(1) / (abs z * log (abs z))`
2. `s.potential c z = 1/abs z + O(1) / abs z ^ k`, where `k = 1.864` if `4 ≤ abs z` and
   `k = 1.927` if `6 ≤ abs z`.
-/

open Filter (Tendsto atTop)
open Metric (ball mem_ball_self mem_ball)
open Real (exp log)
open Set
open scoped Topology
noncomputable section

variable {c z : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

-- We use large `norm_num`s in this file. Let them all through.
set_option exponentiation.threshold 10000

/-!
## `potential` is the limit of roots of iterates
-/

/-- `potential` is the limit of roots of iterates -/
lemma tendsto_potential (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    Tendsto (fun n ↦ ‖(f' d c)^[n] z‖ ^ (-((d ^ n : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 ((superF d).potential c z)) := by
  set s := superF d
  suffices h : Tendsto (fun n ↦ (‖(f' d c)^[n] z‖ *
      s.potential c ↑((f' d c)^[n] z)) ^ (-((d ^ n : ℕ) : ℝ)⁻¹))
      atTop (𝓝 1) by
    replace h := h.mul_const (s.potential c z)
    simp only [div_mul_cancel₀ _ potential_pos.ne', one_mul, ← f_f'_iter, s.potential_eqn_iter,
      Real.mul_rpow (norm_nonneg _) (pow_nonneg s.potential_nonneg _),
      Real.pow_rpow_inv_natCast s.potential_nonneg (pow_ne_zero _ (d_ne_zero d)),
      Real.rpow_neg (pow_nonneg s.potential_nonneg _), ← div_eq_mul_inv] at h
    exact h
  simp only [← s.norm_bottcher, ← norm_mul, mul_comm _ (s.bottcher _ _)]
  rw [Metric.tendsto_atTop]; intro r rp
  rcases Metric.tendsto_atTop.mp ((bottcher_large_approx d c).comp (tendsto_iter_cobounded d z3 cz))
      (min (1 / 2) (r / 4)) (by bound) with ⟨n, h⟩
  use n; intro k nk; specialize h k nk
  generalize hw : (f' d c)^[k] z = w; generalize hp : s.bottcher c w * w = p
  simp only [hw, hp, Function.comp, Complex.dist_eq, Real.dist_eq] at h ⊢
  clear hp w hw nk n s cz z3
  generalize ha : ‖p‖ = a
  generalize hb : ((d ^ k : ℕ) : ℝ)⁻¹ = b
  have a1 : |a - 1| < min (1 / 2) (r / 4) := by
    rw [← ha]; refine lt_of_le_of_lt ?_ h
    rw [← norm_one (α := ℂ)]
    apply abs_norm_sub_norm_le
  have am : a ∈ ball (1 : ℝ) (1 / 2) := by
    simp only [mem_ball, Real.dist_eq]; exact (lt_min_iff.mp a1).1
  have b0 : 0 ≤ b := by rw [← hb]; bound
  have b1 : b ≤ 1 := by rw [← hb]; bound
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
      _ ≤ 1 * |x| ^ (-b - 1) := by bound
      _ = (x ^ (b + 1))⁻¹ := by rw [← Real.rpow_neg x0.le, neg_add', one_mul, abs_of_pos x0]
      _ ≤ ((1 / 2 : ℝ) ^ (b + 1))⁻¹ := by bound
      _ = 2 ^ (b + 1) := by rw [one_div, Real.inv_rpow zero_le_two, inv_inv]
      _ ≤ 2 ^ (1 + 1 : ℝ) := by bound
      _ ≤ 4 := by norm_num
  have le := Convex.norm_image_sub_le_of_norm_deriv_le (fun x m ↦ (hd x m).differentiableAt) bound
      (convex_ball _ _) (mem_ball_self (by norm_num)) am
  simp only [Real.norm_eq_abs, Real.one_rpow] at le
  calc |a ^ (-b) - 1|
    _ ≤ 4 * |a - 1| := le
    _ < 4 * (r / 4) := by linarith [(lt_min_iff.mp a1).2]
    _ = r := by ring

/-- `log (-log potential)` is the limit of roots of iterates -/
lemma tendsto_log_neg_log_potential (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    Tendsto (fun n ↦ log (log (‖(f' d c)^[n] z‖)) - n * log d) atTop
      (𝓝 (log (-log ((superF d).potential c z)))) := by
  set s := superF d
  have zn1 : ∀ {n}, 1 < ‖(f' d c)^[n] z‖ := by
    intro n; exact lt_of_lt_of_le (by norm_num) (le_trans z3 (le_self_iter d z3 cz _))
  have zn0 : ∀ {n}, 0 < ‖(f' d c)^[n] z‖ := fun {_} ↦ lt_trans zero_lt_one zn1
  have ln0 : ∀ {n}, 0 < log (‖(f' d c)^[n] z‖) := fun {_} ↦ Real.log_pos zn1
  have dn0 : ∀ {n}, (d:ℝ)^n ≠ 0 := fun {_} ↦ pow_ne_zero _ (Nat.cast_ne_zero.mpr (d_ne_zero d))
  have p0 : 0 < s.potential c z := potential_pos
  have p1 : s.potential c z < 1 := potential_lt_one_of_two_lt (by linarith) cz
  set f := fun x ↦ log (log x⁻¹)
  have fc : ContinuousAt f ((superF d).potential c z) := by
    refine ((NormedField.continuousAt_inv.mpr p0.ne').log (inv_ne_zero p0.ne')).log ?_
    exact Real.log_ne_zero_of_pos_of_ne_one (inv_pos.mpr p0) (inv_ne_one.mpr p1.ne)
  have t := Tendsto.comp fc (tendsto_potential d z3 cz)
  simpa only [Real.log_inv, Real.log_neg_eq_log, Nat.cast_pow, Function.comp_def, Real.log_rpow zn0,
    neg_mul, ← div_eq_inv_mul, Real.log_div ln0.ne' dn0, Real.log_pow, f] using t

/-- `log (-log potential)` inherits the `iter_approx` bound by taking limits -/
public lemma log_neg_log_potential_approx (d : ℕ) [Fact (2 ≤ d)] (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |log (-log ((superF d).potential c z)) - log (log (‖z‖))| ≤ iter_error d c z := by
  apply le_of_forall_pos_lt_add; intro e ep
  rcases (Metric.tendsto_nhds.mp (tendsto_log_neg_log_potential d z3 cz) e ep).exists with ⟨n,t⟩
  have ie := iter_approx d z3 cz n
  generalize log (-log ((superF d).potential c z)) = p at ie t
  generalize log (log ‖(f' d c)^[n] z‖) = x at ie t
  generalize log (log ‖z‖) = y at ie t
  rw [Real.dist_eq, abs_sub_comm] at t
  rw [add_comm]
  calc |p - y|
      _ = |(p - (x - n * log d)) + (x - y - n * log d)| := by ring_nf
      _ ≤ |p - (x - n * log d)| + |x - y - n * log d| := abs_add_le _ _
      _ < e + _ := add_lt_add_of_lt_of_le t ie

/-!
### We use `ene x = exp (-exp x)` below for Lipschitz bounds

This undoes the `log (log (abs z))` from `iter_approx`.
-/

/-- `d ene / dx = dene` -/
lemma hasDerivAt_ene (x : ℝ) : HasDerivAt ene (-dene x) x := by
  have h : HasDerivAt (fun x ↦ exp (-exp x)) (exp (-exp x) * -exp x) x :=
    HasDerivAt.exp (Real.hasDerivAt_exp x).neg
  simp only [mul_neg, ← Real.exp_add, neg_add_eq_sub] at h; exact h

/-- `d ene / dx = dene` -/
lemma deriv_ene (x : ℝ) : deriv ene x = -dene x := (hasDerivAt_ene x).deriv

/-- `0 ≤ dene x` -/
lemma dene_nonneg {x : ℝ} : 0 ≤ dene x := Real.exp_nonneg _

/-- `dene x` is decreasing for positive `x` -/
lemma dene_anti {x y : ℝ} (x0 : 0 ≤ x) (xy : x ≤ y) : dene x ≥ dene y := by
  refine Real.exp_le_exp.mpr ?_
  have a : AntitoneOn (fun x ↦ x - exp x) (Ici 0) := by
    have hd : ∀ x, HasDerivAt (fun x ↦ x - exp x) (1 - exp x) x :=
      fun x ↦ (hasDerivAt_id x).sub (Real.hasDerivAt_exp x)
    have d : Differentiable ℝ (fun x ↦ x - exp x) := fun x ↦ (hd x).differentiableAt
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact d.continuous.continuousOn
    · exact d.differentiableOn
    · intro x m; simp only [nonempty_Iio, interior_Ici', mem_Ioi] at m
      simp only [(hd x).deriv, sub_nonpos, Real.one_le_exp m.le]
  exact a x0 (le_trans x0 xy) xy

/-- Below we evaluate `dene x = -exp (-exp x)` at a point of the form `log (log (abs z)) - k`.
    The derivative simplifies in this case. -/
lemma dene_eq {z : ℝ} (z1 : 1 < z) (k : ℝ) :
    dene (log (log z) - k) = exp (-k) * log z * z ^ (-exp (-k)) := by
  have l0 : 0 < log z := Real.log_pos z1
  simp only [dene, sub_eq_add_neg, Real.exp_add, Real.exp_log l0, mul_comm _ (exp (-k)), ←neg_mul]
  apply congr_arg₂ _ rfl
  rw [mul_comm, Real.exp_mul, Real.exp_log (by positivity)]

/-!
## Effective bounds on `potential`
-/

/-- Generic `potential_error` bound for any `b ≤ abs z` lower bound -/
lemma potential_error_le (d : ℕ) [Fact (2 ≤ d)] {b : ℝ} {c z : ℂ}
    (b4 : 4 ≤ b) (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ (1 + exp (-0.8095 / (‖z‖ * log (‖z‖)))) := by
  have z1 : 1 < ‖z‖ := by linarith
  have z4 : 4 ≤ ‖z‖ := by linarith
  have l1 : 1.386 < log ‖z‖ := lt_of_lt_of_le lt_log_4 (Real.log_le_log (by linarith) z4)
  have l0 : 0 < log ‖z‖ := lt_trans (by norm_num) l1
  simp only [potential_error, dene_eq z1]
  have ie := iter_error_le_of_z4 d z4 cz
  have ie0 := iter_error_nonneg d (by linarith) cz
  generalize hk : (0.8095 : ℝ) = k at ie
  have k0 : 0 < k := by rw [← hk]; norm_num
  generalize hx : ‖z‖ = x at ie z1 l0 l1 z4
  generalize iter_error d c z = i at ie ie0
  have x0 : 0 < x := by rw [←hx]; linarith
  refine le_trans (mul_le_mul_of_nonneg_left ie (by positivity)) ?_
  simp only [←mul_assoc, div_eq_inv_mul, mul_inv, mul_comm _ (log x)]
  simp only [←mul_assoc, mul_comm _ (log x)⁻¹, inv_mul_cancel₀ l0.ne', one_mul]
  simp only [mul_assoc]
  refine le_trans (mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by linarith))) ?_
  simp only [←mul_assoc, ←Real.rpow_neg_one x, ←Real.rpow_add (lt_trans zero_lt_one z1),
    ←Real.rpow_neg x0.le]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le z1.le ?_) k0.le
  simp only [Real.rpow_neg_one, mul_neg, neg_add_rev, le_add_neg_iff_add_le, neg_add_cancel_right,
    neg_le_neg_iff, Real.exp_le_exp, ←mul_inv, ←div_eq_inv_mul k, mul_comm _ x, ie]

/-- Helper for specifix `b` `potential_error` bounds.  Python formulas are:
      `i = 1 + np.exp(-0.8095 / (b * np.log(b)))  -- round down`
      `j = 0.8095 / (b * np.log(b))  -- round up` -/
lemma potential_error_le' (d : ℕ) [Fact (2 ≤ d)] (i j b : ℝ) {c z : ℂ}
    (b4 : 4 ≤ b) (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (j0 : 0 < j) (ij : i - 1 ≤ exp (-j)) (bj : exp (0.8095 / b / j) ≤ b) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ i := by
  have z0 : 0 < ‖z‖ := by linarith
  have l1 : 1.386 < log ‖z‖ :=
    lt_of_lt_of_le lt_log_4 (Real.log_le_log (by linarith) (by linarith))
  have l0 : 0 < log ‖z‖ := lt_trans (by norm_num) l1
  refine le_trans (potential_error_le d b4 bz cz) (div_le_div_of_nonneg_left (by norm_num)
    (by positivity) ?_)
  refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
  simp only [add_comm (1:ℝ), ←sub_le_iff_le_add]
  refine le_trans ij (Real.exp_le_exp.mpr ?_)
  simp only [neg_div, neg_le_neg_iff, div_mul_eq_div_div]
  rw [div_le_iff₀ l0, mul_comm j, ←div_le_iff₀ j0]
  trans 0.8095 / b / j
  · gcongr
  · rw [Real.le_log_iff_exp_le z0]
    exact le_trans bj bz

/-- `potential_error` bound for `4 ≤ abs z` -/
public lemma potential_error_le_of_z4 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ}
    (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ (1.864 : ℝ) := by
  apply potential_error_le' d _ (j := 0.146) (b := 4) (by norm_num) z4 cz (by norm_num)
  · norm_num; exact (lt_exp_neg_div).le
  · norm_num; exact (exp_div_lt).le

/-- `potential_error` bound for `6 ≤ abs z` -/
public lemma potential_error_le_of_z6 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ}
    (z6 : 6 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    potential_error d c z ≤ 0.8095 / ‖z‖ ^ (1.927 : ℝ) := by
  apply potential_error_le' d _ (j := 0.0753) (b := 6) (by norm_num) z6 cz (by norm_num)
  · norm_num; exact (lt_exp_neg_div).le
  · norm_num; exact (exp_div_lt).le

/-- We need `iter_error d c z ≤ log (log (abs z))` below to make `dene` monotonic -/
lemma iter_error_le_log_log_abs (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : iter_error d c z ≤ log (log ‖z‖) := by
  have hl : 1.38 ≤ log ‖z‖ := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num
    exact le_trans (exp_div_lt).le z4
  have hll : 0.32 ≤ log (log ‖z‖) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num
    exact le_trans (exp_div_lt).le hl
  refine le_trans ?_ hll
  apply le_trans (iter_error_le_of_z4 d z4 cz)
  rw [div_le_iff₀' (by positivity), ←div_le_iff₀ (by norm_num)]
  refine le_trans (by norm_num) (mul_le_mul z4 hl (by positivity) (by positivity))

/-- `s.potential ≈ ‖z‖⁻¹` -/
public theorem potential_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |(superF d).potential c z - 1 / ‖z‖| ≤ potential_error d c z := by
  set s := superF d
  have z3 : 3 ≤ ‖z‖ := le_trans (by norm_num) z4
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) z3
  have l2 : 0 < log ‖z‖ := Real.log_pos (by linarith)
  have h := log_neg_log_potential_approx d z3 cz
  have p0 : 0 < s.potential c z := potential_pos
  have lp0 : 0 < -log (s.potential c z) :=
    neg_pos.mpr (Real.log_neg p0 (potential_lt_one_of_two_lt (by linarith) cz))
  generalize s.potential c z = p at h p0 lp0
  generalize hr : iter_error d c z = r at h
  have r0 : 0 ≤ r := le_trans (abs_nonneg _) h
  set t := Ici (log (log ‖z‖) - r)
  have yt : log (-log p) ∈ t := by
    simp only [abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right, add_comm r] at h
    simp only [mem_Ici, tsub_le_iff_right, h, t]
  have lt : log (log ‖z‖) ∈ t := by
    simp only [mem_Ici, tsub_le_iff_right, le_add_iff_nonneg_right, r0, t]
  generalize hb : dene (log (log ‖z‖) - r) = b
  have b0 : 0 ≤ b := by rw [←hb]; exact dene_nonneg
  have bound : ∀ x, x ∈ t → ‖deriv ene x‖ ≤ b := by
    intro x m
    simp only [mem_Ici, ← hr, t] at m
    simp only [deriv_ene, norm_neg, Real.norm_of_nonneg dene_nonneg, ←hb, ←hr]
    apply dene_anti (sub_nonneg.mpr (iter_error_le_log_log_abs d z4 cz)) m
  have m := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x _ ↦ (hasDerivAt_ene x).differentiableAt) bound (convex_Ici _) lt yt
  simp only [Real.norm_eq_abs] at m
  replace m := le_trans m (mul_le_mul_of_nonneg_left h (by bound))
  simp only [ene, Real.exp_log lp0, neg_neg, Real.exp_log p0, Real.exp_log l2, Real.exp_neg,
    Real.exp_log z0, inv_eq_one_div] at m
  refine le_trans m (le_of_eq ?_)
  simp only [←hr, ←hb, potential_error]
