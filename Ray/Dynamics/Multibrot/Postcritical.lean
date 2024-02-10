import Ray.Dynamics.Multibrot.Potential

/-!
## Effective bounds on postcritical points for Multibrot sets

We show that any `(c,z)` with `4 ≤ abs c ≤ abs z` is postcritical.
-/

open Complex (abs)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `log (log x)` is monotone for `1 < x` -/
lemma log_log_mono {x y : ℝ} (x0 : 1 < x) (xy : x ≤ y) : log (log x) ≤ log (log y) :=
  Real.log_le_log (Real.log_pos x0) (Real.log_le_log (by positivity) xy)

/-- `log (-log x)` is antitone for `0 < x < 1` -/
lemma log_neg_log_strict_anti {x y : ℝ} (x0 : 0 < x) (y0 : 0 < y) (x1 : x < 1) (y1 : y < 1) :
    log (-log y) < log (-log x) ↔ x < y := by
  have lx := neg_pos.mpr (Real.log_neg x0 x1)
  have ly := neg_pos.mpr (Real.log_neg y0 y1)
  rw [Real.log_lt_log_iff ly lx, neg_lt_neg_iff, Real.log_lt_log_iff x0 y0]

/-- `log 2 * x ≤ log (1 + x)` for `0 ≤ x ≤ 1` -/
lemma le_log_one_add {x : ℝ} (x0 : 0 ≤ x) (x1 : x ≤ 1) : log 2 * x ≤ log (1 + x) := by
  rw [Real.le_log_iff_exp_le (by linarith)] --, Real.exp_mul, Real.exp_log (by norm_num)]
  have x0' : 0 ≤ 1 - x := by linarith
  have h := convexOn_exp.2 (mem_univ 0) (mem_univ (log 2)) x0' x0 (by abel)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, Real.exp_log zero_lt_two] at h
  ring_nf at h
  rwa [mul_comm]

/-- `log (x-1) / log x` is increasing for `2 ≤ x` -/
lemma log_ratio_mono : MonotoneOn (fun x ↦ log (x-1) / log x) (Ici 2) := by
  have hd : ∀ x, 2 ≤ x → HasDerivAt (fun x ↦ log (x-1) / log x)
      ((1 / (x-1) * log x - log (x-1) * x⁻¹) / (log x)^2) x := by
    intro x x2
    have l0 : 0 < log x := Real.log_pos (by linarith)
    refine HasDerivAt.div ?_ (Real.hasDerivAt_log (by positivity)) l0.ne'
    exact HasDerivAt.log ((hasDerivAt_id _).sub_const _) (by linarith)
  have d : DifferentiableOn ℝ (fun x ↦ log (x-1) / log x) (Ici 2) :=
    fun x m ↦ (hd x m).differentiableAt.differentiableWithinAt
  apply (convex_Ici _).monotoneOn_of_deriv_nonneg
  · exact d.continuousOn
  · exact d.mono interior_subset
  · intro x m
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at m
    have l0 : 0 < log x := Real.log_pos (by linarith)
    simp only [(hd x m.le).deriv, one_div]
    refine div_nonneg ?_ (by positivity)
    simp only [sub_nonneg, mul_comm]
    apply mul_le_mul
    · exact inv_le_inv_of_le (by linarith) (by linarith)
    · exact Real.log_le_log (by linarith) (by linarith)
    · exact Real.log_nonneg (by linarith)
    · exact inv_nonneg.mpr (by linarith)

/-- One iterate increases `log (log (abs z))` by `Ω(1)` for large `z` -/
lemma log_log_iter {c z : ℂ} (z4 : 4 ≤ abs z) (cz : abs c ≤ abs z) :
    log (log (abs z)) + 0.548 ≤ log (log (abs (f' d c z))) := by
  have zw : (abs z - 1)^1 * abs z ≤ abs (f' d c z) := by
    refine iter_large (d := d) (n := 1) ?_ ?_ ?_ cz
    · linarith
    · exact le_refl _
  generalize abs (f' d c z) = w at zw
  generalize abs z = x at zw cz z4
  clear z c cz
  have x0 : 0 < x := by linarith
  have x1 : 1 < x := by linarith
  simp only [pow_one] at zw
  have lx1 : 1 < log (x-1) :=
    lt_trans (by norm_num) (lt_of_lt_of_le lt_log_3 (Real.log_le_log (by norm_num) (by linarith)))
  have lx : 1 < log x := lt_trans lx1 (Real.log_lt_log (by linarith) (by linarith))
  have ll : 0.791 ≤ log (x-1) / log x := by
    calc log (x-1) / log x
      _ ≥ log (4-1) / log 4 := by
          apply log_ratio_mono ?_ ?_ z4
          · simp only [mem_Ici]; norm_num
          · simp only [mem_Ici]; linarith
      _ = log 3 / log 4 := by norm_num
      _ ≥ 1.098 / 1.387 := div_le_div (by positivity) lt_log_3.le (by positivity) log_4_lt.le
      _ ≥ 0.791 := by norm_num
  have ll0 : 0 ≤ log (x-1) / log x := by positivity
  have ll1 : log (x-1) / log x ≤ 1 :=
    div_le_one_of_le (Real.log_le_log (by linarith) (by linarith)) (by positivity)
  calc log (log w)
    _ ≥ log (log ((x-1)*x)) := log_log_mono (by nlinarith) zw
    _ = log (log x + log (x-1)) := by rw [mul_comm, Real.log_mul (by positivity) (by linarith)]
    _ = log (log x) + log (1 + log (x-1) / log x) := by rw [log_add _ _ (by linarith) (by linarith)]
    _ ≥ log (log x) + log 2 * (log (x-1) / log x) := by bound [le_log_one_add ll0 ll1]
    _ ≥ log (log x) + 0.693 * 0.791 := by bound [lt_log_2]
    _ ≥ log (log x) + 0.548 := by bound

/-- For large `c`, large `z`'s are postcritical -/
theorem postcritical_large {c z : ℂ} (c4 : 4 ≤ abs c) (cz : abs c ≤ abs z) :
    Postcritical (superF d) c z := by
  -- Record a variety of inequalities
  have d0 : 0 < d := d_pos d
  have lcz : log (log (abs c)) ≤ log (log (abs z)) := log_log_mono (by linarith) cz
  -- Reduce to s.potential c (f' d c z) < s.potential c ↑c
  simp only [Postcritical, multibrot_p]
  set s := superF d
  rw [← Real.pow_rpow_inv_natCast s.potential_nonneg d0.ne', ←
    Real.pow_rpow_inv_natCast (s.potential_nonneg : 0 ≤ s.potential c 0) d0.ne']
  simp only [← s.potential_eqn]
  refine Real.rpow_lt_rpow s.potential_nonneg ?_ (by bound)
  generalize hw : f' d c z = w
  have e : f d c z = w := by rw [f, lift_coe', hw]
  simp only [f_0, e]; clear e
  have zw : abs z ≤ abs w := by rw [←hw]; exact le_self_iter d (by linarith) cz 1
  have cw : abs c ≤ abs w := le_trans cz zw
  -- Move to log (-log _) space
  have pc1 : s.potential c c < 1 := potential_lt_one_of_two_lt (by linarith) (le_refl _)
  have pw1 : s.potential c w < 1 := potential_lt_one_of_two_lt (by linarith) (by linarith)
  rw [←log_neg_log_strict_anti potential_pos potential_pos pw1 pc1]
  -- Use `log_neg_log_potential_approx` to replace `s.potential` with `log (log (abs _))`
  refine lt_of_lt_of_le ?_ (le_sub_iff_add_le.mp (abs_le.mp
    (log_neg_log_potential_approx d (by linarith) cw)).1)
  refine lt_of_le_of_lt (sub_le_iff_le_add.mp (abs_le.mp
    (log_neg_log_potential_approx d (by linarith) (le_refl _))).2) ?_
  -- Settle our inequality
  have lzw : log (log (abs z)) + 0.548 ≤ log (log (abs w)) := by
    rw [←hw]; exact log_log_iter (by linarith) cz
  have ie : ∀ z : ℂ, 4 ≤ abs z → abs c ≤ abs z → iter_error d c z ≤ 0.15 := by
    intro z z4 cz
    refine le_trans (iter_error_le_of_z4 d z4 cz) ?_
    calc 0.8095 / (abs z * log (abs z))
      _ ≤ 0.8095 / (4 * log 4) := by bound
      _ ≤ 0.8095 / (4 * 1.386) := by bound [lt_log_4]
      _ ≤ 0.15 := by norm_num
  have iec := ie c c4 (le_refl _)
  have iew := ie w (by linarith) cw
  refine lt_of_lt_of_le (lt_of_le_of_lt (add_le_add iec lcz) ?_) (add_le_add (neg_le_neg iew) lzw)
  ring_nf; simp only [add_lt_add_iff_right]; norm_num
