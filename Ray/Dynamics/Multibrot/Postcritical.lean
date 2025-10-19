import Ray.Dynamics.Multibrot.Potential

/-!
## Effective bounds on postcritical points for Multibrot sets

We show that any `(c,z)` with `4 ≤ abs c ≤ abs z` is postcritical.
-/

open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c z : ℂ}

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
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact d.continuousOn
  · exact d.mono interior_subset
  · intro x m
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at m
    have l0 : 0 < log x := Real.log_pos (by linarith)
    simp only [(hd x m.le).deriv, one_div]
    refine div_nonneg ?_ (by positivity)
    simp only [sub_nonneg, mul_comm]
    apply mul_le_mul
    · exact inv_anti₀ (by linarith) (by linarith)
    · exact Real.log_le_log (by linarith) (by linarith)
    · exact Real.log_nonneg (by linarith)
    · exact inv_nonneg.mpr (by linarith)

/-- One iterate increases `log (log (abs z))` by `Ω(1)` for large `z` -/
lemma log_log_iter (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    log (log ‖z‖) + 0.548 ≤ log (log ‖f' d c z‖) := by
  have zw : (‖z‖ - 1)^1 * ‖z‖ ≤ ‖f' d c z‖ := by
    refine iter_large (d := d) (n := 1) ?_ ?_ ?_ cz
    · linarith
    · exact le_refl _
  generalize ‖f' d c z‖ = w at zw
  generalize ‖z‖ = x at zw cz z4
  clear cz
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
      _ ≥ 1.098 / 1.387 := div_le_div₀ (by positivity) lt_log_3.le (by positivity) log_4_lt.le
      _ ≥ 0.791 := by norm_num
  have ll0 : 0 ≤ log (x-1) / log x := by positivity
  have ll1 : log (x-1) / log x ≤ 1 :=
    div_le_one_of_le₀ (Real.log_le_log (by linarith) (by linarith)) (by positivity)
  calc log (log w)
    _ ≥ log (log ((x-1)*x)) := log_log_mono (by nlinarith) zw
    _ = log (log x + log (x-1)) := by rw [mul_comm, Real.log_mul (by positivity) (by linarith)]
    _ = log (log x) + log (1 + log (x-1) / log x) := by rw [log_add _ _ (by linarith) (by linarith)]
    _ ≥ log (log x) + log 2 * (log (x-1) / log x) := by bound [le_log_one_add ll0 ll1]
    _ ≥ log (log x) + 0.693 * 0.791 := by bound [lt_log_2]
    _ ≥ log (log x) + 0.548 := by bound

/-- For large `c`, large `z`'s are postcritical -/
theorem postcritical_large (c4 : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) : Postcritical (superF d) c z := by
  -- Record a variety of inequalities
  have d0 : 0 < d := d_pos d
  have lcz : log (log ‖c‖) ≤ log (log ‖z‖) := log_log_mono (by linarith) cz
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
  have zw : ‖z‖ ≤ ‖w‖ := by rw [←hw]; exact le_self_iter d (by linarith) cz 1
  have cw : ‖c‖ ≤ ‖w‖ := le_trans cz zw
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
  have lzw : log (log ‖z‖) + 0.548 ≤ log (log ‖w‖) := by
    rw [←hw]; exact log_log_iter (by linarith) cz
  have ie : ∀ z : ℂ, 4 ≤ ‖z‖ → ‖c‖ ≤ ‖z‖ → iter_error d c z ≤ 0.15 := by
    intro z z4 cz
    refine le_trans (iter_error_le_of_z4 d z4 cz) ?_
    calc 0.8095 / (‖z‖ * log ‖z‖)
      _ ≤ 0.8095 / (4 * log 4) := by bound
      _ ≤ 0.8095 / (4 * 1.386) := by bound [lt_log_4]
      _ ≤ 0.15 := by norm_num
  have iec := ie c c4 (le_refl _)
  have iew := ie w (by linarith) cw
  refine lt_of_lt_of_le (lt_of_le_of_lt (add_le_add iec lcz) ?_) (add_le_add (neg_le_neg iew) lzw)
  ring_nf; simp only [add_lt_add_iff_right]; norm_num

/-- For large `c` and small `z`, `(c,z⁻¹)` is postcritical -/
lemma postcritical_small (c4 : 4 ≤ ‖c‖) (z1 : ‖z‖ ≤ ‖c‖⁻¹) : (c, (z : 𝕊)⁻¹) ∈ (superF d).post := by
  set s := superF d
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', s.post_a]
  · rw [inv_coe z0]
    apply postcritical_large c4
    rwa [norm_inv, le_inv_comm₀ (by linarith) (by simpa)]
