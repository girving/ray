import Ray.Dynamics.Mandelbrot

/-!
## A lower bounds `potential c z` for small `z`

`potential_approx` in `Dynamics.Multibrot.Potential` gives an effective estimate on
`s.potential c z` for `max 4 (abs c) ≤ abs z`.  However, for rendering we also need an effective
lower bound for small `z`, in order to show that iterations which stay bounded have potential
near `1`.  We do this by noting that if `abs c, abs z ≤ 4`, then iteration must eventually pass
through the interval `abs w ∈ [4,20]`.  On this interval, we have the estimate

  `potential c w ≥ 1/abs w - 0.8095 / abs w ^ 1.864 ≥ 0.0469`
  `potential c z ≥ potential c w ^ (1/2) ≥ 0.216`

Note that if `z` is the result of at least 10 iterations, we then know that the potential of the
intial `z` is at least `1 - 1/512`.
-/

open Classical
open Real (log)
open Set

variable {c z : ℂ}
private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- Small iterates eventually pass through `abs z ∈ [4,20]` -/
lemma pass_through (c4 : ‖c‖ ≤ 4) (z4 : ‖z‖ ≤ 4) (m : (c,↑z) ∈ (superF 2).basin) :
    ∃ n, ‖(f' 2 c)^[n+1] z‖ ∈ Ioc 4 20 := by
  set s := superF 2
  simp only [s.basin_iff_attracts, Attracts, RiemannSphere.tendsto_inf_iff_tendsto_cobounded, f_f'_iter,
    tendsto_cobounded_iff_norm_tendsto_atTop] at m
  rcases Filter.tendsto_atTop_atTop.mp m 5 with ⟨n,h⟩
  generalize hp : (fun n ↦ 4 < ‖(f' 2 c)^[n] z‖) = p
  replace h : p n := by rw [←hp]; linarith [h n (by linarith)]
  --have fp : ∀ n, 4 < abs ((f' 2 c)^[n] z) → p (n+1) := by
  --  intro n n4; simp only [←hp, Function.iterate_succ_apply']
  --  exact lt_of_lt_of_le ?_ (iter_small 2 c _)
  generalize hk : Nat.find (p := p) ⟨_,h⟩ = k
  have k4 : p k := by rw [←hk]; exact Nat.find_spec (p := p) ⟨_,h⟩
  have k0 : k ≠ 0 := by
    contrapose k4
    simp only [not_not] at k4
    simp only [k4, ←hp, not_lt, Function.iterate_zero_apply, z4]
  have k1 : 1 ≤ k := Nat.pos_iff_ne_zero.mpr k0
  use k-1
  have lt : ¬p (k-1) := by apply Nat.find_min; rw [hk]; omega
  simp only [Nat.sub_add_cancel k1, ←hp, not_lt] at k4 k1 lt ⊢
  use k4
  have fs := iter_small 2 c ((f' 2 c)^[k-1] z)
  simp only [←Function.iterate_succ_apply', Nat.succ_eq_add_one, Nat.sub_add_cancel k1] at fs
  exact le_trans fs (le_trans (add_le_add (pow_le_pow_left₀ (by positivity) lt 2) c4)
    (by norm_num))

/-- Our lower bound is decreasing in `abs z` -/
lemma lower_anti (k p : ℝ) (kp : k * p ≤ 2 := by norm_num) (hp : 3/2 ≤ p := by norm_num) :
    AntitoneOn (fun x : ℝ ↦ 1 / x - k / x^p) (Ici 4) := by
  have hd : ∀ x, 4 ≤ x → HasDerivAt (fun x : ℝ ↦ 1 / x - k / x^p)
      (-(x^2)⁻¹ - k * (-(p * x^(p-1)) / (x^p)^2)) x := by
    intro x x2
    simp only [div_eq_mul_inv, one_mul]
    refine (hasDerivAt_inv (by positivity)).sub (HasDerivAt.const_mul _ ?_)
    exact (Real.hasDerivAt_rpow_const (Or.inl (by positivity))).inv (by positivity)
  simp only [ge_iff_le] at kp hp
  have d : DifferentiableOn ℝ (fun x ↦ 1 / x - k / x^p) (Ici 4) :=
    fun x m ↦ (hd x m).differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact d.continuousOn
  · exact d.mono interior_subset
  · intro x x4
    simp only [nonempty_Iio, interior_Ici', mem_Ioi] at x4
    have x0 : 0 < x := by linarith
    simp only [(hd x x4.le).deriv]
    simp only [← Real.rpow_mul x0.le, neg_div, mul_div_assoc p, ← Real.rpow_sub x0, mul_neg, ←
      mul_assoc k p, sub_neg_eq_add, neg_add_le_iff_le_add, add_zero, ← Real.rpow_two, ←
      Real.rpow_neg x0.le]
    ring_nf
    simp only [←neg_add', Real.rpow_neg x0.le (1 + p)]
    rw [mul_inv_le_iff₀ (by positivity), ← Real.rpow_add x0]
    ring_nf
    have p1' : 1/2 ≤ -1 + p := by linarith
    refine le_trans kp (le_trans ?_ (Real.rpow_le_rpow_of_exponent_le (by linarith) p1'))
    rw [one_div, Real.le_rpow_inv_iff_of_pos (by norm_num) x0.le (by norm_num)]
    norm_num; exact x4.le

/-- If `abs c, abs z ≤ 4`, `0.216 ≤ s.potential c z` (for `d = 2`) -/
lemma le_potential (c4 : ‖c‖ ≤ 4) (z4 : ‖z‖ ≤ 4) : 0.216 ≤ (superF 2).potential c z := by
  set s := superF 2
  by_cases m : (c,↑z) ∈ s.basin
  · rcases pass_through c4 z4 m with ⟨n,w4,w20⟩
    generalize hw : (f' 2 c)^[n+1] z = w at w4 w20
    have cw : ‖c‖ ≤ ‖w‖ := by linarith
    have pw : 0.0469 ≤ s.potential c w := by
      have pw := (abs_le.mp (le_trans (potential_approx 2 w4.le cw)
        (potential_error_le_of_z4 2 w4.le cw))).1
      rw [le_sub_iff_add_le, neg_add_eq_sub] at pw
      have anti := lower_anti 0.8095 1.864 (by norm_num) (by norm_num)
        (a := ‖w‖) (b := 20) w4.le (by norm_num) w20
      refine le_trans ?_ (le_trans anti pw)
      norm_num
      have le : (266 : ℝ) ≤ 20 ^ (233 / 125 : ℝ) := by
        rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.le_rpow_inv_iff_of_pos (by norm_num)
          (by positivity) (by positivity)]
        norm_num
      exact le_trans (by norm_num) (sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num)
        (by norm_num) le) _)
    have pwz : s.potential c w = s.potential c z ^ 2^(n+1) := by
      simp only [←hw, ←f_f'_iter, s.potential_eqn_iter]
    rw [←Real.rpow_natCast] at pwz
    rw [←Real.rpow_inv_eq s.potential_nonneg s.potential_nonneg
      (NeZero.natCast_ne (2^(n+1)) ℝ)] at pwz
    rw [←pwz]
    refine le_trans ?_ (Real.rpow_le_rpow (by norm_num) pw (by positivity))
    rw [Real.le_rpow_inv_iff_of_pos (by norm_num) (by norm_num) (by positivity), Real.rpow_natCast]
    refine le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left 1 n))) ?_
    norm_num
  · rw [s.potential_eq_one (not_exists.mp m)]
    norm_num
