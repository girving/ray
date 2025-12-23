module
public import Ray.Multibrot.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Potential
import Ray.Misc.Cobounded
import Ray.Multibrot.Basic
import Ray.Multibrot.Potential

/-!
## A lower bounds `potential c z` for small `z`

`potential_approx` in `Dynamics.Multibrot.Potential` gives an effective estimate on
`s.potential c z` for `max 4 ‖c‖ ≤ ‖z‖`.  However, for rendering we also need an effective
lower bound for small `z`, in order to show that iterations which stay bounded have potential
near `1`.  We do this by noting that if `‖c‖, ‖z‖ ≤ 4`, then iteration must eventually pass
through the interval `‖w‖ ∈ [4,4^d+4]`.  On this interval, we have the estimate

  `potential c w ≥ 1/‖w‖ - 0.8095 / ‖w‖ ^ 1.864 ≥ 0.0469`
  `potential c z ≥ potential c w ^ d⁻¹ ≥ 0.216`

Note that if `z` is the result of at least 10 iterations, we then know that the potential of the
intial `z` is at least `1 - 1/512`.
-/

open Classical
open Real (log)
open Set

variable {c z : ℂ}
variable {d : ℕ} [Fact (2 ≤ d)]

/-- Small iterates eventually pass through `‖z‖ ∈ (4, 4 ^ d + 4]` -/
lemma pass_through (c4 : ‖c‖ ≤ 4) (z4 : ‖z‖ ≤ 4) (m : (c,↑z) ∈ (superF d).basin) :
    ∃ n, ‖(f' d c)^[n+1] z‖ ∈ Ioc 4 (4 ^ d + 4) := by
  set s := superF d
  simp only [s.basin_iff_attracts, Attracts, RiemannSphere.tendsto_inf_iff_tendsto_cobounded,
    f_f'_iter, tendsto_cobounded_iff_norm_tendsto_atTop] at m
  rcases Filter.tendsto_atTop_atTop.mp m 5 with ⟨n,h⟩
  generalize hp : (fun n ↦ 4 < ‖(f' d c)^[n] z‖) = p
  replace h : p n := by rw [←hp]; linarith [h n (by linarith)]
  generalize hk : Nat.find (p := p) ⟨_,h⟩ = k
  have k4 : p k := by rw [←hk]; exact Nat.find_spec (p := p) ⟨_,h⟩
  have k0 : k ≠ 0 := by
    contrapose k4
    simp only [k4, ← hp, not_lt, Function.iterate_zero_apply, z4]
  have k1 : 1 ≤ k := Nat.pos_iff_ne_zero.mpr k0
  use k-1
  have lt : ¬p (k-1) := by apply Nat.find_min; rw [hk]; omega
  simp only [Nat.sub_add_cancel k1, ←hp, not_lt] at k4 k1 lt ⊢
  use k4
  have fs := iter_small d c ((f' d c)^[k-1] z)
  simp only [← Function.iterate_succ_apply', Nat.succ_eq_add_one, Nat.sub_add_cancel k1] at fs
  exact le_trans fs (by bound)

/-- Our lower bound is decreasing in `‖z‖` -/
lemma lower_anti (k p : ℝ) (kp : k * p ≤ 2 := by norm_num) (hp : 3/2 ≤ p := by norm_num) :
    AntitoneOn (fun x : ℝ ↦ 1 / x - k / x^p) (Ici 4) := by
  have hd : ∀ x, 4 ≤ x → HasDerivAt (fun x : ℝ ↦ 1 / x - k / x^p)
      (-(x^2)⁻¹ - k * (-(p * x^(p-1)) / (x^p)^2)) x := by
    intro x x2
    simp only [div_eq_mul_inv, one_mul]
    refine (hasDerivAt_inv (by positivity)).sub (HasDerivAt.const_mul _ ?_)
    exact (Real.hasDerivAt_rpow_const (Or.inl (by positivity))).inv (by positivity)
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

/-- A bound we need below -/
lemma le_of_d3 {d : ℕ} (d3 : 3 ≤ d) :
    (0.216 : ℝ) ^ d ≤ (4 ^ d + 4)⁻¹ - 0.8095 / (4 ^ d + 4) ^ (1.864 : ℝ) := by
  have e : (0.216 * 4 : ℝ) = 0.864 := by norm_num
  rw [le_sub_iff_add_le, ← one_div, le_div_iff₀ (by apply add_pos <;> bound), add_mul, mul_add,
    ← mul_pow, e, mul_comm _ (4 : ℝ), div_mul, ← Real.rpow_sub_one (by positivity)]
  have le : 38 ≤ (68 : ℝ) ^ (108 / 125 : ℝ) := by
    rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.le_rpow_inv_iff_of_pos (by norm_num)
      (by positivity) (by positivity)]
    norm_num
  trans 0.864 ^ 3 + 4 * 0.216 ^ 3 + 0.8095 / (4 ^ 3 + 4) ^ (1.864 - 1 : ℝ)
  · bound
  · norm_num
    grw [← le]
    norm_num

/-- If `‖c‖, ‖z‖ ≤ 4`, `0.216 ≤ s.potential c z` -/
@[bound] public lemma le_potential (c4 : ‖c‖ ≤ 4) (z4 : ‖z‖ ≤ 4) :
    0.216 ≤ (superF d).potential c z := by
  set s := superF d
  by_cases m : (c,↑z) ∉ s.basin
  · rw [s.potential_eq_one m]
    norm_num
  simp only [not_not] at m
  obtain ⟨n,w4,w20⟩ := pass_through c4 z4 m
  generalize hw : (f' d c)^[n+1] z = w at w4 w20
  have cw : ‖c‖ ≤ ‖w‖ := by linarith
  have pw : 1 / (4 ^ d + 4) - 0.8095 / (4 ^ d + 4) ^ (1.864 : ℝ) ≤ s.potential c w := by
    have pw := (abs_le.mp (le_trans (potential_approx d w4.le cw)
      (potential_error_le_of_z4 d w4.le cw))).1
    rw [le_sub_iff_add_le, neg_add_eq_sub] at pw
    have anti := lower_anti 0.8095 1.864 (by norm_num) (by norm_num)
      (a := ‖w‖) (b := 4 ^ d + 4) w4.le (by norm_num) w20
    simp only at anti
    exact le_trans anti pw
  have pwz : s.potential c w ^ (d⁻¹ : ℝ) ≤ s.potential c z := by
    have pwz : s.potential c w = s.potential c z ^ d ^ (n+1) := by
      simp only [←hw, ←f_f'_iter, s.potential_eqn_iter]
    rw [← Real.rpow_natCast] at pwz
    have dn0 : ((d ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by simp [s.d0]
    rw [← Real.rpow_inv_eq s.potential_nonneg s.potential_nonneg dn0] at pwz
    rw [← pwz]
    apply Real.rpow_le_rpow_of_exponent_ge (by bound) (by bound)
    simp only [Nat.cast_pow]
    bound
  refine le_trans ?_ pwz
  rw [Real.le_rpow_inv_iff_of_pos (by norm_num) (by bound) (by bound)]
  refine le_trans ?_ pw
  simp only [Real.rpow_natCast, one_div]
  -- Handle `d = 2` explicitly since it's tight, and be more relaxed for `2 < d`
  by_cases d2 : d = 2
  · simp only [d2]
    have le : (266 : ℝ) ≤ 20 ^ (233 / 125 : ℝ) := by
      rw [div_eq_mul_inv, Real.rpow_mul (by positivity), Real.le_rpow_inv_iff_of_pos (by norm_num)
        (by positivity) (by positivity)]
      norm_num
    norm_num
    grw [← le]
    norm_num
  · have d3 : 3 ≤ d := by have : 2 ≤ d := s.d2; omega
    exact le_of_d3 d3
