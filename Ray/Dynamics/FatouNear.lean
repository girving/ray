module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Bound
import Ray.Analytic.Uniform

/-!
## Fatou coordinates for near-translations of a half-plane

Near a parabolic fixed point, the coordinate `w = -1 / (k a z^k)` turns each petal into a right half-plane on which
the dynamics is nearly the translation `w ↦ w + 1`:

  `G w = w + 1 + β / w + O(‖w‖^(-1-δ))`

This file builds the attracting Fatou coordinate of such a `G`.  The approximate coordinate `φ w = w - β log w`
satisfies `φ (G w) = φ w + 1 + O(‖w‖^(-1-δ))`, orbits march right (`re (G^[n] w) ≥ re w + n / 2`), so the errors along
an orbit are summable and

  `Φ w = lim (φ (G^[n] w) - n)`

converges uniformly.  This first part proves the hypotheses' basic consequences: `G` maps the half-plane into itself,
orbits march right, and the one-step error of `φ`.
-/

open Complex (log arg slitPlane)
open Set
open scoped Real

/-- The right half-plane `R < re w` -/
@[expose] public def rightHalf (R : ℝ) : Set ℂ := {w | R < w.re}

/-- `G` is the translation by `1` up to `β / w` and an error `A / ‖w‖^(1 + δ)` on the half-plane `R < re w` -/
public structure NearTranslation (G : ℂ → ℂ) (β : ℂ) (R A δ : ℝ) : Prop where
  four_le : 4 ≤ R
  large : 4 * (‖β‖ + A) ≤ R
  A0 : 0 ≤ A
  δ0 : 0 < δ
  δ1 : δ ≤ 1
  ga : AnalyticOnNhd ℂ G (rightHalf R)
  approx : ∀ w ∈ rightHalf R, ‖G w - (w + 1 + β / w)‖ ≤ A / ‖w‖ ^ (1 + δ)

/-- The approximate Fatou coordinate `φ w = w - β log w` -/
@[expose] public noncomputable def approxFatou (β w : ℂ) : ℂ := w - β * log w

namespace NearTranslation

variable {G : ℂ → ℂ} {β : ℂ} {R A δ : ℝ}

lemma lt_norm {w : ℂ} (m : w ∈ rightHalf R) : R < ‖w‖ := lt_of_lt_of_le m (Complex.re_le_norm w)

lemma one_le_norm (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : 1 ≤ ‖w‖ := by
  linarith [lt_norm m, h.four_le]

lemma norm_pos (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : 0 < ‖w‖ := by
  linarith [h.one_le_norm m]

/-- `‖w‖ ≤ ‖w‖^(1 + δ) ≤ ‖w‖^2`, since `1 ≤ ‖w‖` -/
lemma norm_le_rpow (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : ‖w‖ ≤ ‖w‖ ^ (1 + δ) := by
  simpa using Real.rpow_le_rpow_of_exponent_le (h.one_le_norm m) (by linarith [h.δ0] : (1 : ℝ) ≤ 1 + δ)

lemma rpow_le_sq (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : ‖w‖ ^ (1 + δ) ≤ ‖w‖ ^ 2 := by
  have e := Real.rpow_le_rpow_of_exponent_le (h.one_le_norm m) (by linarith [h.δ1] : 1 + δ ≤ (2 : ℝ))
  simpa using e

/-- The step is close to `1`: `‖G w - w - 1‖ ≤ (‖β‖ + A) / ‖w‖` -/
lemma dev (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) :
    ‖G w - (w + 1)‖ ≤ (‖β‖ + A) / ‖w‖ := by
  have n0 := h.norm_pos m
  have e1 : ‖G w - (w + 1)‖ ≤ ‖G w - (w + 1 + β / w)‖ + ‖β / w‖ := by
    calc ‖G w - (w + 1)‖ = ‖(G w - (w + 1 + β / w)) + β / w‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have e2 : A / ‖w‖ ^ (1 + δ) ≤ A / ‖w‖ := div_le_div_of_nonneg_left h.A0 n0 (h.norm_le_rpow m)
  rw [norm_div] at e1
  have e3 := h.approx w m
  rw [add_div]
  linarith

/-- The step is within `1/4` of `1` -/
lemma dev_le (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : ‖G w - (w + 1)‖ ≤ 1 / 4 := by
  refine le_trans (h.dev m) ?_
  rw [div_le_iff₀ (h.norm_pos m)]
  linarith [h.large, lt_norm m]

/-- Orbits march right: `re w + 3/4 ≤ re (G w)` -/
lemma re_step (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : w.re + 3 / 4 ≤ (G w).re := by
  have e := le_trans (Complex.abs_re_le_norm (G w - (w + 1))) (h.dev_le m)
  rw [abs_le] at e
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re] at e
  linarith [e.1]

/-- `G` maps the half-plane into itself -/
public lemma mapsTo (h : NearTranslation G β R A δ) : MapsTo G (rightHalf R) (rightHalf R) := by
  intro w m
  have := h.re_step m
  simp only [rightHalf, mem_ofPred_eq] at m ⊢
  linarith

/-- Orbits march right: `re w + n / 2 ≤ re (G^[n] w)` -/
public lemma re_iter (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) (n : ℕ) :
    w.re + n / 2 ≤ (G^[n] w).re := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have mn : G^[n] w ∈ rightHalf R := (h.mapsTo.iterate n) m
    have := h.re_step mn
    push_cast
    linarith

/-- The half-plane lies in the slit plane where `log` is analytic -/
lemma mem_slitPlane (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) : w ∈ slitPlane := by
  left
  have := h.four_le
  simp only [rightHalf, mem_ofPred_eq] at m
  linarith

/-- The one-step error of the approximate coordinate: `‖φ (G w) - φ w - 1‖ ≤ K / ‖w‖^(1 + δ)` -/
public lemma approxFatou_step (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) :
    ‖approxFatou β (G w) - approxFatou β w - 1‖ ≤ (A + ‖β‖ * (‖β‖ + A + 2)) / ‖w‖ ^ (1 + δ) := by
  have n0 := h.norm_pos m
  have w0 : w ≠ 0 := norm_pos_iff.mp n0
  have n4 : 4 ≤ ‖w‖ := by linarith [lt_norm m, h.four_le]
  set e := G w - (w + 1 + β / w) with he
  set u := (G w - w) / w with hu
  have gw : G w = w * (1 + u) := by rw [hu]; field_simp; ring
  -- `‖u‖ ≤ (5/4) / ‖w‖ ≤ 5/16`
  have dn : ‖G w - w‖ ≤ 5 / 4 := by
    calc ‖G w - w‖ = ‖(G w - (w + 1)) + 1‖ := by ring_nf
      _ ≤ ‖G w - (w + 1)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 := by rw [norm_one]; linarith [h.dev_le m]
      _ = 5 / 4 := by norm_num
  have un : ‖u‖ ≤ 5 / 4 / ‖w‖ := by rw [hu, norm_div]; exact div_le_div_of_nonneg_right dn n0.le
  have un' : ‖u‖ ≤ 5 / 16 := by
    refine le_trans un ?_
    rw [div_le_iff₀ n0]; linarith
  -- `log (G w) = log w + log (1 + u)`: both lie in the right half-plane
  have wr : 0 < w.re := by have := h.four_le; simp only [rightHalf, mem_ofPred_eq] at m; linarith
  have ur : 0 < (1 + u).re := by
    have := Complex.abs_re_le_norm u
    simp only [Complex.add_re, Complex.one_re]
    rw [abs_le] at this; linarith
  have u0 : 1 + u ≠ 0 := fun z ↦ by simp [z] at ur
  have hlog : log (G w) = log w + log (1 + u) := by
    rw [gw]
    refine (Complex.log_mul_eq_add_log_iff w0 u0).mpr ?_
    have a1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl wr)
    have a2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ur)
    rw [abs_lt] at a1 a2
    constructor <;> linarith
  -- the exact error: `e - β (β / w + e) / w - β (log (1 + u) - u)`
  have key : approxFatou β (G w) - approxFatou β w - 1 =
      e - β * ((β / w + e) / w) - β * (log (1 + u) - u) := by
    simp only [approxFatou]
    rw [hlog]
    generalize log (1 + u) = L
    rw [he, hu]
    field_simp
    ring
  rw [key]
  -- the three terms
  set P := ‖w‖ ^ (1 + δ) with hP
  have P0 : 0 < P := Real.rpow_pos_of_pos n0 _
  have Psq : P ≤ ‖w‖ ^ 2 := h.rpow_le_sq m
  have en : ‖e‖ ≤ A / P := h.approx w m
  have en' : ‖e‖ ≤ A / ‖w‖ := le_trans en (div_le_div_of_nonneg_left h.A0 n0 (h.norm_le_rpow m))
  have t2 : ‖β * ((β / w + e) / w)‖ ≤ ‖β‖ * (‖β‖ + A) / P := by
    have b1 : ‖β / w + e‖ ≤ (‖β‖ + A) / ‖w‖ := by
      calc ‖β / w + e‖ ≤ ‖β / w‖ + ‖e‖ := norm_add_le _ _
        _ ≤ ‖β‖ / ‖w‖ + A / ‖w‖ := by rw [norm_div]; linarith
        _ = (‖β‖ + A) / ‖w‖ := by ring
    calc ‖β * ((β / w + e) / w)‖ = ‖β‖ * (‖β / w + e‖ / ‖w‖) := by rw [norm_mul, norm_div]
      _ ≤ ‖β‖ * ((‖β‖ + A) / ‖w‖ / ‖w‖) := by gcongr
      _ = ‖β‖ * (‖β‖ + A) / ‖w‖ ^ 2 := by ring
      _ ≤ ‖β‖ * (‖β‖ + A) / P := by have := h.A0; gcongr
  have t3 : ‖β * (log (1 + u) - u)‖ ≤ ‖β‖ * 2 / P := by
    have l1 := Complex.norm_log_one_add_sub_self_le (by linarith : ‖u‖ < 1)
    have l2 : ‖u‖ ^ 2 * (1 - ‖u‖)⁻¹ / 2 ≤ ‖u‖ ^ 2 := by
      have : (1 - ‖u‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      nlinarith [sq_nonneg ‖u‖]
    have l3 : ‖u‖ ^ 2 ≤ 2 / ‖w‖ ^ 2 := by
      have : ‖u‖ ^ 2 ≤ (5 / 4 / ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) un 2
      refine le_trans this ?_
      rw [div_pow]; gcongr; norm_num
    calc ‖β * (log (1 + u) - u)‖ = ‖β‖ * ‖log (1 + u) - u‖ := norm_mul _ _
      _ ≤ ‖β‖ * (2 / ‖w‖ ^ 2) := by gcongr; linarith
      _ = ‖β‖ * 2 / ‖w‖ ^ 2 := by ring
      _ ≤ ‖β‖ * 2 / P := by gcongr
  calc ‖e - β * ((β / w + e) / w) - β * (log (1 + u) - u)‖
      ≤ ‖e‖ + ‖β * ((β / w + e) / w)‖ + ‖β * (log (1 + u) - u)‖ := by
        refine le_trans (norm_sub_le _ _) ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ A / P + ‖β‖ * (‖β‖ + A) / P + ‖β‖ * 2 / P := by gcongr
    _ = (A + ‖β‖ * (‖β‖ + A + 2)) / P := by ring

/-!
### The Fatou coordinate
-/

/-- The constant of the one-step error -/
@[expose] public noncomputable def errC (β : ℂ) (A : ℝ) : ℝ := A + ‖β‖ * (‖β‖ + A + 2)

lemma errC_nonneg (h : NearTranslation G β R A δ) : 0 ≤ errC β A := by unfold errC; have := h.A0; positivity

/-- The shifted approximate coordinates along the orbit, `φ (G^[n] w) - n` -/
@[expose] public noncomputable def fatouSeq (G : ℂ → ℂ) (β : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  approxFatou β (G^[n] w) - n

/-- The Fatou coordinate `Φ = φ + ∑ (Φ_{n+1} - Φ_n) = lim Φ_n` -/
@[expose] public noncomputable def fatou (G : ℂ → ℂ) (β : ℂ) (w : ℂ) : ℂ :=
  approxFatou β w + ∑' n, (fatouSeq G β (n + 1) w - fatouSeq G β n w)

lemma fatouSeq_succ_sub (G : ℂ → ℂ) (β : ℂ) (n : ℕ) (w : ℂ) :
    fatouSeq G β (n + 1) w - fatouSeq G β n w = approxFatou β (G (G^[n] w)) - approxFatou β (G^[n] w) - 1 := by
  simp only [fatouSeq, Function.iterate_succ_apply']
  push_cast
  ring

/-- The terms of the series are bounded by `K / (re w + n / 2)^(1 + δ)` -/
lemma term_le (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) (n : ℕ) :
    ‖fatouSeq G β (n + 1) w - fatouSeq G β n w‖ ≤ errC β A / (w.re + n / 2) ^ (1 + δ) := by
  have mn : G^[n] w ∈ rightHalf R := (h.mapsTo.iterate n) m
  rw [fatouSeq_succ_sub]
  refine le_trans (h.approxFatou_step mn) ?_
  have r0 : 0 < w.re + n / 2 := by
    have := h.four_le; have n0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    simp only [rightHalf, mem_ofPred_eq] at m; linarith
  have le : w.re + n / 2 ≤ ‖G^[n] w‖ := le_trans (h.re_iter m n) (Complex.re_le_norm _)
  exact div_le_div_of_nonneg_left (errC_nonneg h) (Real.rpow_pos_of_pos r0 _)
    (Real.rpow_le_rpow r0.le le (by linarith [h.δ0]))

/-- `n ↦ K / (a + n / 2)^(1 + δ)` is summable for `a ≥ 1/2` -/
lemma summable_bound (h : NearTranslation G β R A δ) {a : ℝ} (a1 : 1 / 2 ≤ a) :
    Summable fun n : ℕ ↦ errC β A / (a + n / 2) ^ (1 + δ) := by
  have s1 : Summable fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + δ) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr (by linarith [h.δ0]))
  refine (s1.mul_left (errC β A * 2 ^ (1 + δ))).of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
  · have : 0 < a + n / 2 := by positivity
    exact div_nonneg (errC_nonneg h) (Real.rpow_nonneg this.le _)
  · have p0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / 2 := by positivity
    have le : ((n + 1 : ℕ) : ℝ) / 2 ≤ a + n / 2 := by push_cast; linarith
    have e : ((n + 1 : ℕ) : ℝ) ^ (1 + δ) = 2 ^ (1 + δ) * (((n + 1 : ℕ) : ℝ) / 2) ^ (1 + δ) := by
      rw [Real.div_rpow (by positivity) (by norm_num), mul_div_cancel₀ _ (by positivity)]
    rw [e]
    have hp := Real.rpow_pos_of_pos p0 (1 + δ)
    have h2 : (0 : ℝ) < 2 ^ (1 + δ) := by positivity
    calc errC β A / (a + n / 2) ^ (1 + δ)
        ≤ errC β A / (((n + 1 : ℕ) : ℝ) / 2) ^ (1 + δ) :=
          div_le_div_of_nonneg_left (errC_nonneg h) hp (Real.rpow_le_rpow p0.le le (by linarith [h.δ0]))
      _ = errC β A * 2 ^ (1 + δ) * (1 / (2 ^ (1 + δ) * (((n + 1 : ℕ) : ℝ) / 2) ^ (1 + δ))) := by
          field_simp

/-- The partial sums telescope: `Φ_N = φ + ∑_{n < N} (Φ_{n+1} - Φ_n)` -/
lemma fatouSeq_eq_sum (G : ℂ → ℂ) (β : ℂ) (N : ℕ) (w : ℂ) :
    fatouSeq G β N w =
      approxFatou β w + ∑ n ∈ Finset.range N, (fatouSeq G β (n + 1) w - fatouSeq G β n w) := by
  rw [Finset.sum_range_sub (fun n ↦ fatouSeq G β n w)]
  simp [fatouSeq]

/-- `Φ_N → Φ` uniformly on the half-plane -/
public lemma tendstoUniformlyOn_fatou (h : NearTranslation G β R A δ) :
    TendstoUniformlyOn (fatouSeq G β) (fatou G β) Filter.atTop (rightHalf R) := by
  have hs := h.summable_bound (a := R) (by linarith [h.four_le])
  have u := tendstoUniformlyOn_tsum_nat hs (s := rightHalf R)
    (f := fun n w ↦ fatouSeq G β (n + 1) w - fatouSeq G β n w) (fun n w m ↦ by
      refine le_trans (h.term_le m n) ?_
      have r : R + n / 2 ≤ w.re + n / 2 := by simp only [rightHalf, mem_ofPred_eq] at m; linarith
      have n0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact div_le_div_of_nonneg_left (errC_nonneg h)
        (Real.rpow_pos_of_pos (by linarith [h.four_le]) _)
        (Real.rpow_le_rpow (by linarith [h.four_le]) r (by linarith [h.δ0])))
  -- adding the fixed function `φ` keeps the convergence uniform
  rw [Metric.tendstoUniformlyOn_iff] at u ⊢
  intro ε ε0
  filter_upwards [u ε ε0] with N hN w m
  rw [fatouSeq_eq_sum, fatou, dist_add_left]
  exact hN w m

/-- The half-plane is open -/
public lemma isOpen_rightHalf (R : ℝ) : IsOpen (rightHalf R) :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Iterates of `G` are analytic on the half-plane -/
lemma iterate_analytic (h : NearTranslation G β R A δ) (n : ℕ) : AnalyticOnNhd ℂ G^[n] (rightHalf R) := by
  induction n with
  | zero => exact analyticOnNhd_id
  | succ n ih =>
    intro w m
    rw [Function.iterate_succ']
    exact (h.ga _ ((h.mapsTo.iterate n) m)).comp (ih w m)

/-- `φ` is analytic on the half-plane -/
lemma approxFatou_analytic (h : NearTranslation G β R A δ) : AnalyticOnNhd ℂ (approxFatou β) (rightHalf R) :=
  fun _ m ↦ analyticAt_id.sub (analyticAt_const.mul (analyticAt_clog (h.mem_slitPlane m)))

lemma fatouSeq_analytic (h : NearTranslation G β R A δ) (n : ℕ) :
    AnalyticOnNhd ℂ (fatouSeq G β n) (rightHalf R) := fun w m ↦
  ((h.approxFatou_analytic _ ((h.mapsTo.iterate n) m)).comp (h.iterate_analytic n w m)).sub analyticAt_const

/-- The Fatou coordinate is analytic on the half-plane -/
public theorem fatou_analytic (h : NearTranslation G β R A δ) : AnalyticOnNhd ℂ (fatou G β) (rightHalf R) :=
  uniform_analytic_lim (isOpen_rightHalf R) h.fatouSeq_analytic h.tendstoUniformlyOn_fatou

/-- The Fatou coordinate conjugates `G` to the translation by `1`: `Φ (G w) = Φ w + 1` -/
public theorem fatou_eqn (h : NearTranslation G β R A δ) {w : ℂ} (m : w ∈ rightHalf R) :
    fatou G β (G w) = fatou G β w + 1 := by
  have t1 := h.tendstoUniformlyOn_fatou.tendsto_at (h.mapsTo m)
  have t2 := (h.tendstoUniformlyOn_fatou.tendsto_at m).comp (Filter.tendsto_add_atTop_nat 1)
  have e : (fun N ↦ fatouSeq G β N (G w)) = fun N ↦ fatouSeq G β (N + 1) w + 1 := by
    funext N
    simp only [fatouSeq, Function.iterate_succ_apply]
    push_cast
    ring
  rw [e] at t1
  exact tendsto_nhds_unique t1 (t2.add_const 1)

end NearTranslation
