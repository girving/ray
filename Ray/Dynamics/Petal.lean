module
public import Ray.Dynamics.FatouRepel
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Bound

/-!
## Petals of a tangent-to-identity germ

A germ `g z = z + a z^(k+1) + b z^(2k+1) + O(z^(2k+2))` with `a ≠ 0` (petal normal form) has `k` attracting and `k`
repelling petals at `0`.  The petal coordinate `w = -1 / (k a z^k)` turns each into a half-plane neighbourhood of `∞`
on which `g` is a near-translation:

  `G w = w + 1 + β / w + O(‖w‖^(-1-1/k))`,   `β = (k + 1) / (2k) - b / (k a²)`

(`β` is the iterative residue).  Each petal is a branch `z = c exp (-log w / k)` of the inverse of the coordinate,
one for each `k`-th root `c` of `-1 / (k a)` (attracting, `re w > R`) or of `1 / (k a)` (repelling, `w` near `∞` off
the ray `[0, ∞)`).  We prove:

1. `PetalGerm.attracting`: on each attracting petal, `G` is a `NearTranslation`, and the petal branch `ψ` of the
   inverse of the coordinate semiconjugates it to `g`: `g (ψ w) = ψ (G w)`.
2. `PetalGerm.repelling`: on each repelling petal, `G` is a `NearTranslationOut`, and `g (ψ w) = ψ (G w)` on a left
   half-plane.

Branch consistency (`g (ψ w)` and `ψ (G w)` are the same `k`-th root, not two that differ by a root of unity) holds
because both are within a factor `exp L` of `ψ w` with `k ‖L‖ < 2π`.

The estimate is an expansion in `z` near `0`: with `g z = z (1 + u)`, `G w = w (1 + u)^(-k)`, and
`(1 + u)^(-k) = 1 - k u + k (k + 1) / 2 u² + O(u³)`.
-/

open Asymptotics Filter
open Complex (exp log slitPlane)
open Set
open scoped Real Topology

/-- The petal coordinate `w = -1 / (k a z^k)` -/
@[expose] public noncomputable def petalCoord (k : ℕ) (a z : ℂ) : ℂ := -1 / (k * a * z ^ k)

/-- The branch `z = c exp (-log s / k)` of `z^k = c^k / s`: the inverse of the petal coordinate on a petal -/
@[expose] public noncomputable def petalRoot (k : ℕ) (c s : ℂ) : ℂ := c * exp (-log s / k)

/-- The iterative residue `β` of `z + a z^(k+1) + b z^(2k+1)`: `G w = w + 1 + β / w + ...` in the petal coordinate -/
@[expose] public noncomputable def petalResidue (k : ℕ) (a b : ℂ) : ℂ := (k + 1) / (2 * k) - b / (k * a ^ 2)

/-- `g` is in petal normal form: `g z = z + a z^(k+1) + b z^(2k+1) + O(z^(2k+2))` near `0`, with `a ≠ 0` -/
public structure PetalGerm (g : ℂ → ℂ) (k : ℕ) (a b : ℂ) : Prop where
  k0 : 0 < k
  a0 : a ≠ 0
  ga : AnalyticAt ℂ g 0
  approx : (fun z ↦ g z - (z + a * z ^ (k + 1) + b * z ^ (2 * k + 1))) =O[𝓝 0] fun z ↦ z ^ (2 * k + 2)

/-!
### Power expansions
-/

public lemma pow_isBigO_pow {m n : ℕ} (h : m ≤ n) : (fun z : ℂ ↦ z ^ n) =O[𝓝 0] fun z ↦ z ^ m := by
  rcases h.lt_or_eq with h | h
  · exact (isLittleO_pow_pow h).isBigO
  · subst h; exact isBigO_refl _ _

/-- `(1 + u)^k = 1 + k u + k (k - 1) / 2 u² + O(u³)` -/
public lemma one_add_pow_expand (k : ℕ) :
    (fun u : ℂ ↦ (1 + u) ^ k - (1 + k * u + k * (k - 1) / 2 * u ^ 2)) =O[𝓝 0] fun u ↦ u ^ 3 := by
  induction k with
  | zero => exact (isBigO_zero (fun u : ℂ ↦ u ^ 3) _).congr_left (fun u ↦ by simp)
  | succ k ih =>
    have e : ∀ u : ℂ, (1 + u) ^ (k + 1) - (1 + ↑(k + 1) * u + ↑(k + 1) * (↑(k + 1) - 1) / 2 * u ^ 2) =
        (1 + u) * ((1 + u) ^ k - (1 + k * u + k * (k - 1) / 2 * u ^ 2)) + k * (k - 1) / 2 * u ^ 3 := by
      intro u; push_cast; ring
    simp only [e]
    have t : Tendsto (fun u : ℂ ↦ 1 + u) (𝓝 0) (𝓝 1) := by
      have c : Continuous (fun u : ℂ ↦ 1 + u) := by fun_prop
      simpa using c.tendsto 0
    exact (t.isBigO_one ℂ |>.mul ih |>.congr_right (by simp)).add ((isBigO_refl _ _).const_mul_left _)

/-- `(1 + u)^(-k) = 1 - k u + k (k + 1) / 2 u² + O(u³)` -/
lemma one_add_pow_inv_expand (k : ℕ) :
    (fun u : ℂ ↦ ((1 + u) ^ k)⁻¹ - (1 - k * u + k * (k + 1) / 2 * u ^ 2)) =O[𝓝 0] fun u ↦ u ^ 3 := by
  set Q : ℂ → ℂ := fun u ↦ 1 + k * u + k * (k - 1) / 2 * u ^ 2
  set P : ℂ → ℂ := fun u ↦ 1 - k * u + k * (k + 1) / 2 * u ^ 2
  have t : Tendsto (fun u : ℂ ↦ ((1 + u) ^ k)⁻¹) (𝓝 0) (𝓝 1) := by
    have c : ContinuousAt (fun u : ℂ ↦ ((1 + u) ^ k)⁻¹) 0 :=
      ((continuous_const.add continuous_id).pow k).continuousAt.inv₀ (by simp)
    simpa using c.tendsto
  have tP : Tendsto P (𝓝 0) (𝓝 1) := by
    have c : Continuous P := by fun_prop
    simpa [P] using c.tendsto (0 : ℂ)
  -- `(1 + u)^(-k) - P = (1 + u)^(-k) ((Q - (1 + u)^k) P + (1 - Q P))`, and `1 - Q P = -u³ (k² + k² (k² - 1) / 4 u)`
  have e : ∀ᶠ u : ℂ in 𝓝 0, ((1 + u) ^ k)⁻¹ * (-((1 + u) ^ k - Q u) * P u -
      u ^ 3 * (k ^ 2 + k ^ 2 * (k ^ 2 - 1) / 4 * u)) = ((1 + u) ^ k)⁻¹ - P u := by
    have n : ∀ᶠ u : ℂ in 𝓝 0, 1 + u ≠ 0 :=
      (continuous_const.add continuous_id).continuousAt.eventually_ne (by simp)
    filter_upwards [n] with u n
    have : (1 + u) ^ k ≠ 0 := pow_ne_zero _ n
    field_simp
    simp only [P, Q]; ring
  refine IsBigO.congr' ?_ e (by rfl)
  have q : (fun u ↦ k ^ 2 + k ^ 2 * (k ^ 2 - 1) / 4 * u : ℂ → ℂ) =O[𝓝 0] fun _ ↦ (1 : ℂ) :=
    (Continuous.tendsto (by fun_prop) 0).isBigO_one ℂ
  refine (t.isBigO_one ℂ).mul (((one_add_pow_expand k).neg_left.mul (tP.isBigO_one ℂ)).sub
    ((isBigO_refl _ _).mul q)) |>.congr_right ?_
  intro u; simp

/-!
### The expansion near `0`
-/

namespace PetalGerm

variable {g : ℂ → ℂ} {k : ℕ} {a b : ℂ}

/-- The error term `g z - (z + a z^(k+1) + b z^(2k+1))` -/
noncomputable def err (g : ℂ → ℂ) (k : ℕ) (a b z : ℂ) : ℂ := g z - (z + a * z ^ (k + 1) + b * z ^ (2 * k + 1))

/-- `g z = z (1 + u z)` -/
noncomputable def pu (g : ℂ → ℂ) (k : ℕ) (a b z : ℂ) : ℂ := a * z ^ k + b * z ^ (2 * k) + err g k a b z / z

/-- `(1 + u)^(-k) - 1 + k a z^k - β k² a² z^(2k)`: the petal step error, divided by the petal coordinate -/
noncomputable def pF (g : ℂ → ℂ) (k : ℕ) (a b z : ℂ) : ℂ :=
  ((1 + pu g k a b z) ^ k)⁻¹ - 1 + k * a * z ^ k - petalResidue k a b * k ^ 2 * a ^ 2 * z ^ (2 * k)

lemma g_eq {z : ℂ} (z0 : z ≠ 0) : g z = z * (1 + pu g k a b z) := by
  simp only [pu, err]; field_simp; ring

lemma v_isBigO (h : PetalGerm g k a b) :
    (fun z ↦ err g k a b z / z) =O[𝓝 0] fun z ↦ z ^ (2 * k + 1) := by
  obtain ⟨C, hC⟩ := h.approx.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with z hz
  by_cases z0 : z = 0
  · simp [z0]
  · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr z0)]
    calc ‖err g k a b z‖ ≤ C * ‖z ^ (2 * k + 2)‖ := hz
      _ = C * ‖z ^ (2 * k + 1)‖ * ‖z‖ := by rw [pow_succ z (2 * k + 1), norm_mul]; ring

lemma u_isBigO (h : PetalGerm g k a b) : (fun z ↦ pu g k a b z) =O[𝓝 0] fun z ↦ z ^ k := by
  have e1 := (isBigO_refl (fun z : ℂ ↦ z ^ k) (𝓝 0)).const_mul_left a
  have e2 := (pow_isBigO_pow (by omega : k ≤ 2 * k)).const_mul_left b
  have e3 := h.v_isBigO.trans (pow_isBigO_pow (by omega : k ≤ 2 * k + 1))
  exact (e1.add e2).add e3

lemma u_sub_isBigO (h : PetalGerm g k a b) :
    (fun z ↦ pu g k a b z - a * z ^ k) =O[𝓝 0] fun z ↦ z ^ (2 * k) := by
  have e2 := (isBigO_refl (fun z : ℂ ↦ z ^ (2 * k)) (𝓝 0)).const_mul_left b
  have e3 := h.v_isBigO.trans (pow_isBigO_pow (by omega : 2 * k ≤ 2 * k + 1))
  refine (e2.add e3).congr_left fun z ↦ ?_
  simp only [pu]; ring

lemma u_tendsto (h : PetalGerm g k a b) : Tendsto (fun z ↦ pu g k a b z) (𝓝 0) (𝓝 0) := by
  refine h.u_isBigO.trans_tendsto ?_
  have := (continuous_pow k).tendsto (0 : ℂ)
  simpa [zero_pow h.k0.ne'] using this

lemma F_isBigO (h : PetalGerm g k a b) : (fun z ↦ pF g k a b z) =O[𝓝 0] fun z ↦ z ^ (2 * k + 1) := by
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.k0.ne'
  have a0 := h.a0
  have k1 := h.k0
  have e1 := (one_add_pow_inv_expand k).comp_tendsto h.u_tendsto
  have e2 : (fun z ↦ pu g k a b z ^ 3) =O[𝓝 0] fun z ↦ z ^ (2 * k + 1) := by
    refine (h.u_isBigO.pow 3).trans ?_
    refine (pow_isBigO_pow (by omega : 2 * k + 1 ≤ k * 3)).congr_left fun z ↦ ?_
    rw [pow_mul]
  have e4 : (fun z ↦ (pu g k a b z - a * z ^ k) * (pu g k a b z + a * z ^ k)) =O[𝓝 0]
      fun z ↦ z ^ (2 * k + 1) := by
    have u_add := h.u_isBigO.add ((isBigO_refl (fun z : ℂ ↦ z ^ k) (𝓝 0)).const_mul_left a)
    refine (h.u_sub_isBigO.mul u_add).trans ?_
    refine (pow_isBigO_pow (by omega : 2 * k + 1 ≤ 2 * k + k)).congr_left fun z ↦ ?_
    rw [pow_add]
  refine ((e1.trans e2).add ((h.v_isBigO.const_mul_left (-(k : ℂ))).add
    (e4.const_mul_left ((k : ℂ) * (k + 1) / 2)))).congr_left fun z ↦ ?_
  simp only [Function.comp_apply, pF]
  generalize hX : ((1 + pu g k a b z) ^ k)⁻¹ = X
  simp only [pu, petalResidue]
  field_simp
  ring

/-- The core estimate near `0`: `w (g z) = w z + 1 + β / w z + O(‖z‖^(k+1))` for the petal coordinate `w` -/
lemma core (h : PetalGerm g k a b) : ∃ C ε : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε →
    AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ (∃ u, g z = z * (1 + u) ∧ k * ‖u‖ ≤ 1 / 2) ∧ ‖petalCoord k a (g z) - (petalCoord k a z + 1 + petalResidue k a b /
      petalCoord k a z)‖ ≤ C * ‖z‖ ^ (k + 1) := by
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.k0.ne'
  have a0 := h.a0
  obtain ⟨C, C0, hC⟩ := h.F_isBigO.exists_pos
  have hu : ∀ᶠ z in 𝓝 (0 : ℂ), ‖pu g k a b z‖ < 1 / (2 * k) := by
    have t := h.u_tendsto.norm
    rw [norm_zero] at t
    exact t.eventually (gt_mem_nhds (by have := h.k0; positivity))
  obtain ⟨ε, ε0, hε⟩ := Metric.eventually_nhds_iff.mp (hC.bound.and (hu.and h.ga.eventually_analyticAt))
  have ka : 0 < (k : ℝ) * ‖a‖ := mul_pos (Nat.cast_pos.mpr h.k0) (norm_pos_iff.mpr a0)
  refine ⟨C / (k * ‖a‖), ε, ε0, by positivity, fun z z0 zε ↦ ?_⟩
  obtain ⟨hF, hu, ha⟩ := hε (by simpa using zε)
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast h.k0
  have ku : k * ‖pu g k a b z‖ ≤ 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at hu; linarith
  have u1 : 1 + pu g k a b z ≠ 0 := by
    intro e
    have : pu g k a b z = -1 := by linear_combination e
    rw [this] at ku; norm_num at ku; linarith
  have gz : g z = z * (1 + pu g k a b z) := g_eq z0
  have g0 : g z ≠ 0 := by rw [gz]; exact mul_ne_zero z0 u1
  refine ⟨ha, g0, ⟨_, gz, ku⟩, ?_⟩
  have e : petalCoord k a (g z) - (petalCoord k a z + 1 + petalResidue k a b / petalCoord k a z) =
      petalCoord k a z * pF g k a b z := by
    simp only [petalCoord, pF, gz, mul_pow]
    generalize hU : pu g k a b z = U at u1
    field_simp
    ring
  have nz : 0 < ‖z‖ := norm_pos_iff.mpr z0
  have nw : ‖petalCoord k a z‖ = (k * ‖a‖ * ‖z‖ ^ k)⁻¹ := by
    simp [petalCoord]
  rw [e, norm_mul, nw, inv_mul_le_iff₀ (by positivity)]
  calc ‖pF g k a b z‖ ≤ C * ‖z ^ (2 * k + 1)‖ := hF
    _ = k * ‖a‖ * ‖z‖ ^ k * (C / (k * ‖a‖) * ‖z‖ ^ (k + 1)) := by
      have : (k : ℝ) ≠ 0 := ka.ne' |> fun h e ↦ h (by simp [e])
      rw [norm_pow]; field_simp; ring

/-- Any `z` with `z^k = -1 / (k a w)`, for `w` far out, has `w (g z) = w + 1 + β / w + O(‖w‖^(-1-1/k))` -/
lemma transfer (h : PetalGerm g k a b) : ∃ R₀ A : ℝ, 0 ≤ A ∧ ∀ w z : ℂ, R₀ < ‖w‖ → z ^ k = -1 / (k * a * w) →
    AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ (∃ u, g z = z * (1 + u) ∧ k * ‖u‖ ≤ 1 / 2) ∧ petalCoord k a z = w ∧
      ‖petalCoord k a (g z) - (w + 1 + petalResidue k a b / w)‖ ≤ A / ‖w‖ ^ (1 + (k : ℝ)⁻¹) := by
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.k0.ne'
  have kr0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.k0.ne'
  have a0 := h.a0
  obtain ⟨C, ε, ε0, C0, hc⟩ := h.core
  set t : ℝ := k * ‖a‖
  have t0 : 0 < t := mul_pos (Nat.cast_pos.mpr h.k0) (norm_pos_iff.mpr a0)
  refine ⟨(t * ε ^ k)⁻¹, C * t⁻¹ ^ (1 + (k : ℝ)⁻¹), by positivity, fun w z wR zk ↦ ?_⟩
  have w0 : 0 < ‖w‖ := lt_of_le_of_lt (by positivity) wR
  have z0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow h.k0.ne'] at zk
    have : (k : ℂ) * a * w ≠ 0 := mul_ne_zero (mul_ne_zero k0 a0) (norm_pos_iff.mp w0)
    exact div_ne_zero (by norm_num) this zk.symm
  have nzk : ‖z‖ ^ k = (t * ‖w‖)⁻¹ := by
    rw [← norm_pow, zk]; simp [t, mul_assoc]
  have zε : ‖z‖ < ε := by
    refine (pow_lt_pow_iff_left₀ (norm_nonneg _) ε0.le h.k0.ne').mp ?_
    rw [nzk, inv_lt_comm₀ (by positivity) (by positivity)]
    rw [inv_lt_iff_one_lt_mul₀ (by positivity)] at wR
    rw [inv_eq_one_div, div_lt_iff₀ (by positivity)]
    linarith
  obtain ⟨ga, g0, hu, hz⟩ := hc z z0 zε
  have pw : petalCoord k a z = w := by
    simp only [petalCoord, zk]
    have : (k : ℂ) * a ≠ 0 := mul_ne_zero k0 a0
    field_simp
  refine ⟨ga, g0, hu, pw, ?_⟩
  rw [pw] at hz
  refine le_trans hz (le_of_eq ?_)
  have z1 : ‖z‖ = (t * ‖w‖)⁻¹ ^ (k⁻¹ : ℝ) := by
    rw [← nzk, Real.pow_rpow_inv_natCast (norm_nonneg _) h.k0.ne']
  rw [pow_succ, nzk, z1, ← Real.rpow_one_add' (by positivity) (by positivity), mul_inv,
    Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow w0.le, ← div_eq_mul_inv, mul_div_assoc]

/-- `c exp (-log w / k)` is a `k`-th root of `c^k / w` -/
public lemma root_pow {c w : ℂ} (w0 : w ≠ 0) (k0 : 0 < k) : (petalRoot k c w) ^ k = c ^ k / w := by
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  rw [petalRoot, mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ k0, Complex.exp_neg, Complex.exp_log w0, div_eq_mul_inv]

public lemma analyticAt_root {c w : ℂ} (m : w ∈ slitPlane) : AnalyticAt ℂ (fun w ↦ petalRoot k c w) w :=
  analyticAt_const.mul ((analyticAt_clog m).neg.div_const).cexp

public lemma analyticAt_petalCoord {y : ℂ} (y0 : y ≠ 0) (k0 : (k : ℂ) ≠ 0) (a0 : a ≠ 0) :
    AnalyticAt ℂ (petalCoord k a) y :=
  analyticAt_const.div (analyticAt_const.mul (analyticAt_id.pow k))
    (mul_ne_zero (mul_ne_zero k0 a0) (pow_ne_zero _ y0))

/-- Two `k`-th roots that differ by a factor `exp L` with `k ‖L‖ < 2π` are equal -/
lemma root_eq {x L : ℂ} (k0 : 0 < k) (e : (x * exp L) ^ k = x ^ k) (x0 : x ≠ 0)
    (small : k * ‖L‖ < 2 * π) : x * exp L = x := by
  have xk : x ^ k ≠ 0 := pow_ne_zero _ x0
  have e1 : exp (k * L) = 1 := by
    rw [mul_pow, ← Complex.exp_nat_mul] at e
    calc exp (k * L) = x ^ k * exp (k * L) / x ^ k := by field_simp
      _ = 1 := by rw [e, div_self xk]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e1
  have nk : ‖(k : ℂ) * L‖ = |(n : ℝ)| * (2 * π) := by
    rw [hn, norm_mul, Complex.norm_intCast]
    simp [abs_of_pos Real.pi_pos]
  have n0 : n = 0 := by
    rw [norm_mul, Complex.norm_natCast] at nk
    have : |(n : ℝ)| < 1 := by
      by_contra c
      push Not at c
      nlinarith [Real.pi_pos]
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast this)
  have L0 : L = 0 := by
    have kr : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
    simpa [n0, kr] using hn
  simp [L0]

/-- Branch consistency: if `z (1 + u)` and the root `c exp (-log s' / k)` have the same `k`-th power, `s' ≈ s` and
`u ≈ 0`, they are equal -/
lemma branch {c s s' u u' : ℂ} (k0 : 0 < k) (c0 : c ≠ 0) (sr : 0 < s.re) (hs : s' = s * (1 + u'))
    (un' : ‖u'‖ ≤ 5 / 16) (un : k * ‖u‖ ≤ 1 / 2)
    (e : (petalRoot k c s * (1 + u)) ^ k = (petalRoot k c s') ^ k) :
    petalRoot k c s * (1 + u) = petalRoot k c s' := by
  have kr : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast k0
  have ur : 0 < (1 + u').re := by
    have := Complex.abs_re_le_norm u'
    simp only [Complex.add_re, Complex.one_re]
    rw [abs_le] at this; linarith
  have u'0 : 1 + u' ≠ 0 := fun z ↦ by simp [z] at ur
  have s0 : s ≠ 0 := fun z ↦ by simp [z] at sr
  have un1 : ‖u‖ ≤ 1 / 2 := by nlinarith [norm_nonneg u]
  have u0 : 1 + u ≠ 0 := by
    intro z
    have : u = -1 := by linear_combination z
    rw [this] at un1; norm_num at un1
  have hlog : log s' = log s + log (1 + u') := by
    rw [hs]
    refine (Complex.log_mul_eq_add_log_iff s0 u'0).mpr ?_
    have a1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl sr)
    have a2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ur)
    rw [abs_lt] at a1 a2
    constructor <;> linarith
  set L := log (1 + u') / k + log (1 + u)
  have ex : petalRoot k c s * (1 + u) = petalRoot k c s' * exp L := by
    simp only [petalRoot, L, hlog, Complex.exp_add, Complex.exp_log u0]
    have : -log s / k = -(log s + log (1 + u')) / k + log (1 + u') / k := by ring
    rw [this, Complex.exp_add]; ring
  rw [ex] at e ⊢
  refine root_eq k0 e (mul_ne_zero c0 (Complex.exp_ne_zero _)) ?_
  have l1 := Complex.norm_log_one_add_half_le_self (z := u') (by linarith)
  have l2 := Complex.norm_log_one_add_half_le_self (z := u) un1
  have kp : (0 : ℝ) < k := by linarith
  calc k * ‖L‖ ≤ k * (‖log (1 + u')‖ / k + ‖log (1 + u)‖) := by
        gcongr
        refine le_trans (norm_add_le _ _) (le_of_eq ?_)
        rw [norm_div, Complex.norm_natCast]
    _ = ‖log (1 + u')‖ + k * ‖log (1 + u)‖ := by field_simp
    _ ≤ 3 / 2 * (5 / 16) + 3 / 2 * (k * ‖u‖) := by nlinarith
    _ < 2 * π := by nlinarith [Real.two_le_pi]

/-- A near-translation step moves at most `5/4` -/
lemma step_le {w w' : ℂ} (d : ‖w' - (w + 1)‖ ≤ 1 / 4) : ‖w' - w‖ ≤ 5 / 4 := by
  calc ‖w' - w‖ = ‖(w' - (w + 1)) + 1‖ := by ring_nf
    _ ≤ ‖w' - (w + 1)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 5 / 4 := by rw [norm_one]; linarith

/-- `w' = w (1 + u')` with `‖u'‖ ≤ 5/16`, for a near-translation step -/
lemma step_ratio {w w' : ℂ} (n4 : 4 ≤ ‖w‖) (dn : ‖w' - w‖ ≤ 5 / 4) :
    ∃ u', w' = w * (1 + u') ∧ ‖u'‖ ≤ 5 / 16 := by
  have n0 : 0 < ‖w‖ := by linarith
  have w0 : w ≠ 0 := norm_pos_iff.mp n0
  refine ⟨(w' - w) / w, by field_simp; ring, ?_⟩
  rw [norm_div, div_le_iff₀ n0]; linarith

/-- On each attracting petal, `g` is a near-translation in the petal coordinate, and the petal branch
`ψ w = c exp (-log w / k)` of the inverse of `w = -1 / (k a z^k)` semiconjugates it to `g`: `g (ψ w) = ψ (G w)`.
There is one petal for each `k`-th root `c` of `-1 / (k a)`. -/
public theorem attracting (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = -1 / (k * a)) :
    ∃ R A, NearTranslation (fun w ↦ petalCoord k a (g (petalRoot k c w))) (petalResidue k a b) R A (k : ℝ)⁻¹ ∧
      ∀ w ∈ rightHalf R, g (petalRoot k c w) = petalRoot k c (petalCoord k a (g (petalRoot k c w))) := by
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.k0.ne'
  have a0 := h.a0
  have c0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow h.k0.ne'] at hc
    exact div_ne_zero (by norm_num) (mul_ne_zero k0 a0) hc.symm
  obtain ⟨R₀, A, A0, ht⟩ := h.transfer
  set R := max R₀ (max 4 (4 * (‖petalResidue k a b‖ + A)))
  have w4 : 4 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hw : ∀ w ∈ rightHalf R, R₀ < ‖w‖ ∧ (petalRoot k c w) ^ k = -1 / (k * a * w) ∧ w ∈ slitPlane :=
      fun w (m : R < w.re) ↦ by
    have wR : R₀ < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le m (Complex.re_le_norm w))
    have w0 : w ≠ 0 := by rintro rfl; simp at m; linarith
    have zk : (petalRoot k c w) ^ k = -1 / (k * a * w) := by
      rw [root_pow w0 h.k0, hc]; field_simp
    exact ⟨wR, zk, by rw [Complex.mem_slitPlane_iff]; left; linarith⟩
  have nt : NearTranslation (fun w ↦ petalCoord k a (g (petalRoot k c w))) (petalResidue k a b) R A (k : ℝ)⁻¹ := {
    four_le := w4
    large := le_trans (le_max_right _ _) (le_max_right _ _)
    A0 := A0
    δ0 := by have := h.k0; positivity
    δ1 := inv_le_one_of_one_le₀ (by exact_mod_cast h.k0)
    ga := fun w m ↦ by
      obtain ⟨wR, zk, sm⟩ := hw w m
      obtain ⟨ga, g0, -, -, -⟩ := ht w _ wR zk
      exact (analyticAt_petalCoord g0 k0 h.a0).comp (f := fun w ↦ g (petalRoot k c w))
        (ga.comp (f := fun w ↦ petalRoot k c w) (analyticAt_root sm))
    approx := fun w m ↦ (ht w _ (hw w m).1 (hw w m).2.1).2.2.2.2 }
  refine ⟨R, A, nt, fun w m ↦ ?_⟩
  obtain ⟨wR, zk, -⟩ := hw w m
  obtain ⟨-, g0, ⟨u, gu, ku⟩, -, -⟩ := ht w _ wR zk
  set w' := petalCoord k a (g (petalRoot k c w)) with hw'
  have m' : w' ∈ rightHalf R := nt.mapsTo m
  have w'0 : w' ≠ 0 := by rintro e; rw [e] at m'; simp [rightHalf] at m'; linarith
  have wr : 0 < w.re := by have : R < w.re := m; linarith
  have d : ‖w' - (w + 1)‖ ≤ 1 / 4 := nt.dev_le m
  have wR' : R < w.re := m
  obtain ⟨u', hs, un'⟩ := step_ratio (by linarith [Complex.re_le_norm w]) (step_le d)
  rw [gu]
  refine branch h.k0 c0 wr hs un' ku ?_
  rw [← gu, root_pow w'0 h.k0, hc]
  have gk : g (petalRoot k c w) ^ k ≠ 0 := pow_ne_zero _ g0
  simp only [hw', petalCoord]
  field_simp

/-- On each repelling petal, `g` is a near-translation (near `∞`, off the ray `[0, ∞)`) in the petal coordinate, and
the petal branch `ψ w = c exp (-log (-w) / k)` of the inverse of `w = -1 / (k a z^k)` semiconjugates it to `g` on a
left half-plane: `g (ψ w) = ψ (G w)`.  There is one petal for each `k`-th root `c` of `1 / (k a)`. -/
public theorem repelling (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = 1 / (k * a)) :
    ∃ R A, NearTranslationOut (fun w ↦ petalCoord k a (g (petalRoot k c (-w)))) (petalResidue k a b) R A
      (k : ℝ)⁻¹ ∧
      ∀ w ∈ leftHalf R, g (petalRoot k c (-w)) = petalRoot k c (-petalCoord k a (g (petalRoot k c (-w)))) := by
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h.k0.ne'
  have a0 := h.a0
  have c0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow h.k0.ne'] at hc
    exact div_ne_zero one_ne_zero (mul_ne_zero k0 a0) hc.symm
  obtain ⟨R₀, A, A0, ht⟩ := h.transfer
  set R := max R₀ (max 4 (4 * (‖petalResidue k a b‖ + A)))
  have w4 : 4 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have hw : ∀ w ∈ slitOut R, R₀ < ‖w‖ ∧ (petalRoot k c (-w)) ^ k = -1 / (k * a * w) ∧ -w ∈ slitPlane :=
      fun w (m : R < ‖w‖ ∧ (w.re < 0 ∨ w.im ≠ 0)) ↦ by
    have wR : R₀ < ‖w‖ := lt_of_le_of_lt (le_max_left _ _) m.1
    have w0 : w ≠ 0 := by rintro rfl; simp at m
    have zk : (petalRoot k c (-w)) ^ k = -1 / (k * a * w) := by
      rw [root_pow (neg_ne_zero.mpr w0) h.k0, hc]; field_simp
    refine ⟨wR, zk, ?_⟩
    rw [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im]
    rcases m.2 with r | i
    · left; linarith
    · right; exact neg_ne_zero.mpr i
  have nt : NearTranslationOut (fun w ↦ petalCoord k a (g (petalRoot k c (-w)))) (petalResidue k a b) R A
      (k : ℝ)⁻¹ := {
    four_le := w4
    large := le_trans (le_max_right _ _) (le_max_right _ _)
    A0 := A0
    δ0 := by have := h.k0; positivity
    δ1 := inv_le_one_of_one_le₀ (by exact_mod_cast h.k0)
    ga := fun w m ↦ by
      obtain ⟨wR, zk, sm⟩ := hw w m
      obtain ⟨ga, g0, -, -, -⟩ := ht w _ wR zk
      have r : AnalyticAt ℂ (fun w ↦ petalRoot k c (-w)) w :=
        (analyticAt_root (k := k) (c := c) sm).comp (f := fun w ↦ -w) (x := w) analyticAt_id.neg
      exact (analyticAt_petalCoord g0 k0 h.a0).comp (f := fun w ↦ g (petalRoot k c (-w)))
        (ga.comp (f := fun w ↦ petalRoot k c (-w)) r)
    approx := fun w m ↦ (ht w _ (hw w m).1 (hw w m).2.1).2.2.2.2 }
  refine ⟨R, A, nt, fun w (m : w.re < -R) ↦ ?_⟩
  have wn : R < ‖w‖ := by
    have := Complex.abs_re_le_norm w; rw [abs_le] at this; linarith
  have ms : w ∈ slitOut R := ⟨wn, Or.inl (by linarith)⟩
  obtain ⟨wR, zk, -⟩ := hw w ms
  obtain ⟨-, g0, ⟨u, gu, ku⟩, -, -⟩ := ht w _ wR zk
  set w' := petalCoord k a (g (petalRoot k c (-w))) with hw'
  have d : ‖w' - (w + 1)‖ ≤ 1 / 4 := by simpa [sub_sub] using nt.eps_le_quarter ms
  have d' := step_le d
  obtain ⟨u', hs, un'⟩ := step_ratio (w := -w) (w' := -w') (by rw [norm_neg]; linarith)
    (by rw [show -w' - -w = -(w' - w) by ring, norm_neg]; exact d')
  have w'0 : w' ≠ 0 := by
    rintro e; rw [e, zero_sub, norm_neg] at d'; linarith
  have sr : 0 < (-w).re := by rw [Complex.neg_re]; linarith
  rw [gu]
  refine branch h.k0 c0 sr hs un' ku ?_
  rw [← gu, root_pow (neg_ne_zero.mpr w'0) h.k0, hc]
  have gk : g (petalRoot k c (-w)) ^ k ≠ 0 := pow_ne_zero _ g0
  simp only [hw', petalCoord]
  field_simp

end PetalGerm
