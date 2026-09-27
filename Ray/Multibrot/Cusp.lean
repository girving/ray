module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Bound

/-!
## Slow escape through the parabolic gate at the cusp `c = 1/4`

For real `c = 1/4 + s^2` with small `s > 0`, the critical orbit `z_0 = 0, z_{n+1} = z_n^2 + c` creeps
through the gap between the two nearby fixed points, taking about `π / s` steps.  Writing
`u_n = z_n - 1/2` and `φ(u) = u^2 + s^2`, the orbit is `u_{n+1} = u_n + φ(u_n)`.

We prove:
1. `u_le_of_mul_le`: the passage is slow: `u_n ≤ s` while `n s ≤ 1`.
2. `sum_inv_phi_le`: `∑ 1 / φ(u_k) ≤ 18 (1 + π) / s^3` while `u_k ≤ 7/5`, by telescoping the potential
   `H(u) = u / (2 s^2 φ(u)) + arctan(u / s) / (2 s^3)`, whose derivative is `1 / φ(u)^2`.
3. `shadow`: complex orbits of `c + h` with `|h| ≲ s^3` stay within `τ_n φ(u_n)` of the real orbit,
   where `τ_n = |h| ∑_{k ≤ n} 1 / φ(u_k)`.

These show that a rectangle of area `≍ s^5` outside the Mandelbrot set escapes only after `≍ 1/s`
steps.  This lower-bounds the area near the set with small Green's function, and so lower-bounds
the tail of the Grönwall series.
-/

open Real (arctan)
open scoped Real
open Set

namespace Cusp

variable {s : ℝ}

/-- `φ(u) = u^2 + s^2`, the step size of the real orbit at `u` -/
@[expose] public def φ (s u : ℝ) : ℝ := u ^ 2 + s ^ 2

/-- The real orbit, shifted by `1/2`: `u_n = z_n - 1/2` where `z_0 = 0`, `z_{n+1} = z_n^2 + 1/4 + s^2` -/
@[expose] public noncomputable def u (s : ℝ) : ℕ → ℝ
  | 0 => -1 / 2
  | n + 1 => u s n + φ s (u s n)

@[simp] public lemma u_zero : u s 0 = -1 / 2 := rfl
public lemma u_succ (n : ℕ) : u s (n + 1) = u s n + φ s (u s n) := rfl

public lemma φ_pos (s0 : 0 < s) (x : ℝ) : 0 < φ s x := by unfold φ; positivity

/-- The shifted orbit is the orbit of `z ↦ z^2 + 1/4 + s^2` -/
public lemma u_succ_eq (n : ℕ) : u s (n + 1) + 1 / 2 = (u s n + 1 / 2) ^ 2 + (1 / 4 + s ^ 2) := by
  rw [u_succ, φ]; ring

public lemma u_le_succ (s0 : 0 < s) (n : ℕ) : u s n ≤ u s (n + 1) := by
  rw [u_succ]; linarith [φ_pos s0 (u s n)]

public lemma u_mono (s0 : 0 < s) : Monotone (u s) := monotone_nat_of_le_succ (u_le_succ s0)

public lemma neg_half_le_u (s0 : 0 < s) (n : ℕ) : -1 / 2 ≤ u s n := by
  simpa using u_mono s0 (Nat.zero_le n)

/-- Each step moves by at least `s^2`, so the orbit is unbounded -/
public lemma u_ge (n : ℕ) : -1 / 2 + n * s ^ 2 ≤ u s n := by
  induction n with
  | zero => simp
  | succ n h =>
    rw [u_succ, φ]; push_cast
    nlinarith [sq_nonneg (u s n)]

/-- The exact step ratio: `φ(u_{n+1}) = φ(u_n) (1 + 2 u_n + φ(u_n))` -/
public lemma φ_succ (n : ℕ) : φ s (u s (n + 1)) = φ s (u s n) * (1 + 2 * u s n + φ s (u s n)) := by
  simp only [u_succ, φ]; ring

/-- `x ↦ x + φ(x)` is monotone on `[-1/2, ∞)` -/
lemma step_mono {x y : ℝ} (hx : -1 / 2 ≤ x) (xy : x ≤ y) : x + φ s x ≤ y + φ s y := by
  unfold φ; nlinarith

/-- The passage through the gate is slow: `u_n ≤ -s + 2 s^2 n` while `n s ≤ 1` -/
public lemma u_le_gate (s0 : 0 < s) (s4 : s ≤ 1 / 4) :
    ∀ n : ℕ, n * s ≤ 1 → u s n ≤ -s + 2 * s ^ 2 * n := by
  intro n
  induction n with
  | zero => intro _; simp; linarith
  | succ n h =>
    intro ns
    push_cast at ns ⊢
    have ns' : n * s ≤ 1 := by nlinarith
    have ih := h ns'
    rw [u_succ]
    by_cases us : u s n ≤ -s
    · -- Below the gate: monotonicity of the step map
      have e := step_mono (s := s) (neg_half_le_u s0 n) us
      have e2 : -s + φ s (-s) = -s + 2 * s ^ 2 := by unfold φ; ring
      rw [e2] at e
      nlinarith
    · -- Inside the gate, where |u| ≤ s and steps are at most 2 s^2
      have us' : u s n ≤ s := by nlinarith
      have ph : φ s (u s n) ≤ 2 * s ^ 2 := by
        unfold φ; nlinarith
      nlinarith

/-- While `n s ≤ 1`, the orbit stays below `s` -/
public lemma u_le_of_mul_le (s0 : 0 < s) (s4 : s ≤ 1 / 4) {n : ℕ} (ns : n * s ≤ 1) : u s n ≤ s := by
  have h := u_le_gate s0 s4 n ns
  nlinarith


/-!
### The key sum `∑ 1/φ(u_k)`, via the potential `H` with `H' = 1/φ^2`
-/

/-- The potential `H(x) = x / (2 s^2 φ(x)) + arctan(x / s) / (2 s^3)`, with `H' = 1 / φ^2` -/
@[expose] public noncomputable def H (s x : ℝ) : ℝ := x / (2 * s ^ 2 * φ s x) + arctan (x / s) / (2 * s ^ 3)

lemma hasDerivAt_H (s0 : 0 < s) (x : ℝ) : HasDerivAt (H s) (1 / φ s x ^ 2) x := by
  have p := φ_pos s0 x
  have dφ : HasDerivAt (φ s) (2 * x) x := by
    have : HasDerivAt (fun x ↦ x ^ 2 + s ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (s ^ 2)
    exact this
  have d1 : HasDerivAt (fun x ↦ x / (2 * s ^ 2 * φ s x))
      ((1 * (2 * s ^ 2 * φ s x) - x * (2 * s ^ 2 * (2 * x))) / (2 * s ^ 2 * φ s x) ^ 2) x :=
    (hasDerivAt_id x).div (dφ.const_mul _) (by positivity)
  have d2 : HasDerivAt (fun x ↦ arctan (x / s) / (2 * s ^ 3))
      (1 / (1 + (x / s) ^ 2) * (1 / s) / (2 * s ^ 3)) x := by
    have := ((hasDerivAt_id x).div_const s).arctan
    simpa using this.div_const (2 * s ^ 3)
  convert d1.add d2 using 1
  · funext y; rfl
  have s0' : s ≠ 0 := s0.ne'
  have p' : φ s x ≠ 0 := p.ne'
  have e : 1 + (x / s) ^ 2 = φ s x / s ^ 2 := by unfold φ; field_simp; ring
  rw [e]
  field_simp
  unfold φ
  ring

/-- `|x| / φ(x) ≤ 1 / (2 s)` -/
lemma abs_div_φ_le (s0 : 0 < s) (x : ℝ) : |x| / φ s x ≤ 1 / (2 * s) := by
  rw [div_le_div_iff₀ (φ_pos s0 x) (by positivity)]
  unfold φ
  nlinarith [sq_nonneg (|x| - s), sq_abs x, abs_nonneg x]

/-- `|H(x)| ≤ (1 + π) / (4 s^3)` -/
public lemma abs_H_le (s0 : 0 < s) (x : ℝ) : |H s x| ≤ (1 + π) / (4 * s ^ 3) := by
  have p := φ_pos s0 x
  have a1 : |x / (2 * s ^ 2 * φ s x)| ≤ 1 / (4 * s ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * s ^ 2 * φ s x)]
    have h := abs_div_φ_le s0 x
    rw [div_le_iff₀ p] at h
    rw [div_le_iff₀ (by positivity)]
    calc |x| ≤ 1 / (2 * s) * φ s x := h
      _ = 1 / (4 * s ^ 3) * (2 * s ^ 2 * φ s x) := by field_simp; ring
  have a2 : |arctan (x / s) / (2 * s ^ 3)| ≤ π / (4 * s ^ 3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * s ^ 3), div_le_div_iff₀ (by positivity) (by positivity)]
    have := abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan (x / s), Real.arctan_lt_pi_div_two (x / s)⟩
    have := mul_lt_mul_of_pos_right this (by positivity : 0 < 4 * s ^ 3)
    linarith
  calc |H s x| ≤ |x / (2 * s ^ 2 * φ s x)| + |arctan (x / s) / (2 * s ^ 3)| := abs_add_le _ _
    _ ≤ 1 / (4 * s ^ 3) + π / (4 * s ^ 3) := add_le_add a1 a2
    _ = (1 + π) / (4 * s ^ 3) := by ring

/-- Below `7/5`, a step grows `φ` by at most a factor of `6` -/
lemma φ_succ_le (s4 : s ≤ 1 / 4) (s0 : 0 < s) {n : ℕ} (un : u s n ≤ 7 / 5) :
    φ s (u s (n + 1)) ≤ 6 * φ s (u s n) := by
  rw [φ_succ]
  have p := φ_pos s0 (u s n)
  have h : 1 + 2 * u s n + φ s (u s n) ≤ 6 := by
    have l := neg_half_le_u s0 n
    unfold φ; nlinarith
  nlinarith

/-- Each step increases `H` by at least `1 / (36 φ(u_n))` -/
lemma inv_φ_le_H (s4 : s ≤ 1 / 4) (s0 : 0 < s) {n : ℕ} (un : u s n ≤ 7 / 5) :
    1 / φ s (u s n) ≤ 36 * (H s (u s (n + 1)) - H s (u s n)) := by
  set a := u s n
  set b := u s (n + 1)
  have ab : a < b := by simp only [a, b, u_succ]; linarith [φ_pos s0 (u s n)]
  obtain ⟨ξ, ⟨aξ, ξb⟩, e⟩ := exists_hasDerivAt_eq_slope (H s) (fun x ↦ 1 / φ s x ^ 2) ab
    (fun x _ ↦ (hasDerivAt_H s0 x).continuousAt.continuousWithinAt) (fun x _ ↦ hasDerivAt_H s0 x)
  have pa := φ_pos s0 a
  have pξ := φ_pos s0 ξ
  have ba : b - a = φ s a := by simp only [a, b, u_succ]; ring
  -- φ is convex, so its maximum on [a, b] is at an endpoint
  have ξmax : φ s ξ ≤ 6 * φ s a := by
    have la : -1 / 2 ≤ a := neg_half_le_u s0 n
    have hb := φ_succ_le s4 s0 un
    have : ξ ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
      rcases le_total 0 ξ with h | h
      · exact le_max_of_le_right (by nlinarith)
      · exact le_max_of_le_left (by nlinarith)
    unfold φ at hb ⊢
    rcases le_total (a ^ 2) (b ^ 2) with h | h
    · rw [max_eq_right h] at this; nlinarith
    · rw [max_eq_left h] at this; nlinarith
  have slope : H s b - H s a = (b - a) / φ s ξ ^ 2 := by
    rw [eq_div_iff (by linarith : b - a ≠ 0)] at e
    rw [← e]; ring
  rw [slope, ba]
  have hξ2 : φ s ξ ^ 2 ≤ 36 * φ s a ^ 2 := by nlinarith
  have key : φ s a / (36 * φ s a ^ 2) ≤ φ s a / φ s ξ ^ 2 :=
    div_le_div_of_nonneg_left pa.le (by positivity) hξ2
  have e2 : 1 / φ s a = 36 * (φ s a / (36 * φ s a ^ 2)) := by field_simp
  rw [e2]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

/-- The key sum: `∑_{k < n} 1 / φ(u_k) ≤ 18 (1 + π) / s^3` while `u_k ≤ 7/5` -/
public lemma sum_inv_φ_le (s4 : s ≤ 1 / 4) (s0 : 0 < s) {n : ℕ} (un : ∀ k < n, u s k ≤ 7 / 5) :
    ∑ k ∈ Finset.range n, 1 / φ s (u s k) ≤ 18 * (1 + π) / s ^ 3 := by
  calc ∑ k ∈ Finset.range n, 1 / φ s (u s k)
    _ ≤ ∑ k ∈ Finset.range n, 36 * (H s (u s (k + 1)) - H s (u s k)) := by
        refine Finset.sum_le_sum fun k m ↦ inv_φ_le_H s4 s0 (un k (Finset.mem_range.mp m))
    _ = 36 * (H s (u s n) - H s (u s 0)) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k ↦ H s (u s k))]
    _ ≤ 36 * (|H s (u s n)| + |H s (u s 0)|) := by
        gcongr; linarith [le_abs_self (H s (u s n)), neg_abs_le (H s (u s 0))]
    _ ≤ 36 * ((1 + π) / (4 * s ^ 3) + (1 + π) / (4 * s ^ 3)) := by
        gcongr <;> exact abs_H_le s0 _
    _ = 18 * (1 + π) / s ^ 3 := by field_simp; ring

/-!
### Shadowing: complex orbits near the real one
-/

/-- The complex orbit `z_0 = 0`, `z_{n+1} = z_n^2 + (1/4 + s^2 + h)` -/
@[expose] public noncomputable def zc (s : ℝ) (h : ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => zc s h n ^ 2 + ((1 / 4 + s ^ 2 : ℝ) + h)

/-- The accumulated error scale `τ_n = |h| ∑_{1 ≤ k ≤ n} 1 / φ(u_k)` -/
@[expose] public noncomputable def τ (s : ℝ) (h : ℂ) (n : ℕ) : ℝ :=
  ‖h‖ * ∑ k ∈ Finset.range n, 1 / φ s (u s (k + 1))

lemma τ_succ (h : ℂ) (n : ℕ) : τ s h (n + 1) = τ s h n + ‖h‖ / φ s (u s (n + 1)) := by
  simp only [τ, Finset.sum_range_succ]; ring

lemma τ_le_succ (s0 : 0 < s) (h : ℂ) (n : ℕ) : τ s h n ≤ τ s h (n + 1) := by
  rw [τ_succ]; exact le_add_of_nonneg_right (div_nonneg (norm_nonneg h) (φ_pos s0 _).le)

/-- The real orbit is nonnegative: `z_n = u_n + 1/2 ≥ 0` -/
lemma z_nonneg (s0 : 0 < s) (n : ℕ) : 0 ≤ u s n + 1 / 2 := by linarith [neg_half_le_u s0 n]

/-- Shadowing: `|z'_n - z_n| ≤ τ_n φ(u_n)` while `τ_n ≤ 1` -/
public lemma shadow (s0 : 0 < s) (h : ℂ) :
    ∀ n, τ s h n ≤ 1 → ‖zc s h n - ((u s n + 1 / 2 : ℝ) : ℂ)‖ ≤ τ s h n * φ s (u s n) := by
  intro n
  induction n with
  | zero => intro _; simp [zc, τ]; norm_num
  | succ n ih =>
    intro t1
    have e := ih ((τ_le_succ s0 h n).trans t1)
    set r := u s n + 1 / 2
    set en := zc s h n - (r : ℂ)
    have r0 : 0 ≤ r := z_nonneg s0 n
    have pn := φ_pos s0 (u s n)
    have t0 : 0 ≤ τ s h n := by unfold τ; exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun k _ ↦ (one_div_pos.mpr (φ_pos s0 _)).le)
    have tn : τ s h n ≤ 1 := (τ_le_succ s0 h n).trans t1
    -- The error recursion `e_{n+1} = e_n (e_n + 2 z_n) + h`
    have hrec : zc s h (n + 1) - ((u s (n + 1) + 1 / 2 : ℝ) : ℂ) = en * (en + 2 * r) + h := by
      have := u_succ_eq (s := s) n
      rw [show u s (n + 1) + 1 / 2 = r ^ 2 + (1 / 4 + s ^ 2) by rw [this]]
      simp only [zc, en]; push_cast; ring
    rw [hrec]
    have en_le : ‖en‖ ≤ φ s (u s n) := e.trans (by nlinarith)
    have bound : ‖en * (en + 2 * r) + h‖ ≤ τ s h n * φ s (u s n) * (φ s (u s n) + 2 * r) + ‖h‖ := by
      calc ‖en * (en + 2 * r) + h‖ ≤ ‖en‖ * (‖en‖ + 2 * r) + ‖h‖ := by
            refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
            rw [norm_mul]
            refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
            simp [Complex.norm_real, abs_of_nonneg r0]
        _ ≤ τ s h n * φ s (u s n) * (φ s (u s n) + 2 * r) + ‖h‖ := by
            gcongr
    refine bound.trans (le_of_eq ?_)
    have ps := φ_pos s0 (u s (n + 1))
    rw [τ_succ, φ_succ]
    have : 2 * r = 1 + 2 * u s n := by simp only [r]; ring
    rw [this]
    have q : 0 < 1 + 2 * u s n + φ s (u s n) := by linarith [neg_half_le_u s0 n]
    field_simp
    ring

/-!
### Consequences: slow passage and eventual escape for `|h| ≤ s^3 / 10^4`
-/

/-- Shifting the sum index: `∑_{k < n} f(k+1) ≤ ∑_{k < n+1} f(k)` for positive `f` -/
lemma sum_shift_le (s0 : 0 < s) (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / φ s (u s (k + 1)) ≤ ∑ k ∈ Finset.range (n + 1), 1 / φ s (u s k) := by
  rw [Finset.sum_range_succ']
  exact le_add_of_nonneg_right (one_div_pos.mpr (φ_pos s0 _)).le

/-- `18 (1 + π) + 1 ≤ 76` -/
lemma const_le : 18 * (1 + π) + 1 ≤ 76 := by linarith [Real.pi_lt_d2]

/-- While the real orbit stays below `7/5` through step `n`, `τ_n ≤ 1/100` -/
lemma τ_le (s0 : 0 < s) (s4 : s ≤ 1 / 4) {h : ℂ} (hs : ‖h‖ ≤ s ^ 3 / 10000) {n : ℕ}
    (un : ∀ k < n, u s k ≤ 7 / 5) (last : 1 ≤ φ s (u s n)) : τ s h n ≤ 1 / 100 := by
  have sum : ∑ k ∈ Finset.range (n + 1), 1 / φ s (u s k) ≤ 18 * (1 + π) / s ^ 3 + 1 := by
    rw [Finset.sum_range_succ]
    exact add_le_add (sum_inv_φ_le s4 s0 un) ((div_le_one (φ_pos s0 _)).mpr last)
  have s3 : s ^ 3 ≤ 1 := by
    have : s ^ 3 ≤ (1 / 4) ^ 3 := by gcongr
    linarith
  calc τ s h n ≤ s ^ 3 / 10000 * (18 * (1 + π) / s ^ 3 + 1) := by
        unfold τ
        refine mul_le_mul hs ((sum_shift_le s0 n).trans sum) ?_ (by positivity)
        exact Finset.sum_nonneg fun k _ ↦ (one_div_pos.mpr (φ_pos s0 _)).le
    _ = (18 * (1 + π) + s ^ 3) / 10000 := by field_simp
    _ ≤ 1 / 100 := by linarith [const_le]

/-- During the slow passage (`n s ≤ 1`), the perturbed orbit stays in the unit disk -/
public lemma norm_zc_le_one (s0 : 0 < s) (s4 : s ≤ 1 / 4) {h : ℂ} (hs : ‖h‖ ≤ s ^ 3 / 10000) {n : ℕ}
    (ns : n * s ≤ 1) : ‖zc s h n‖ ≤ 1 := by
  have ul : ∀ k ≤ n, u s k ≤ s := fun k kn ↦
    u_le_of_mul_le s0 s4 (le_trans (by gcongr) ns)
  have lo := neg_half_le_u s0 n
  have un := ul n le_rfl
  have ph : φ s (u s n) ≤ 1 / 4 + s ^ 2 := by unfold φ; nlinarith
  -- The sum bound only needs the orbit below 7/5, which holds since u ≤ s; pad `last` via φ ≥ s^2
  have t : τ s h n ≤ 1 / 100 := by
    have sum : ∑ k ∈ Finset.range (n + 1), 1 / φ s (u s k) ≤ 18 * (1 + π) / s ^ 3 :=
      sum_inv_φ_le s4 s0 fun k kn ↦ (ul k (Nat.lt_succ_iff.mp kn)).trans (by linarith)
    have s3 : s ^ 3 ≤ 1 := by
      have : s ^ 3 ≤ (1 / 4) ^ 3 := by gcongr
      linarith
    calc τ s h n ≤ s ^ 3 / 10000 * (18 * (1 + π) / s ^ 3) := by
          unfold τ
          refine mul_le_mul hs ((sum_shift_le s0 n).trans sum) ?_ (by positivity)
          exact Finset.sum_nonneg fun k _ ↦ (one_div_pos.mpr (φ_pos s0 _)).le
      _ = 18 * (1 + π) / 10000 := by field_simp
      _ ≤ 1 / 100 := by linarith [const_le]
  have e := shadow s0 h n (t.trans (by norm_num))
  have r := z_nonneg s0 n
  calc ‖zc s h n‖ = ‖(zc s h n - ((u s n + 1 / 2 : ℝ) : ℂ)) + ((u s n + 1 / 2 : ℝ) : ℂ)‖ := by ring_nf
    _ ≤ ‖zc s h n - ((u s n + 1 / 2 : ℝ) : ℂ)‖ + (u s n + 1 / 2) := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg r]
    _ ≤ 1 / 100 * (1 / 4 + s ^ 2) + (s + 1 / 2) := by
        gcongr
        · exact e.trans (mul_le_mul t ph (φ_pos s0 _).le (by norm_num))
    _ ≤ 1 := by nlinarith

/-- Eventually the perturbed orbit escapes the disk of radius 2 -/
public lemma exists_two_lt_norm_zc (s0 : 0 < s) (s4 : s ≤ 1 / 4) {h : ℂ} (hs : ‖h‖ ≤ s ^ 3 / 10000) :
    ∃ n, 2 < ‖zc s h n‖ := by
  have ex : ∃ n, 7 / 5 ≤ u s n := by
    refine ⟨⌈(19 / 10) / s ^ 2⌉₊, le_trans ?_ (u_ge _)⟩
    have := Nat.le_ceil ((19 / 10) / s ^ 2)
    have e : (19 / 10) / s ^ 2 * s ^ 2 = 19 / 10 := by field_simp
    nlinarith [sq_nonneg s]
  classical
  set m := Nat.find ex
  have hm : 7 / 5 ≤ u s m := Nat.find_spec ex
  have lt : ∀ k < m, u s k ≤ 7 / 5 := fun k km ↦ (not_le.mp (Nat.find_min ex km)).le
  have m0 : m ≠ 0 := by intro m0; rw [m0] at hm; simp at hm; linarith
  obtain ⟨p, mp⟩ := Nat.exists_eq_succ_of_ne_zero m0
  -- Bound the real orbit at the escape step: u_m ≤ 7/5 + φ(7/5) and φ(u_m) ≤ 12
  have up : u s p ≤ 7 / 5 := lt p (by omega)
  have lp := neg_half_le_u s0 p
  have um : u s m ≤ 7 / 5 + ((7 / 5) ^ 2 + s ^ 2) := by
    rw [mp, u_succ]; unfold φ; nlinarith
  have s2 : s ^ 2 ≤ 1 / 16 := by nlinarith
  have phm : φ s (u s m) ≤ 12 := by unfold φ; nlinarith
  have phm1 : 1 ≤ φ s (u s m) := by unfold φ; nlinarith
  have t := τ_le s0 s4 hs lt phm1
  have e := shadow s0 h m (t.trans (by norm_num))
  have en : ‖zc s h m - ((u s m + 1 / 2 : ℝ) : ℂ)‖ ≤ 12 / 100 :=
    e.trans (by nlinarith [φ_pos s0 (u s m), τ s h m])
  have zm : 1.78 ≤ ‖zc s h m‖ := by
    have := norm_sub_norm_le (((u s m + 1 / 2 : ℝ) : ℂ)) (((u s m + 1 / 2 : ℝ) : ℂ) - zc s h m)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (z_nonneg s0 m), sub_sub_cancel,
      norm_sub_rev] at this
    linarith
  refine ⟨m + 1, ?_⟩
  have c' : ‖(((1 / 4 + s ^ 2 : ℝ) : ℂ) + h)‖ ≤ 1 / 3 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : s ^ 3 ≤ 1 := by nlinarith
    linarith
  have := norm_sub_norm_le (zc s h m ^ 2) (-(((1 / 4 + s ^ 2 : ℝ) : ℂ) + h))
  simp only [sub_neg_eq_add, norm_neg, norm_pow] at this
  simp only [zc]
  nlinarith

end Cusp
