module
public import Ray.Multibrot.Basic
public import Ray.Multibrot.Cusp
import Mathlib.Analysis.Complex.ExponentialBounds
import Ray.Dynamics.Potential
import Ray.Multibrot.PotentialLower

/-!
## Slowly escaping parameters near the cusp `c = 1/4`

We connect the orbit estimates of `Ray.Multibrot.Cusp` to the Mandelbrot set: for small `s > 0` and
`|h| ≤ s^3 / 10^4`, the parameter `c = 1/4 + s^2 + h` is outside the Mandelbrot set, but its potential
is at least `exp (-2 / 2^m)` whenever `(m + 1) s ≤ 1`.  That is, its Green's function is `≤ 2^{1-m}`.
-/

open RiemannSphere
open Set
open scoped OnePoint RiemannSphere

namespace Cusp

variable {s : ℝ} {h : ℂ}

/-- The cusp parameter `c = 1/4 + s^2 + h` -/
@[expose] public noncomputable def param (s : ℝ) (h : ℂ) : ℂ := ((1 / 4 + s ^ 2 : ℝ) : ℂ) + h

/-- `zc` is the critical orbit of `param s h` -/
public lemma zc_succ_eq_iter (n : ℕ) : zc s h (n + 1) = (f' 2 (param s h))^[n] (param s h) := by
  induction n with
  | zero => simp [zc, param]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih]
    simp only [zc, f', param]

/-- Parameters near the cusp escape, so are outside the Mandelbrot set -/
public lemma param_notMem (s0 : 0 < s) (s4 : s ≤ 1 / 4) (hs : ‖h‖ ≤ s ^ 3 / 10000) :
    param s h ∉ multibrot 2 := by
  obtain ⟨n, hn⟩ := exists_two_lt_norm_zc s0 s4 hs
  cases n with
  | zero => simp [zc] at hn; linarith
  | succ n =>
    rw [zc_succ_eq_iter] at hn
    exact not_multibrot_of_two_lt hn

lemma norm_param_le (s4 : s ≤ 1 / 4) (s0 : 0 < s) (hs : ‖h‖ ≤ s ^ 3 / 10000) : ‖param s h‖ ≤ 4 := by
  unfold param
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : s ^ 3 ≤ (1 / 4) ^ 3 := pow_le_pow_left₀ s0.le s4 3
  nlinarith

lemma exp_neg_two_le : Real.exp (-2) ≤ 0.216 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  nlinarith [Real.exp_one_gt_d9]

/-- The potential of a cusp parameter is close to `1`: `exp (-2 / 2^m) ≤ potential` if `(m+1) s ≤ 1` -/
public lemma exp_le_potential (s0 : 0 < s) (s4 : s ≤ 1 / 4) (hs : ‖h‖ ≤ s ^ 3 / 10000) {m : ℕ}
    (ms : (m + 1 : ℕ) * s ≤ 1) : Real.exp (-2 / 2 ^ m) ≤ potential 2 (param s h : 𝕊) := by
  set c := param s h
  set sp := superF 2
  have c4 := norm_param_le s4 s0 hs
  -- The `m`-th iterate is `zc (m + 1)`, which stays in the unit disk
  have z4 : ‖(f' 2 c)^[m] c‖ ≤ 4 := by
    rw [← zc_succ_eq_iter]; exact (norm_zc_le_one s0 s4 hs ms).trans (by norm_num)
  have lo := le_potential (d := 2) c4 z4
  have eqn : sp.potential c ((f 2 c)^[m] ↑c) = sp.potential c ↑c ^ 2 ^ m := sp.potential_eqn_iter m
  rw [f_f'_iter] at eqn
  rw [potential_coe]
  have p0 : 0 ≤ sp.potential c ↑c := sp.potential_nonneg
  have key : Real.exp (-2 / 2 ^ m) ^ 2 ^ m ≤ sp.potential c ↑c ^ 2 ^ m := by
    rw [← Real.exp_nat_mul, ← eqn]
    push_cast
    rw [mul_div_cancel₀ _ (by positivity)]
    exact exp_neg_two_le.trans lo
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le p0 (by positivity)).mp key

end Cusp
