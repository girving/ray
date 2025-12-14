module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Ray.Misc.Bound

/-!
## Facts about Möbius transforms

We consider only Möbius transform of the form `z ↦ (w - z) / (1 - conj w * z)`, which is what we
need to prove the Schwarz-Pick theorem.
-/

open Metric (ball)
open Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section

variable {w z a : ℂ} {r : ℝ}

/-- The particular Möbius transform we need for Schwarz-Pick -/
public def mobius (w z : ℂ) : ℂ :=
  (w - z) / (1 - conj w * z)

/-- As a definition, for simp convenience -/
public lemma mobius_def (w z : ℂ) : mobius w z = (w - z) / (1 - conj w * z) := by rfl

/-- Our Möbius denominator is nonsingular -/
public lemma norm_mobius_denom_pos (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : 0 < ‖1 - conj w * z‖ := by
  calc ‖1 - conj w * z‖
    _ ≥ ‖(1 : ℂ)‖ - ‖conj w * z‖ := by bound
    _ = 1 - ‖w‖ * ‖z‖ := by simp
    _ ≥ 1 - ‖z‖ := by bound
    _ > 0 := by linarith

/-- Our Möbius denominator is nonsingular -/
public lemma mobius_denom_ne_zero (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : 1 - conj w * z ≠ 0 :=
  norm_pos_iff.mp (norm_mobius_denom_pos w1 z1)

/-- Our Möbius transforms map the unit disk to itself -/
public lemma mapsTo_mobius (w1 : ‖w‖ < 1) : MapsTo (mobius w) (ball 0 1) (ball 0 1) := by
  intro z z1
  simp only [Metric.mem_ball, dist_zero_right] at z1
  simp only [Metric.mem_ball, dist_zero_right, mobius, Complex.norm_div,
    div_lt_iff₀ (norm_mobius_denom_pos w1 z1), one_mul]
  rw [← sq_lt_sq₀ (by bound) (by bound), ← Complex.ofReal_re (‖w - z‖ ^ 2),
    ← Complex.ofReal_re (‖1 - (starRingEnd ℂ) w * z‖ ^ 2)]
  simp only [← Complex.conj_mul', Complex.ofReal_pow, map_sub, mul_sub, sub_mul, Complex.sub_re,
    mul_one, map_one, Complex.one_re, Complex.conj_conj, map_mul, one_mul]
  rw [← sub_pos]
  ring_nf
  refine lt_of_lt_of_le (b := (1 - ‖w‖ ^ 2 : ℂ).re * (1 - ‖z‖ ^ 2 : ℂ).re) ?_ (le_of_eq ?_)
  · simp only [Complex.ofReal_re, ← Complex.ofReal_pow, Complex.sub_re, Complex.one_re]
    bound
  · simp only [Complex.conj_mul', ← mul_assoc, mul_comm _ (conj w)]
    simp only [mul_assoc, Complex.conj_mul', Complex.sub_re, Complex.one_re, ← Complex.ofReal_pow,
      Complex.ofReal_re, ← Complex.ofReal_mul]
    ring

/-- Our Möbius transforms are analytic -/
public lemma contDiffAt_mobius {n : WithTop ℕ∞} (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) :
    ContDiffAt ℂ n (mobius w) z := by
  refine ContDiffAt.div (by fun_prop) (by fun_prop) ?_
  exact mobius_denom_ne_zero w1 z1

/-- Our Möbius transforms are analytic -/
public lemma contDiffOn_mobius {n : WithTop ℕ∞} (w1 : ‖w‖ < 1) :
    ContDiffOn ℂ n (mobius w) (ball 0 1) :=
  fun z z1 ↦ (contDiffAt_mobius w1 (by simpa using z1)).contDiffWithinAt

/-- Our Möbius transforms map the unit disk to itself -/
public lemma norm_mobius_lt_one (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : ‖mobius w z‖ < 1 := by
  simpa using mapsTo_mobius w1 (x := z) (by simpa)

/-- Our Möbius transforms are involutions -/
public lemma mobius_mobius (w1 : ‖w‖ < 1) (z1 : ‖z‖ < 1) : mobius w (mobius w z) = z := by
  have n1 := mobius_denom_ne_zero w1 z1
  have n2 := mobius_denom_ne_zero w1 (norm_mobius_lt_one w1 z1)
  simp only [mobius] at n1 n2 ⊢
  rw [div_eq_iff n2, ← mul_left_inj' n1]
  simp only [sub_mul, div_mul_cancel₀ _ n1, mul_assoc]
  ring

@[simp] public lemma mobius_zero : mobius w 0 = w := by simp [mobius]
@[simp] public lemma mobius_self : mobius w w = 0 := by simp [mobius]

/-- Convenience lemma to pull a inverse scale out of a Möbius denominator -/
public lemma mobius_denom_inv_mul (r0 : r ≠ 0) (w z : ℂ) :
    (1 - conj (r⁻¹ * w) * (r⁻¹ * z)) = r⁻¹ ^ 2 * (r ^ 2 - conj w * z) := by
  rw [Complex.ofReal_inv, inv_pow, ← div_eq_inv_mul _ (_ ^ 2), eq_div_iff (by simpa)]
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, sub_mul, one_mul]
  have r0' : (r : ℂ) ≠ 0 := by simp [r0]
  field_simp
