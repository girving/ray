import Mathlib.Analysis.Complex.Schwarz
import Ray.Schwarz.Mobius

/-!
## Schwarz-Pick theorem

The Schwarz-Pick theorem provides the tightest bounds on finite differences and derivatives of
an anlytic function on the unit disk:

  https://en.wikipedia.org/wiki/Schwarz_lemma#Schwarz%E2%80%93Pick_theorem
-/

open Filter (Tendsto)
open Metric (ball isOpen_ball)
open Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section

variable {w z : ℂ} {f : ℂ → ℂ}

/-- Finite difference version of Schwarz-Pick for the unit disk -/
lemma Complex.dist_le_mul_mobius_of_mapsTo_unit_ball (fa : ContDiffOn ℂ ω f (ball 0 1))
    (fi : MapsTo f (ball 0 1) (ball 0 1)) (z1 : ‖z‖ < 1) (w1 : ‖w‖ < 1) :
    ‖f z - f w‖ ≤ ‖1 - conj (f z) * f w‖ * ‖mobius z w‖ := by
  have fz1 : ‖f z‖ < 1 := by simpa using fi (x := z) (by simpa)
  have fw1 : ‖f w‖ < 1 := by simpa using fi (x := w) (by simpa)
  set g := mobius (f z) ∘ f ∘ mobius z
  have gm' := fi.comp (mapsTo_mobius z1)
  have gm : MapsTo g (ball 0 1) (ball 0 1) := (mapsTo_mobius fz1).comp gm'
  have ga : ContDiffOn ℂ ω g (ball 0 1) :=
    (contDiffOn_mobius fz1).comp (fa.comp (contDiffOn_mobius z1) (mapsTo_mobius z1)) gm'
  have g0 : g 0 = 0 := by simp only [g, Function.comp_apply, mobius_zero, mobius_self]
  set u := mobius z w
  have u1 : ‖u‖ < 1 := norm_mobius_lt_one z1 w1
  simpa only [g, Function.comp_apply, mobius_def (f z), u, mobius_mobius z1 w1, norm_div,
    div_le_iff₀ (norm_mobius_denom_pos fz1 fw1), mul_comm ‖mobius _ _‖] using
    Complex.norm_le_norm_of_mapsTo_ball_self (ga.differentiableOn le_top) gm g0 u1

/-- Derivative version of Schwarz-Pick for the unit disk -/
lemma Complex.norm_deriv_le_div_of_mapsTo_unit_ball (fa : ContDiffOn ℂ ω f (ball 0 1))
    (fi : MapsTo f (ball 0 1) (ball 0 1)) (z1 : ‖z‖ < 1) :
    ‖deriv f z‖ ≤ (1 - ‖f z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
  have zm : z ∈ ball 0 1 := by simpa using z1
  have fz1 : ‖f z‖ < 1 := by simpa using fi (x := z) (by simpa)
  have df := (fa.differentiableOn le_top).differentiableAt (x := z) (isOpen_ball.mem_nhds zm)
  have s : ∀ᶠ w in 𝓝[≠] z, ‖slope f z w‖ - ‖1 - conj (f z) * f w‖ / ‖1 - conj z * w‖ ≤ 0 := by
    simp only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff]
    filter_upwards [isOpen_ball.eventually_mem zm] with w w1 wz
    simp only [Metric.mem_ball, dist_zero_right] at w1
    have s := Complex.dist_le_mul_mobius_of_mapsTo_unit_ball fa fi z1 w1
    simp only [mobius, Complex.norm_div, ← mul_div_assoc, mul_div_right_comm] at s
    rw [← div_le_iff₀ (norm_pos_iff.mpr (by grind))] at s
    simpa [slope, ← div_eq_inv_mul, norm_sub_rev (f w), norm_sub_rev w]
  have dc : ContinuousAt (fun w ↦ ‖1 - conj (f z) * f w‖ / ‖1 - conj z * w‖) z :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (norm_mobius_denom_pos z1 z1).ne'
  have t1 := (continuous_norm.tendsto _).comp df.hasDerivAt.tendsto_slope
  have t2 := dc.tendsto
  have e : ∀ x : ℝ, (1 - x : ℂ) = (1 - x : ℝ) := by simp
  have n : ∀ {z : ℂ}, ‖z‖ < 1 → |1 - ‖z‖ ^ 2| = (1 - ‖z‖ ^ 2) := by
    intro z z1
    rw [abs_of_nonneg]
    bound
  simp only [Function.comp_def, conj_mul', ← Complex.ofReal_pow, e, Complex.norm_real,
    Real.norm_eq_abs, n z1, n fz1] at t1 t2
  rw [← sub_nonpos]
  exact le_of_tendsto (t1.sub (t2.mono_left nhdsWithin_le_nhds)) s
