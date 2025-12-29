module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Ray.Analytic.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Ray.Analytic.Analytic
import Ray.Koebe.Koebe
import Ray.Schwarz.Mobius

/-!
## Koebe-Pick theorem

The Koebe-Pick theorem is the analogue of Koebe if `f : ball 0 1 → ℂ` is analytic and injective,
and we know value and derivative at some `‖c‖ < 1`. Given that, it produces the largest disk that we
know is contained in the image. It is the analogue of Schwarz-Pick over Schwarz: we use a Möbius
transform to move `c` to the origin so that we can exploit knowledge of the full disk.
-/

open Metric (ball isOpen_ball)
open Set
open scoped ContDiff Topology
noncomputable section

variable {f : ℂ → ℂ} {c : ℂ}

/-- The Koebe-Pick theorem, unit ball case -/
public theorem koebe_pick (fa : ContDiffOn ℂ ω f (ball 0 1)) (inj : InjOn f (ball 0 1))
    (c1 : ‖c‖ < 1) : ball (f c) ((1 - ‖c‖ ^ 2) * ‖deriv f c‖ / 4) ⊆ f '' (ball 0 1) := by
  set g : ℂ → ℂ := f ∘ mobius c
  have ga : ContDiffOn ℂ ω g (ball 0 1) := fa.comp (contDiffOn_mobius c1) (mapsTo_mobius c1)
  have gi : InjOn g (ball 0 1) := inj.comp (injOn_mobius c1) (mapsTo_mobius c1)
  have gim : g '' ball 0 1 = f '' ball 0 1 := by simp only [g, image_comp, image_mobius c1]
  have dg : deriv g 0 = deriv f c * (‖c‖ ^ 2 - 1) := by
    simp only [g]
    rw [deriv_comp]
    · simp only [mobius_zero, deriv_mobius_zero c1]
    · exact (fa.contDiffAt (mobius_zero ▸ isOpen_ball.mem_nhds (by simpa))).differentiableAt
        (by decide)
    · exact ((contDiffOn_mobius c1).contDiffAt (isOpen_ball.mem_nhds (by simp))).differentiableAt
        one_ne_zero
  have k := koebe_quarter (f := g) (ga.analyticOnNhd isOpen_ball) gi
  have e1 : ‖(‖c‖ ^ 2 - 1 : ℂ)‖ = 1 - ‖c‖ ^ 2 := by
    norm_cast
    rw [norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg (by bound)]
  rw [dg, gim] at k
  simpa only [g, Function.comp_apply, mobius_zero, mul_comm (deriv f c), norm_mul, e1] using k
