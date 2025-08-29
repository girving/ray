import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Ray.Analytic.Holomorphic
import Ray.Koebe.WindArea
import Ray.Misc.Annuli
import Ray.Misc.Cobounded

/-!
## Koebe quarter theorem

If `f : ball 0 1 → ℂ` is analytic and injective, with `f' 0 = 1`, then its image contains a disk
of radius `1/4` centered at `f 0`.

The proof follows Wikipedia: https://en.wikipedia.org/wiki/Koebe_quarter_theorem

DO NOT SUBMIT: Rename to Gromwall.lean for the Gromwall's area theorem part.
-/

open Classical
open Complex (abs arg)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped ContDiff Topology NNReal
noncomputable section

/-!
## Koebe quarter theorem
-/

/-- The Koebe quarter theorem -/
theorem koebe_quarter {f : ℂ → ℂ} (fa : AnalyticOn ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) (df : HasDerivAt f 1 0) :
    ball (f 0) (1/4) ⊆ f '' (ball 0 1) :=
  sorry
