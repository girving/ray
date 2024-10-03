import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Ray.Analytic.Analytic
import Ray.Analytic.HolomorphicUpstream
import Ray.Misc.Bounds
import Ray.Misc.Multilinear
import Ray.Hartogs.Osgood
import Ray.Misc.Topology

/-!
## Basics about complex analytic functions
-/

open Complex (abs exp I log)
open Filter (atTop)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `f : ℂ × ℂ → E` is differentiable iff it is analytic -/
theorem differentiable_iff_analytic2 {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (o : IsOpen s) :
    DifferentiableOn ℂ f s ↔ AnalyticOnNhd ℂ f s := by
  constructor
  · intro d; apply osgood o d.continuousOn
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d0 : DifferentiableOn ℂ (fun z0 ↦ f (z0, z1)) (ball z0 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prod differentiableOn_id (differentiableOn_const _)
        intro z0 z0s; apply rs; simp at z0s ⊢; assumption
      exact (analyticOn_iff_differentiableOn isOpen_ball).mpr d0 z0 (Metric.mem_ball_self rp)
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d1 : DifferentiableOn ℂ (fun z1 ↦ f (z0, z1)) (ball z1 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prod (differentiableOn_const _) differentiableOn_id
        intro z1 z1s; apply rs; simp at z1s ⊢; assumption
      exact (analyticOn_iff_differentiableOn isOpen_ball).mpr d1 z1 (Metric.mem_ball_self rp)
  · exact fun a ↦ a.differentiableOn

/-- `f : ℂ × ℂ → E` is `ContDiffAt` iff it is analytic -/
theorem contDiffAt_iff_analytic_at2 {E : Type} {f : ℂ × ℂ → E} {x : ℂ × ℂ} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {n : ℕ∞} (n1 : 1 ≤ n) :
    ContDiffAt ℂ n f x ↔ AnalyticAt ℂ f x := by
  constructor
  · intro d; rcases d.contDiffOn n1 with ⟨u, un, d⟩
    rcases mem_nhds_iff.mp un with ⟨v, uv, vo, vx⟩
    refine (differentiable_iff_analytic2 vo).mp ?_ _ vx
    exact (d.mono uv).differentiableOn (by norm_num)
  · intro a; exact a.contDiffAt.of_le le_top

/-- The principle branch of sqrt -/
def sqrt (z : ℂ) : ℂ :=
  exp (log z / 2)
