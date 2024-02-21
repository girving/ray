import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic

/-!
## Basics about complex analytic (holomorphic) functions
-/

open Complex (abs exp I log)
open Filter (atTop)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A function is analytic at `z` iff it's differentiable on a surrounding open set -/
theorem analyticOn_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOn ℂ f s ↔ DifferentiableOn ℂ f s := by
  constructor
  · exact AnalyticOn.differentiableOn
  · intro d z zs
    exact DifferentiableOn.analyticAt d (o.mem_nhds zs)

/-- A function is entire iff it's differentiable everywhere -/
theorem analyticOn_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOn ℂ f univ ↔ Differentiable ℂ f := by
  simp only [←  differentiableOn_univ]
  exact analyticOn_iff_differentiableOn isOpen_univ

/-- A function is analytic at `z` iff it's differentiable on near `z` -/
theorem analyticAt_iff_eventually_differentiableAt {f : ℂ → E} {c : ℂ} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z := by
  constructor
  · intro fa; rcases fa.exists_ball_analyticOn with ⟨r, rp, fa⟩
    exact fa.differentiableOn.eventually_differentiableAt (Metric.ball_mem_nhds _ rp)
  · intro d; rcases Metric.eventually_nhds_iff.mp d with ⟨r, rp, d⟩
    have dr : DifferentiableOn ℂ f (ball c r) := by
      intro z zs; simp only [Metric.mem_ball] at zs; exact (d zs).differentiableWithinAt
    rw [← analyticOn_iff_differentiableOn isOpen_ball] at dr
    exact dr _ (Metric.mem_ball_self rp)

/-- `exp` is entire -/
theorem AnalyticOn.exp : AnalyticOn ℂ exp univ := by
  rw [analyticOn_univ_iff_differentiable]; exact Complex.differentiable_exp

/-- `exp` is analytic at any point -/
theorem AnalyticAt.exp {z : ℂ} : AnalyticAt ℂ exp z :=
  AnalyticOn.exp z (Set.mem_univ _)

/-- `log` is analytic away from nonpositive reals -/
theorem analyticAt_log {c : ℂ} (m : c ∈ Complex.slitPlane) : AnalyticAt ℂ log c := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [Complex.isOpen_slitPlane.eventually_mem m]
  intro z m
  exact differentiableAt_id.clog m

/-- `log` is analytic away from nonpositive reals -/
theorem AnalyticAt.log {f : E → ℂ} {c : E} (fa : AnalyticAt ℂ f c) (m : f c ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z ↦ log (f z)) c :=
  (analyticAt_log m).comp fa

/-- `log` is analytic away from nonpositive reals -/
theorem AnalyticOn.log {f : E → ℂ} {s : Set E} (fs : AnalyticOn ℂ f s)
    (m : ∀ z ∈ s, f z ∈ Complex.slitPlane) : AnalyticOn ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).comp (fs z n)

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
theorem AnalyticAt.cpow {f g : E → ℂ} {c : E} (fa : AnalyticAt ℂ f c) (ga : AnalyticAt ℂ g c)
    (m : f c ∈ Complex.slitPlane) : AnalyticAt ℂ (fun z ↦ f z ^ g z) c := by
  have fc : f c ≠ 0 := Complex.slitPlane_ne_zero m
  have e : (fun z ↦ f z ^ g z) =ᶠ[𝓝 c] fun z ↦ Complex.exp (Complex.log (f z) * g z) := by
    refine (fa.continuousAt.eventually_ne fc).mp (Filter.eventually_of_forall ?_)
    intro z fz; simp only [fz, Complex.cpow_def, if_false]
  rw [analyticAt_congr e]
  exact AnalyticAt.exp.comp ((fa.log m).mul ga)
