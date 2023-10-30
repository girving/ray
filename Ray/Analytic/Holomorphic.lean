import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Ray.Analytic.Analytic
import Ray.Misc.Bounds
import Ray.Misc.Multilinear
import Ray.Hartogs.Osgood
import Ray.Misc.Topology

/-!
## Basics about complex analytic (holomorphic) functions
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Complex (abs exp I log)
open Filter (atTop)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A function is entire iff it's differentiable everywhere -/
theorem Differentiable.entire {f : ℂ → E} : Differentiable ℂ f ↔ AnalyticOn ℂ f univ :=
  ⟨fun d z _ ↦ d.analyticAt z, fun a z ↦ (a z (Set.mem_univ _)).differentiableAt⟩

/-- A function is analytic at `z` iff it's differentiable on a surrounding open set -/
theorem differentiable_iff_analytic {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    DifferentiableOn ℂ f s ↔ AnalyticOn ℂ f s := by
  constructor
  · intro d z zs
    have n : s ∈ nhds z := IsOpen.mem_nhds o zs
    exact DifferentiableOn.analyticAt d n
  · exact AnalyticOn.differentiableOn

/-- A function is analytic at `z` iff it's differentiable on near `z` -/
theorem analyticAt_iff_eventually_differentiableAt {f : ℂ → E} {c : ℂ} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z := by
  constructor
  · intro fa; rcases fa.exists_ball_analyticOn with ⟨r, rp, fa⟩
    exact fa.differentiableOn.eventually_differentiableAt (Metric.ball_mem_nhds _ rp)
  · intro d; rcases Metric.eventually_nhds_iff.mp d with ⟨r, rp, d⟩
    have dr : DifferentiableOn ℂ f (ball c r) := by
      intro z zs; simp only [Metric.mem_ball] at zs; exact (d zs).differentiableWithinAt
    rw [differentiable_iff_analytic isOpen_ball] at dr
    exact dr _ (Metric.mem_ball_self rp)

/-- `f : ℂ × ℂ → E` is differentiable iff it is analytic -/
theorem differentiable_iff_analytic2 {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (o : IsOpen s) :
    DifferentiableOn ℂ f s ↔ AnalyticOn ℂ f s := by
  constructor
  · intro d; apply osgood o d.continuousOn
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d0 : DifferentiableOn ℂ (fun z0 ↦ f (z0, z1)) (ball z0 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prod differentiableOn_id (differentiableOn_const _)
        intro z0 z0s; apply rs; simp at z0s ⊢; assumption
      exact (differentiable_iff_analytic isOpen_ball).mp d0 z0 (Metric.mem_ball_self rp)
    · intro z0 z1 zs
      rcases Metric.isOpen_iff.mp o (z0, z1) zs with ⟨r, rp, rs⟩
      have d1 : DifferentiableOn ℂ (fun z1 ↦ f (z0, z1)) (ball z1 r) := by
        apply DifferentiableOn.comp d
        exact DifferentiableOn.prod (differentiableOn_const _) differentiableOn_id
        intro z1 z1s; apply rs; simp at z1s ⊢; assumption
      exact (differentiable_iff_analytic isOpen_ball).mp d1 z1 (Metric.mem_ball_self rp)
  · exact fun a ↦ a.differentiableOn

/-- `f : ℂ × ℂ → E` is `ContDiffAt` iff it is analytic -/
theorem contDiffAt_iff_analytic_at2 {E : Type} {f : ℂ × ℂ → E} {x : ℂ × ℂ} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {n : ℕ∞} (n1 : 1 ≤ n) :
    ContDiffAt ℂ n f x ↔ AnalyticAt ℂ f x := by
  constructor
  · intro d; rcases d.contDiffOn n1 with ⟨u, un, um, d⟩
    simp only [Set.mem_univ, Set.insert_eq_of_mem, Set.subset_univ] at un um
    rw [nhdsWithin_univ] at un
    rcases mem_nhds_iff.mp un with ⟨v, uv, vo, vx⟩
    refine' (differentiable_iff_analytic2 vo).mp _ _ vx
    exact (d.mono uv).differentiableOn (by norm_num)
  · intro a; exact a.contDiffAt.of_le le_top

/-- `exp` is entire -/
theorem AnalyticOn.exp : AnalyticOn ℂ exp univ := by
  rw [← Differentiable.entire]; exact Complex.differentiable_exp

/-- `exp` is analytic at any point -/
theorem AnalyticAt.exp {z : ℂ} : AnalyticAt ℂ exp z :=
  AnalyticOn.exp z (Set.mem_univ _)

/-- `log` is analytic away from negative reals -/
theorem analyticAt_log {c : ℂ} (a : c.re > 0 ∨ c.im ≠ 0) : AnalyticAt ℂ log c := by
  rw [analyticAt_iff_eventually_differentiableAt]
  cases' a with a a
  · have ae : ∀ᶠ z : ℂ in 𝓝 c, z.re > 0 :=
      ContinuousAt.eventually_lt continuousAt_const Complex.continuous_re.continuousAt a
    refine' ae.mp (Filter.eventually_of_forall _); intro z zr
    exact differentiableAt_id.clog (Or.inl zr)
  · have ae : ∀ᶠ z : ℂ in 𝓝 c, z.im ≠ 0 := Complex.continuous_im.continuousAt.eventually_ne a
    refine' ae.mp (Filter.eventually_of_forall _); intro z zr
    exact differentiableAt_id.clog (Or.inr zr)

/-- `log` is analytic away from negative reals -/
theorem AnalyticAt.log {f : E → ℂ} {c : E} (fa : AnalyticAt ℂ f c)
    (a : (f c).re > 0 ∨ (f c).im ≠ 0) : AnalyticAt ℂ (fun z ↦ log (f z)) c :=
  (analyticAt_log a).comp fa

/-- `log` is analytic near 1 -/
theorem log_analytic_near_one {f : ℂ → ℂ} {s : Set ℂ} (o : IsOpen s) (fa : AnalyticOn ℂ f s)
    (n : ∀ z, z ∈ s → abs (f z - 1) < 1) : AnalyticOn ℂ (fun z ↦ log (f z)) s := by
  rw [← differentiable_iff_analytic o]
  refine' DifferentiableOn.clog _ _
  rw [differentiable_iff_analytic o]; assumption
  intro z zs
  exact near_one_avoids_negative_reals (n z zs)

/-- The principle branch of sqrt -/
def sqrt (z : ℂ) : ℂ :=
  exp (log z / 2)

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
theorem AnalyticAt.cpow {f g : E → ℂ} {c : E} (fa : AnalyticAt ℂ f c) (ga : AnalyticAt ℂ g c)
    (a : 0 < (f c).re ∨ (f c).im ≠ 0) : AnalyticAt ℂ (fun z ↦ f z ^ g z) c := by
  have fc : f c ≠ 0 := by
    contrapose a; simp only [not_not] at a
    simp only [a, Complex.zero_re, gt_iff_lt, lt_self_iff_false, Complex.zero_im, Ne.def,
      eq_self_iff_true, not_true, or_self_iff, not_false_iff]
  have e : (fun z ↦ f z ^ g z) =ᶠ[𝓝 c] fun z ↦ Complex.exp (Complex.log (f z) * g z) := by
    refine' (fa.continuousAt.eventually_ne fc).mp (Filter.eventually_of_forall _)
    intro z fz; simp only [fz, Complex.cpow_def, if_false]
  rw [analyticAt_congr e]; exact AnalyticAt.exp.comp ((fa.log a).mul ga)
