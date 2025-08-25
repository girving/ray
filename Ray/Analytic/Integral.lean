import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Init
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Ray.Analytic.Analytic
import Ray.Analytic.Uniform
import Ray.Misc.Bounds
import Ray.Misc.Bound

/-!
## Integrals of analytic functions are analytic

We consider a function `f : X → ℂ → E` which is continuous on a complex `s : Set X` and analytic
for `z ∈ closedBall c r`. Interchanging the order of integration shows that the integral is
analytic.
-/

open Classical
open Function (uncurry)
open MeasureTheory (Measure volume)
open Metric (ball closedBall)
open scoped NNReal Real
noncomputable section

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {f : X → ℂ → E} {μ : Measure X} {s : Set X} {c : ℂ} {r : ℝ≥0}
variable {x : X} {z : ℂ} {p : X × ℂ} {n : ℕ}

/-- Our various assumptions -/
structure Holo [CompleteSpace E] (f : X → ℂ → E) (μ : Measure X) (s : Set X) (c : ℂ) (r : ℝ≥0) :
    Prop where
  r0 : 0 < r
  sc : IsCompact s
  fc : ContinuousOn (uncurry f) (s ×ˢ closedBall c r)
  fd : ∀ x ∈ s, ∀ z ∈ ball c r, DifferentiableAt ℂ (f x) z
  μs : μ s < ⊤

namespace Holo

attribute [bound_forward] Holo.r0

/-- Our power series is the `cauchyPowerSeries`, integrated over `s` -/
def series (_ : Holo f μ s c r) : FormalMultilinearSeries ℂ ℂ E :=
  fun n ↦ ∫ x in s, cauchyPowerSeries (f x) c r n ∂μ

-- `f` is uniformly bounded
lemma pc (i : Holo f μ s c r) : IsCompact (s ×ˢ closedBall c r) :=
  i.sc.prod (isCompact_closedBall _ _)
lemma bounded (i : Holo f μ s c r) : ∃ C, ∀ x ∈ s ×ˢ closedBall c r, ‖uncurry f x‖ ≤ C :=
  i.pc.exists_bound_of_continuousOn i.fc
def C (i : Holo f μ s c r) : ℝ := choose i.bounded
def le_C (i : Holo f μ s c r) (m : p ∈ s ×ˢ closedBall c r) : ‖uncurry f p‖ ≤ i.C :=
  choose_spec i.bounded _ m
def le_C' (i : Holo f μ s c r) (xs : x ∈ s) (zm : z ∈ closedBall c r) : ‖f x z‖ ≤ i.C :=
  i.le_C (p := (x, z)) ⟨xs, zm⟩

/-- The inner cauchy series is bounded -/
lemma norm_cauchyPowerSeries_le (i : Holo f μ s c r) (xm : x ∈ s) :
    ‖cauchyPowerSeries (f x) c r n‖ ≤ i.C * r⁻¹ ^ n := by
  have le : ‖∫ t in 0..2 * π, ‖f x (circleMap c r t)‖‖ ≤ i.C * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x m ↦ ?_
    simp only [norm_norm]
    apply i.le_C' xm
    simp only [Metric.mem_closedBall, dist_eq_norm, circleMap_sub_center, norm_circleMap_zero,
      NNReal.abs_eq, le_refl]
  simp only [Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos, mul_comm i.C] at le
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg (by bound) (by bound))] at le
  refine le_trans (_root_.norm_cauchyPowerSeries_le _ _ _ _) ?_
  rw [abs_of_pos (by bound), NNReal.coe_inv]
  refine mul_le_mul_of_nonneg_right ?_ (by bound)
  rwa [inv_mul_le_iff₀ (by bound)]

/-- Our series is bounded -/
@[bound] lemma norm_series_le (i : Holo f μ s c r) : ‖i.series n‖ ≤ i.C * r⁻¹ ^ n * μ.real s :=
  MeasureTheory.norm_setIntegral_le_of_norm_le_const i.μs (C := i.C * r⁻¹ ^ n)
    (fun _ m ↦ i.norm_cauchyPowerSeries_le m)

/-- Our series has nice radius of convergence -/
lemma le_radius_series (i : Holo f μ s c r) : r ≤ i.series.radius := by
  refine FormalMultilinearSeries.le_radius_of_bound _ (C := i.C * μ.real s) fun n ↦ ?_
  calc ‖i.series n‖ * r ^ n
    _ ≤ i.C * r⁻¹ ^ n * μ.real s * r ^ n := by bound
    _ = i.C * μ.real s * (r / r) ^ n := by simp only [NNReal.coe_inv, inv_pow]; ring
    _ = i.C * μ.real s := by rw [div_self (ne_of_gt (by bound)), one_pow, mul_one]

lemma diffContOnCl (i : Holo f μ s c r) (xs : x ∈ s) : DiffContOnCl ℂ (f x) (ball c r) where
  differentiableOn := fun z zm ↦ (i.fd x xs z zm).differentiableWithinAt
  continuousOn := by
    exact ContinuousOn.uncurry_left i.fc x xm

/-- Integrals of analytic functions are analytic -/
theorem hasFPowerSeriesOnBall_integral (i : Holo f μ s c r) :
    HasFPowerSeriesOnBall (fun z ↦ ∫ x in s, f x z ∂μ) i.series c r where
  r_le := i.le_radius_series
  r_pos := by bound
  hasSum := by
    intro z zm
    have h : ∀ x ∈ s, HasFPowerSeriesOnBall (f x) (cauchyPowerSeries (f x) c r) c r := by
      intro x xs
      apply DiffContOnCl.hasFPowerSeriesOnBall

-- DO NOT SUBMIT: #min_imports
