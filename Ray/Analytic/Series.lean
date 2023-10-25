import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Ray.Analytic.Analytic
import Ray.Analytic.Uniform
import Ray.Misc.Bounds
import Ray.Tactic.Bound

/-!
## Infinite series of analytic functions

Uniformly convergent series of analytic functions have analytic limits.
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Complex (abs)
open Filter (atTop)
open Metric (ball closedBall sphere)
open scoped Real NNReal ENNReal Topology
noncomputable section

/-- Summability restricted to sets -/
def SummableOn (f : ℕ → ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → Summable fun n ↦ f n z

/-- `n ↦ f n z` has a convergent sum for each `z ∈ s` -/
def HasSumOn (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : Set ℂ) :=
  ∀ z, z ∈ s → HasSum (fun n ↦ f n z) (g z)

/-- The parameterized limit of an infinite sum, if it exists -/
noncomputable def tsumOn (f : ℕ → ℂ → ℂ) := fun z ↦ tsum fun n ↦ f n z

/-- Uniform convergence of sums on a set -/
def HasUniformSum (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : Set ℂ) :=
  TendstoUniformlyOn (fun (N : Finset ℕ) z ↦ N.sum fun n ↦ f n z) g atTop s

/-- Uniform vanishing means late sums are uniformly small -/
def UniformVanishing (f : ℕ → ℂ → ℂ) (s : Set ℂ) :=
  ∀ e : ℝ, e > 0 → ∃ n : ℕ, ∀ (N : Finset ℕ) (z), Late N n → z ∈ s → (N.sum fun n ↦ abs (f n z)) < e

/-- Uniformly vanishing series are summable -/
theorem uniformVanishing_to_summable {f : ℕ → ℂ → ℂ} {s : Set ℂ} {z : ℂ} (zs : z ∈ s)
    (h : UniformVanishing f s) : Summable fun n ↦ f n z := by
  rw [summable_iff_vanishing_norm]; intro e ep
  rcases h e ep with ⟨m, hm⟩
  use Finset.range m; intro A d
  calc ‖A.sum (fun n ↦ f n z)‖
    _ ≤ A.sum (fun n ↦ ‖f n z‖) := by bound [norm_sum_le]
    _ < e := hm _ _ (late_iff_disjoint_range.mpr d) zs

/-- Uniformly vanishing series results in uniform Cauchy sequences of finite sums -/
theorem uniformVanishing_to_uniform_cauchy_series {f : ℕ → ℂ → ℂ} {s : Set ℂ}
    (h : UniformVanishing f s) :
    UniformCauchySeqOn (fun (N : Finset ℕ) z ↦ N.sum fun n ↦ f n z) atTop s := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro e ep
  rcases h e ep with ⟨m, hm⟩
  use Finset.range m
  intro A HA B HB z zs
  calc dist (A.sum fun n ↦ f n z) (B.sum fun n ↦ f n z)
    _ ≤ (A ∆ B).sum fun n ↦ abs (f n z) := symmDiff_bound _ _ _
    _ < e := hm (A ∆ B) z (symmDiff_late HA HB) zs

/-- If a series is uniformly vanishing, it tends to its limit uniformly -/
theorem uniformVanishing_to_tendsto_uniformly_on {f : ℕ → ℂ → ℂ} {s : Set ℂ}
    (h : UniformVanishing f s) : HasUniformSum f (tsumOn f) s := by
  rw [HasUniformSum, Metric.tendstoUniformlyOn_iff]
  intro e ep
  rcases h (e / 4) (by linarith) with ⟨m, hm⟩
  rw [Filter.eventually_atTop]
  use Finset.range m
  intro N Nm z zs
  rw [tsumOn]
  generalize G : tsum (fun n ↦ f n z) = g
  have S : Summable (fun n ↦ f n z) := uniformVanishing_to_summable zs h
  have GS : HasSum (fun n ↦ f n z) g := by rw [← G]; exact Summable.hasSum S
  clear S
  rw [HasSum] at GS
  rw [Metric.tendsto_atTop] at GS
  rcases GS (e / 4) (by linarith) with ⟨M, HM⟩; clear GS G h
  set A := N ∪ M \ N
  have AM : M ⊆ A := subset_union_sdiff _ _
  simp at HM
  specialize HM A AM
  rw [dist_comm] at HM
  calc dist g (N.sum fun n ↦ f n z)
    _ ≤ dist g (A.sum fun n ↦ f n z) + dist (A.sum fun n ↦ f n z) (N.sum fun n ↦ f n z) := by bound
    _ ≤ e / 4 + dist (A.sum fun n ↦ f n z) (N.sum fun n ↦ f n z) := by linarith
    _ = e / 4 + dist ((N.sum fun n ↦ f n z) + (M \ N).sum fun n ↦ f n z)
        (N.sum fun n ↦ f n z) := by rw [Finset.sum_union Finset.disjoint_sdiff]
    _ = e / 4 + abs (((N.sum fun n ↦ f n z) + (M \ N).sum fun n ↦ f n z) -
        N.sum fun n ↦ f n z) := by rw [Complex.dist_eq]
    _ = e / 4 + abs ((M \ N).sum fun n ↦ f n z) := by ring_nf
    _ ≤ e / 4 + (M \ N).sum fun n ↦ abs (f n z) := by
      linarith [finset_complex_abs_sum_le (M \ N) fun n ↦ f n z]
    _ ≤ e / 4 + e / 4 := by linarith [hm (M \ N) z (sdiff_late M Nm) zs]
    _ = e / 2 := by ring
    _ < e := by linarith

/-- Geometric bounds with c ≤ 0 are degenerate -/
theorem CNonpos.degenerate {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (c0 : c ≤ 0) (a0 : 0 ≤ a)
    (hf : ∀ n z, z ∈ s → abs (f n z) ≤ c * a ^ n) : ∀ n z, z ∈ s → f n z = 0 := by
  intro n z zs; specialize hf n z zs
  have ca : c * a ^ n ≤ 0 := mul_nonpos_iff.mpr (Or.inr ⟨c0, by bound⟩)
  exact Complex.abs.eq_zero.mp (le_antisymm (le_trans hf ca) (Complex.abs.nonneg _))

/-- Uniformly exponentially converging series converge uniformly -/
theorem fast_series_converge_uniformly_on {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (a0 : 0 ≤ a)
    (a1 : a < 1) (hf : ∀ n z, z ∈ s → abs (f n z) ≤ c * a ^ n) : HasUniformSum f (tsumOn f) s := by
  by_cases c0 : c ≤ 0
  · have fz := CNonpos.degenerate c0 a0 hf; simp only at fz
    rw [HasUniformSum, Metric.tendstoUniformlyOn_iff]
    intro e ep; apply Filter.eventually_of_forall; intro n z zs
    rw [tsumOn]
    simp_rw [fz _ z zs]
    simp only [tsum_zero, Finset.sum_const_zero, dist_zero_left, Complex.norm_eq_abs,
      AbsoluteValue.map_zero]
    assumption
  · simp only [not_le] at c0
    apply uniformVanishing_to_tendsto_uniformly_on
    intro e ep
    set t := (1 - ↑a) / ↑c * (e / 2)
    have tp : t > 0 := by bound
    rcases exists_pow_lt_of_lt_one tp a1 with ⟨n, nt⟩
    use n; intro N z NL zs
    have a1p : 1 - (a : ℝ) > 0 := by linarith
    calc (N.sum fun n ↦ abs (f n z))
      _ ≤ N.sum fun n ↦ c * a ^ n := Finset.sum_le_sum fun n _ ↦ hf n z zs
      _ = c * N.sum fun n ↦ a ^ n := Finset.mul_sum.symm
      _ ≤ c * (a ^ n * (1 - a)⁻¹) := by bound [late_geometric_bound NL a0 a1]
      _ = a ^ n * (c * (1 - a)⁻¹) := by ring
      _ ≤ t * (c * (1 - a)⁻¹) := by bound
      _ = (1 - a) / c * (e / 2) * (c * (1 - a)⁻¹) := rfl
      _ = (1 - a) * (1 - a)⁻¹ * (c / c) * (e / 2) := by ring
      _ = 1 * 1 * (e / 2) := by rw [mul_inv_cancel a1p.ne', div_self c0.ne']
      _ = e / 2 := by ring
      _ < e := by linarith

/-- Exponentially converging series converge -/
theorem fast_series_converge_at {f : ℕ → ℂ} {c a : ℝ} (a0 : 0 ≤ a) (a1 : a < 1)
    (hf : ∀ n, abs (f n) ≤ c * a ^ n) : Summable f := by
  set s : Set ℂ := {0}
  set g : ℕ → ℂ → ℂ := fun n _ ↦ f n
  have hg : ∀ n z, z ∈ s → abs (g n z) ≤ c * a ^ n := fun n z _ ↦ hf n
  have u := fast_series_converge_uniformly_on a0 a1 hg
  simp at u
  rw [HasUniformSum] at u
  rw [tendstoUniformlyOn_singleton_iff_tendsto] at u
  apply HasSum.summable; assumption

/-- Analytic series that converge exponentially converge to analytic functions -/
theorem fast_series_converge {f : ℕ → ℂ → ℂ} {s : Set ℂ} {c a : ℝ} (o : IsOpen s) (a0 : 0 ≤ a)
    (a1 : a < 1) (h : ∀ n, AnalyticOn ℂ (f n) s) (hf : ∀ n z, z ∈ s → abs (f n z) ≤ c * a ^ n) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g s ∧ HasSumOn f g s := by
  use tsumOn f; constructor
  · exact uniform_analytic_lim o (fun N ↦ N.analyticOn_sum fun _ _ ↦ h _)
      (fast_series_converge_uniformly_on a0 a1 hf)
  · exact fun z zs ↦ Summable.hasSum (fast_series_converge_at a0 a1 fun n ↦ hf n z zs)
