module
public import Ray.Multibrot.Isomorphism
import Mathlib.Analysis.Complex.RemovableSingularity
import Ray.Koebe.Gronwall
import Ray.Multibrot.Basic
import Ray.Multibrot.InvRay

/-!
## Multibrot area via Grönwall's area theorem

We construct the `z ↦ z⁻¹ / ray d z` map needed to plug into Grönwall's area theorem.
-/

open MeasureTheory (volume)
open Metric (ball isOpen_ball mem_ball)
open Set
open scoped OnePoint Real RiemannSphere Topology
noncomputable section

variable {z : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- The inner dslope is nonzero -/
lemma pray_dslope_ne_zero (m : z ∈ ball (0 : ℂ) 1) : dslope (inv_ray d) 0 z ≠ 0 := by
  by_cases z0 : z = 0
  · simp [z0, ray_hasDerivAt_one.deriv]
  · simp [z0, dslope_of_ne _ z0, slope, inv_ray_ne_zero z0 m]

@[simp] public lemma pray_zero : pray d 0 = 1 := by
  simp only [pray, dslope_same, ray_hasDerivAt_one.deriv, inv_one]

@[simp] public lemma pray_ne_zero (m : z ∈ ball (0 : ℂ) 1) : pray d z ≠ 0 := by
  simp only [pray, ne_eq, _root_.inv_eq_zero, pray_dslope_ne_zero m, not_false_eq_true]

/-- `inv_ray` in terms of `pray` -/
lemma inv_ray_eq_pray : inv_ray d z = z / pray d z := by
  by_cases z0 : z = 0
  · simp [pray, z0]
  · simp [pray, dslope_of_ne _ z0, slope]
    field_simp [z0]

/-- `ray` in terms of `pray` -/
public lemma ray_eq_pray (m : z ∈ ball (0 : ℂ) 1) : ray d z = (z / pray d z : 𝕊)⁻¹ := by
  rw [← inv_ray_eq_pray, inv_ray, RiemannSphere.coe_toComplex (by simp [m]), inv_inv]

/-- `ray` in terms of `pray`, `norm_Ioi` version -/
lemma ray_inv_eq_pray (m : z ∈ norm_Ioi 1) : ray d z⁻¹ = z * pray d z⁻¹ := by
  simp only [norm_Ioi, mem_setOf_eq] at m
  have m' : z⁻¹ ∈ ball (0 : ℂ) 1 := by simp only [mem_ball, dist_zero_right, norm_inv]; bound
  rw [ray_eq_pray m', RiemannSphere.inv_coe]
  · simp [mul_comm]
  · simp only [ne_eq, div_eq_zero_iff, _root_.inv_eq_zero, pray_ne_zero m', or_false]
    simp only [← norm_pos_iff]
    linarith

/-- `pray` is analytic on the ball -/
public lemma pray_analytic (m : z ∈ ball (0 : ℂ) 1) : ContDiffAt ℂ ⊤ (pray d) z := by
  have pa : ∀ z : ℂ, z ∈ ball (0 : ℂ) 1 → z ≠ 0 → ContDiffAt ℂ ⊤ (pray d) z := by
    intro z m z0
    have e : pray d =ᶠ[𝓝 z] fun z ↦ z / inv_ray d z := by
      filter_upwards [eventually_ne_nhds z0] with z z0
      simp [pray, dslope_of_ne _ z0, slope, div_eq_inv_mul]
    refine ContDiffAt.congr_of_eventuallyEq ?_ e
    exact contDiffAt_id.div (inv_ray_analytic m) (inv_ray_ne_zero z0 m)
  by_cases z0 : z = 0
  · apply AnalyticAt.contDiffAt
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · simp only [z0, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, ← ne_eq]
      filter_upwards [isOpen_ball.eventually_mem (by simp : 0 ∈ ball (0 : ℂ) 1)] with w m wz
      exact (pa w m wz).differentiableAt (by decide)
    · unfold pray
      refine ContinuousAt.inv₀ ?_ (pray_dslope_ne_zero m)
      simp only [z0, continuousAt_dslope_same]
      exact (inv_ray_analytic (by simp)).differentiableAt (by decide)
  · exact pa z m z0

public lemma pray_analyticOnNhd : AnalyticOnNhd ℂ (pray d) (ball 0 1) := by
  intro z m
  exact (pray_analytic m).analyticAt

/-- The exterior of the multibrot set in terms of `pray` -/
lemma multibrot_eq_pray : (multibrot d)ᶜ = (fun z ↦ z * pray d z⁻¹) '' norm_Ioi 1 := by
  ext z
  simp only [mem_compl_iff, ← multibrotExt_coe, mem_image]
  constructor
  · intro m
    have b1 : 1 < ‖bottcher d ↑z‖⁻¹ := by
      rw [one_lt_inv₀]
      · exact norm_bottcher_lt_one m
      · simp only [norm_pos_iff, ne_eq, bottcher_coe_ne_zero, not_false_eq_true]
    refine ⟨(bottcher d z)⁻¹, ?_, ?_⟩
    · simp only [norm_Ioi, mem_setOf_eq, norm_inv, b1]
    · rw [← RiemannSphere.coe_eq_coe, ← ray_inv_eq_pray, inv_inv, ray_bottcher m]
      simp only [norm_Ioi, mem_setOf_eq, norm_inv, b1]
  · intro ⟨w,w1,wz⟩
    rw [← RiemannSphere.coe_eq_coe, ← ray_inv_eq_pray w1] at wz
    rw [← wz]
    apply ray_mem_multibrotExt
    simp only [norm_Ioi, mem_setOf_eq, mem_ball, dist_zero_right, norm_inv] at w1 ⊢
    exact inv_lt_one_of_one_lt₀ w1

/-- `ray` in terms of `pray` is injective -/
lemma pray_inj : InjOn (fun z ↦ z * pray d z⁻¹) (norm_Ioi 1) := by
  intro z z1 w w1 e
  simp only [← RiemannSphere.coe_eq_coe, ← ray_inv_eq_pray, z1, w1] at e
  simp only [norm_Ioi, mem_setOf_eq] at z1 w1
  rwa [ray_inj.eq_iff, inv_inj] at e
  all_goals rw [mem_ball, dist_zero_right, norm_inv]; exact inv_lt_one_of_one_lt₀ (by assumption)

/-- Grönwall area series for `multibrot d` -/
theorem multibrot_volume_sum :
    HasSum (fun n ↦ π * n * ‖iteratedDeriv (n + 1) (pray d) 0 / (n + 1).factorial‖ ^ 2)
      (π - volume.real (multibrot d)) := by
  rw [← compl_compl (multibrot d), multibrot_eq_pray]
  exact gronwall_volume_sum pray_analyticOnNhd pray_zero pray_inj

/-- Upper bound on the `multibrot d` area using a finite set of Grönwall's terms -/
theorem multibrot_volume_le (s : Finset ℕ) :
    volume.real (multibrot d) ≤
      π - ∑ n ∈ s, π * n * ‖iteratedDeriv (n + 1) (pray d) 0 / (n + 1).factorial‖ ^ 2 := by
  rw [← compl_compl (multibrot d), multibrot_eq_pray]
  exact gronwall_volume_le pray_analyticOnNhd pray_zero pray_inj s
