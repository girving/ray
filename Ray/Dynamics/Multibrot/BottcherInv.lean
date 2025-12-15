module
public import Ray.Dynamics.Multibrot.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Ray.Dynamics.BottcherNear
import Ray.Dynamics.Multibrot.Basic
import Ray.Dynamics.Multibrot.Bottcher
import Ray.Dynamics.Multibrot.Isomorphism
import Ray.Dynamics.Multibrot.Postcritical
import Ray.Dynamics.Postcritical
import Ray.Manifold.Analytic

/-!
## `s.bottcher_inv` as an analytic function

We show that `s.bottcher_inv` is analytic for large `c`, small `z`.  We prove everything we need to
write down the functional equations in `RayEqn.lean`, including injectivity for the Koebe quarter
theorem at infinity.
-/

open Complex
open Function (uncurry)
open Filter (Tendsto)
open Metric (ball)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint RiemannSphere Topology
noncomputable section

variable {c x z : ℂ} {r : ℝ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
### Dynamical space facts about `sbottcher_inv`
-/

/-- `s.bottcher` is analytic for large `c, z` -/
public lemma contDiffAt_bottcher_large (c4 : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ContMDiffAt II I ⊤ (uncurry (superF d).bottcher) (c, z) := by
  set s := superF d
  apply s.bottcher_mAnalyticOn
  exact postcritical_large c4 cz

@[simp] public lemma sbottcher_inv_zero : sbottcher_inv d c 0 = 0 := by
  simp only [sbottcher_inv_def, coe_zero, inv_zero', Super.bottcher_a]

/-- `sbottcher_inv` is analytic for large `c`, small `z` -/
public lemma analyticAt_sbottcher_inv (c4 : 4 ≤ ‖c‖) (zc : ‖z‖ ≤ ‖c‖⁻¹) :
    AnalyticAt ℂ (uncurry (sbottcher_inv d)) (c, z) := by
  set s := superF d
  apply ContMDiffAt.analyticAt (I := II) (J := I)
  have e : uncurry (sbottcher_inv d) =
      uncurry (superF d).bottcher ∘ fun p : ℂ × ℂ ↦ (p.1, (p.2 : 𝕊)⁻¹) := by
    simp only [sbottcher_inv_def, Function.comp_def, Function.uncurry_def]
  rw [e]
  have ba : ContMDiffAt II I ⊤ (uncurry (superF d).bottcher) (c, (z : 𝕊)⁻¹) := by
    by_cases z0 : z = 0
    · apply s.bottcher_mAnalyticOn
      simp only [z0, coe_zero, inv_zero', s.post_a]
    · rw [inv_coe z0]
      apply contDiffAt_bottcher_large c4
      rwa [norm_inv, le_inv_comm₀ (by linarith) (by simpa)]
  refine ba.comp_of_eq ?_ (by rfl)
  apply contMDiffAt_fst.prodMk
  apply mAnalytic_inv.comp (by apply mAnalytic_coe.comp (by apply contMDiffAt_snd))

/-- `sbottcher_inv` is injective for large `c`, small `z` -/
public lemma sbottcher_inv_inj (c4 : 4 ≤ ‖c‖) : InjOn (sbottcher_inv d c) (ball 0 ‖c‖⁻¹) := by
  set s := superF d
  intro z0 m0 z1 m1 e
  simp only [Metric.mem_ball, dist_zero_right] at m0 m1
  simp only [sbottcher_inv_def] at e
  rw [(s.bottcher_inj c).eq_iff] at e
  · simpa only [inv_inj, OnePoint.some_eq_iff] using e
  · exact postcritical_small c4 m0.le
  · exact postcritical_small c4 m1.le

/-- `sbottcher_inv` is monic at `z = 0`, for large `c` -/
public lemma sbottcher_inv_monic (c4 : 4 ≤ ‖c‖) : HasDerivAt (sbottcher_inv d c) 1 0 := by
  have c0 : 0 < ‖c‖ := by linarith
  have ci0 : 0 < ‖c‖⁻¹ := by bound
  have e : sbottcher_inv d c =ᶠ[𝓝 0] bottcherNear (fl (f d) ∞ c) d := by
    filter_upwards [eventually_norm_sub_lt 0 ci0] with z zc
    simp only [sub_zero] at zc
    by_cases z0 : z = 0
    · simp only [z0, sbottcher_inv_zero, bottcherNear_zero]
    · nth_rw 2 [← inv_inv z]
      rw [← bottcher_eq_bottcherNear_z c4, sbottcher_inv_def]
      simp only [inv_coe z0]
      rw [norm_inv, le_inv_comm₀ c0 (by simpa)]
      exact zc.le
  exact (bottcherNear_monic (superNearF d c)).congr_of_eventuallyEq e

/-- `sbottcher_inv d c z = z + O(z^2)` -/
public theorem sbottcher_inv_approx_z (d : ℕ) [Fact (2 ≤ d)] (c4 : 4 ≤ ‖c‖) (zc : ‖z‖ ≤ ‖c‖⁻¹) :
    ‖sbottcher_inv d c z - z‖ ≤ 0.943 * ‖z‖ ^ 2 := by
  by_cases z0 : z = 0
  · simp [z0]
  · have czi : ‖c‖ ≤ ‖z⁻¹‖ := by rwa [norm_inv, le_inv_comm₀ (by linarith) (norm_pos_iff.mpr z0)]
    simpa only [inv_inv, norm_inv, inv_inv, ← inv_coe z0, sbottcher_inv_def] using
      bottcher_approx_z d c4 czi

/-!
### Parameter space facts about `bottcher_inv`
-/

/-- Small `z`s invert into `multibrotExt d` -/
public lemma inv_mem_multibrotExt (m : ‖z‖ < 2⁻¹) : (z : 𝕊)⁻¹ ∈ multibrotExt d := by
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', multibrotExt_inf]
  · rw [inv_coe z0, multibrotExt_coe]
    apply multibrot_two_lt
    rwa [norm_inv, lt_inv_comm₀ (by norm_num) (norm_pos_iff.mpr z0)]

/-- `bottcher_inv d` is analytic for small `z` -/
public lemma analyticAt_bottcher_inv (m : ‖z‖ < 2⁻¹) : AnalyticAt ℂ (bottcher_inv d) z := by
  apply ContMDiffAt.analyticAt (I := I) (J := I)
  simp only [bottcher_inv_def]
  refine (bottcherMAnalytic d (z : 𝕊)⁻¹ (inv_mem_multibrotExt m)).comp_of_eq ?_ (by rfl)
  apply mAnalytic_inv.comp mAnalytic_coe

/-- `bottcher_inv d` is injective for small `z` -/
public lemma bottcher_inv_inj : InjOn (bottcher_inv d) (ball 0 2⁻¹) := by
  intro z0 m0 z1 m1 e
  simp only [Metric.mem_ball, dist_zero_right] at m0 m1
  simpa [bottcher_inj.eq_iff (inv_mem_multibrotExt m0) (inv_mem_multibrotExt m1),
    bottcher_inv_def] using e

/-- `bottcher_inv d c = c + O(c^2)` -/
public theorem bottcher_inv_approx (d : ℕ) [Fact (2 ≤ d)] (z4 : ‖z‖ ≤ 4⁻¹) :
    ‖bottcher_inv d z - z‖ ≤ 0.943 * ‖z‖ ^ 2 := by
  by_cases z0 : z = 0
  · simp [z0]
  · have zi : 4 ≤ ‖z⁻¹‖ := by rwa [norm_inv, le_inv_comm₀ (by linarith) (norm_pos_iff.mpr z0)]
    simpa [bottcher_inv_def, bottcher, inv_coe z0] using bottcher_approx d zi
