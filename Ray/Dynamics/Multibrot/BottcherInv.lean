import Ray.Dynamics.Multibrot.Bottcher
import Ray.Dynamics.Multibrot.Postcritical
import Ray.Koebe.Koebe

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

variable {c z : ℂ} {r : ℝ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `s.bottcher` is analytic for large `c, z` -/
lemma contDiffAt_bottcher_large (c4 : 4 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) :
    ContMDiffAt II I ⊤ (uncurry (superF d).bottcher) (c, z) := by
  set s := superF d
  apply s.bottcher_mAnalyticOn
  exact postcritical_large c4 cz

/-- `s.bottcher_inv` as an analytic `ℂ → ℂ → ℂ` function -/
def sbottcher_inv (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ → ℂ :=
  fun c z ↦ (superF d).bottcher c (z : 𝕊)⁻¹

@[simp] lemma sbottcher_inv_zero : sbottcher_inv d c 0 = 0 := by
  simp only [sbottcher_inv, coe_zero, inv_zero', Super.bottcher_a]

/-- `sbottcher_inv` is analytic for large `c`, small `z` -/
lemma analyticAt_sbottcher_inv (c4 : 4 ≤ ‖c‖) (zc : ‖z‖ ≤ ‖c‖⁻¹) :
    AnalyticAt ℂ (uncurry (sbottcher_inv d)) (c, z) := by
  set s := superF d
  apply ContMDiffAt.analyticAt (I := II) (J := I)
  have e : uncurry (sbottcher_inv d) =
      uncurry (superF d).bottcher ∘ fun p : ℂ × ℂ ↦ (p.1, (p.2 : 𝕊)⁻¹) := rfl
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
lemma sbottcher_inv_inj (c4 : 4 ≤ ‖c‖) : InjOn (sbottcher_inv d c) (ball 0 ‖c‖⁻¹) := by
  set s := superF d
  intro z0 m0 z1 m1 e
  simp only [Metric.mem_ball, dist_zero_right] at m0 m1
  simp only [sbottcher_inv] at e
  rw [(s.bottcher_inj c).eq_iff] at e
  · simpa only [inv_inj, OnePoint.some_eq_iff] using e
  · exact postcritical_small c4 m0.le
  · exact postcritical_small c4 m1.le

/-- `sbottcher_inv` is monic at `z = 0`, for large `c` -/
lemma sbottcher_inv_monic (c16 : 16 < ‖c‖) : HasDerivAt (sbottcher_inv d c) 1 0 := by
  have c0 : 0 < ‖c‖ := by linarith
  have ci0 : 0 < ‖c‖⁻¹ := by bound
  have e : sbottcher_inv d c =ᶠ[𝓝 0] bottcherNear (fl (f d) ∞ c) d := by
    filter_upwards [eventually_norm_sub_lt 0 ci0] with z zc
    simp only [sub_zero] at zc
    by_cases z0 : z = 0
    · simp only [z0, sbottcher_inv_zero, bottcherNear_zero]
    · nth_rw 2 [← inv_inv z]
      rw [← bottcher_eq_bottcherNear_z c16, sbottcher_inv, inv_coe z0]
      rw [norm_inv, le_inv_comm₀ c0 (by simpa)]
      exact zc.le
  exact (bottcherNear_monic (superNearF d c)).congr_of_eventuallyEq e

/-!
### Koebe quarter theorem at infinity applied to `sbottcher_inv`
-/

/-- `sbottcher_inv` covers a large disk around the origin, by the Koebe quarter theorem -/
lemma sbottcher_inv_koebe (c16 : 16 < ‖c‖) (rc : r ≤ ‖c‖⁻¹) :
    ball 0 (r / 4) ⊆ sbottcher_inv d c '' (ball 0 r) := by
  have c4 : 4 ≤ ‖c‖ := by linarith
  have k := koebe_quarter' (f := sbottcher_inv d c) (c := 0) (r := r) ?_ ?_
  · simpa [(sbottcher_inv_monic c16).deriv] using k
  · intro z zr
    refine (analyticAt_sbottcher_inv c4 ?_).along_snd
    simp only [Metric.mem_ball, dist_zero_right] at zr
    linarith
  · exact (sbottcher_inv_inj c4).mono (Metric.ball_subset_ball rc)
