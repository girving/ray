module
public import Ray.Multibrot.Defs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Ray.Manifold.Analytic
import Ray.Manifold.Manifold
import Ray.Manifold.OneDimension
import Ray.Misc.Bound
import Ray.Multibrot.Bottcher
import Ray.Multibrot.BottcherInv
import Ray.Multibrot.Postcritical
import Ray.Multibrot.Rinv
import Ray.Schwarz.SchwarzPick

/-!
## Effective bounds on the derivative of the Multibrot `bottcher` function

We use Schwarz-Pick on top of our bounds on `bottcher` itself.
-/

open Metric (mem_closedBall)
open Real (sqrt)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint Real RiemannSphere Topology
noncomputable section

variable {c z : ℂ} {f g : ℂ → ℂ} {r0 r1 a : ℝ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

@[bound] lemma le_243 : 0.943 * (√3 ^ 2 - 1)⁻¹ * √3 ^ 3 ≤ (2.45 : ℝ) := by
  have a3 : sqrt 3 ^ 3 = 3 * sqrt 3 := by simp [pow_succ', mul_comm]
  simp only [Nat.ofNat_nonneg, Real.sq_sqrt, a3, ← mul_assoc]
  rw [mul_comm, ← le_div_iff₀ (by norm_num), Real.sqrt_le_iff]
  norm_num

/-!
### Dynamical space versions
-/

/-- The derivative of `sbottcher_inv d c z` w.r.t `z` is approximately 1 for small `z` -/
public lemma deriv_sbottcher_inv_z_approx (zc : ‖z‖ ≤ rinv 4⁻¹ c / sqrt 3) :
    ‖deriv (sbottcher_inv d c) z - 1‖ ≤ 2.45 * ‖z‖ := by
  have zc3 := (le_div_iff₀ (by bound)).mp zc
  obtain ⟨z34, cz3⟩ := le_rinv.mp zc3
  have z43 : ‖z‖ ≤ 4⁻¹ / sqrt 3 := (le_div_iff₀ (by bound)).mpr z34
  have zc' : ‖z‖ ≤ rinv 4⁻¹ c := le_trans zc (by bound)
  by_cases z0 : z = 0
  · simp [z0, sbottcher_inv_monic.deriv]
  replace z0 : 0 < ‖z‖ := norm_pos_iff.mpr z0
  have a0 : 0 < sqrt 3 := by bound
  have a1 : 1 < sqrt 3 := by bound
  set r0 := sqrt 3 * ‖z‖
  have r04 : r0 ≤ 4⁻¹ := by simpa only [r0, le_div_iff₀ a0, mul_comm] using z43
  set r1 := 0.943 * r0 ^ 2
  have r1p : 0 < r1 := by bound
  have zr : ‖z‖ < r0 := by bound
  have s := Complex.norm_deriv_le_mul_div_of_mapsTo_ball (f := fun z ↦ sbottcher_inv d c z - z)
    (r1 := r1) ?_ ?_ zr
  · rw [deriv_fun_sub ?_ (by fun_prop), deriv_id''] at s
    · refine le_trans s ?_
      clear s
      trans r0 / r1 * r1 ^ 2 / (r0 ^ 2 - ‖z‖ ^ 2)
      · bound
      · field_simp [r1p.ne']
        simp only [mul_left_comm r0, ← pow_succ', Nat.reduceAdd, r1]
        simp only [r0, mul_pow, ← sub_one_mul, mul_div_mul_comm]
        simp only [div_eq_mul_inv, mul_assoc, ← pow_sub_of_lt _ (by norm_num : 2 < 3), Nat.reduceSub,
          pow_one]
        simp only [← mul_assoc, mul_comm ‖z‖]
        bound
    · exact (analyticAt_sbottcher_inv (d := d) zc').along_snd.differentiableAt
  · refine ContDiffOn.sub ?_ (by fun_prop)
    intro w wr
    simp only [Metric.mem_ball, dist_zero_right] at wr
    exact (analyticAt_sbottcher_inv (d := d) (by linarith)).along_snd.contDiffAt.contDiffWithinAt
  · intro w wr
    simp only [Metric.mem_ball, dist_zero_right, mem_closedBall] at wr ⊢
    exact le_trans (sbottcher_inv_approx_z (d := d) (by linarith)) (by bound)

/-- The derivative of `s.bottcher c z` w.r.t. `z` is approximately `-z⁻¹ ^ 2` for large `z` -/
public lemma deriv_sbottcher_z_approx (c3z : sqrt 3 * max 4 ‖c‖ ≤ ‖z‖) :
    ‖deriv (fun z : ℂ ↦ (superF d).bottcher c z) z + (z ^ 2)⁻¹‖ ≤ 2.45 / ‖z‖ ^ 3 := by
  set s := superF d
  have z6 : 6 ≤ ‖z‖ := by
    trans sqrt 3 * 4
    · rw [← div_le_iff₀ (by norm_num)]
      bound
    · exact le_trans (by bound) c3z
  have z0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have e : (fun z ↦ s.bottcher c z) =ᶠ[𝓝 z] sbottcher_inv d c ∘ fun z ↦ z⁻¹ := by
    filter_upwards [eventually_ne_nhds z0] with w w0
    simp [sbottcher_inv_def, ← inv_coe w0]
  rw [e.deriv_eq, deriv_comp _ _ (differentiableAt_inv z0)]
  · simp only [deriv_inv, mul_neg, ← neg_mul, ← add_one_mul, neg_add_eq_sub, Complex.norm_mul,
      norm_sub_rev (1 : ℂ), norm_inv, norm_pow]
    refine le_trans (mul_le_mul_of_nonneg_right (deriv_sbottcher_inv_z_approx ?_) (by bound))
      (le_of_eq ?_)
    · rw [norm_inv, inv_le_comm₀ (by bound) (by bound)]
      simpa
    · simp only [norm_inv]
      ring
  · refine (analyticAt_sbottcher_inv (d := d) ?_).along_snd.differentiableAt
    rw [norm_inv, inv_le_comm₀ (by positivity) (by bound), inv_rinv (by norm_num)]
    exact le_trans (by bound) c3z

/-- The derivative of `s.bottcher c z` w.r.t. `c` is small for large `z` -/
public lemma deriv_sbottcher_c_approx (cz : max 4 ‖c‖ < ‖z‖) :
    ‖deriv (fun c : ℂ ↦ (superF d).bottcher c z) c‖ ≤ 0.943 / (‖z‖ * (‖z‖ ^ 2 - ‖c‖ ^ 2)) := by
  set s := superF d
  obtain ⟨z4, cz'⟩ := max_lt_iff.mp cz
  set r1 := 0.943 * ‖z‖⁻¹ ^ 2
  have r1p : 0 < r1 := by bound
  have sp := Complex.norm_deriv_le_mul_div_of_mapsTo_ball (f := fun c ↦ s.bottcher c z - z⁻¹)
    (r1 := r1) ?_ ?_ cz'
  · rw [deriv_sub_const_fun] at sp
    refine le_trans sp ?_
    trans ‖z‖ / r1 * r1 ^ 2 / (‖z‖ ^ 2 - ‖c‖ ^ 2)
    · bound
    · simp only [r1] at r1p ⊢
      field_simp [r1p.ne']
      rfl
  · refine ContDiffOn.sub ?_ (by fun_prop)
    intro w wr
    refine (s.bottcher_mAnalyticOn _ ?_).along_fst.analyticAt.contDiffAt.contDiffWithinAt
    exact postcritical_large z4.le (by simp at wr; exact wr.le)
  · intro w wr
    simp only [Metric.mem_ball, dist_zero_right, mem_closedBall] at wr ⊢
    exact bottcher_approx_z _ z4.le wr.le

/-!
### Parameter space versions
-/

/-- The derivative of `bottcher_inv d` is approximately 1 for small `z` -/
public lemma deriv_bottcher_inv_approx (z4 : ‖z‖ ≤ 4⁻¹ / sqrt 3) :
    ‖deriv (bottcher_inv d) z - 1‖ ≤ 2.45 * ‖z‖ := by
  by_cases z0 : z = 0
  · simp [z0, bottcher_hasDerivAt_one.deriv]
  replace z0 : 0 < ‖z‖ := norm_pos_iff.mpr z0
  have a0 : 0 < sqrt 3 := by bound
  have a1 : 1 < sqrt 3 := by bound
  set r0 := sqrt 3 * ‖z‖
  have r04 : r0 ≤ 4⁻¹ := by simpa only [r0, le_div_iff₀ a0, mul_comm] using z4
  set r1 := 0.943 * r0 ^ 2
  have r1p : 0 < r1 := by bound
  have zr : ‖z‖ < r0 := by bound
  have s := Complex.norm_deriv_le_mul_div_of_mapsTo_ball (f := fun z ↦ bottcher_inv d z - z)
    (r1 := r1) ?_ ?_ zr
  · rw [deriv_fun_sub (analyticAt_bottcher_inv (by linarith)).differentiableAt (by fun_prop),
      deriv_id''] at s
    refine le_trans s ?_
    clear s
    trans r0 / r1 * r1 ^ 2 / (r0 ^ 2 - ‖z‖ ^ 2)
    · bound
    · field_simp [r1p.ne']
      simp only [mul_left_comm r0, ← pow_succ', Nat.reduceAdd, r1]
      simp only [r0, mul_pow, ← sub_one_mul, mul_div_mul_comm]
      simp only [div_eq_mul_inv, mul_assoc, ← pow_sub_of_lt _ (by norm_num : 2 < 3), Nat.reduceSub,
        pow_one]
      simp only [← mul_assoc, mul_comm ‖z‖]
      bound
  · refine ContDiffOn.sub ?_ (by fun_prop)
    intro w wr
    simp only [Metric.mem_ball, dist_zero_right] at wr
    exact (analyticAt_bottcher_inv (by linarith)).contDiffAt.contDiffWithinAt
  · intro w wr
    simp only [Metric.mem_ball, dist_zero_right, mem_closedBall] at wr ⊢
    exact le_trans (bottcher_inv_approx d (by linarith)) (by bound)

/-- The derivative of `bottcher' d` is approximately `-z⁻¹ ^ 2` for large `z` -/
public lemma deriv_bottcher_approx (z4 : 4 * sqrt 3 ≤ ‖z‖) :
    ‖deriv (bottcher' d) z + (z ^ 2)⁻¹‖ ≤ 2.45 / ‖z‖ ^ 3 := by
  have z6 : 6 ≤ ‖z‖ := le_trans (by rw [mul_comm, ← div_le_iff₀ (by norm_num)]; bound) z4
  have z0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have e : bottcher' d =ᶠ[𝓝 z] bottcher_inv d ∘ fun z ↦ z⁻¹ := by
    filter_upwards [eventually_ne_nhds z0] with w w0
    simp [bottcher_inv_def, bottcher, ← inv_coe w0]
  rw [e.deriv_eq, deriv_comp _ _ (differentiableAt_inv z0)]
  · simp only [deriv_inv, mul_neg, ← neg_mul, ← add_one_mul, neg_add_eq_sub, Complex.norm_mul,
      norm_sub_rev (1 : ℂ), norm_inv, norm_pow]
    refine le_trans (mul_le_mul_of_nonneg_right (deriv_bottcher_inv_approx ?_) (by bound))
      (le_of_eq ?_)
    · rw [norm_inv, inv_le_comm₀ (by bound) (by bound)]
      simpa [mul_comm] using z4
    · simp only [norm_inv]
      ring
  · refine (analyticAt_bottcher_inv ?_).differentiableAt
    simp only [norm_inv]
    bound
