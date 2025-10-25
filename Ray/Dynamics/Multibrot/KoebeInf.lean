import Ray.Dynamics.Multibrot.BottcherInv
import Ray.Koebe.Koebe

/-!
# The Koebe quarter theorem at infinity, applied to dynamical and parameter space Böttcher maps
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

/-- Large `c`, small `x` has small `sbottcher_inv` preimage -/
lemma sbottcher_inv_small_mem_preimage (c16 : 16 < ‖c‖) (xc : ‖x‖ < ‖c‖⁻¹ / 4) :
    ∃ z : ℂ, ‖z‖ < ‖c‖⁻¹ ∧ ‖z‖ ≤ 4 * ‖x‖ ∧ (c, (z : 𝕊)⁻¹) ∈ (superF d).post ∧
      sbottcher_inv d c z = x := by
  set s := superF d
  by_cases x0 : x = 0
  · refine ⟨0, ?_, ?_, ?_, ?_⟩
    · simp only [norm_zero]
      bound
    · bound
    · simp only [coe_zero, inv_zero', s.post_a]
    · simp only [sbottcher_inv_zero, x0]
  · obtain ⟨t, t0, t1⟩ := exists_between xc
    have tc : 4 * t ≤ ‖c‖⁻¹ := by linarith
    obtain ⟨z,zm,zx⟩ := sbottcher_inv_koebe (d := d) c16 tc (a := x) (by simp; linarith)
    simp only [Metric.mem_ball, dist_zero_right] at zm
    have zc : ‖z‖ < ‖c‖⁻¹ := by linarith
    refine ⟨z, (by linarith), ?_, ?_, zx⟩
    · refine le_of_forall_pos_le_add fun e e0 ↦ ?_
      have small : x ∈ ball 0 (min (4 * ‖x‖ + e) ‖c‖⁻¹ / 4) := by
        simp only [Metric.mem_ball, dist_zero_right, lt_min_iff,
          ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 4)]
        constructor <;> linarith
      obtain ⟨z',zm',zx'⟩ := sbottcher_inv_koebe (d := d) c16 (r := min (4 * ‖x‖ + e) ‖c‖⁻¹)
        (by exact min_le_right _ _) (a := x) small
      simp only [Metric.mem_ball, dist_zero_right, lt_inf_iff] at zm'
      have e := zx.trans zx'.symm
      rw [(sbottcher_inv_inj (by linarith)).eq_iff (by simpa) (by simp [zm'])] at e
      exact e ▸ zm'.1.le
    · exact postcritical_small (by linarith) (by linarith)

/-- Large `c`, small `x` is in `s.ext` -/
lemma small_mem_ext (c16 : 16 < ‖c‖) (xc : ‖x‖ < ‖c‖⁻¹ / 4) : (c, x) ∈ (superF d).ext := by
  obtain ⟨z,_,_,zp,zx⟩ := sbottcher_inv_small_mem_preimage (d := d) c16 xc
  exact zx ▸ ((superF d).homeomorphSlice c).map_target zp

/-!
### Koebe quarter theorem at infinity applied to `bottcher`
-/

/-- `bottcher` covers a large disk around the origin, by the Koebe quarter theorem -/
lemma bottcher_inv_koebe (r2 : r ≤ 2⁻¹) :
    ball 0 (r / 4) ⊆ bottcher_inv d '' (ball 0 r) := by
  have k := koebe_quarter' (f := bottcher_inv d) (c := 0) (r := r) ?_ ?_
  · simpa [bottcher_hasDerivAt_one.deriv] using k
  · intro z zr
    simp only [Metric.mem_ball, dist_zero_right] at zr
    exact analyticAt_bottcher_inv (by linarith)
  · exact bottcher_inv_inj.mono (Metric.ball_subset_ball r2)

/-- Small `z`s have small `bottcher_inv` preimages -/
lemma bottcher_inv_small_mem_preimage (z2 : ‖z‖ < 8⁻¹) :
    ∃ c : ℂ, ‖c‖ ≤ 4 * ‖z‖ ∧ (c : 𝕊)⁻¹ ∈ multibrotExt d ∧ bottcher_inv d c = z := by
  set s := superF d
  by_cases z0 : z = 0
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp only [norm_zero]
      bound
    · simp only [coe_zero, inv_zero', multibrotExt_inf]
    · simp only [bottcher_inv_zero, z0]
  · obtain ⟨t, t0, t1⟩ := exists_between z2
    obtain ⟨c,cm,cx⟩ := bottcher_inv_koebe (d := d) (r := 4 * t) (by linarith) (a := z)
      (by simp; linarith)
    have c2 : ‖c‖ < 2⁻¹ := by
      simp only [Metric.mem_ball, dist_zero_right] at cm
      linarith
    have cz : ‖c‖ ≤ 4 * ‖z‖ := by
      refine le_of_forall_pos_le_add fun e e0 ↦ ?_
      have small : z ∈ ball 0 (min (4 * ‖z‖ + e) 2⁻¹ / 4) := by
        simp only [Metric.mem_ball, dist_zero_right, lt_min_iff,
          ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 4)]
        constructor <;> linarith
      obtain ⟨c',cm',cx'⟩ := bottcher_inv_koebe (d := d) (r := min (4 * ‖z‖ + e) 2⁻¹)
        (min_le_right _ _) (a := z) small
      simp only [Metric.mem_ball, dist_zero_right, lt_inf_iff] at cm'
      have e := cx.trans cx'.symm
      rw [bottcher_inv_inj.eq_iff (by simpa) (by simp [cm'])] at e
      exact e ▸ cm'.1.le
    exact ⟨c, cz, inv_mem_multibrotExt c2, cx⟩
