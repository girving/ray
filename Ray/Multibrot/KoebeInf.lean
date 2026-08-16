module
public import Ray.Multibrot.Defs
import Ray.Dynamics.Bottcher
import Ray.Dynamics.Postcritical
import Ray.Koebe.Koebe
import Ray.Multibrot.Basic
import Ray.Multibrot.Bottcher
import Ray.Multibrot.BottcherInv
import Ray.Multibrot.Postcritical
import Ray.Multibrot.Rinv

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
public lemma sbottcher_inv_koebe (rc : r ≤ rinv 4⁻¹ c) :
    ball 0 (r / 4) ⊆ sbottcher_inv d c '' (ball 0 r) := by
  have k := koebe_quarter' (f := sbottcher_inv d c) (c := 0) (r := r) ?_ ?_
  · simpa [sbottcher_inv_monic.deriv] using k
  · intro z zr
    refine (analyticAt_sbottcher_inv ?_).along_snd
    simp only [Metric.mem_ball, dist_zero_right] at zr
    linarith
  · exact sbottcher_inv_inj.mono (Metric.ball_subset_ball rc)

@[irreducible] def four_le (c : ℂ) : Prop := 4 ≤ ‖c‖

/-- Large `c`, small `x` has small `sbottcher_inv` preimage -/
public lemma sbottcher_inv_small_mem_preimage (xc : ‖x‖ < rinv 4⁻¹ c / 4) :
    ∃ z : ℂ, ‖z‖ ≤ 4 * ‖x‖ ∧ ‖c‖ * ‖z‖ < 1 ∧ (c, (z : 𝕊)⁻¹) ∈ (superF d).post ∧
      sbottcher_inv d c z = x := by
  set s := superF d
  by_cases x0 : x = 0
  · refine ⟨0, ?_, ?_, ?_, ?_⟩
    · bound
    · simp
    · bound
    · simp only [sbottcher_inv_zero, x0]
  · obtain ⟨t, t0, t1⟩ := exists_between xc
    have tc' : 4 * t ≤ rinv 4⁻¹ c := by rw [mul_comm, ← le_div_iff₀ (by norm_num)]; exact t1.le
    obtain ⟨z,zm,zx⟩ := sbottcher_inv_koebe (d := d) (r := 4 * t) tc' (a := x) (by simp; linarith)
    simp only [Metric.mem_ball, dist_zero_right] at zm
    have zr : ‖z‖ < rinv 4⁻¹ c := lt_of_lt_of_le zm tc'
    refine ⟨z, ?_, (lt_rinv.mp zr).2, ?_, zx⟩
    · refine le_of_forall_pos_le_add fun e e0 ↦ ?_
      have small : x ∈ ball 0 (min (4 * ‖x‖ + e) (rinv 4⁻¹ c) / 4) := by
        simp only [Metric.mem_ball, dist_zero_right, lt_min_iff,
          ← min_div_div_right (by norm_num : (0 : ℝ) ≤ 4)]
        constructor <;> linarith
      obtain ⟨z',zm',zx'⟩ := sbottcher_inv_koebe (d := d) (r := min (4 * ‖x‖ + e) (rinv 4⁻¹ c))
        (by exact min_le_right _ _) (a := x) small
      simp only [Metric.mem_ball, dist_zero_right, lt_inf_iff] at zm'
      have e := zx.trans zx'.symm
      rw [(sbottcher_inv_inj).eq_iff (by simpa) (by simp [zm'])] at e
      exact e ▸ zm'.1.le
    · exact postcritical_small zr.le

/-- Large `c`, small `x` is in `s.ext` -/
public lemma small_mem_ext (xc : ‖x‖ < rinv 4⁻¹ c / 4) : (c, x) ∈ (superF d).ext := by
  obtain ⟨z,_,_,zp,zx⟩ := sbottcher_inv_small_mem_preimage (d := d) xc
  simp only [sbottcher_inv_def] at zx
  have t := ((superF d).homeomorphSlice c).map_target (x := z⁻¹)
  simp only [Super.target_homeomorphSlice, mem_ofPred_eq, zp, Super.source_homeomorphSlice,
    Super.invFun_homeomorphSlice, forall_const] at t
  simpa [zx] using t

/-!
### Koebe quarter theorem at infinity applied to `bottcher`
-/

/-- `bottcher` covers a large disk around the origin, by the Koebe quarter theorem -/
public lemma bottcher_inv_koebe (r2 : r ≤ 2⁻¹) :
    ball 0 (r / 4) ⊆ bottcher_inv d '' (ball 0 r) := by
  have k := koebe_quarter' (f := bottcher_inv d) (c := 0) (r := r) ?_ ?_
  · simpa [bottcher_hasDerivAt_one.deriv] using k
  · intro z zr
    simp only [Metric.mem_ball, dist_zero_right] at zr
    exact analyticAt_bottcher_inv (by linarith)
  · exact bottcher_inv_inj.mono (Metric.ball_subset_ball r2)

/-- Small `z`s have small `bottcher_inv` preimages -/
public lemma bottcher_inv_small_mem_preimage (z8 : ‖z‖ < 8⁻¹) :
    ∃ c : ℂ, ‖c‖ ≤ 4 * ‖z‖ ∧ (c : 𝕊)⁻¹ ∈ multibrotExt d ∧ bottcher_inv d c = z := by
  set s := superF d
  by_cases z0 : z = 0
  · refine ⟨0, ?_, ?_, ?_⟩
    · simp only [norm_zero]
      bound
    · simp only [coe_zero, inv_zero', multibrotExt_inf]
    · simp only [bottcher_inv_zero, z0]
  · obtain ⟨t, t0, t1⟩ := exists_between z8
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
