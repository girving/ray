module
public import Ray.Multibrot.Defs
import Ray.Multibrot.Basic

/-!
## Properties of `rinv`
-/

open Complex
open Metric (ball closedBall mem_closedBall)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint Real RiemannSphere Topology
noncomputable section

variable {c z : ℂ} {r x : ℝ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

@[simp, bound] public lemma rinv_nonneg (r0 : 0 ≤ r) : 0 ≤ rinv r c := by
  simp only [rinv]
  split_ifs <;> bound

@[bound] public lemma rinv_pos (r0 : 0 < r) : 0 < rinv r c := by
  simp only [rinv]
  split_ifs <;> aesop

public lemma lt_rinv : x < rinv r c ↔ x < r ∧ ‖c‖ * x < 1 := by
  simp only [rinv]
  split_ifs with c0
  · simp only [c0, norm_zero, zero_mul, zero_lt_one, and_true]
  · simp only [← one_div, lt_inf_iff, lt_div_iff₀ (norm_pos_iff.mpr c0), mul_comm]

public lemma le_rinv : x ≤ rinv r c ↔ x ≤ r ∧ ‖c‖ * x ≤ 1 := by
  simp only [rinv]
  split_ifs with c0
  · simp only [c0, norm_zero, zero_mul, zero_le_one, and_true]
  · simp only [← one_div, le_inf_iff, le_div_iff₀ (norm_pos_iff.mpr c0), mul_comm]

@[simp] public lemma inv_rinv (r0 : 0 < r) : (rinv r⁻¹ c)⁻¹ = max r ‖c‖ := by
  by_cases c0 : c = 0
  · simp [c0, rinv, r0.le]
  · simp only [rinv, c0, ↓reduceIte, min_def, inv_le_comm₀ r0 (inv_pos.mpr (norm_pos_iff.mpr c0)),
      inv_inv, max_def]
    grind

@[simp] public lemma div_rinv (r0 : 0 < r) : x / rinv r⁻¹ c = x * max r ‖c‖ := by
  simp only [div_eq_mul_inv, inv_rinv r0]

@[simp] public lemma mem_ball_rinv : z ∈ ball 0 (rinv r c) ↔ ‖z‖ < r ∧ ‖c‖ * ‖z‖ < 1 := by
  simp only [ball, dist_zero_right, lt_rinv, mem_setOf_eq]

@[simp] public lemma mem_closedBall_rinv :
    z ∈ closedBall 0 (rinv r c) ↔ ‖z‖ ≤ r ∧ ‖c‖ * ‖z‖ ≤ 1 := by
  simp only [closedBall, dist_zero_right, le_rinv, mem_setOf_eq]

@[simp] public lemma zero_mem_ball_rinv (r0 : 0 < r := by norm_num) :
    0 ∈ ball (0 : ℂ) (rinv r c) := by simp; bound

@[simp] public lemma zero_mem_closedBall_rinv (r0 : 0 ≤ r := by norm_num) :
    0 ∈ closedBall (0 : ℂ) (rinv r c) := by simp; bound

@[simp] public lemma inv_mem_closedBall_rinv (z4 : r ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (r0 : 0 < r := by norm_num) : z⁻¹ ∈ closedBall 0 (rinv r⁻¹ c) := by
  by_cases z0 : z = 0
  · simp [z0]
    bound
  · simp only [rinv, mem_closedBall, dist_zero_right, norm_inv]
    split_ifs with c0
    · bound
    · bound [norm_pos_iff.mpr c0]
