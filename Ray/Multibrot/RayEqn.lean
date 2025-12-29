module
public import Ray.Multibrot.Isomorphism
import Mathlib.Tactic.Cases
import Ray.Dynamics.Bottcher
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Ray
import Ray.Multibrot.Area
import Ray.Multibrot.Basic
import Ray.Multibrot.BottcherInv
import Ray.Multibrot.InvRay
import Ray.Multibrot.RayBound
import Ray.Multibrot.Rinv

/-!
## Functional equations for `ray` and `pray`
-/

open Asymptotics
open Metric (ball closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall mem_closedBall_self)
open RiemannSphere
open OneDimension
open Set
open scoped OnePoint Real RiemannSphere Topology
noncomputable section

variable {c x z : ℂ} {n : ℕ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `ray d` with the zero value cut out -/
@[expose] public def ray' (d : ℕ) [Fact (2 ≤ d)] (z : ℂ) : ℂ :=
  (ray d z).toComplex

@[simp] lemma coe_ray' (z0 : z ≠ 0) (z1 : z ∈ ball (0 : ℂ) 1) : (ray' d z : 𝕊) = ray d z := by
  rw [ray', coe_toComplex]
  simp only [ne_eq, ray_eq_inf z1, z0, not_false_eq_true]

lemma ray'_mem_ext (z0 : z ≠ 0) (z1 : z ∈ ball (0 : ℂ) 1) :
    (ray' d z, z ^ d ^ n) ∈ (superF d).ext := by
  set s := superF d
  set c := ray' d z
  have ce : c = ray d z := by simp only [c, coe_ray' z0 z1]
  have e : z = bottcher d c := by simp only [ce, bottcher_ray z1]
  apply s.pow_ext
  simp only [e, bottcher, fill_coe, bottcher']
  refine s.bottcher_ext (multibrotPost ?_)
  simp only [← multibrotExt_coe, ce]
  exact ray_mem_multibrotExt z1

/-- `ray'` in terms of `pray` -/
lemma ray'_eq_pray (m : z ∈ ball (0 : ℂ) 1) : ray' d z = pray d z / z := by
  by_cases z0 : z = 0
  · simp only [ray', z0, ray_zero, toComplex_inf, pray_zero, div_zero]
  · rw [ray', ray_eq_pray m, inv_coe, toComplex_coe, inv_div]
    simp only [ne_eq, div_eq_zero_iff, z0, pray_ne_zero m, or_self, not_false_eq_true]

/-- Conjugacy identity for the parameter external map `ray`. This is the key functional equation
relating the dynamical-space ray map `s.ray` to the parameter-space ray map `ray d`. -/
public lemma ray_conjugacy (z0 : z ≠ 0) (z1 : z ∈ ball (0 : ℂ) 1) :
    ray d z = (superF d).ray (ray' d z) z := by
  set s := superF d
  set c := ray' d z
  have ce : c = ray d z := by simp only [c, coe_ray' z0 z1]
  have e : z = bottcher d c := by simp only [ce, bottcher_ray z1]
  nth_rw 2 [e]
  rw [bottcher, fill_coe, bottcher', s.ray_bottcher, ce]
  apply multibrotPost
  simp only [← multibrotExt_coe, ce]
  exact ray_mem_multibrotExt z1

/-- The cascaded version of `pray d`, using higher powers for the second argument to `s.ray`. We'll
start with power s.t. `cascade d n z ≈ 1` and descend to `cascade d 0 z = pray d z`. -/
@[expose] public def cascade (d : ℕ) [Fact (2 ≤ d)] (n : ℕ) (z : ℂ) : ℂ :=
  if z = 0 then 1 else z ^ d ^ n * ((superF d).ray (ray' d z) (z ^ d ^ n)).toComplex

@[simp] public lemma cascade_z0 : cascade d n 0 = 1 := by
  simp only [cascade, ↓reduceIte]

/-- At the bottom of the cascade, we get `pray d` -/
public lemma cascade_zero (m : z ∈ ball (0 : ℂ) 1) : cascade d 0 z = pray d z := by
  by_cases z0 : z = 0
  · simp only [z0, cascade_z0, pray_zero]
  · simp only [cascade, z0, ↓reduceIte, pow_zero, pow_one, ← ray_conjugacy z0 m, ray_eq_pray m]
    rw [inv_coe, toComplex_coe]
    · field_simp [z0]
    · simp only [ne_eq, div_eq_zero_iff, z0, m, pray_ne_zero, or_self, not_false_eq_true]

/-- One step down the cascade -/
public lemma cascade_succ (m : z ∈ ball (0 : ℂ) 1) :
    cascade d (n + 1) z = cascade d n z ^ d + z ^ (d ^ (n + 1) - 1) * pray d z := by
  set s := superF d
  by_cases z0 : z = 0
  · simp [z0, cascade_z0, Nat.sub_eq_zero_iff_le, s.d1]
  · simp only [cascade, z0, if_false, pow_succ, pow_mul]
    have em : (ray' d z, z ^ d ^ n) ∈ s.ext := ray'_mem_ext z0 m
    rw [← s.ray_eqn em]
    unfold f
    rw [toComplex_lift', f', mul_add, mul_pow, add_right_inj, ray'_eq_pray m,
      div_eq_inv_mul, ← mul_assoc, pow_sub₀ _ z0 (by bound), pow_one, pow_mul]
    rw [ne_eq, s.ray_eq_a_iff em]
    simp only [pow_eq_zero_iff', z0, ne_eq, not_and, not_not, false_and, not_false_eq_true]

/-- The whole `cascade` is analytic -/
public lemma cascade_analytic (m : z ∈ ball (0 : ℂ) 1) : ContDiffAt ℂ ⊤ (cascade d n) z := by
  induction' n with n h
  · refine (pray_analytic (d := d) m).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.eventually_mem m] with w m
    simp only [cascade_zero m]
  · have e : cascade d (n + 1) =ᶠ[𝓝 z]
        fun z ↦ cascade d n z ^ d + z ^ (d ^ (n + 1) - 1) * pray d z := by
      filter_upwards [isOpen_ball.eventually_mem m] with w m
      simp only [cascade_succ m]
    refine ContDiffAt.congr_of_eventuallyEq ?_ e
    exact (h.pow _).add ((contDiffAt_id.pow _).mul (pray_analytic m))

/-- `cascade ≈ 1` for large `n` -/
public lemma cascade_approx : (fun z ↦ cascade d n z - 1) =O[𝓝 0] (fun z : ℂ ↦ z ^ d ^ n) := by
  by_cases n0 : n = 0
  · simpa only [n0, pow_zero, pow_one, cascade_z0, sub_zero] using
      ((cascade_analytic (d := d) (n := 0) (z := 0) (by simp)).differentiableAt
      (by decide)).isBigO_sub
  set s := superF d
  have cz := Asymptotics.isLittleO_iff.mp (hasDerivAt_iff_isLittleO_nhds_zero.mp
    ((inv_ray_analytic (d := d) (z := 0) (by simp)).differentiableAt (by decide)).hasDerivAt)
    (c := 2⁻¹) (by norm_num)
  simp only [inv_ray_zero, sub_zero, zero_add, deriv_inv_ray_zero, smul_eq_mul, mul_one] at cz
  simp only [cascade]
  refine Asymptotics.isBigO_iff.mpr ⟨4, ?_⟩
  filter_upwards [cz, eventually_norm_sub_lt 0 (ε := 32) (by norm_num),
    eventually_norm_sub_lt 0 (ε := 80⁻¹) (by bound)] with z cz lt_c z_lt
  by_cases z0 : z = 0
  · simp [z0]
  set c := ray' d z
  have hc : (ray d z).toComplex = c := rfl
  simp only [z0, ↓reduceIte, sub_zero, inv_ray, hc, toComplex_inv] at cz lt_c z_lt ⊢
  have cb := hc ▸ ray_le (d := d) (by linarith)
  have lt_zi : 80 < ‖z‖⁻¹ := by rwa [lt_inv_comm₀ (by norm_num) (norm_pos_iff.mpr z0)]
  have lt_c : 16 < ‖c‖ := by
    calc ‖c‖
      _ = ‖z⁻¹ + (c - z⁻¹)‖ := by ring_nf
      _ ≥ ‖z⁻¹‖ - ‖c - z⁻¹‖ := by bound
      _ > 80 - 64 := by rw [norm_inv]; bound
      _ = 16 := by norm_num
  have le_ci : ‖z‖ ≤ 2 * ‖c‖⁻¹ := by
    calc 2 * ‖c‖⁻¹
      _ = 2 * ‖z + (c⁻¹ - z)‖ := by rw [← norm_inv c]; ring_nf
      _ ≥ 2 * (‖z‖ - ‖c⁻¹ - z‖) := by bound
      _ ≥ 2 * (‖z‖ - 2⁻¹ * ‖z‖) := by bound
      _ = ‖z‖ := by ring
  have small : ‖z ^ d ^ n‖ < rinv 4⁻¹ c / 4 := by
    rw [lt_div_iff₀ (by norm_num), lt_rinv]
    have le_p : 2 ≤ d ^ n := by
      calc d ^ n
        _ ≥ 2 ^ n := by bound
        _ ≥ 2 := Nat.le_self_pow n0 2
    constructor
    · calc ‖z ^ d ^ n‖ * 4
        _ = ‖z‖ ^ d ^ n * 4 := by simp only [norm_pow]
        _ ≤ ‖z‖ ^ 2 * 4 := by bound
        _ ≤ 80⁻¹ ^ 2 * 4 := by bound
        _ < 4⁻¹ := by norm_num
    · calc ‖c‖ * (‖z ^ d ^ n‖ * 4)
        _ = ‖c‖ * (‖z‖ * ‖z‖ * ‖z‖ ^ (d ^ n - 2) * 4) := by
            rw [← pow_two, ← pow_add, Nat.add_sub_cancel' le_p, norm_pow]
        _ ≤ ‖c‖ * (2 * ‖c‖⁻¹ * 80⁻¹ * 1 * 4) := by bound
        _ = 10⁻¹ * (‖c‖ * ‖c‖⁻¹) := by ring_nf
        _ = 10⁻¹ := by rw [mul_inv_cancel₀ (by positivity), mul_one]
        _ < 1 := by norm_num
  generalize hw : z ^ d ^ n = w at small
  have w0 : w ≠ 0 := by simp [← hw, n0, z0]
  calc ‖w * (s.ray c w).toComplex - 1‖
    _ = ‖(s.ray c w).toComplex - w⁻¹‖ * ‖w‖ := by
        rw [← norm_mul, sub_mul, inv_mul_cancel₀ w0, mul_comm w]
    _ ≤ 4 * ‖w‖ := by bound [sray_le (d := d) small]
