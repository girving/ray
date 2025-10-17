import Ray.Dynamics.Multibrot.Area

/-!
## Functional equations for `ray` and `pray`
-/

open MeasureTheory (volume)
open Metric (ball closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall mem_closedBall_self)
open RiemannSphere
open OneDimension
open Set
open scoped OnePoint Real RiemannSphere Topology
noncomputable section

variable {z : ℂ} {n : ℕ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `ray d` with the zero value cut out -/
def ray' (d : ℕ) [Fact (2 ≤ d)] (z : ℂ) : ℂ :=
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
  exact (bottcherHomeomorph d).map_target z1

/-- `ray'` in terms of `pray` -/
lemma ray'_eq_pray (m : z ∈ ball (0 : ℂ) 1) : ray' d z = pray d z / z := by
  by_cases z0 : z = 0
  · simp only [ray', z0, ray_zero, toComplex_inf, pray_zero, div_zero]
  · rw [ray', ray_eq_pray m, inv_coe, toComplex_coe, inv_div]
    simp only [ne_eq, div_eq_zero_iff, z0, pray_ne_zero m, or_self, not_false_eq_true]

/-- Conjugacy identity for the parameter external map `ray`. This is the key functional equation
relating the dynamical-space ray map `s.ray` to the parameter-space ray map `ray d`. -/
lemma ray_conjugacy (z0 : z ≠ 0) (z1 : z ∈ ball (0 : ℂ) 1) :
    ray d z = (superF d).ray (ray' d z) z := by
  set s := superF d
  set c := ray' d z
  have ce : c = ray d z := by simp only [c, coe_ray' z0 z1]
  have e : z = bottcher d c := by simp only [ce, bottcher_ray z1]
  nth_rw 2 [e]
  rw [bottcher, fill_coe, bottcher', s.ray_bottcher, ce]
  apply multibrotPost
  simp only [← multibrotExt_coe, ce]
  exact (bottcherHomeomorph d).map_target z1

/-- The cascaded version of `pray d`, using higher powers for the second argument to `s.ray`. We'll
start with power s.t. `cascade d n z ≈ 1` and descend to `cascade d 0 z = pray d z`. -/
def cascade (d : ℕ) [Fact (2 ≤ d)] (n : ℕ) (z : ℂ) : ℂ :=
  if z = 0 then 1 else z ^ d ^ n * ((superF d).ray (ray' d z) (z ^ d ^ n)).toComplex

@[simp] lemma cascade_z0 : cascade d n 0 = 1 := by
  simp only [cascade, ↓reduceIte]

/-- At the bottom of the cascade, we get `pray d` -/
lemma cascade_zero (m : z ∈ ball (0 : ℂ) 1) : cascade d 0 z = pray d z := by
  by_cases z0 : z = 0
  · simp only [z0, cascade_z0, pray_zero]
  · simp only [cascade, z0, ↓reduceIte, pow_zero, pow_one, ← ray_conjugacy z0 m, ray_eq_pray m]
    rw [inv_coe, toComplex_coe]
    · field_simp [z0]
    · simp only [ne_eq, div_eq_zero_iff, z0, m, pray_ne_zero, or_self, not_false_eq_true]

/-- One step down the cascade -/
lemma cascade_succ (m : z ∈ ball (0 : ℂ) 1) :
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
