import Ray.Dynamics.Multibrot.Isomorphism

/-!
## `inv_ray`: The external ray map as an analytic function
-/

open Function (uncurry)
open Metric (ball isOpen_ball)
open RiemannSphere
open OneDimension
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]
variable {c z : ℂ}

/-!
### Parameter space `inv_ray`
-/

/-- `ray` as an analytic `ℂ → ℂ` function -/
def inv_ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ :=
  fun z ↦ (ray d z)⁻¹.toComplex

@[simp] lemma inv_ray_zero : inv_ray d 0 = 0 := by
  simp only [inv_ray, ray_zero, RiemannSphere.inv_inf, toComplex_zero]

@[simp] lemma inv_ray_ne_zero (z0 : z ≠ 0) (m : z ∈ ball (0 : ℂ) 1) : inv_ray d z ≠ 0 := by
  simp only [inv_ray, ne_eq, toComplex_eq_zero, RiemannSphere.inv_eq_zero, inv_eq_inf,
    ray_ne_zero m, or_false]
  rw [← ray_zero (d := d)]
  exact ray_inj.ne m (by simp) z0

/-- `ray_inv d` is analytic on `ball 0 1` -/
lemma inv_ray_analytic (m : z ∈ ball (0 : ℂ) 1) : ContDiffAt ℂ ⊤ (inv_ray d) z := by
  refine ContDiffAt.contDiffWithinAt (ContMDiffAt.contDiffAt ?_)
  refine ((mAnalyticAt_toComplex' ?_).comp _ (mAnalytic_inv _)).comp _ (rayMAnalytic d z m)
  simp [m]

lemma bottcher_inv_inv_ray (m : z ∈ ball (0 : ℂ) 1) : bottcher_inv d (inv_ray d z) = z := by
  simp only [bottcher_inv, inv_ray]
  rw [RiemannSphere.coe_toComplex (by simp [ray_ne_zero m]), inv_inv, bottcher_ray m]

/-- `ray` is monic at `0 ↦ ∞` -/
lemma ray_hasDerivAt_one : HasDerivAt (inv_ray d) 1 0 := by
  have m : 0 ∈ ball (0 : ℂ) 1 := by simp
  have dr : DifferentiableAt ℂ (inv_ray d) 0 := (inv_ray_analytic m).differentiableAt le_top
  have dc : HasDerivAt (fun z ↦ bottcher_inv d (inv_ray d z)) 1 0 := by
    apply (hasDerivAt_id _).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.eventually_mem m] with z m
    simp only [bottcher_inv_inv_ray m, id]
  have c := deriv_comp_of_eq (h₂ := bottcher_inv d) (h := inv_ray d) 0
    bottcher_hasDerivAt_one.differentiableAt dr (by simp)
  simp only [Function.comp_def, dc.deriv, bottcher_hasDerivAt_one.deriv, one_mul, inv_ray_zero] at c
  exact c ▸ dr.hasDerivAt

/-!
### Dynamical space `s.inv_ray` and `s.bottcher_inv`
-/

/-- `s.inv_ray` as an analytic `ℂ → ℂ` function -/
def sinv_ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ → ℂ :=
  fun c z ↦ ((superF d).ray c z)⁻¹.toComplex
