module
public import Ray.Multibrot.Isomorphism
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Ray.Manifold.Analytic
import Ray.Multibrot.Bottcher
import Ray.Multibrot.BottcherInv
import Ray.Multibrot.Isomorphism
import Ray.Multibrot.KoebeInf

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
variable {c x z : ℂ}

/-!
### Parameter space `inv_ray`
-/

@[simp] public lemma inv_ray_zero : inv_ray d 0 = 0 := by
  simp only [inv_ray, ray_zero, RiemannSphere.inv_inf, toComplex_zero]

@[simp] public lemma inv_ray_ne_zero (z0 : z ≠ 0) (m : z ∈ ball (0 : ℂ) 1) : inv_ray d z ≠ 0 := by
  simp only [inv_ray, ne_eq, toComplex_eq_zero, RiemannSphere.inv_eq_zero, inv_eq_inf,
    ray_ne_zero m, or_false]
  rw [← ray_zero (d := d)]
  exact ray_inj.ne m (by simp) z0

/-- `ray_inv d` is analytic on `ball 0 1` -/
public lemma inv_ray_analytic (m : z ∈ ball (0 : ℂ) 1) : ContDiffAt ℂ ⊤ (inv_ray d) z := by
  refine ContDiffAt.contDiffWithinAt (ContMDiffAt.contDiffAt ?_)
  refine ((mAnalyticAt_toComplex' ?_).comp _ (mAnalytic_inv _)).comp _ (rayMAnalytic d z m)
  simp [m]

public lemma bottcher_inv_inv_ray (m : z ∈ ball (0 : ℂ) 1) : bottcher_inv d (inv_ray d z) = z := by
  simp only [bottcher_inv_def, inv_ray]
  rw [RiemannSphere.coe_toComplex (by simp [ray_ne_zero m]), inv_inv, bottcher_ray m]

/-- `ray` is monic at `0 ↦ ∞` -/
public lemma ray_hasDerivAt_one : HasDerivAt (inv_ray d) 1 0 := by
  have m : 0 ∈ ball (0 : ℂ) 1 := by simp
  have dr : DifferentiableAt ℂ (inv_ray d) 0 := (inv_ray_analytic m).differentiableAt (by decide)
  have dc : HasDerivAt (fun z ↦ bottcher_inv d (inv_ray d z)) 1 0 := by
    apply (hasDerivAt_id _).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.eventually_mem m] with z m
    simp only [bottcher_inv_inv_ray m, id]
  have c := deriv_comp_of_eq (h₂ := bottcher_inv d) (h := inv_ray d) 0
    bottcher_hasDerivAt_one.differentiableAt dr (by simp)
  simp only [Function.comp_def, dc.deriv, bottcher_hasDerivAt_one.deriv, one_mul, inv_ray_zero] at c
  exact c ▸ dr.hasDerivAt

@[simp] public lemma deriv_inv_ray_zero : deriv (inv_ray d) 0 = 1 := ray_hasDerivAt_one.deriv

/-!
### Dynamical space `s.inv_ray`
-/

/-- `sinv_ray` is analytic for large `c`, small `x` -/
public lemma sinv_ray_analytic (xc : ‖x‖ < rinv 4⁻¹ c / 4) :
    AnalyticAt ℂ (uncurry (sinv_ray d)) (c, x) := by
  set s := superF d
  obtain ⟨z,_,zm,zp,zx⟩ := sbottcher_inv_small_mem_preimage (d := d) xc
  have xe := small_mem_ext (d := d) xc
  refine ContMDiffAt.analyticAt (I := II) (J := I) ?_
  have e : uncurry (sinv_ray d) = (fun z : 𝕊 ↦ z⁻¹.toComplex) ∘ uncurry (superF d).ray := rfl
  rw [e]
  refine ContMDiffAt.comp _ ?_ (s.ray_mAnalytic xe)
  apply ContMDiffAt.comp _ ?_ (mAnalytic_inv _)
  apply mAnalyticAt_toComplex'
  simp [← zx, sbottcher_inv_def, s.ray_bottcher zp]
