module
import Mathlib.Topology.Algebra.Module.LinearMap

/-!
## Continuous linear map facts
-/

@[simp] lemma ContinuousLinearMap.smulRight_zero {M₁ : Type} [TopologicalSpace M₁]
    [AddCommMonoid M₁] {M₂ : Type} [TopologicalSpace M₂] [AddCommMonoid M₂] {R : Type} {S : Type}
    [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S] [Module S M₂]
    [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂] (c : M₁ →L[R] S)
    : (c.smulRight (0 : M₂) : M₁ →L[R] M₂) = 0 := by
  ext
  simp only [ContinuousLinearMap.smulRight_apply, smul_zero, ContinuousLinearMap.zero_apply]
