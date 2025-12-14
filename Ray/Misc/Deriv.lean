module
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
## Derivative facts
-/

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {𝕝 : Type} [NontriviallyNormedField 𝕝]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

public lemma HasFDerivAt.comp_of_eq {f : E → F} {f' : E →L[𝕜] F} (x : E) {g : F → G}
    {g' : F →L[𝕜] G} {y : F} (hg : HasFDerivAt g g' y) (hf : HasFDerivAt f f' x) (e : f x = y) :
    HasFDerivAt (g ∘ f) (g'.comp f') x := by
  rw [← e] at hg
  exact hg.comp x hf

/-- A composed derivative is zero if the right derivative is zero -/
public lemma hasFDeriv_zero_of_comp_right {f : F → G} {g : E → F} {y : F} {x : E}
    (df : DifferentiableAt 𝕜 f y) (dg : HasFDerivAt g (0 : E →L[𝕜] F) x) (e : g x = y) :
    HasFDerivAt (fun x ↦ f (g x)) (0 : E →L[𝕜] G) x := by
  convert df.hasFDerivAt.comp_of_eq _ dg e
  simp only [ContinuousLinearMap.comp_zero]

/-- Version of `HasDerivAt.inv` that works nicely over field towers -/
public theorem HasDerivAt.inv_tower [NormedAlgebra 𝕜 𝕝] {x : 𝕜} {c : 𝕜 → 𝕝} {c' : 𝕝}
    (dc : HasDerivAt c c' x) (c0 : c x ≠ 0) : HasDerivAt c⁻¹ (-c' / c x ^ 2) x := by
  have di := (hasFDerivAt_inv c0).restrictScalars 𝕜
  have d := (di.comp x dc.hasFDerivAt).hasDerivAt
  simpa [Function.comp_def, ← neg_div, ← div_eq_mul_inv] using d
