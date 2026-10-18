module
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Ray.Misc.Bound

/-!
## Real facts
-/

open Real (cosh sinh tanh)
open scoped Real
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {x y : ℝ}

lemma Real.analyticAt_tanh : AnalyticAt ℝ tanh x := by
  rw [analyticAt_congr (.of_forall Real.tanh_eq_sinh_div_cosh)]
  exact Real.analyticAt_sinh.div Real.analyticAt_cosh (Real.cosh_pos _).ne'

@[fun_prop] lemma Real.continuous_tanh : Continuous tanh := by
  rw [continuous_iff_continuousAt]
  intro
  exact Real.analyticAt_tanh.continuousAt

@[fun_prop] lemma Continuous.tanh {f : X → ℝ} (fc : Continuous f) :
    Continuous (fun x ↦ tanh (f x)) := by
  fun_prop

lemma Real.hasDerivAt_tanh {x : ℝ} : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have e : tanh = fun x ↦ sinh x / cosh x := by ext; rw [Real.tanh_eq_sinh_div_cosh]
  rw [e, ← Real.cosh_sq_sub_sinh_sq x]
  nth_rw 1 [pow_two]
  nth_rw 1 [pow_two]
  exact (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'

@[simp] lemma Real.deriv_tanh : deriv tanh x = 1 / cosh x ^ 2 := hasDerivAt_tanh.deriv

lemma Real.strictMono_tanh : StrictMono tanh := by
  apply strictMono_of_deriv_pos
  simp only [deriv_tanh, one_div, inv_pos]
  bound

@[simp] lemma Real.tanh_eq_tanh (x : ℝ) : tanh x = tanh y ↔ x = y :=
  Real.tanh_injective.eq_iff
