module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Ray.Dynamics.Bottcher
public import Ray.Manifold.RiemannSphere
public import Ray.Multibrot.D
import Mathlib.Analysis.Calculus.Deriv.Pow
import Ray.Analytic.Analytic
import Ray.Misc.Bound
import Ray.Misc.Cobounded

/-!
## Multibrot definitions, allowing minimal public imports
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Function (uncurry)
open OneDimension
open RiemannSphere
open Set
open scoped ContDiff OnePoint RiemannSphere Topology

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]
variable {c : ℂ}

/-!
## The defining iteration, the Multibrot set, and its complement
-/

/-- The Multibrot iteration, `ℂ → ℂ` version -/
@[expose] public def f' (d : ℕ) (c z : ℂ) : ℂ :=
  z ^ d + c

/-- The Multibrot iteration, `𝕊 → 𝕊` version -/
@[expose] public def f (d : ℕ) : ℂ → 𝕊 → 𝕊 :=
  lift' (f' d) ∞

/-- The Multibrot set is those points that do not escape to `∞` -/
@[expose] public def multibrot (d : ℕ) : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ (f d c)^[n] ↑c) atTop (𝓝 ∞)}

/-- The complement of the Multibrot set, including `∞` -/
@[expose] public def multibrotExt (d : ℕ) : Set 𝕊 :=
  ((fun z : ℂ ↦ (z : 𝕊)) '' multibrot d)ᶜ ∪ {(∞ : 𝕊)}

/-!
## Basic properties of the iteration `f`

In particular, we show that `f d` has a superattracting fixpoint at `∞`.
-/

-- Basic properties of f
@[simp] public lemma f_0' (d : ℕ) [Fact (2 ≤ d)] : f' d c 0 = c := by
  simp only [f', zero_pow (d_ne_zero _), zero_add]

@[simp] public lemma f_0 (d : ℕ) [Fact (2 ≤ d)] : f d c 0 = c := by
  simp only [f, ← coe_zero, lift_coe', f', zero_pow (d_ne_zero _), zero_add]

public theorem analytic_f' {d : ℕ} : AnalyticOnNhd ℂ (uncurry (f' d)) univ := fun _ _ ↦
  (analyticAt_snd.pow _).add analyticAt_fst

theorem tendsto_f'_cobounded (c : ℂ) :
    Tendsto (uncurry (f' d)) (𝓝 c ×ˢ cobounded ℂ) (cobounded ℂ) := by
  simp only [hasBasis_cobounded_norm_lt.tendsto_right_iff, Set.mem_setOf_eq,
    forall_true_left, uncurry, Metric.eventually_nhds_prod_iff]
  intro r; use 1, zero_lt_one, fun z ↦ max r 0 + ‖c‖ + 1 < ‖z‖; constructor
  · refine (eventually_cobounded (max r 0 + ‖c‖ + 1)).mp (.of_forall fun w h ↦ ?_)
    exact h
  · intro e ec z h
    simp only [Complex.dist_eq] at ec
    have zz : ‖z‖ ≤ ‖z ^ d‖ := by
      rw [norm_pow]
      refine le_self_pow₀ ?_ (d_ne_zero _)
      exact le_trans (le_add_of_nonneg_left (add_nonneg (le_max_right _ _) (norm_nonneg _))) h.le
    calc ‖f' d e z‖
      _ = ‖z ^ d + e‖ := rfl
      _ = ‖z ^ d + (c + (e - c))‖ := by ring_nf
      _ ≥ ‖z ^ d‖ - ‖c + (e - c)‖ := by bound
      _ ≥ ‖z ^ d‖ - (‖c‖ + ‖e - c‖) := by bound
      _ ≥ ‖z‖ - (‖c‖ + 1) := by bound
      _ > max r 0 + ‖c‖ + 1 - (‖c‖ + 1) := by bound
      _ = max r 0 := by ring_nf
      _ ≥ r := le_max_left _ _

public theorem mAnalyticAt_f : ContMDiff II I ω (uncurry (f d)) :=
  mAnalytic_lift' analytic_f' tendsto_f'_cobounded

public theorem writtenInExtChartAt_coe_f {d : ℕ} {z : ℂ} :
    writtenInExtChartAt I I (z : 𝕊) (f d c) = f' d c := by
  simp only [writtenInExtChartAt, f, Function.comp_def, lift_coe', RiemannSphere.extChartAt_coe,
    PartialEquiv.symm_symm, coePartialEquiv_apply, coePartialEquiv_symm_apply, toComplex_coe]

public lemma fl_f : fl (f d) ∞ = fun c z : ℂ ↦ z^d / (1 + c * z^d) := by
  funext c z
  simp only [fl, RiemannSphere.extChartAt_inf, Function.comp_def, invEquiv_apply,
    PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, PartialEquiv.coe_trans_symm,
    coePartialEquiv_symm_apply, PartialEquiv.symm_symm, coePartialEquiv_apply,
    Equiv.toPartialEquiv_symm_apply, invEquiv_symm, RiemannSphere.inv_inf, toComplex_zero,
    add_zero, sub_zero]
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', f, lift_inf', RiemannSphere.inv_inf, toComplex_zero,
      zero_pow (d_ne_zero _), zero_div]
  simp only [f, f', inv_coe z0, lift_coe', inv_pow]
  have zd := pow_ne_zero d z0
  by_cases h : (z ^ d)⁻¹ + c = 0
  · simp only [h, coe_zero, inv_zero', toComplex_inf]
    simp only [← add_eq_zero_iff_neg_eq.mp h, neg_mul, inv_mul_cancel₀ zd, ← sub_eq_add_neg,
      sub_self, div_zero]
  rw [inv_coe h, toComplex_coe, eq_div_iff, inv_mul_eq_iff_eq_mul₀ h, right_distrib,
    inv_mul_cancel₀ zd]
  contrapose h
  rw [add_comm, add_eq_zero_iff_eq_neg, ← eq_div_iff zd, neg_div, ←
    inv_eq_one_div, ← add_eq_zero_iff_eq_neg, add_comm] at h
  exact h

/-- `f` near `∞` with the `z^d` factor removed -/
@[expose] public noncomputable def gl (d : ℕ) (c z : ℂ) :=
  (1 + c * z ^ d)⁻¹

public theorem gl_f {z : ℂ} : g (fl (f d) ∞ c) d z = gl d c z := by
  simp only [fl_f, gl, g]
  by_cases z0 : z = 0
  simp only [if_pos, z0, zero_pow (d_ne_zero _), MulZeroClass.mul_zero, add_zero, inv_one]
  rw [if_neg z0, div_eq_mul_inv _ (_ + _), mul_comm, mul_div_assoc, div_self (pow_ne_zero _ z0),
    mul_one]

theorem analyticAt_gl : AnalyticAt ℂ (gl d c) 0 := by
  apply (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow _))).inv
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow (d_ne_zero _), mul_zero,
    add_zero, ne_eq, one_ne_zero, not_false_eq_true]

theorem fl_f' : fl (f d) ∞ = fun c z : ℂ ↦ (z - 0) ^ d • gl d c z := by
  funext c z; simp only [fl_f, gl, sub_zero, smul_eq_mul, div_eq_mul_inv]

theorem gl_zero : gl d c 0 = 1 := by
  simp only [gl, zero_pow (d_ne_zero _), MulZeroClass.mul_zero]; norm_num

theorem gl_frequently_ne_zero : ∃ᶠ z in 𝓝 0, gl d c z ≠ 0 := by
  refine (analyticAt_gl.continuousAt.eventually_ne ?_).frequently; simp only [gl_zero]
  exact one_ne_zero

public lemma fc_f : leadingCoeff (fl (f d) ∞ c) 0 = 1 := by
  rw [fl_f', analyticAt_gl.monomial_mul_leadingCoeff gl_frequently_ne_zero, leadingCoeff_of_ne_zero]
  exact gl_zero; rw [gl_zero]; exact one_ne_zero

public lemma fd_f : orderAt (fl (f d) ∞ c) 0 = d := by
  rw [fl_f', analyticAt_gl.monomial_mul_orderAt gl_frequently_ne_zero, orderAt_eq_zero, add_zero]
  rw [gl_zero]; exact one_ne_zero

theorem f_inf {d : ℕ} : f d c ∞ = (∞ : 𝕊) := by
  simp only [f, lift_inf']

-- f has a superattracting fixpoint at ∞
public theorem superF (d : ℕ) [Fact (2 ≤ d)] : Super (f d) d ∞ :=
  { d2 := two_le_d d
    fa := mAnalyticAt_f
    fc := fun _ ↦ fc_f
    fd := fun _ ↦ fd_f
    f0 := fun _ ↦ f_inf }

/-- `f` has one preimage of `∞` -/
public instance onePreimageF : OnePreimage (superF d) where
  eq_a := by
    intro c z; induction z using OnePoint.rec
    · simp only [imp_true_iff]
    · simp only [f, lift_coe', OnePoint.coe_ne_infty, IsEmpty.forall_iff]

/-!
## Bottcher coordinates!
-/

/-- The Böttcher map for the Multibrot set is the diagonal of the dynamical map (`ℂ → ℂ` version) -/
@[expose] public noncomputable def bottcher' (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) : ℂ :=
  (superF d).bottcher c c

/-- The Böttcher map for the Multibrot set is the diagonal of the dynamical map (`𝕊 → ℂ` version) -/
@[expose] public noncomputable def bottcher (d : ℕ) [Fact (2 ≤ d)] : 𝕊 → ℂ :=
  fill (bottcher' d) 0

/-- `bottcher` near `∞` as an analytic `ℂ → ℂ` function -/
public noncomputable def bottcher_inv (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ :=
  fun z ↦ bottcher d (↑z)⁻¹

/-- `s.bottcher_inv` as an analytic `ℂ → ℂ → ℂ` function -/
public noncomputable def sbottcher_inv (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ → ℂ :=
  fun c z ↦ (superF d).bottcher c (z : 𝕊)⁻¹

public lemma bottcher_inv_def : bottcher_inv d = fun z : ℂ ↦ bottcher d (↑z)⁻¹ := by rfl
public lemma sbottcher_inv_def :
    sbottcher_inv d = fun c z : ℂ ↦ (superF d).bottcher c (z : 𝕊)⁻¹ := by rfl

/-- `s.inv_ray` as an analytic `ℂ → ℂ` function -/
@[expose] public noncomputable def sinv_ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ → ℂ :=
  fun c z ↦ ((superF d).ray c z)⁻¹.toComplex


/-!
## Error bound functions for iterates and potentials
-/

/-- Weird bound that we use below to be reasonably tight -/
@[expose] public noncomputable def f_error (d : ℕ) (z : ℂ) :=
  -Real.log (1 - -Real.log (1 - 1/‖z‖) / (d * Real.log (‖z‖)))

/-- The infinite sum of `f_error` -/
@[expose] public noncomputable def iter_error (d : ℕ) (c z : ℂ) :=
  ∑' n, f_error d ((f' d c)^[n] z)

/-- We will use this function below to produce bounds on `s.potential` approximates -/
@[expose] public noncomputable def ene (x : ℝ) : ℝ := Real.exp (-Real.exp x)

/-- The (negated) derivative of `ene` -/
@[expose] public noncomputable def dene (x : ℝ) : ℝ := Real.exp (x - Real.exp x)

/-- Error term in the `potential` approximate -/
@[expose] public noncomputable def potential_error (d : ℕ) (c z : ℂ) : ℝ :=
  dene (Real.log (Real.log ‖z‖) - iter_error d c z) * iter_error d c z

/-!
## Balls whose size depends on an inverse

These work correctly if the inverse would be infinite.
-/

/-- `min r ‖c‖⁻¹`, but do the right thing if `c = 0` -/
@[expose] public noncomputable def rinv (r : ℝ) (c : ℂ) : ℝ :=
  if c = 0 then r else min r ‖c‖⁻¹
