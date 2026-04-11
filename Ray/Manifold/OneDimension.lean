module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Ray.Manifold.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.LocalInvariantProperties
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Tactic.Cases
import Ray.Analytic.Analytic
import Ray.Hartogs.Osgood
import Ray.Manifold.Analytic
import Ray.Manifold.Manifold
import Ray.Misc.Multilinear

/-!
## Special properties of 1D complex manifolds

One complex dimension is special, and 1D complex manifolds inherit this specialness.

Unfortunately, a lot of proofs here are messy, as we abuse the definitional quality
of `TangentSpace I z = ℂ` to do noncanonical field arithmetic over `ℂ`.
-/

open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Manifold Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [cs : ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ct : ChartedSpace ℂ T]
variable {U : Type} [TopologicalSpace U] [cu : ChartedSpace ℂ U]

/-- 1D tangent spaces are nontrivial -/
instance one_dimension_tangentSpace_nontrivial (z : S) : Nontrivial (TangentSpace I z) := by
  simp only [TangentSpace]; infer_instance

/-- 1D tangent spaces are `NormedAddCommGroup`s -/
instance oneDimensionTangentSpaceNormedAddCommGroup (z : S) :
    NormedAddCommGroup (TangentSpace I z) := by
  simp only [TangentSpace]; infer_instance

/-- 1D tangent spaces are `NormedSpace`s -/
instance oneDimensionTangentSpaceNormedSpace (z : S) : NormedSpace ℂ (TangentSpace I z) := by
  simpa [TangentSpace] using (inferInstance : NormedSpace ℂ ℂ)

/-- The tangent space norm is `abs`, if we unpack types -/
theorem tangentSpace_norm_eq_complex_norm (z : S) (x : TangentSpace I z) :
    ‖x‖ = Complex.instNorm.norm x := rfl

/-- 1D tangent space maps are (noncanonically!) equivalent to `ℂ` (linear equivalence) -/
def mderivToScalar' (z : S) (w : T) : (TangentSpace I z →L[ℂ] TangentSpace I w) ≃ₗ[ℂ] ℂ := by
  exact ContinuousLinearMap.toSpanSingletonCLE.symm.toLinearEquiv

/-- 1D tangent space maps are (noncanonically!) equivalent to `ℂ` (continuous linear equivalence) -/
def mderivToScalar (z : S) (w : T) : (TangentSpace I z →L[ℂ] TangentSpace I w) ≃L[ℂ] ℂ := by
  exact ContinuousLinearMap.toSpanSingletonCLE.symm

private theorem clm_apply_eq_mul (f : ℂ →L[ℂ] ℂ) (u : ℂ) : f u = f 1 * u := by
  simpa [smul_eq_mul, mul_comm] using f.map_smul u (1 : ℂ)

private theorem clm_eq_zero_iff_one_eq_zero (f : ℂ →L[ℂ] ℂ) : f = 0 ↔ f 1 = 0 := by
  constructor
  · intro h; simp [h]
  · intro h
    apply ContinuousLinearMap.ext
    intro u
    rw [clm_apply_eq_mul, h, zero_mul, ContinuousLinearMap.zero_apply]

/-- Given nonzero `u`, a tangent space map `x` is `0` iff `x u = 0` -/
theorem mderiv_eq_zero_iff {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (u : TangentSpace I z) : f u = 0 ↔ f = 0 ∨ u = 0 := by
  let f' : ℂ →L[ℂ] ℂ := f
  constructor
  · rw [or_iff_not_imp_right]; intro f0 u0
    have h : f' u = 0 := by simpa [TangentSpace, f'] using f0
    rw [clm_apply_eq_mul] at h
    simpa [TangentSpace, f'] using
      (clm_eq_zero_iff_one_eq_zero f').2 ((mul_eq_zero.mp h).resolve_right u0)
  · rintro (rfl | rfl) <;> simp

/-- Given nonzero `u`, a tangent space map `x` is `0` iff `x u = 0` -/
theorem mderiv_eq_zero_iff' {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    {u : TangentSpace I z} (u0 : u ≠ 0) : f u = 0 ↔ f = 0 := by
  simp only [mderiv_eq_zero_iff, u0, or_false]

/-- Given nonzero `u`, a tangent space map `x` is `≠ 0` iff `x u ≠ 0` -/
theorem mderiv_ne_zero_iff {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (u : TangentSpace I z) : f u ≠ 0 ↔ f ≠ 0 ∧ u ≠ 0 := by
  simp only [← not_or]; exact Iff.not (mderiv_eq_zero_iff _ _)

/-- Given nonzero `u`, a tangent space map `x` is `≠ 0` iff `x u ≠ 0` -/
theorem mderiv_ne_zero_iff' {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    {u : TangentSpace I z} (u0 : u ≠ 0) : f u ≠ 0 ↔ f ≠ 0 := by
  simp only [ne_eq, mderiv_ne_zero_iff, u0, not_false_eq_true, and_true]

/-- 1D map composition is zero iff either side is -/
public theorem mderiv_comp_eq_zero_iff {x : S} {y : T} {z : U}
    (f : TangentSpace I y →L[ℂ] TangentSpace I z) (g : TangentSpace I x →L[ℂ] TangentSpace I y) :
    f.comp g = 0 ↔ f = 0 ∨ g = 0 := by
  rcases exists_ne (0 : TangentSpace I x) with ⟨t, t0⟩
  constructor
  · intro h; simp only [← mderiv_eq_zero_iff' t0, ContinuousLinearMap.comp_apply] at h
    by_cases g0 : g t = 0
    right; rw [mderiv_eq_zero_iff' t0] at g0; exact g0
    left; rwa [← mderiv_eq_zero_iff' g0]
  · intro h; cases' h with h h; simp only [h, g.zero_comp]; simp only [h, f.comp_zero]

/-- 1D map composition is nonzero if both sides are -/
public theorem mderiv_comp_ne_zero {x : S} {y : T} {z : U}
    (f : TangentSpace I y →L[ℂ] TangentSpace I z) (g : TangentSpace I x →L[ℂ] TangentSpace I y) :
    f ≠ 0 → g ≠ 0 → f.comp g ≠ 0 := by
  intro f0 g0; simp only [Ne, mderiv_comp_eq_zero_iff, f0, g0, or_self_iff, not_false_iff]

/-- Nonzero `mfderiv` implies differentiability -/
theorem has_mfderiv_at_of_mderiv_ne_zero {f : S → T} {x : S} (d0 : mfderiv I I f x ≠ 0) :
    MDifferentiableAt I I f x := by
  contrapose d0
  simp only [mfderiv, d0, if_false]

/-- If two functions have nonzero derivative, their composition has nonzero derivative -/
public theorem mderiv_comp_ne_zero' {f : T → U} {g : S → T} {x : S} :
    mfderiv I I f (g x) ≠ 0 → mfderiv I I g x ≠ 0 → mfderiv I I (fun x ↦ f (g x)) x ≠ 0 := by
  intro df dg
  have e : (fun x ↦ f (g x)) = f ∘ g := rfl
  rw [e, mfderiv_comp x (has_mfderiv_at_of_mderiv_ne_zero df) (has_mfderiv_at_of_mderiv_ne_zero dg)]
  exact mderiv_comp_ne_zero _ _ df dg

/-- Nonzero 1D derivatives are invertible -/
@[expose] public def mderivEquiv {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (f0 : f ≠ 0) : TangentSpace I z ≃L[ℂ] TangentSpace I w := by
  change ℂ ≃L[ℂ] ℂ
  let f' : ℂ →L[ℂ] ℂ := f; have hmul : ∀ x : ℂ, f' x = f' 1 * x := by
    intro x; simpa [smul_eq_mul, mul_comm] using f'.map_smul x (1 : ℂ)
  have h1 : f' 1 ≠ 0 := by
    intro h
    apply f0
    apply ContinuousLinearMap.ext
    intro x
    change f' x = (0 : ℂ →L[ℂ] ℂ) x
    rw [hmul, h, zero_mul, ContinuousLinearMap.zero_apply]
  refine
    { toFun := f'
      map_add' := f'.map_add'
      map_smul' := f'.map_smul'
      invFun := fun x ↦ (f' 1)⁻¹ * x
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := f'.cont
      continuous_invFun := Continuous.mul continuous_const continuous_id }
  · intro x; rw [show f' x = f' 1 * x from hmul x]; simp [h1]
  · intro x; rw [show f' ((f' 1)⁻¹ * x) = f' 1 * ((f' 1)⁻¹ * x) from hmul _]; simp [h1]

public theorem mderivEquiv_apply {z : S} {w : T} {f : TangentSpace I z →L[ℂ] TangentSpace I w}
    (f0 : f ≠ 0) (x : TangentSpace I z) : mderivEquiv f f0 x = f x := by rfl

public theorem mderivEquiv_eq {z : S} {w : T} (f : TangentSpace I z →L[ℂ] TangentSpace I w)
    (f0 : f ≠ 0) : ↑(mderivEquiv f f0) = f := by
  apply ContinuousLinearMap.ext; intro x; rfl

/-- Identity derivatives are nonzero -/
public theorem id_mderiv_ne_zero {z : S} : mfderiv I I (fun z ↦ z) z ≠ 0 := by
  have d : MDifferentiableAt I I (fun z ↦ z) z := mdifferentiableAt_id
  simp only [mfderiv, d, if_true, writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
    fderivWithin_univ]
  have e : (fun w ↦ extChartAt I z ((extChartAt I z).symm w)) =ᶠ[𝓝 (extChartAt I z z)] id := by
    apply ((isOpen_extChartAt_target z).eventually_mem (mem_extChartAt_target z)).mp
    refine .of_forall fun w m ↦ ?_
    simp only [id, PartialEquiv.right_inv _ m]
  simp only [e.fderiv_eq, fderiv_id, Ne, Function.comp_def]
  intro h
  have h1 := congrArg (fun f : ℂ →L[ℂ] ℂ ↦ f 1) h
  exact one_ne_zero h1

/-- Critical points of iterations are precritical points -/
public theorem critical_iter {f : S → S} {n : ℕ} {z : S} (fa : ContMDiff I I ω f)
    (c : Critical f^[n] z) : Precritical f z := by
  induction' n with n h
  · have hc : mfderiv I I id z = 0 := by
      simpa [Critical, Function.iterate_zero, mfderiv_id] using c
    simpa [id] using id_mderiv_ne_zero (z := z) hc
  · rw [Function.iterate_succ', Critical,
      mfderiv_comp z ((fa _).mdifferentiableAt (by decide))
        ((fa.iterate _ _).mdifferentiableAt (by decide))] at c
    rcases (mderiv_comp_eq_zero_iff _ _).mp c with c | c
    · exact ⟨n, c⟩
    · exact h c

variable [IsManifold I ω S] [IsManifold I ω T] [IsManifold I ω U]

/-- Chart derivatives are nonzero -/
public theorem extChartAt_mderiv_ne_zero' {z w : S} (m : w ∈ (extChartAt I z).source) :
    mfderiv I I (extChartAt I z) w ≠ 0 := by
  rcases exists_ne (0 : TangentSpace I z) with ⟨t, t0⟩
  have ht : mfderiv I I (extChartAt I z) w t ≠ 0 := by
    intro h0
    have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse m) t
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h0, ContinuousLinearMap.map_zero] at h; exact t0 h.symm
  intro h0
  have hz : mfderiv I I (extChartAt I z) w t =
      (0 : TangentSpace I w →L[ℂ] TangentSpace I (extChartAt I z w)) t := by rw [h0]
  exact ht (by simpa using hz)

/-- Chart derivatives are nonzero -/
public theorem extChartAt_symm_mderiv_ne_zero' {z : S} {w : ℂ} (m : w ∈ (extChartAt I z).target) :
    mfderiv I I (extChartAt I z).symm w ≠ 0 := by
  rcases exists_ne (0 : TangentSpace I (extChartAt I z z)) with ⟨t, t0⟩
  have ht : mfderiv I I (extChartAt I z).symm w t ≠ 0 := by
    intro h0
    have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_right_inverse m) t
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h0, ContinuousLinearMap.map_zero] at h; exact t0 h.symm
  intro h0
  have hz : mfderiv I I (extChartAt I z).symm w t =
      (0 : TangentSpace I w →L[ℂ] TangentSpace I ((extChartAt I z).symm w)) t := by rw [h0]
  exact ht (by simpa using hz)

/-- Chart derivatives are nonzero -/
public theorem extChartAt_mderiv_ne_zero (z : S) : mfderiv I I (extChartAt I z) z ≠ 0 :=
  extChartAt_mderiv_ne_zero' (mem_extChartAt_source z)

/-- Chart derivatives are nonzero -/
public theorem extChartAt_symm_mderiv_ne_zero (z : S) :
    mfderiv I I (extChartAt I z).symm (extChartAt I z z) ≠ 0 :=
  extChartAt_symm_mderiv_ne_zero' (mem_extChartAt_target z)

/-- Nonzeroness of `mfderiv` reduces to nonzeroness of `deriv` -/
public theorem mfderiv_eq_zero_iff_deriv_eq_zero {f : ℂ → ℂ} {z : ℂ} :
    mfderiv I I f z = 0 ↔ deriv f z = 0 := by
  by_cases d : DifferentiableAt ℂ f z
  · constructor
    · have h := d.mdifferentiableAt.hasMFDerivAt; intro e; rw [e] at h
      have p := h.hasFDerivAt.hasDerivAt
      simp only at p; exact p.deriv
    · have h := d.hasDerivAt
      intro e
      rw [e] at h
      have p := h.hasFDerivAt.hasMFDerivAt
      simp only [ContinuousLinearMap.toSpanSingleton_zero] at p
      exact p.mfderiv
  · have d' : ¬MDifferentiableAt I I f z := by
      contrapose d; exact d.differentiableAt
    simp only [deriv_zero_of_not_differentiableAt d, mfderiv_zero_of_not_mdifferentiableAt d']

/-- `mfderiv ≠ 0` iff `deriv ≠ 0` -/
public theorem mfderiv_ne_zero_iff_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ} :
    mfderiv I I f z ≠ 0 ↔ deriv f z ≠ 0 := by rw [not_iff_not, mfderiv_eq_zero_iff_deriv_eq_zero]

/-!
## Facts about `mfderiv` related to continuity and analyticity

These facts would ideally follow from continuity and analyticity of `mfderiv`, but we can't
express that directly as `mfderiv` lives in a different type at each point.  Rather than detour
into the necessary theory, I'm going to express what I need in coordinates for now.
-/

/-- A curried function in coordinates -/
@[expose] public def inChart (f : ℂ → S → T) (c : ℂ) (z : S) : ℂ → ℂ → ℂ := fun e w ↦
  extChartAt I (f c z) (f e ((extChartAt I z).symm w))

/-- `inChart` is analytic -/
public theorem ContMDiffAt.inChart {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) :
    AnalyticAt ℂ (uncurry (inChart f c z)) (c, _root_.extChartAt I z z) := by
  apply ContMDiffAt.analyticAt II I
  apply (contMDiffAt_extChartAt' (extChartAt_source I (f c z) ▸
    (mem_extChartAt_source (f c z)))).comp_of_eq
  apply fa.comp₂_of_eq contMDiffAt_fst
  apply ((contMDiffOn_extChartAt_symm _).contMDiffAt (extChartAt_target_mem_nhds'
    (mem_extChartAt_target z))).comp_of_eq contMDiffAt_snd
  repeat' simp only [PartialEquiv.left_inv _ (mem_extChartAt_source z)]

/-- `inChart` preserves critical points locally -/
public theorem inChart_critical {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z),
      mfderiv I I (f p.1) p.2 = 0 ↔ deriv (inChart f c z p.1) (extChartAt I z p.2) = 0 := by
  apply (fa.continuousAt.eventually_mem ((isOpen_extChartAt_source (f c z)).mem_nhds
    (mem_extChartAt_source (I := I) (f c z)))).mp
  apply ((isOpen_extChartAt_source (c, z)).eventually_mem (mem_extChartAt_source (I := II) _)).mp
  refine fa.eventually.mp (.of_forall ?_); intro ⟨e, w⟩ fa m fm
  simp only [extChartAt_prod, PartialEquiv.prod_source, extChartAt_eq_refl,
    PartialEquiv.refl_source, mem_prod, mem_univ, true_and] at m
  simp only [uncurry] at fm
  have m' := PartialEquiv.map_source _ m
  simp only [← mfderiv_eq_zero_iff_deriv_eq_zero]
  have cd : ContMDiffAt I I ω (extChartAt I (f c z)) (f e w) := contMDiffAt_extChartAt' (extChartAt_source I (f c z) ▸ fm)
  have fd : ContMDiffAt I I ω (f e ∘ (extChartAt I z).symm) (extChartAt I z w) := by
    simp only [Function.comp_def]
    exact ContMDiffAt.comp_of_eq fa.along_snd ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' m'))
      (PartialEquiv.right_inv _ m)
  have ce : inChart f c z e = extChartAt I (f c z) ∘ f e ∘ (extChartAt I z).symm := rfl
  rw [ce,
    mfderiv_comp_of_eq (cd.mdifferentiableAt (by decide)) (fd.mdifferentiableAt (by decide)) _,
    mfderiv_comp_of_eq (fa.along_snd.mdifferentiableAt (by decide))
      (((contMDiffOn_extChartAt_symm _).contMDiffAt
        (extChartAt_target_mem_nhds' m')).mdifferentiableAt WithTop.top_ne_zero)]
  · rw [(extChartAt I z).left_inv m]
    constructor
    · intro h
      rw [h, ContinuousLinearMap.zero_comp]
      simpa using
        (mfderiv I I (extChartAt I (f c z)) ((f e ∘ (extChartAt I z).symm) (extChartAt I z w))).comp_zero
    · intro h
      rcases (mderiv_comp_eq_zero_iff _ _).mp h with h | h
      · have h' : mfderiv I I (extChartAt I (f c z)) (f e w) = 0 := by
          rw [Function.comp, (extChartAt I z).left_inv m] at h
          exact h
        exact False.elim ((extChartAt_mderiv_ne_zero' fm) h')
      · rcases (mderiv_comp_eq_zero_iff _ _).mp h with h | h
        · exact h
        · exact False.elim ((extChartAt_symm_mderiv_ne_zero' m') h)
  · exact PartialEquiv.left_inv _ m
  · simp only [Function.comp, PartialEquiv.left_inv _ m]

/-- `mfderiv` is nonzero near where it is nonzero (parameterized version) -/
public theorem mfderiv_ne_zero_eventually' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (f0 : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z), mfderiv I I (f p.1) p.2 ≠ 0 := by
  set g := inChart f c z
  have g0 := inChart_critical fa
  have g0n : ∀ᶠ p : ℂ × S in 𝓝 (c, z), deriv (g p.1) (extChartAt I z p.2) ≠ 0 := by
    refine ContinuousAt.eventually_ne ?_ ?_
    · have e : (fun p : ℂ × S ↦ deriv (g p.1) (extChartAt I z p.2)) =
        (fun p : ℂ × ℂ ↦ deriv (g p.1) p.2) ∘ fun p : ℂ × S ↦ (p.1, extChartAt I z p.2) := rfl
      rw [e]
      exact fa.inChart.deriv2.continuousAt.comp_of_eq
        (continuousAt_fst.prodMk ((continuousAt_extChartAt z).comp_of_eq continuousAt_snd rfl))
        rfl
    · contrapose! f0; rwa [g0.self_of_nhds]
  refine g0.mp (g0n.mp (.of_forall fun w g0 e ↦ ?_))
  simpa [Ne, e] using g0

/-- `mfderiv` is nonzero near where it is nonzero -/
public theorem mfderiv_ne_zero_eventually {f : S → T} {z : S} (fa : ContMDiffAt I I ω f z)
    (f0 : mfderiv I I f z ≠ 0) : ∀ᶠ w in 𝓝 z, mfderiv I I f w ≠ 0 := by
  set c : ℂ := 0
  set g : ℂ → S → T := fun _ z ↦ f z
  have ga : ContMDiffAt II I ω (uncurry g) (c, z) := by
    have e : uncurry g = f ∘ fun p ↦ p.2 := rfl
    rw [e]
    apply ContMDiffAt.comp_of_eq fa contMDiffAt_snd; simp only
  have pc : Tendsto (fun z ↦ (c, z)) (𝓝 z) (𝓝 (c, z)) := continuousAt_const.prodMk continuousAt_id
  exact pc.eventually (mfderiv_ne_zero_eventually' ga f0)

/-- The set of noncritical points is open -/
public theorem isOpen_noncritical {f : ℂ → S → T} (fa : ContMDiff II I ω (uncurry f)) :
    IsOpen {p : ℂ × S | ¬Critical (f p.1) p.2} := by
  rw [isOpen_iff_eventually]; intro ⟨c, z⟩ m; exact mfderiv_ne_zero_eventually' (fa _) m

/-- The set of critical points is closed -/
public theorem isClosed_critical {f : ℂ → S → T} (fa : ContMDiff II I ω (uncurry f)) :
    IsClosed {p : ℂ × S | Critical (f p.1) p.2} := by
  simpa [compl_setOf, not_not] using (isOpen_noncritical fa).isClosed_compl

/-- Osgood's theorem on 2D product manifolds: separate analyticity + continuity
    implies joint analyticity.  I'm not sure if a Hartogs' analogue is possible,
    since we use continuity to remain within the right charts. -/
public theorem osgoodManifold {f : S × T → U} (fc : Continuous f)
    (f0 : ∀ x y, ContMDiffAt I I ω (fun x ↦ f (x, y)) x)
    (f1 : ∀ x y, ContMDiffAt I I ω (fun y ↦ f (x, y)) y) : ContMDiff II I ω f := by
  rw [mAnalytic_iff_of_boundaryless]; use fc; intro p; apply osgood_at'
  have fm : ∀ᶠ q in 𝓝 (extChartAt II p p),
      f ((extChartAt II p).symm q) ∈ (extChartAt I (f p)).source := by
    refine (fc.continuousAt.comp (continuousAt_extChartAt_symm p)).eventually_mem
        ((isOpen_extChartAt_source (f p)).mem_nhds ?_)
    simp only [Function.comp, (extChartAt II p).left_inv (mem_extChartAt_source _)]
    apply mem_extChartAt_source
  apply ((isOpen_extChartAt_target p).eventually_mem (mem_extChartAt_target p)).mp
  refine fm.mp (.of_forall fun q fm m ↦ ⟨?_, ?_, ?_⟩)
  · exact (continuousAt_extChartAt' fm).comp_of_eq
        (fc.continuousAt.comp (continuousAt_extChartAt_symm'' m)) rfl
  · apply ContMDiffAt.analyticAt I I
    refine (contMDiffAt_extChartAt' (extChartAt_source I (f p) ▸ fm)).comp_of_eq ?_ rfl
    rw [extChartAt_prod] at m; simp only [Function.comp, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe, PartialEquiv.prod_target, mem_prod_eq] at m ⊢
    exact (f0 _ _).comp _ ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' m.1))
  · apply ContMDiffAt.analyticAt I I
    refine (contMDiffAt_extChartAt' (extChartAt_source I (f p) ▸ fm)).comp_of_eq ?_ rfl
    rw [extChartAt_prod] at m; simp only [Function.comp, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe, PartialEquiv.prod_target, mem_prod_eq] at m ⊢
    exact (f1 _ _).comp _ ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' m.2))
