module
public import Ray.Manifold.Defs
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Ray.Analytic.Holomorphic
import Ray.Manifold.Analytic
import Ray.Manifold.Manifold
import Ray.Manifold.OneDimension

/-!
## The parameterized inverse function theorem on 1D complex manifolds

Given `f : ℂ × S → T`, we seek `g : ℂ × T → S` s.t. `g c (f c z) = z`.

The key theorems are `complex_inverse_fun` and `complex_inverse_fun'`; everything else is
intermediate lemmas.

These results are straightforward consequences of the 2D inverse function theorem
applied to `(c,z) ↦ (c, f c z)` mapped to charts, but (at least for me)
this takes a while to write out.  A subtlety is that `TangentSpace I z` for
`z ∈ ℂ` is definitionally and canonically `ℂ`, and we take advantage of this
to express manifold invertibility in charts as nonmanifold invertibility.  But
this means that the type signatures on all the small definitions are very important
to make `simp` go through correctly.
-/

open Classical
open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff OneDimension Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T]

namespace ComplexInverseFun

/-- Data for our 1D inverse function theorem -/
structure Cinv (f : ℂ → S → T) (c : ℂ) (z : S) : Prop where
  fa : ContMDiffAt II I ω (uncurry f) (c, z)
  nc : mfderiv I I (f c) z ≠ 0

variable {f : ℂ → S → T} {c : ℂ} {z : S}

/-- `z` in charts -/
@[nolint unusedArguments] def Cinv.z' (_ : Cinv f c z) : ℂ := extChartAt I z z

/-- `f z` in charts -/
@[nolint unusedArguments] def Cinv.fz' (_ : Cinv f c z) : ℂ := extChartAt I (f c z) (f c z)

lemma Cinv.zz (i : Cinv f c z) : (extChartAt I z).symm (c, i.z').snd = z := by
  simp only [Cinv.z', PartialEquiv.left_inv _ (mem_extChartAt_source _)]

/-- `f` in coordinates -/
@[nolint unusedArguments] def Cinv.f' (_ : Cinv f c z) : ℂ × ℂ → ℂ := fun x ↦
  extChartAt I (f c z) (f x.1 ((extChartAt I z).symm x.2))

/-- `(c,z) → (c, f c z)`, in coordinates.  We will show this function is invertible. -/
def Cinv.h (i : Cinv f c z) : ℂ × ℂ → ℂ × ℂ := fun x ↦ (x.1, i.f' x)

-- f' and h are analytic
theorem Cinv.fa' (i : Cinv f c z) : AnalyticAt ℂ i.f' (c, i.z') := by
  have fa := i.fa
  simp only [mAnalyticAt_iff_of_boundaryless, uncurry, extChartAt_prod, PartialEquiv.prod_coe_symm,
    PartialEquiv.prod_coe] at fa
  exact fa.2
theorem Cinv.ha (i : Cinv f c z) : AnalyticAt ℂ i.h (c, i.z') := analyticAt_fst.prod i.fa'

/-- The key nonzero derivative: `d(f c z)/dz` -/
@[nolint unusedArguments]
def Cinv.dfz (_ : Cinv f c z) : TangentSpace I z →L[ℂ] TangentSpace I (f c z) := mfderiv I I (f c) z

/-- The inverse of the key nonzero derivative: `(d(f c z)/dz)⁻¹` -/
def Cinv.dfzi (i : Cinv f c z) :
    TangentSpace I (f c z) →L[ℂ] TangentSpace I z := (mderivEquiv i.dfz i.nc).symm

lemma Cinv.dfzi_dfz (i : Cinv f c z) : ∀ t, i.dfzi (i.dfz t) = t :=
    fun _ ↦ (mderivEquiv _ i.nc).left_inv _
lemma Cinv.dfz_dfzi (i : Cinv f c z) : ∀ t, i.dfz (i.dfzi t) = t :=
    fun _ ↦ (mderivEquiv _ i.nc).right_inv _

-- The derivative i.dh of i.h
--   dh = dc.prod (i.de'.comp (i.dfc.comp dc + i.dfz.comp (i.de.comp dz)))
--      = (    1               0      )
--        (de' ∘ dfc    de' ∘ dfz ∘ de)

/-- The inverse chart derivative at `z` -/
def Cinv.de (i : Cinv f c z) : ℂ →L[ℂ] TangentSpace I z := mfderiv I I (extChartAt I z).symm i.z'
/-- The chart derivative at `f c z` -/
def Cinv.de' (_ : Cinv f c z) :
    TangentSpace I (f c z) →L[ℂ] ℂ := mfderiv I I (extChartAt I (f c z)) (f c z)
/-- The derivative of `(c,z) ↦ c` is `fst` -/
def dc : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ ℂ
/-- The derivative of `(c,z) ↦ z` is `snd` -/
def dz : ℂ × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ
/-- `d(f c z)/dc` -/
def Cinv.dfc (_ : Cinv f c z) : ℂ →L[ℂ] TangentSpace I (f c z) := mfderiv I I (fun c : ℂ ↦ f c z) c
/-- `df = d(f c z)/dc dc + d(f c z)/dz dz` -/
def Cinv.df (i : Cinv f c z) :
    ℂ × ℂ →L[ℂ] TangentSpace I (f c z) := i.dfc.comp dc + i.dfz.comp (i.de.comp dz)
/-- `df` in charts -/
def Cinv.df' (i : Cinv f c z) : ℂ × ℂ →L[ℂ] ℂ := i.de'.comp i.df
/-- `dh` (in charts) -/
def Cinv.dh (i : Cinv f c z) : ℂ × ℂ →L[ℂ] ℂ × ℂ := dc.prod i.df'

-- dh is invertible
--   dh (u,v) = (a,b)
--   (u, (de' ∘ dfc)u + (de' ∘ dfz ∘ de)v) = (a,b)
--   u = a
--   (de' ∘ dfc)a + (de' ∘ dfz ∘ de)v = b
--   v = (de' ∘ dfz ∘ de)⁻¹ (b - (de' ∘ dfc)a)
--   v = (de⁻¹  ∘ dfz⁻¹ ∘ de'⁻¹) (b - (de' ∘ dfc)a)
/-- The chart derivative at `z` -/
def Cinv.dei (_ : Cinv f c z) :
    TangentSpace I z →L[ℂ] ℂ := mfderiv I I (extChartAt I z) z
/-- The inverse chart derivative at `z` -/
def Cinv.dei' (i : Cinv f c z) :
    ℂ →L[ℂ] TangentSpace I (f c z) := mfderiv I I (extChartAt I (f c z)).symm i.fz'
/-- The key inverse derivative of `f` w.r.t. `z`, in charts -/
def Cinv.dfi' (i : Cinv f c z) : ℂ →L[ℂ] ℂ := (i.dei.comp i.dfzi).comp i.dei'
/-- The overall inverse derivative of `h` -/
def Cinv.dhi (i : Cinv f c z) :
    ℂ × ℂ →L[ℂ] ℂ × ℂ := dc.prod (i.dfi'.comp (dz - (i.de'.comp i.dfc).comp dc))

variable [cms : IsManifold I ω S]

lemma Cinv.dei_de (i : Cinv f c z) : ∀ t, i.dei (i.de t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp
    (extChartAt_mderiv_right_inverse' (mem_extChartAt_source (I := I) z)) t
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h; exact h

variable [cmt : IsManifold I ω T]

lemma Cinv.has_df' (i : Cinv f c z) : HasMFDerivAt II I i.f' (c, i.z') i.df' := by
  apply HasMFDerivAt.comp (I' := I) (c, i.z')
  · rw [i.zz]
    exact ((contMDiffAt_extChartAt' (mem_chart_source _ _)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  · simp only [Cinv.df]
    have fd := i.fa.mdifferentiableAt (by decide)
    rw [← i.zz] at fd
    apply MDifferentiableAt.hasMFDerivAt_comp2 fd
    · apply hasMFDerivAt_fst
    · refine HasMFDerivAt.comp _ ?_ (hasMFDerivAt_snd _)
      exact (((contMDiffOn_extChartAt_symm _).contMDiffAt
        (extChartAt_target_mem_nhds'
        (mem_extChartAt_target _))).mdifferentiableAt one_ne_zero).hasMFDerivAt
    · rw [i.zz]; exact (i.fa.along_fst.mdifferentiableAt (by decide)).hasMFDerivAt
    · rw [i.zz]; exact (i.fa.along_snd.mdifferentiableAt (by decide)).hasMFDerivAt

lemma Cinv.has_dh (i : Cinv f c z) : HasMFDerivAt II II i.h (c, i.z') i.dh := by
  refine HasMFDerivAt.prodMk ?_ i.has_df'; apply hasMFDerivAt_fst

omit cms in
lemma Cinv.dei_de' (i : Cinv f c z) : ∀ t, i.dei' (i.de' t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse
    (mem_extChartAt_source (f c z))) t
  simp only [ContinuousLinearMap.comp_apply] at h; exact h

omit cmt in
lemma Cinv.de_dei (i : Cinv f c z) : ∀ t, i.de (i.dei t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_left_inverse
    (mem_extChartAt_source z)) t
  simp only [ContinuousLinearMap.comp_apply] at h; exact h

omit cms in
lemma Cinv.de_dei' (i : Cinv f c z) : ∀ t, i.de' (i.dei' t) = t := by
  intro t
  have h := ContinuousLinearMap.ext_iff.mp (extChartAt_mderiv_right_inverse'
    (mem_extChartAt_source (I := I) (f c z))) t
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h; exact h

lemma Cinv.dhi_dh (i : Cinv f c z) : ∀ t, i.dhi (i.dh t) = t := by
  intro ⟨u, v⟩
  simp only [Cinv.dh, Cinv.dhi, dc, dz, Cinv.dfi', Cinv.df', Cinv.df, i.dei_de', i.dei_de,
    i.dfzi_dfz, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add, add_sub_cancel_left]

lemma Cinv.dh_dhi (i : Cinv f c z) : ∀ t, i.dh (i.dhi t) = t := by
  intro ⟨u, v⟩
  simp only [Cinv.dh, Cinv.dhi, dc, dz, Cinv.dfi', Cinv.df', Cinv.df, i.de_dei', i.de_dei,
    i.dfz_dfzi, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.add_apply, ContinuousLinearMap.map_add, ContinuousLinearMap.map_sub,
    add_sub_cancel_left, ← add_sub_assoc]

/-- `dh` as a `ContinuousLinearEquiv` -/
def Cinv.dhe (i : Cinv f c z) : (ℂ × ℂ) ≃L[ℂ] ℂ × ℂ :=
  ContinuousLinearEquiv.equivOfInverse i.dh i.dhi i.dhi_dh i.dh_dhi

lemma Cinv.has_dhe (i : Cinv f c z) : HasFDerivAt i.h (i.dhe : ℂ × ℂ →L[ℂ] ℂ × ℂ) (c, i.z') :=
  hasMFDerivAt_iff_hasFDerivAt'.mp i.has_dh

/-- `h` as a `PartialHomeomorph` -/
def Cinv.he (i : Cinv f c z) :=
  ContDiffAt.toOpenPartialHomeomorph i.h i.ha.contDiffAt i.has_dhe one_ne_zero

/-- `h` inverts at the point -/
theorem Cinv.inv_at (i : Cinv f c z) :
    (i.he.symm (c, extChartAt I (f c z) (f c z))).2 = extChartAt I z z := by
  have a := ContDiffAt.localInverse_apply_image i.ha.contDiffAt i.has_dhe one_ne_zero
  have e : ContDiffAt.localInverse i.ha.contDiffAt i.has_dhe one_ne_zero = i.he.symm := rfl
  rw [e] at a; clear e
  simp only [Cinv.z', Cinv.h, Cinv.f', PartialEquiv.left_inv _ (mem_extChartAt_source _)] at a
  rw [a]

/-- Our inverse function! -/
def Cinv.g (i : Cinv f c z) : ℂ → T → S := fun b w ↦
  (extChartAt I z).symm (i.he.symm (b, extChartAt I (f c z) w)).2

/-- `g` is a local left inverse -/
theorem Cinv.left_inv (i : Cinv f c z) : ∀ᶠ x : ℂ × S in 𝓝 (c, z), i.g x.1 (f x.1 x.2) = x.2 := by
  generalize ht :
      ((extChartAt II (c, z)).source ∩ extChartAt II (c, z) ⁻¹' i.he.source : Set (ℂ × S)) = t
  have o : IsOpen t := by
    rw [← ht]
    exact (continuousOn_extChartAt _).isOpen_inter_preimage (isOpen_extChartAt_source _)
      i.he.open_source
  have m : (c, z) ∈ t := by
    simp only [mem_inter_iff, mem_preimage, mem_extChartAt_source, true_and, ← ht]
    exact ContDiffAt.mem_toOpenPartialHomeomorph_source i.ha.contDiffAt i.has_dhe one_ne_zero
  apply Filter.eventuallyEq_of_mem (o.mem_nhds m); intro x m
  simp only [mem_inter_iff, mem_preimage, extChartAt_prod, extChartAt_eq_refl, ← ht,
    PartialEquiv.prod_source, PartialEquiv.refl_source, mem_prod_eq, mem_univ, true_and,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id] at m
  have inv := i.he.left_inv m.2
  simp only [Cinv.g]
  generalize hq : i.he.symm = q; rw [hq] at inv
  rw [Cinv.he, ContDiffAt.toOpenPartialHomeomorph_coe i.ha.contDiffAt i.has_dhe one_ne_zero] at inv
  simp only [Cinv.h, Cinv.f', PartialEquiv.left_inv _ m.1] at inv
  simp only [inv, PartialEquiv.left_inv _ m.1]

/-- `h⁻¹` passes through its first argument -/
theorem Cinv.inv_fst (i : Cinv f c z) : ∀ x, x ∈ i.he.target → (i.he.symm x).1 = x.1 := by
  intro x m
  have e : i.he (i.he.symm x) = x := i.he.right_inv m
  generalize hq : i.he.symm x = q; rw [hq] at e
  rw [Cinv.he, ContDiffAt.toOpenPartialHomeomorph_coe i.ha.contDiffAt i.has_dhe one_ne_zero,
    Cinv.h] at e
  rw [← e]

/-- `g` is a local right inverse -/
theorem Cinv.right_inv (i : Cinv f c z) :
    ∀ᶠ x : ℂ × T in 𝓝 (c, f c z), f x.1 (i.g x.1 x.2) = x.2 := by
  generalize ht : ((extChartAt II (c, f c z)).source ∩ extChartAt II (c, f c z) ⁻¹' i.he.target
      : Set (ℂ × T)) = t
  have o : IsOpen t := by
    rw [← ht]
    exact (continuousOn_extChartAt _).isOpen_inter_preimage (isOpen_extChartAt_source _)
      i.he.open_target
  have m' : (c, extChartAt I (f c z) (f c z)) ∈ i.he.toPartialEquiv.target := by
    have m := ContDiffAt.image_mem_toOpenPartialHomeomorph_target i.ha.contDiffAt i.has_dhe
      one_ne_zero
    have e : i.h (c, i.z') = (c, extChartAt I (f c z) (f c z)) := by
      simp only [Cinv.h, Cinv.z', Cinv.f', PartialEquiv.left_inv _ (mem_extChartAt_source _)]
    rw [e] at m; exact m
  have m : (c, f c z) ∈ t := by
    simp only [m', mem_inter_iff, mem_preimage, mem_extChartAt_source, true_and, ← ht,
      extChartAt_prod, PartialEquiv.prod_coe, extChartAt_eq_refl, PartialEquiv.refl_coe, id,
      PartialEquiv.prod_source, prodMk_mem_set_prod_eq, PartialEquiv.refl_source, mem_univ]
  have fm : ∀ᶠ x : ℂ × T in 𝓝 (c, f c z),
      f x.1 ((extChartAt I z).symm (i.he.symm (x.1, extChartAt I (f c z) x.2)).2) ∈
        (extChartAt I (f c z)).source := by
    refine ContinuousAt.eventually_mem ?_ (extChartAt_source_mem_nhds' ?_)
    · apply i.fa.continuousAt.comp₂_of_eq continuousAt_fst
      · refine ContinuousAt.comp ?_ ?_
        · simp only [i.inv_at]; exact continuousAt_extChartAt_symm _
        · apply continuousAt_snd.comp
          · refine (OpenPartialHomeomorph.continuousAt i.he.symm ?_).comp ?_
            · simp only [m', (he i).symm_source]
            · apply continuousAt_fst.prodMk
              apply (continuousAt_extChartAt _).comp_of_eq
              · exact continuousAt_snd
              · rfl
      · simp only [i.inv_at, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
    · simp only [i.inv_at, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
      apply mem_extChartAt_source
  refine fm.mp (Filter.eventually_of_mem (o.mem_nhds m) ?_)
  intro x m mf
  simp only [mem_inter_iff, mem_preimage, extChartAt_prod, extChartAt_eq_refl,
    PartialEquiv.prod_source, PartialEquiv.refl_source, mem_prod_eq, mem_univ, true_and,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, ← ht] at m
  have inv := i.he.right_inv m.2
  simp only [Cinv.g]
  generalize hq : i.he.symm = q; rw [hq] at inv mf
  rw [Cinv.he, ContDiffAt.toOpenPartialHomeomorph_coe i.ha.contDiffAt i.has_dhe one_ne_zero] at inv
  have q1 : (q (x.1, extChartAt I (f c z) x.2)).1 = x.1 := by simp only [← hq, i.inv_fst _ m.2]
  simp only [Cinv.h, Cinv.f', Prod.eq_iff_fst_eq_snd_eq, q1] at inv
  nth_rw 2 [← PartialEquiv.left_inv _ m.1]; nth_rw 2 [← inv.2]
  refine (PartialEquiv.left_inv _ mf).symm

theorem Cinv.he_symm_mAnalytic (i : Cinv f c z) : ContMDiffAt II II ω i.he.symm (c, i.fz') := by
  have d : ContDiffAt ℂ ω i.he.symm _ :=
    ContDiffAt.to_localInverse i.ha.contDiffAt i.has_dhe (by decide)
  have e : i.h (c, i.z') = (c, i.fz') := by
    simp only [Cinv.h, Cinv.fz', Cinv.f']
    simp only [Cinv.z', (extChartAt I z).left_inv (mem_extChartAt_source _)]
  rw [e] at d
  rw [← analyticAt_iff_mAnalyticAt]
  exact (contDiffAt_iff_analytic_at2 le_top).mp d

/-- Our inverse `g` is analytic -/
theorem Cinv.ga (i : Cinv f c z) : ContMDiffAt II I ω (uncurry i.g) (c, f c z) := by
  apply ((contMDiffOn_extChartAt_symm _).contMDiffAt
    (extChartAt_target_mem_nhds' (mem_extChartAt_target z))).comp_of_eq
  · refine contMDiffAt_snd.comp _ (i.he_symm_mAnalytic.comp_of_eq ?_ ?_)
    · apply contMDiffAt_fst.prodMk
      refine (contMDiffAt_extChartAt' ?_).comp _ contMDiffAt_snd
      exact mem_chart_source _ _
    · rfl
  · exact i.inv_at

end ComplexInverseFun

variable [IsManifold I ω S] [IsManifold I ω T]

/-- The 1D inverse function theorem for complex manifolds (parameterized version):
    If `f : ℂ → S → T` is analytic with nonzero derivative (w.r.t. the second
    argument) at a point `(c,z)`, it is a parameterized local inverse `g : ℂ → T → S` s.t.
    `g c (f c z) = z` and `f c (g c z) = z` locally. -/
public theorem complex_inverse_fun {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (nc : mfderiv I I (f c) z ≠ 0) :
    ∃ g : ℂ → T → S,
      ContMDiffAt II I ω (uncurry g) (c, f c z) ∧
        (∀ᶠ x : ℂ × S in 𝓝 (c, z), g x.1 (f x.1 x.2) = x.2) ∧
          ∀ᶠ x : ℂ × T in 𝓝 (c, f c z), f x.1 (g x.1 x.2) = x.2 := by
  have i : ComplexInverseFun.Cinv f c z :=
    { fa
      nc }
  use i.g, i.ga, i.left_inv, i.right_inv

/-- The 1D inverse function theorem for complex manifolds (nonparameterized version):
    If `f : S → T` is analytic with nonzero derivative, it has a local inverse `g : T → S`. -/
public theorem complex_inverse_fun' {f : S → T} {z : S} (fa : ContMDiffAt I I ω f z)
    (nc : mfderiv I I f z ≠ 0) :
    ∃ g : T → S,
      ContMDiffAt I I ω g (f z) ∧ (∀ᶠ x in 𝓝 z, g (f x) = x) ∧ ∀ᶠ x in 𝓝 (f z), f (g x) = x := by
  set f' : ℂ → S → T := fun _ z ↦ f z
  have fa' : ContMDiffAt II I ω (uncurry f') (0, z) := fa.comp_of_eq contMDiffAt_snd rfl
  rcases complex_inverse_fun fa' nc with ⟨g, ga, gf, fg⟩
  use g 0, ga.comp _ (contMDiffAt_const.prodMk contMDiffAt_id),
    (continuousAt_const.prodMk continuousAt_id).eventually gf,
    (continuousAt_const.prodMk continuousAt_id).eventually fg
