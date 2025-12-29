module
public import Ray.Manifold.Defs
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Ray.Analytic.Analytic
import Ray.Dynamics.BottcherNear
import Ray.Manifold.Analytic
import Ray.Manifold.Inverse
import Ray.Manifold.LocalInj
import Ray.Manifold.Manifold
import Ray.Manifold.OneDimension
import Ray.Misc.Multilinear

/-!
## Non-injectivity near multiple roots

Let `f : S → T` be an analytic function between 1D complex manifolds.  We show that if
`f` has zero derivative at a point, it is not locally injective near that point.  Indeed,
we show that there is a nontrivial local nonlinear rotation `g : S → S` around the point
that locally commutes with `f`: `f (g z) = f z` and `g z ≠ z` except at the point.

This is a bit of a sledgehammer, as (1) the rotation `g` is defined using Böttcher coordinates
and so far we use only (2) the fact that injectivity implies nonzero derivative.  There are
surely simpler proofs of (2), but it's nice to have the rotation fact, and we already have
Böttcher coordinates.

The proof proceeds in w.l.o.g. stages, reducing first from manifolds to `ℂ → ℂ`, then moving
the point to `0` and standardizing the leading coefficient to be 1.
-/

open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology Real
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold I ω T]

/-- There are nontrivial `d`th roots of unity if `2 ≤ d` -/
theorem exist_root_of_unity {d : ℕ} (d2 : 2 ≤ d) : ∃ a : ℂ, a ≠ 1 ∧ a ^ d = 1 := by
  set n : ℕ+ := ⟨d, lt_of_lt_of_le (by norm_num) d2⟩
  have two : Nontrivial (rootsOfUnity n ℂ) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, Complex.card_rootsOfUnity]
    simp only [PNat.mk_coe, n]; exact lt_of_lt_of_le (by norm_num) d2
  rcases two with ⟨⟨a, am⟩, ⟨b, bm⟩, ab⟩
  simp only [Ne, Subtype.mk_eq_mk, mem_rootsOfUnity] at am bm ab
  by_cases a1 : a = 1
  · use b; rw [a1] at ab; constructor
    · simp only [ne_eq, Units.val_eq_one, Ne.symm ab, not_false_eq_true]
    · simp only [PNat.mk_coe, n] at bm; rw [← Units.val_pow_eq_pow_val, bm, Units.val_one]
  · use a; constructor
    · simp only [ne_eq, Units.val_eq_one, a1, not_false_eq_true]
    · simp only [PNat.mk_coe, n] at am; rw [← Units.val_pow_eq_pow_val, am, Units.val_one]

/-- Case `c = 0, f 0 = 0`, when `f` has a monic, superattracting fixpoint at 0.  Every
    nearby point is achieved at least twice.  We operationalize this statement via a
    nontrivial function `g : ℂ → ℂ` s.t. `f (g z) = f z`. -/
theorem SuperAt.not_local_inj {f : ℂ → ℂ} {d : ℕ} (s : SuperAt f d) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ ∀ᶠ z in 𝓝[{0}ᶜ] 0, g z ≠ z ∧ f (g z) = f z := by
  rcases s.superNear with ⟨t, s⟩
  have ba : AnalyticAt ℂ (bottcherNear f d) 0 := bottcherNear_analytic_z s _ s.t0
  have nc : mfderiv I I (bottcherNear f d) 0 ≠ 0 := by
    rw [mfderiv_eq_fderiv, ← toSpanSingleton_deriv, (bottcherNear_monic s).deriv]
    exact ContinuousLinearMap.smulRight_ne_zero ContinuousLinearMap.one_ne_zero (by norm_num)
  rcases complex_inverse_fun' (ba.mAnalyticAt I I) nc with ⟨i, ia, ib, bi⟩
  rw [bottcherNear_zero] at bi ia
  have i0 : i 0 = 0 := by nth_rw 1 [← bottcherNear_zero]; rw [ib.self_of_nhds]
  have inj : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), i p.1 = i p.2 → p.1 = p.2 := by
    refine ia.local_inj ?_
    have d0 : mfderiv I I (fun z : ℂ ↦ z) 0 ≠ 0 := id_mderiv_ne_zero
    rw [(Filter.EventuallyEq.symm ib).mfderiv_eq] at d0
    rw [←Function.comp_def, mfderiv_comp 0 _ ba.differentiableAt.mdifferentiableAt] at d0
    simp only [Ne, mderiv_comp_eq_zero_iff, nc, or_false] at d0
    rw [bottcherNear_zero] at d0; exact d0
    rw [bottcherNear_zero]; exact ia.mdifferentiableAt (by decide)
  rcases exist_root_of_unity s.d2 with ⟨a, a1, ad⟩
  refine ⟨fun z ↦ i (a * bottcherNear f d z), ?_, ?_, ?_⟩
  · apply ContMDiffAt.analyticAt I I
    refine ia.comp_of_eq (contMDiffAt_const.mul (ba.mAnalyticAt I I)) ?_
    simp only [bottcherNear_zero, MulZeroClass.mul_zero]
  · simp only [bottcherNear_zero, MulZeroClass.mul_zero, i0]
  · simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff]
    have t0 : ContinuousAt (fun z ↦ a * bottcherNear f d z) 0 :=
      continuousAt_const.mul ba.continuousAt
    have t1 : ContinuousAt (fun z ↦ f (i (a * bottcherNear f d z))) 0 := by
      refine s.fa0.continuousAt.comp_of_eq (ia.continuousAt.comp_of_eq t0 ?_) ?_
      repeat' simp only [bottcherNear_zero, MulZeroClass.mul_zero, i0]
    have t2 : ContinuousAt f 0 := s.fa0.continuousAt
    have m0 : ∀ᶠ z in 𝓝 0, i (a * bottcherNear f d z) ∈ t := by
      refine (ia.continuousAt.comp_of_eq t0 ?_).eventually_mem (s.o.mem_nhds ?_)
      repeat' simp only [bottcherNear_zero, MulZeroClass.mul_zero, i0, s.t0, Function.comp_def]
    have m1 : ∀ᶠ z in 𝓝 0, z ∈ t := s.o.eventually_mem s.t0
    simp only [ContinuousAt, bottcherNear_zero, MulZeroClass.mul_zero, i0, s.f0] at t0 t1 t2
    have tp := t0.prodMk ba.continuousAt
    simp only [← nhds_prod_eq, bottcherNear_zero] at tp
    apply (tp.eventually inj).mp
    refine ib.mp (bi.mp ((t1.eventually ib).mp
      ((t0.eventually bi).mp ((t2.eventually ib).mp (m0.mp (m1.mp ?_))))))
    refine .of_forall fun z m1 m0 t2 t0 t1 _ ib tp z0 ↦ ⟨?_, ?_⟩
    · contrapose tp; simp only [Classical.not_imp] at tp ⊢
      rw [ib]; use tp
      contrapose a1
      have b0 := bottcherNear_ne_zero s m1 z0
      calc a
        _ = a * bottcherNear f d z / bottcherNear f d z := by field_simp [b0]
        _ = bottcherNear f d z / bottcherNear f d z := by rw [a1]
        _ = 1 := div_self b0
    · rw [← t1, bottcherNear_eqn s m0, t0, mul_pow, ad, one_mul, ← bottcherNear_eqn s m1, t2]

/-- Case `c = 0, f 0 = 0, f' 0 = 0`.  Every nearby point is achieved at least twice.  We
    operationalize this statement via a nontrivial function `g : ℂ → ℂ` s.t. `f (g z) = f z`. -/
theorem not_local_inj_of_deriv_zero' {f : ℂ → ℂ} (fa : AnalyticAt ℂ f 0) (df : HasDerivAt f 0 0)
    (f0 : f 0 = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ ∀ᶠ z in 𝓝[{0}ᶜ] 0, g z ≠ z ∧ f (g z) = f z := by
  by_cases o0 : orderAt f 0 = 0
  · simp only [orderAt_eq_zero_iff fa, f0, Ne, not_true, or_false] at o0
    use fun z ↦ -z, analyticAt_id.neg, neg_zero; rw [eventually_nhdsWithin_iff]
    have e0 : ∀ᶠ z in 𝓝 0, f (-z) = 0 := by
      nth_rw 1 [← neg_zero] at o0; exact continuousAt_neg.eventually o0
    refine o0.mp (e0.mp (.of_forall fun z f0' f0 z0 ↦ ?_))
    simp only [mem_compl_singleton_iff] at z0; rw [Pi.zero_apply] at f0
    rwa [f0, f0', eq_self_iff_true, and_true, neg_ne_self]
  have o1 : orderAt f 0 ≠ 1 := by
    have d := df.deriv; contrapose d
    exact deriv_ne_zero_of_orderAt_eq_one d
  have d2 : 2 ≤ orderAt f 0 := by rw [Nat.two_le_iff]; use o0, o1
  clear o1 df f0
  set a := leadingCoeff f 0
  have a0 : a ≠ 0 := leadingCoeff_ne_zero fa o0
  set g := fun z ↦ a⁻¹ • f z
  have s : SuperAt g (orderAt f 0) :=
    { d2
      fa0 := analyticAt_const.mul fa
      fd := by rw [orderAt_const_smul (inv_ne_zero a0)]
      fc := by rw [leadingCoeff_const_smul]; simp only [smul_eq_mul, inv_mul_cancel₀ a0, a] }
  rcases s.not_local_inj with ⟨h, ha, h0, e⟩
  use h, ha, h0; refine e.mp (.of_forall ?_)
  intro z ⟨h0, hz⟩; use h0
  exact (IsUnit.smul_left_cancel (Ne.isUnit (inv_ne_zero a0))).mp hz

/-- If `f' z = 0`, then every value near `f z` is achieved at least twice (`ℂ → ℂ` version).
    We operationalize this statement via a nontrivial function `g : ℂ → ℂ` s.t. `f (g w) = f w`
    near `z`. -/
theorem not_local_inj_of_deriv_zero {f : ℂ → ℂ} {c : ℂ} (fa : AnalyticAt ℂ f c)
    (df : HasDerivAt f 0 c) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g c ∧ g c = c ∧ ∀ᶠ z in 𝓝[{c}ᶜ] c, g z ≠ z ∧ f (g z) = f z := by
  set f' := fun z ↦ f (z + c) - f c
  have fa' : AnalyticAt ℂ f' 0 :=
    AnalyticAt.sub
      (AnalyticAt.comp (by simp only [zero_add, fa]) (analyticAt_id.add analyticAt_const))
      analyticAt_const
  have df' : HasDerivAt f' (0 * 1) 0 := by
    refine HasDerivAt.sub_const _ ?_
    have e : (fun z ↦ f (z + c)) = f ∘ fun z ↦ z + c := rfl
    rw [e]; apply HasDerivAt.comp; simp only [zero_add, df]
    exact HasDerivAt.add_const _ (hasDerivAt_id _)
  simp only [MulZeroClass.zero_mul] at df'
  have f0' : (fun z ↦ f (z + c) - f c) 0 = 0 := by simp only [zero_add, sub_self]
  rcases not_local_inj_of_deriv_zero' fa' df' f0' with ⟨g, ga, e, h⟩; clear fa df fa' df'
  refine ⟨fun z ↦ g (z - c) + c, ?_, ?_, ?_⟩
  · exact AnalyticAt.add (AnalyticAt.comp (by simp only [sub_self, ga])
      (analyticAt_id.sub analyticAt_const)) analyticAt_const
  · simp only [sub_self, e, zero_add]
  · simp only [eventually_nhdsWithin_iff] at h ⊢
    have sc : Tendsto (fun z ↦ z - c) (𝓝 c) (𝓝 0) := by
      rw [← sub_self c]; exact continuousAt_id.sub continuousAt_const
    refine (sc.eventually h).mp (.of_forall ?_)
    simp only [mem_compl_singleton_iff, sub_ne_zero]
    intro z h zc; rcases h zc with ⟨gz, ff⟩; constructor
    contrapose gz; nth_rw 2 [← gz]; ring
    simp only [sub_left_inj, sub_add_cancel, f'] at ff; exact ff

/-- If `f' z = 0`, then every value near `f z` is achieved at least twice (manifold version).
    We operationalize this statement via a nontrivial function `g : S → T` s.t. `f (g w) = f w`
    near `z`. -/
public theorem not_local_inj_of_mfderiv_zero {f : S → T} {c : S} (fa : ContMDiffAt I I ω f c)
    (df : mfderiv I I f c = 0) :
    ∃ g : S → S, ContMDiffAt I I ω g c ∧ g c = c ∧ ∀ᶠ z in 𝓝[{c}ᶜ] c, g z ≠ z ∧ f (g z) = f z := by
  generalize hg : (fun z ↦ extChartAt I (f c) (f ((extChartAt I c).symm z))) = g
  have dg : mfderiv I I g (extChartAt I c c) = 0 := by
    have fd : MDifferentiableAt I I f ((extChartAt I c).symm (extChartAt I c c)) := by
      rw [PartialEquiv.left_inv]
      exact fa.mdifferentiableAt (by decide)
      apply mem_extChartAt_source
    rw [← hg, ←Function.comp_def, ← Function.comp_def,
      mfderiv_comp _ ((contMDiffAt_extChartAt' _).mdifferentiableAt one_ne_zero) _,
      mfderiv_comp _ fd (((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' _)).mdifferentiableAt one_ne_zero),
      PartialEquiv.left_inv, df, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]
    · apply mem_extChartAt_source
    · apply mem_extChartAt_target
    · simp
    · exact MDifferentiableAt.comp _ fd
        (((contMDiffOn_extChartAt_symm _).contMDiffAt
        (extChartAt_target_mem_nhds' (mem_extChartAt_target c))).mdifferentiableAt one_ne_zero)
  simp only [mAnalyticAt_iff_of_boundaryless, Function.comp_def, hg] at fa
  have dg' := fa.2.differentiableAt.mdifferentiableAt.hasMFDerivAt
  rw [dg, hasMFDerivAt_iff_hasFDerivAt] at dg'
  replace dg := dg'.hasDerivAt; clear dg'
  rcases not_local_inj_of_deriv_zero fa.2 dg with ⟨h, ha, h0, e⟩
  refine ⟨fun z ↦ (extChartAt I c).symm (h (extChartAt I c z)), ?_, ?_, ?_⟩
  · apply ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target c))).comp_of_eq
    apply (ha.mAnalyticAt I I).comp_of_eq
      (contMDiffAt_extChartAt' (mem_chart_source _ c)) rfl
    exact h0
  · simp only [h0, PartialEquiv.left_inv _ (mem_extChartAt_source c)]
  · rw [eventually_nhdsWithin_iff] at e ⊢
    apply ((continuousAt_extChartAt c).eventually e).mp
    apply ((isOpen_extChartAt_source c).eventually_mem (mem_extChartAt_source (I := I) c)).mp
    have m1 : ∀ᶠ z in 𝓝 c, h (extChartAt I c z) ∈ (extChartAt I c).target := by
      refine ContinuousAt.eventually_mem ?_ (extChartAt_target_mem_nhds' ?_)
      · exact ha.continuousAt.comp_of_eq (continuousAt_extChartAt c) rfl
      · rw [h0]; exact mem_extChartAt_target c
    have m2 : ∀ᶠ z in 𝓝 c, f z ∈ (extChartAt I (f c)).source :=
      fa.1.eventually_mem (extChartAt_source_mem_nhds _)
    have m3 : ∀ᶠ z in 𝓝 c,
        f ((extChartAt I c).symm (h (extChartAt I c z))) ∈ (extChartAt I (f c)).source := by
      refine ContinuousAt.eventually_mem ?_ (extChartAt_source_mem_nhds' ?_)
      · apply fa.1.comp_of_eq; apply (continuousAt_extChartAt_symm _).comp_of_eq
        apply ha.continuousAt.comp_of_eq; exact continuousAt_extChartAt _
        rfl; exact h0; rw [h0, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
      · rw [h0, PartialEquiv.left_inv _ (mem_extChartAt_source _)]
        apply mem_extChartAt_source
    refine m1.mp (m2.mp (m3.mp (.of_forall ?_)))
    simp only [mem_compl_singleton_iff]
    intro z m3 m2 m1 m0 even zc
    rcases even ((PartialEquiv.injOn _).ne m0 (mem_extChartAt_source c) zc) with ⟨hz, gh⟩
    constructor
    · nth_rw 2 [← PartialEquiv.left_inv _ m0]
      rw [(PartialEquiv.injOn _).ne_iff]; exact hz
      rw [PartialEquiv.symm_source]; exact m1
      rw [PartialEquiv.symm_source]; exact PartialEquiv.map_source _ m0
    · simp only [← hg] at gh
      rw [PartialEquiv.left_inv _ m0] at gh
      rw [(PartialEquiv.injOn _).eq_iff m3 m2] at gh; exact gh

/-- Injectivity on an open set implies nonzero derivative (flat version) -/
public theorem Set.InjOn.deriv_ne_zero {f : ℂ → ℂ} {s : Set ℂ} (inj : InjOn f s) (so : IsOpen s)
    {c : ℂ} (m : c ∈ s) (fa : AnalyticAt ℂ f c) : deriv f c ≠ 0 := by
  contrapose inj
  simp only [InjOn, not_forall] at inj ⊢
  have d := inj ▸ fa.differentiableAt.hasDerivAt
  rcases not_local_inj_of_deriv_zero fa d with ⟨g, ga, gc, fg⟩
  have gm : ∀ᶠ z in 𝓝 c, g z ∈ s :=
    ga.continuousAt.eventually_mem (so.mem_nhds (by simp only [gc, m]))
  replace fg := fg.and (((so.eventually_mem m).and gm).filter_mono nhdsWithin_le_nhds)
  rcases @Filter.Eventually.exists _ _ _ (AnalyticManifold.punctured_nhds_neBot I c) fg
    with ⟨z, ⟨gz, fg⟩, zs, gs⟩
  use g z, gs, z, zs, fg, gz

/-- Injectivity on an open set implies nonzero derivative (manifold version) -/
public theorem Set.InjOn.mfderiv_ne_zero {f : S → T} {s : Set S} (inj : InjOn f s) (so : IsOpen s)
    {c : S} (m : c ∈ s) (fa : ContMDiffAt I I ω f c) : mfderiv I I f c ≠ 0 := by
  contrapose inj
  simp only [InjOn, not_forall] at inj ⊢
  rcases not_local_inj_of_mfderiv_zero fa inj with ⟨g, ga, gc, fg⟩
  have gm : ∀ᶠ z in 𝓝 c, g z ∈ s :=
    ga.continuousAt.eventually_mem (so.mem_nhds (by simp only [gc, m]))
  replace fg := fg.and (((so.eventually_mem m).and gm).filter_mono nhdsWithin_le_nhds)
  rcases @Filter.Eventually.exists _ _ _ (AnalyticManifold.punctured_nhds_neBot I c) fg
    with ⟨z, ⟨gz, fg⟩, zs, gs⟩
  use g z, gs, z, zs, fg, gz
