module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Ray.Manifold.Defs
import Ray.Dynamics.Multiple
import Ray.Manifold.Nontrivial
import Ray.Manifold.OpenMapping
import all Ray.Manifold.Inverse

/-!
## Global inverse functions theorems on 1D complex manifolds

Given a parameterized analytic function `f : ℂ → S → T` where `(c,z) ↦ (c, f c z)` is
injective, there exists a global inverse `g : ℂ → T → S` to `f` with `g c (f c z) = z`.

We prove several versions of this result, with different hypotheses:
1. `global_complex_inverse_fun_open`: `f : ℂ → S → T` is nonsingular and injective on an open set
2. `global_complex_inverse_fun_compact`: `f : S → T` is nonsingular and injective on a compact set
3. `global_complex_inverse_fun_open': `f` is injective on an open set

These results follow straightforwardly by stitching together local inverses, except that
(3) needs the result from `AnalyticManifold.Multiple` that injectivity implies nonzero derivative.
-/

open Classical
open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [cms : IsManifold I ω S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [cmt : IsManifold I ω T]

/-- The global 1D inverse function theorem (parameterized, open case): if `f : ℂ → S → T`
    is nonsingular and injective on an open set `s`, it has a global analytic inverse. -/
public theorem global_complex_inverse_fun_open {f : ℂ → S → T} [Nonempty S] {s : Set (ℂ × S)}
    (fa : ContMDiffOn II I ω (uncurry f) s) (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) s) (so : IsOpen s) :
    ∃ g : ℂ → T → S,
      ContMDiffOnNhd II I (uncurry g) ((fun p : ℂ × S ↦ (p.1, f p.1 p.2)) '' s) ∧
        ∀ p : ℂ × S, p ∈ s → g p.1 (f p.1 p.2) = p.2 := by
  --obtain blah := complex_inverse_fun
  have i : ∀ p : ℂ × S, p ∈ s → ComplexInverseFun.Cinv f p.1 p.2 := by
    intro ⟨c, z⟩ m; exact
      { fa := fa.contMDiffAt (so.mem_nhds m)
        nc := nc _ m }
  generalize hg : (fun c w ↦
    if h : ∃ z, (c, z) ∈ s ∧ f c z = w then choose h else Classical.arbitrary S) = g
  have left : ∀ c z, (c, z) ∈ s → g c (f c z) = z := by
    intro c z m
    have h : ∃ x, (c, x) ∈ s ∧ f c x = f c z := ⟨z, m, rfl⟩
    simp only [← hg, dif_pos h]
    rcases choose_spec h with ⟨m0, w0⟩
    have left := (i _ m).left_inv.self_of_nhds
    simp only at left
    have e : (c, choose h) = (c, (i _ m).g c (f c z)) := by
      refine (inj.eq_iff m0 ?_).mp ?_
      · simp only [left, m]
      · simp only [left, w0]
    rw [left] at e; exact (Prod.ext_iff.mp e).2
  have ge : ∀ (p : ℂ × S) (m : p ∈ s), ∀ᶠ q : ℂ × T in 𝓝 (p.1, f p.1 p.2),
      g q.1 q.2 = (i p m).g q.1 q.2 := by
    intro ⟨c, z⟩ m; simp only
    have n := nontrivialMAnalyticAt_of_mfderiv_ne_zero
      (fa.contMDiffAt (so.mem_nhds m)).along_snd (nc _ m); simp only at n
    simp only [n.nhds_eq_map_nhds_param (fa.contMDiffAt (so.mem_nhds m)), Filter.eventually_map]
    apply (i _ m).left_inv.mp; apply (so.eventually_mem m).mp
    refine .of_forall fun ⟨e, w⟩ wm gf ↦ ?_
    simp only at gf
    simp only [left _ _ wm, gf]
  use g; constructor
  · intro ⟨c, w⟩ wm
    rcases(mem_image _ _ _).mp wm with ⟨⟨c', z⟩, zm, e⟩
    simp only [Prod.ext_iff] at e; simp only [e.1] at e zm; simp only [← e.2]
    exact ((i _ zm).ga.congr_of_eventuallyEq (ge _ zm)).contMDiffWithinAt
  · intro ⟨c, z⟩ m; exact left _ _ m

/-- The global 1D inverse function theorem (compact case): if `f : S → T` is nonsingular and
    injective on a compact set `s`, it has a global analytic inverse. -/
public theorem global_complex_inverse_fun_compact {f : ℂ → S → T} [Nonempty S] [T2Space T]
    {s : Set (ℂ × S)} (fa : ContMDiffOnNhd II I (uncurry f) s)
    (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) s) (sc : IsCompact s) :
    ∃ g : ℂ → T → S,
      ContMDiffOnNhd II I (uncurry g) ((fun p : ℂ × S ↦ (p.1, f p.1 p.2)) '' s) ∧
        ∀ᶠ p : ℂ × S in 𝓝ˢ s, g p.1 (f p.1 p.2) = p.2 := by
  -- Enlarge s while preserving injectivity
  have t : ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) t := by
    apply inj.exists_isOpen_superset sc (fun _ m ↦ continuousAt_fst.prodMk (fa _ m).continuousAt)
    intro ⟨c, z⟩ m; rcases complex_inverse_fun (fa _ m) (nc _ m) with ⟨g, _, gf, _⟩
    rcases eventually_nhds_iff.mp gf with ⟨t, gf, o, m⟩
    use t, o.mem_nhds m; intro ⟨c0, z0⟩ m0 ⟨c1, z1⟩ m1 e
    simp only [Prod.ext_iff] at e ⊢; use e.1
    have e0 := gf _ m0; have e1 := gf _ m1; simp only at e0 e1
    rw [← e0, ← e1, e.2, ← e.1]
  rcases t with ⟨t, ot, st, ti⟩
  -- Shrink t to recover openness and deriv ≠ 0
  set u := t ∩ {p | ContMDiffAt II I ω (uncurry f) p ∧ mfderiv I I (f p.1) p.2 ≠ 0}
  have tu : u ⊆ t := inter_subset_left
  have su : s ⊆ u := subset_inter st (subset_inter fa nc)
  have uo : IsOpen u := by
    apply ot.inter; rw [isOpen_iff_eventually]; intro ⟨c, z⟩ ⟨fa, nc⟩
    refine fa.eventually.mp ((mfderiv_ne_zero_eventually' fa nc).mp (.of_forall ?_))
    intro ⟨c, z⟩ nc fa; use fa, nc
  -- Find our inverse on u
  have fa' : ∀ x ∈ u, ContMDiffAt II I ω (uncurry f) x := fun _ m ↦ (inter_subset_right m).1
  have d0 : ∀ (p : ℂ × S), p ∈ u → mfderiv I I (f p.fst) p.snd ≠ 0 :=
    fun _ m ↦ (inter_subset_right m).2
  rcases global_complex_inverse_fun_open
    (fun x m ↦ (fa' x m).contMDiffWithinAt) d0 (ti.mono tu) uo with ⟨g, ga, gf⟩
  exact ⟨g, ga.mono (image_mono su), Filter.eventually_of_mem (uo.mem_nhdsSet.mpr su) gf⟩

/-- The global 1D inverse function theorem (weak, open case): if `f : S → T` is nonsingular
    and injective on an open set `s`, it has a global analytic inverse (we remove the need
    for nonsingularity below, by deriving it from injectivity). -/
theorem weak_global_complex_inverse_fun_open {f : S → T} [Nonempty S] {s : Set S}
    (fa : ContMDiffOn I I ω f s) (nc : ∀ z, z ∈ s → mfderiv I I f z ≠ 0) (inj : InjOn f s)
    (so : IsOpen s) : ∃ g : T → S, ContMDiffOnNhd I I g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z := by
  set f' := fun (_ : ℂ) (z : S) ↦ f z
  have nc' : ∀ p : ℂ × S, p ∈ (univ : Set ℂ) ×ˢ s → mfderiv I I (f' p.1) p.2 ≠ 0 := by
    intro ⟨c, z⟩ ⟨_, zs⟩; exact nc _ zs
  have inj' : InjOn (fun p : ℂ × S ↦ (p.1, f' p.1 p.2)) (univ ×ˢ s) := by
    intro ⟨c0, z0⟩ ⟨_, zs0⟩ ⟨c1, z1⟩ ⟨_, zs1⟩ h; simp only [Prod.ext_iff] at h zs0 zs1
    rw [h.1, inj zs0 zs1]; exact h.2
  have fa' : ∀ x ∈ univ ×ˢ s, ContMDiffAt II I ω (uncurry f') x := by
    intro ⟨c, z⟩ ⟨_, zs⟩
    exact (fa.contMDiffAt (so.mem_nhds zs)).comp_of_eq contMDiffAt_snd rfl
  rcases global_complex_inverse_fun_open (fun x m ↦ (fa' x m).contMDiffWithinAt)
    nc' inj' (isOpen_univ.prod so) with ⟨g, ga, gf⟩
  use g 0
  constructor
  · intro z ⟨w, m⟩
    exact (ga ⟨0, z⟩ (by aesop)).along_snd
  · intro z m; exact gf ⟨0, z⟩ ⟨mem_univ _, m⟩

/-- The global 1D inverse function theorem (open case): if `f : S → T` is injective on an
    open set `s`, it has a global analytic inverse. -/
public theorem global_complex_inverse_fun_open' {f : S → T} [Nonempty S] {s : Set S}
    (fa : ContMDiffOn I I ω f s) (inj : InjOn f s) (so : IsOpen s) :
    ∃ g : T → S, ContMDiffOnNhd I I g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z :=
  weak_global_complex_inverse_fun_open fa
    (fun _ m ↦ inj.mfderiv_ne_zero so m (fa.contMDiffAt (so.mem_nhds m))) inj so

/-- The global 1D inverse function theorem (open, complex case): if `f : ℂ → ℂ` is injective on an
    open set `s`, it has a global analytic inverse. -/
public theorem global_complex_inverse_fun_open'' {f : ℂ → ℂ} {s : Set ℂ}
    (fa : AnalyticOnNhd ℂ f s) (inj : InjOn f s) (so : IsOpen s) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z := by
  have ⟨g,ga,gf⟩ := global_complex_inverse_fun_open' (f := f) ?_ inj so
  · refine ⟨g, ?_, gf⟩
    intro z m
    exact (ga z m).analyticAt
  · intro z m
    specialize fa z m
    rw [analyticAt_iff_mAnalyticAt (I := I) (J := I)] at fa
    exact fa.contMDiffWithinAt
