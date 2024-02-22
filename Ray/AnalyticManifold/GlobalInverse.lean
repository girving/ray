import Ray.AnalyticManifold.Inverse
import Ray.Dynamics.Multiple

/-!
## Global inverse functions theorems on 1D complex manifolds

Given a parameterized holomorphic function `f : ℂ → S → T` where `(c,z) ↦ (c, f c z)` is
injective, there exists a global inverse `g : ℂ → T → S` to `f` with `g c (f c z) = z`.

We prove several versions of this result, with different hypotheses:
1. `global_complex_inverse_fun_open`: `f : ℂ → S → T` is nonsingular and injective on an open set
2. `global_complex_inverse_fun_compact`: `f : S → T` is nonsingular and injective on a compact set
3. `global_complex_inverse_fun_open': `f` is injective on an open set

These results follow straightforwardly by stitching together local inverses, except that
(3) needs the result from `AnalyticManifold.Multiple` that injectivity implies nonzero derivative.
-/

open Classical
open Filter (eventually_of_forall Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [cms : AnalyticManifold I S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [cmt : AnalyticManifold I T]

/-- The global 1D inverse function theorem (parameterized, open case): if `f : ℂ → S → T`
    is nonsingular and injective on an open set `s`, it has a global holomorphic inverse. -/
theorem global_complex_inverse_fun_open {f : ℂ → S → T} [Nonempty S] {s : Set (ℂ × S)}
    (fa : HolomorphicOn II I (uncurry f) s) (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) s) (so : IsOpen s) :
    ∃ g : ℂ → T → S,
      HolomorphicOn II I (uncurry g) ((fun p : ℂ × S ↦ (p.1, f p.1 p.2)) '' s) ∧
        ∀ p : ℂ × S, p ∈ s → g p.1 (f p.1 p.2) = p.2 := by
  have i : ∀ p : ℂ × S, p ∈ s → ComplexInverseFun.Cinv f p.1 p.2 := by
    intro ⟨c, z⟩ m; exact
      { fa := fa _ m
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
    have n := nontrivialHolomorphicAt_of_mfderiv_ne_zero (fa _ m).along_snd (nc _ m); simp only at n
    simp only [n.nhds_eq_map_nhds_param (fa _ m), Filter.eventually_map]
    apply (i _ m).left_inv.mp; apply (so.eventually_mem m).mp
    apply eventually_of_forall; intro ⟨e, w⟩ wm gf
    simp only at gf
    simp only [left _ _ wm, gf]
  use g; constructor
  · intro ⟨c, w⟩ wm
    rcases(mem_image _ _ _).mp wm with ⟨⟨c', z⟩, zm, e⟩
    simp only [Prod.ext_iff] at e; simp only [e.1] at e zm; simp only [← e.2]
    exact (i _ zm).ga.congr (Filter.EventuallyEq.symm (ge _ zm))
  · intro ⟨c, z⟩ m; exact left _ _ m

/-- The global 1D inverse function theorem (compact case): if `f : S → T` is nonsingular and
    injective on a compact set `s`, it has a global holomorphic inverse. -/
theorem global_complex_inverse_fun_compact {f : ℂ → S → T} [Nonempty S] [T2Space T]
    {s : Set (ℂ × S)} (fa : HolomorphicOn II I (uncurry f) s)
    (nc : ∀ p : ℂ × S, p ∈ s → mfderiv I I (f p.1) p.2 ≠ 0)
    (inj : InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) s) (sc : IsCompact s) :
    ∃ g : ℂ → T → S,
      HolomorphicOn II I (uncurry g) ((fun p : ℂ × S ↦ (p.1, f p.1 p.2)) '' s) ∧
        ∀ᶠ p : ℂ × S in 𝓝ˢ s, g p.1 (f p.1 p.2) = p.2 := by
  -- Enlarge s while preserving injectivity
  have t : ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn (fun p : ℂ × S ↦ (p.1, f p.1 p.2)) t := by
    apply inj.exists_isOpen_superset sc (fun _ m ↦ continuousAt_fst.prod (fa _ m).continuousAt)
    intro ⟨c, z⟩ m; rcases complex_inverse_fun (fa _ m) (nc _ m) with ⟨g, _, gf, _⟩
    rcases eventually_nhds_iff.mp gf with ⟨t, gf, o, m⟩
    use t, o.mem_nhds m; intro ⟨c0, z0⟩ m0 ⟨c1, z1⟩ m1 e
    simp only [uncurry, Prod.ext_iff] at e ⊢; use e.1
    have e0 := gf _ m0; have e1 := gf _ m1; simp only at e0 e1
    rw [← e0, ← e1, e.2, ← e.1]
  rcases t with ⟨t, ot, st, ti⟩
  -- Shrink t to recover openness and deriv ≠ 0
  set u := t ∩ {p | HolomorphicAt II I (uncurry f) p ∧ mfderiv I I (f p.1) p.2 ≠ 0}
  have tu : u ⊆ t := inter_subset_left t _
  have su : s ⊆ u := subset_inter st (subset_inter fa nc)
  have uo : IsOpen u := by
    apply ot.inter; rw [isOpen_iff_eventually]; intro ⟨c, z⟩ ⟨fa, nc⟩
    refine fa.eventually.mp ((mfderiv_ne_zero_eventually' fa nc).mp (eventually_of_forall ?_))
    intro ⟨c, z⟩ nc fa; use fa, nc
  -- Find our inverse on u
  have fa' : HolomorphicOn II I (uncurry f) u := fun _ m ↦ (inter_subset_right _ _ m).1
  have d0 : ∀ (p : ℂ × S), p ∈ u → mfderiv I I (f p.fst) p.snd ≠ 0 :=
    fun _ m ↦ (inter_subset_right _ _ m).2
  rcases global_complex_inverse_fun_open fa' d0 (ti.mono tu) uo with ⟨g, ga, gf⟩
  use g, ga.mono (image_subset _ su), Filter.eventually_of_mem (uo.mem_nhdsSet.mpr su) gf

/-- The global 1D inverse function theorem (weak, open case): if `f : S → T` is nonsingular
    and injective on an open set `s`, it has a global holomorphic inverse (we remove the need
    for nonsingularity below, by deriving it from injectivity). -/
theorem weak_global_complex_inverse_fun_open {f : S → T} [Nonempty S] {s : Set S}
    (fa : HolomorphicOn I I f s) (nc : ∀ z, z ∈ s → mfderiv I I f z ≠ 0) (inj : InjOn f s)
    (so : IsOpen s) : ∃ g : T → S, HolomorphicOn I I g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z := by
  set f' := fun (_ : ℂ) (z : S) ↦ f z
  have nc' : ∀ p : ℂ × S, p ∈ (univ : Set ℂ) ×ˢ s → mfderiv I I (f' p.1) p.2 ≠ 0 := by
    intro ⟨c, z⟩ ⟨_, zs⟩; exact nc _ zs
  have inj' : InjOn (fun p : ℂ × S ↦ (p.1, f' p.1 p.2)) (univ ×ˢ s) := by
    intro ⟨c0, z0⟩ ⟨_, zs0⟩ ⟨c1, z1⟩ ⟨_, zs1⟩ h; simp only [Prod.ext_iff] at h zs0 zs1
    rw [h.1, inj zs0 zs1]; exact h.2
  have fa' : HolomorphicOn II I (uncurry f') (univ ×ˢ s) := by
    intro ⟨c, z⟩ ⟨_, zs⟩; exact (fa z zs).comp_of_eq holomorphicAt_snd rfl
  rcases global_complex_inverse_fun_open fa' nc' inj' (isOpen_univ.prod so) with ⟨g, ga, gf⟩
  use g 0; constructor
  · intro z ⟨w, m⟩; refine (ga ⟨0, z⟩ ⟨⟨0, w⟩, ⟨mem_univ _, m.1⟩, ?_⟩).along_snd
    simp only [Prod.ext_iff, eq_self_iff_true, true_and_iff]; exact m.2
  · intro z m; exact gf ⟨0, z⟩ ⟨mem_univ _, m⟩

/-- The global 1D inverse function theorem (open case): if `f : S → T` is injective on an
    open set `s`, it has a global holomorphic inverse. -/
theorem global_complex_inverse_fun_open' {f : S → T} [Nonempty S] {s : Set S}
    (fa : HolomorphicOn I I f s) (inj : InjOn f s) (so : IsOpen s) :
    ∃ g : T → S, HolomorphicOn I I g (f '' s) ∧ ∀ z, z ∈ s → g (f z) = z :=
  weak_global_complex_inverse_fun_open fa (fun z m ↦ inj.mfderiv_ne_zero so m (fa z m)) inj so
