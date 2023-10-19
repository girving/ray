import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.RingTheory.RootsOfUnity.Complex
import Ray.Misc.Connected
import Ray.Analytic.Holomorphic
import Ray.AnalyticManifold.OneDimension
import Ray.Misc.TotallyDisconnected
import Ray.Tactic.Bound

/-!
## Nontriviality of holomorphic functions, and consequences

We define several structures representing global and local nontriviality (nonconstness)
of analytic and holomorphic functions, and in 1D or parameterized 1D:

1. `NontrivialAnalyticOn f s`: Near every point `z ∈ s`, `f` is locally holomorphic and nonconstant
1. `NontrivialHolomorphicOn f s`: The same for holomorphic functions between 1D analytic manifolds
2. `NontrivialHolomorphicAt f z`: Near `z`, `f` is holomorphic and nonconstant

These "everyone nontrivial" properties can be derived from properties at one point:

1. If an analytic function is nonconstant on a preconnected set, is it nontrivial there
2. Nonzero holomorphic derivative implies nontriviality
3. Nontriviality is preserved by composition
4. If a composition is nontrivial, both parts are nontrivial
5. `id` is nontrivial
6. Positive `orderAt` implies nontrivial

From these, we have a variety of consequences, such as:

1. Nontrivial functions have isolated zeros or other values.
2. The zeros (or preimages of another value) of a nontrivial function have a discrete topology
3. Pow is nontrivial, so roots of unity are totally disconnected
4. If a nontrivial function is constant on the image of a preconnected set, the image is a singleton
5. Near a point, holomorphic functions are either locally constant or locally ≠ to the point value
6. Locally constant functions are constant on preconnected sets
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Classical
open Complex (abs)
open Filter (Tendsto eventually_of_forall)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball isClosed_ball mem_ball mem_closedBall mem_ball_self
  mem_closedBall_self mem_sphere sphere)
open OneDimension
open Set
open scoped Real Topology Manifold
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [cms : AnalyticManifold I S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [cmt : AnalyticManifold I T]
variable {U : Type} [TopologicalSpace U] [ChartedSpace ℂ U] [cmu : AnalyticManifold I U]

section Nontrivial

variable {f : ℂ → ℂ} {s : Set ℂ}

/-- A nontrivial analytic function is one which is not locally constant -/
structure NontrivialAnalyticOn (f : ℂ → ℂ) (s : Set ℂ) : Prop where
  analyticOn : AnalyticOn ℂ f s
  nonconst : ∀ x, x ∈ s → ∃ᶠ y in 𝓝 x, f y ≠ f x

/-- Nontrivial analytic functions have isolated values -/
theorem NontrivialAnalyticOn.isolated (n : NontrivialAnalyticOn f s) {z : ℂ} (zs : z ∈ s) :
    ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ f z := by
  have fa : AnalyticAt ℂ (fun w ↦ f w - f z) z := (n.analyticOn z zs).sub analyticAt_const
  cases' fa.eventually_eq_zero_or_eventually_ne_zero with h h
  · have b := h.and_frequently (n.nonconst z zs)
    simp only [sub_eq_zero, Ne.def, and_not_self_iff, Filter.frequently_false] at b
  · simp only [sub_ne_zero] at h; exact h

/-- Nontrivial analytic functions have isolated values -/
theorem NontrivialAnalyticOn.isolated' (n : NontrivialAnalyticOn f s) {z : ℂ} (zs : z ∈ s) (a : ℂ) :
    ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ a := by
  by_cases h : f z = a; simp only [← h]; exact n.isolated zs
  exact ((n.analyticOn _ zs).continuousAt.eventually_ne h).filter_mono nhdsWithin_le_nhds

/-- Nonconstant functions on preconnected sets are nontrivial -/
theorem IsPreconnected.nontrivialAnalyticOn (p : IsPreconnected s) (fa : AnalyticOn ℂ f s)
    (ne : ∃ a b, a ∈ s ∧ b ∈ s ∧ f a ≠ f b) : NontrivialAnalyticOn f s :=
  { analyticOn := fa
    nonconst := by
      contrapose ne; simp only [not_forall, Filter.not_frequently, not_not] at ne
      rcases ne with ⟨z, zs, h⟩
      simp only [not_exists, exists_and_left, not_and, not_not]
      have h' := (h.filter_mono (nhdsWithin_le_nhds (s := {z}ᶜ))).frequently
      have e := fa.eqOn_of_preconnected_of_frequently_eq analyticOn_const p zs h'
      intro x xs y ys; rw [e xs, e ys] }

/-- Nonconstant entire functions are nontrivial -/
theorem Entire.nontrivialAnalyticOn (fa : AnalyticOn ℂ f univ) (ne : ∃ a b, f a ≠ f b) :
    NontrivialAnalyticOn f univ := by
  refine' isPreconnected_univ.nontrivialAnalyticOn fa _; simpa only [Set.mem_univ, true_and_iff]

/-- The roots of a nontrivial analytic function form a discrete topology -/
theorem NontrivialAnalyticOn.discreteTopology (n : NontrivialAnalyticOn f s) (a : ℂ) :
    DiscreteTopology (↥(s ∩ f ⁻¹' {a})) := by
  rw [← singletons_open_iff_discrete]; intro ⟨z, m⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at m
  by_cases h : ∃ᶠ z in 𝓝[{z}ᶜ] z, f z = a
  · have i := (n.isolated' m.1 a).and_frequently h
    simp only [not_and_self_iff, Filter.frequently_const] at i
  · simp only [Filter.not_frequently, eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at h
    rcases eventually_nhds_iff.mp h with ⟨t, t0, o, tz⟩
    simp only [isOpen_induced_iff]; use t, o
    apply Set.ext; intro ⟨w, m⟩
    simp only [Set.mem_preimage, Subtype.coe_mk, Set.mem_singleton_iff, Subtype.mk_eq_mk]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at m
    specialize t0 w
    simp only [m.2, imp_false, eq_self_iff_true, not_true, not_not] at t0
    use t0; intro wz; rw [wz]; exact tz

/-- pow is nontrivial -/
theorem powNontrivial {d : ℕ} (dp : d > 0) : NontrivialAnalyticOn (fun z ↦ z ^ d) univ := by
  apply Entire.nontrivialAnalyticOn fun _ _ ↦ (analyticAt_id _ _).pow _; use 0, 1
  simp only [id, one_pow, zero_pow dp, Pi.pow_def]; norm_num

/-- All roots of unity as a set -/
def allRootsOfUnity :=
  {z : ℂ | ∃ n : ℕ, n ≠ 0 ∧ z ^ n = 1}

/-- Roots of unity are nonzero -/
theorem allRootsOfUnity.ne_zero {z : ℂ} (m : z ∈ allRootsOfUnity) : z ≠ 0 := by
  rcases m with ⟨n, n0, z1⟩; contrapose z1; simp only [not_not] at z1
  simp only [z1, zero_pow' _ n0]; exact zero_ne_one

/-- Roots of unity are totally disconnected -/
theorem IsTotallyDisconnected.allRootsOfUnity : IsTotallyDisconnected allRootsOfUnity := by
  apply IsCountable.isTotallyDisconnected
  simp only [_root_.allRootsOfUnity, setOf_exists]; apply countable_iUnion; intro n
  by_cases n0 : n = 0
  simp only [n0, Ne.def, eq_self_iff_true, not_true, false_and_iff, setOf_false, countable_empty]
  simp only [Ne.def, n0, not_false_iff, true_and_iff]
  have np : 0 < n := Nat.pos_of_ne_zero n0
  set n' : ℕ+ := ⟨n, np⟩
  have e : {z : ℂ | z ^ n = 1} ⊆ (fun x : ℂˣ ↦ (x : ℂ)) '' (rootsOfUnity n' ℂ : Set ℂˣ) := by
    intro z e; simp only [mem_setOf] at e
    simp only [mem_image, SetLike.mem_coe, mem_rootsOfUnity, PNat.mk_coe]
    by_cases z0 : z = 0
    · simp only [z0, zero_pow' _ n0, zero_ne_one] at e
    use Units.mk0 z z0
    simp only [Units.val_mk0, eq_self_iff_true, and_true_iff, ← Units.eq_iff,
      Units.val_pow_eq_pow_val, Units.val_one, e]
  apply Set.Countable.mono e; clear e; apply Countable.image; apply Set.Finite.countable
  rw [Set.finite_def]; exact ⟨_root_.rootsOfUnity.fintype ℂ n'⟩

/-- Given continuous `p : X → ℂ` on preconnected `X`, `p` is const if `f ∘ p` is const -/
theorem NontrivialAnalyticOn.const (n : NontrivialAnalyticOn f s) {p : X → ℂ} {t : Set X}
    (tc : IsPreconnected t) (pc : ContinuousOn p t) (ps : Set.MapsTo p t s) {a b : ℂ}
    (p1 : ∃ x, x ∈ t ∧ p x = a) (fp : ∀ x, x ∈ t → f (p x) = b) : ∀ x, x ∈ t → p x = a := by
  have disc : DiscreteTopology (↥(s ∩ f ⁻¹' {b})) := n.discreteTopology b
  rcases p1 with ⟨z, zt, z1⟩; simp only [← z1]
  intro x xt
  refine @IsPreconnected.constant_of_mapsTo _ _ _ _ _ tc _ disc _ pc ?_ _ _ xt zt
  intro y yt; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  use ps yt, fp _ yt

/-- Given `p : X → ℂ`, `p^d = 1 → p = 1` given continuity, `X` preconnected,
    and `p = 1` somewhere -/
theorem eq_one_of_pow_eq_one {p : X → ℂ} {t : Set X} {d : ℕ} (pc : ContinuousOn p t)
    (tc : IsPreconnected t) (dp : d > 0) (pa : ∃ x, x ∈ t ∧ p x = 1)
    (pd : ∀ x, x ∈ t → p x ^ d = 1) : ∀ x, x ∈ t → p x = 1 :=
  (powNontrivial dp).const tc pc (Set.mapsTo_univ _ _) pa pd

/-- Given `p, q : X → ℂ`, `p^d = q^d → p ≠ 0 → p = q` -/
theorem eq_of_pow_eq {p q : X → ℂ} {t : Set X} {d : ℕ} (pc : ContinuousOn p t)
    (qc : ContinuousOn q t) (tc : IsPreconnected t) (dp : d > 0) (pq : ∃ x, x ∈ t ∧ p x = q x)
    (p0 : ∀ x, x ∈ t → p x ≠ 0) (pqd : ∀ x, x ∈ t → p x ^ d = q x ^ d) :
    ∀ x, x ∈ t → p x = q x := by
  set r := fun x ↦ q x / p x
  have rc : ContinuousOn r t := qc.div pc p0
  have h := eq_one_of_pow_eq_one rc tc dp ?_ ?_
  · intro x m; exact ((div_eq_one_iff_eq (p0 _ m)).mp (h _ m)).symm
  · rcases pq with ⟨x, m, e⟩; use x, m; exact (div_eq_one_iff_eq (p0 _ m)).mpr e.symm
  · intro x m; simp only [div_pow]; rw [div_eq_one_iff_eq]; exact (pqd _ m).symm
    exact pow_ne_zero _ (p0 _ m)

/-- At a point, a holomorphic function is either locally constant or locally different from its
    value at the point.  This is the `HolomorphicAt` version of
    `AnalyticAt.eventuallyEq_or_eventually_ne` -/
theorem HolomorphicAt.eventually_eq_or_eventually_ne [T2Space T] {f g : S → T} {z : S}
    (fa : HolomorphicAt I I f z) (ga : HolomorphicAt I I g z) :
    (∀ᶠ w in 𝓝 z, f w = g w) ∨ ∀ᶠ w in 𝓝[{z}ᶜ] z, f w ≠ g w := by
  simp only [holomorphicAt_iff, Function.comp] at fa ga
  rcases fa with ⟨fc, fa⟩; rcases ga with ⟨gc, ga⟩
  by_cases fg : f z ≠ g z
  · right; contrapose fg; simp only [not_not]
    simp only [Filter.not_eventually, not_not] at fg
    exact tendsto_nhds_unique_of_frequently_eq fc gc (fg.filter_mono nhdsWithin_le_nhds)
  simp only [not_not] at fg
  cases' fa.eventually_eq_or_eventually_ne ga with e e
  · left; clear fa ga
    replace e := (continuousAt_extChartAt I z).eventually e
    replace e := Filter.EventuallyEq.fun_comp e (_root_.extChartAt I (f z)).symm
    apply e.congr; simp only [Function.comp]; clear e
    apply (fc.eventually_mem (isOpen_extChartAt_source I (f z)) (mem_extChartAt_source I (f z))).mp
    apply (gc.eventually_mem (isOpen_extChartAt_source I (g z)) (mem_extChartAt_source I (g z))).mp
    refine' eventually_nhds_iff.mpr ⟨(_root_.extChartAt I z).source,
      fun x m gm fm ↦ _, isOpen_extChartAt_source _ _, mem_extChartAt_source I z⟩
    simp only at fm gm; rw [← fg] at gm
    simp only [← fg, LocalEquiv.left_inv _ m, LocalEquiv.left_inv _ fm, LocalEquiv.left_inv _ gm]
  · right; clear fa ga
    simp only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at e ⊢
    replace e := (continuousAt_extChartAt I z).eventually e
    apply (fc.eventually_mem (isOpen_extChartAt_source I (f z)) (mem_extChartAt_source I (f z))).mp
    apply (gc.eventually_mem (isOpen_extChartAt_source I (g z)) (mem_extChartAt_source I (g z))).mp
    apply ((isOpen_extChartAt_source I z).eventually_mem (mem_extChartAt_source I z)).mp
    refine' e.mp (eventually_of_forall _); clear e
    intro x h xm gm fm xz; rw [← fg] at gm
    simp only [← fg, LocalEquiv.left_inv _ xm] at h
    specialize h ((LocalEquiv.injOn _).ne xm (mem_extChartAt_source _ _) xz)
    rwa [← (LocalEquiv.injOn _).ne_iff fm gm]

/-- Locally constant functions are constant on preconnected sets -/
theorem HolomorphicOn.const_of_locally_const [T2Space T] {f : S → T} {s : Set S}
    (fa : HolomorphicOn I I f s) {z : S} {a : T} (zs : z ∈ s) (o : IsOpen s) (p : IsPreconnected s)
    (c : ∀ᶠ w in 𝓝 z, f w = a) : ∀ w, w ∈ s → f w = a := by
  set t := {z | z ∈ s ∧ ∀ᶠ w in 𝓝 z, f w = a}
  suffices st : s ⊆ t; exact fun z m ↦ (st m).2.self
  refine p.subset_of_closure_inter_subset ?_ ?_ ?_
  · rw [isOpen_iff_eventually]; intro z m; simp only [Set.mem_setOf_eq] at m ⊢
    exact ((o.eventually_mem m.1).and m.2.eventually_nhds).mp (eventually_of_forall fun y h ↦ h)
  · use z; simp only [Set.mem_inter_iff]; exact ⟨zs, zs, c⟩
  · intro z m; simp only [Set.mem_inter_iff, mem_closure_iff_frequently] at m
    have aa : HolomorphicAt I I (fun _ ↦ a) z := holomorphicAt_const
    cases' (fa _ m.2).eventually_eq_or_eventually_ne aa with h h; use m.2, h
    simp only [eventually_nhdsWithin_iff, Set.mem_compl_singleton_iff] at h
    have m' := m.1; contrapose m'; simp only [Filter.not_frequently]
    refine' h.mp (eventually_of_forall _); intro x i
    by_cases xz : x = z; rwa [xz]; specialize i xz; contrapose i
    simp only [not_not] at i ⊢; exact i.2.self

/-- If `S` is locally connected, we don't need the open assumption in
    `HolomorphicOn.const_of_locally_const` -/
theorem HolomorphicOn.const_of_locally_const' [LocallyConnectedSpace S] [T2Space T] {f : S → T}
    {s : Set S} (fa : HolomorphicOn I I f s) {z : S} {a : T} (zs : z ∈ s) (p : IsPreconnected s)
    (c : ∀ᶠ w in 𝓝 z, f w = a) : ∀ w, w ∈ s → f w = a := by
  rcases local_preconnected_nhdsSet p (isOpen_holomorphicAt.mem_nhdsSet.mpr fa)
    with ⟨u, uo, su, ua, uc⟩
  exact fun w ws ↦ HolomorphicOn.const_of_locally_const (fun _ m ↦ ua m) (su zs) uo uc c w (su ws)

/-- A holomorphic function that is nonconstant near a point -/
structure NontrivialHolomorphicAt (f : S → T) (z : S) : Prop where
  holomorphicAt : HolomorphicAt I I f z
  nonconst : ∃ᶠ w in 𝓝 z, f w ≠ f z

/-- `NontrivialHolomorphicAt f z` implies `f z` is never locally repeated -/
theorem NontrivialHolomorphicAt.eventually_ne [T2Space T] {f : S → T} {z : S}
    (n : NontrivialHolomorphicAt f z) : ∀ᶠ w in 𝓝 z, w ≠ z → f w ≠ f z := by
  have ca : _root_.HolomorphicAt I I (fun _ ↦ f z) z := holomorphicAt_const
  cases' n.holomorphicAt.eventually_eq_or_eventually_ne ca with h h
  · have b := h.and_frequently n.nonconst
    simp only [and_not_self_iff, Filter.frequently_false] at b
  · simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] at h; convert h

/-- `f` is nontrivial holomorphic everyone in `s` -/
def NontrivialHolomorphicOn (f : S → T) (s : Set S) : Prop :=
  ∀ z, z ∈ s → NontrivialHolomorphicAt f z

/-- Nontrivially at a point of a preconnected set implies nontriviality throughout the set -/
theorem NontrivialHolomorphicAt.on_preconnected [T2Space T] {f : S → T} {s : Set S} {z : S}
    (fa : HolomorphicOn I I f s) (zs : z ∈ s) (o : IsOpen s) (p : IsPreconnected s)
    (n : NontrivialHolomorphicAt f z) : NontrivialHolomorphicOn f s := by
  intro w ws; replace n := n.nonconst; refine' ⟨fa _ ws, _⟩; contrapose n
  simp only [Filter.not_frequently, not_not] at n ⊢; generalize ha : f w = a
  rw [ha] at n
  rw [eventually_nhds_iff]; refine' ⟨s, _, o, zs⟩
  have c := fa.const_of_locally_const ws o p n
  intro x m; rw [c _ m, c _ zs]

/-- If a `f` is nontrivial at `z`, it is nontrivial near `z` -/
theorem NontrivialHolomorphicAt.eventually [T2Space T] {f : S → T} {z : S}
    (n : NontrivialHolomorphicAt f z) : ∀ᶠ w in 𝓝 z, NontrivialHolomorphicAt f w := by
  have lc : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace ℂ _
  rcases eventually_nhds_iff.mp n.holomorphicAt.eventually with ⟨s, fa, os, zs⟩
  rcases locallyConnectedSpace_iff_open_connected_subsets.mp lc z s (os.mem_nhds zs) with
    ⟨t, ts, ot, zt, ct⟩
  rw [eventually_nhds_iff]; refine' ⟨t, _, ot, zt⟩
  exact n.on_preconnected (HolomorphicOn.mono fa ts) zt ot ct.isPreconnected

/-- If the derivative isn't zero, we're nontrivial -/
theorem nontrivialHolomorphicAt_of_mfderiv_ne_zero {f : S → T} {z : S} (fa : HolomorphicAt I I f z)
    (d : mfderiv I I f z ≠ 0) : NontrivialHolomorphicAt f z := by
  refine' ⟨fa, _⟩; contrapose d; simp only [Filter.not_frequently, not_not] at d ⊢
  generalize ha : f z = a; rw [ha] at d; apply HasMFDerivAt.mfderiv
  exact (hasMFDerivAt_const I I a _).congr_of_eventuallyEq d

/-- If `f` and `g` are nontrivial, `f ∘ g` is nontrivial -/
theorem NontrivialHolomorphicAt.comp [T2Space U] {f : T → U} {g : S → T} {z : S}
    (fn : NontrivialHolomorphicAt f (g z)) (gn : NontrivialHolomorphicAt g z) :
    NontrivialHolomorphicAt (fun z ↦ f (g z)) z := by
  use fn.holomorphicAt.comp gn.holomorphicAt
  convert gn.nonconst.and_eventually (gn.holomorphicAt.continuousAt.eventually fn.eventually_ne)
  tauto

/-- If `f ∘ g` is nontrivial, and `f, g` are holomorphic, `f, g` are nontrivial -/
theorem NontrivialHolomorphicAt.anti {f : T → U} {g : S → T} {z : S}
    (h : NontrivialHolomorphicAt (fun z ↦ f (g z)) z) (fa : HolomorphicAt I I f (g z))
    (ga : HolomorphicAt I I g z) :
    NontrivialHolomorphicAt f (g z) ∧ NontrivialHolomorphicAt g z := by
  replace h := h.nonconst; refine' ⟨⟨fa, _⟩, ⟨ga, _⟩⟩
  · contrapose h; simp only [Filter.not_frequently, not_not] at h ⊢
    exact (ga.continuousAt.eventually h).mp (eventually_of_forall fun _ h ↦ h)
  · contrapose h; simp only [Filter.not_frequently, not_not] at h ⊢
    exact h.mp (eventually_of_forall fun x h ↦ by rw [h])

/-- `id` is nontrivial -/
-- There's definitely a better way to prove this, but I'm blanking at the moment.
theorem nontrivialHolomorphicAt_id (z : S) : NontrivialHolomorphicAt (fun w ↦ w) z := by
  use holomorphicAt_id
  rw [Filter.frequently_iff]; intro s sz
  rcases mem_nhds_iff.mp sz with ⟨t, ts, ot, zt⟩
  set u := (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t
  have uo : IsOpen u :=
    (continuousOn_extChartAt_symm I z).preimage_open_of_open (extChartAt_open_target _ _) ot
  have zu : extChartAt I z z ∈ u := by
    simp only [mem_inter_iff, mem_extChartAt_target, true_and_iff, mem_preimage,
      LocalEquiv.left_inv _ (mem_extChartAt_source I z), zt]
  rcases Metric.isOpen_iff.mp uo _ zu with ⟨r, rp, ru⟩
  generalize ha : extChartAt I z z + r / 2 = a
  have au : a ∈ u := by
    rw [← ha]; apply ru; simp only [Metric.mem_ball, Complex.dist_eq, add_sub_cancel']
    simp only [map_div₀, Complex.abs_ofReal, abs_of_pos rp, Complex.abs_two]; exact half_lt_self rp
  use(extChartAt I z).symm a; simp only [mem_inter_iff, mem_preimage] at au
  use ts au.2
  rw [← (LocalEquiv.injOn _).ne_iff ((extChartAt I z).map_target au.1) (mem_extChartAt_source I z)]
  rw [LocalEquiv.right_inv _ au.1, ← ha]
  simp only [Ne.def, add_right_eq_self, div_eq_zero_iff, Complex.ofReal_eq_zero, bit0_eq_zero,
    one_ne_zero, or_false_iff, rp.ne', not_false_iff]; norm_num

/-- If `orderAt f z ≠ 0` (`f` has a zero of positive order), then `f` is nontrivial at `z` -/
theorem nontrivialHolomorphicAt_of_order {f : ℂ → ℂ} {z : ℂ} (fa : AnalyticAt ℂ f z)
    (h : orderAt f z ≠ 0) : NontrivialHolomorphicAt f z := by
  use fa.holomorphicAt I I; contrapose h
  simp only [Filter.not_frequently, not_not] at h ⊢
  have fp : HasFPowerSeriesAt f (constFormalMultilinearSeries ℂ ℂ (f z)) z :=
    hasFPowerSeriesAt_const.congr (Filter.EventuallyEq.symm h)
  simp only [fp.orderAt_unique]; by_contra p0
  have b := FormalMultilinearSeries.apply_order_ne_zero' p0
  simp only [constFormalMultilinearSeries_apply p0, Ne.def, eq_self_iff_true, not_true] at b

/-- `NontrivialAnalyticOn → NontrivialHolomorphicOn` over `ℂ` -/
theorem NontrivialAnalyticOn.nontrivialHolomorphicOn {f : ℂ → ℂ} {s : Set ℂ}
    (n : NontrivialAnalyticOn f s) : NontrivialHolomorphicOn f s := fun z m ↦
  { holomorphicAt := (n.analyticOn z m).holomorphicAt I I
    nonconst := n.nonconst z m }

/-- pow is nontrivial -/
theorem nontrivialHolomorphicAtPow {d : ℕ} (d0 : d > 0) {z : ℂ} :
    NontrivialHolomorphicAt (fun z ↦ z ^ d) z :=
  (powNontrivial d0).nontrivialHolomorphicOn z (mem_univ _)

/-- Nontriviality is invariant to positive powers -/
theorem NontrivialHolomorphicAt.pow_iff {f : S → ℂ} {z : S} {d : ℕ} (fa : HolomorphicAt I I f z)
    (d0 : 0 < d) : NontrivialHolomorphicAt (fun z ↦ f z ^ d) z ↔ NontrivialHolomorphicAt f z := by
  refine' ⟨_, (nontrivialHolomorphicAtPow d0).comp⟩
  have pa : HolomorphicAt I I (fun z ↦ z ^ d) (f z) := HolomorphicAt.pow holomorphicAt_id
  intro h; refine' (NontrivialHolomorphicAt.anti _ pa fa).2; exact h

/-- Nontriviality depends only locally on `f` -/
theorem NontrivialHolomorphicAt.congr {f g : S → T} {z : S} (n : NontrivialHolomorphicAt f z)
    (e : f =ᶠ[𝓝 z] g) : NontrivialHolomorphicAt g z := by
  use n.holomorphicAt.congr e
  refine' n.nonconst.mp (e.mp (eventually_of_forall fun w ew n ↦ _))
  rwa [← ew, ← e.self]

section EqOfLocallyEq

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {A : Type} [TopologicalSpace A] {J : ModelWithCorners ℂ E A}
  [ModelWithCorners.Boundaryless J]
variable {B : Type} [TopologicalSpace B] {K : ModelWithCorners ℂ F B}
  [ModelWithCorners.Boundaryless K]
variable {M : Type} [TopologicalSpace M] [ChartedSpace A M] [AnalyticManifold J M]
variable {N : Type} [TopologicalSpace N] [ChartedSpace B N] [AnalyticManifold K N]

/-- If two holomorphic functions are equal locally, they are equal on preconnected sets.

    This is a manifold version of `AnalyticOn.eqOn_of_preconnected_of_eventuallyEq`.
    This is the one higher dimension result in this file, which shows up in that `e`
    requires `f =ᶠ[𝓝 x] g` everywhere near a point rather than only frequent equality
    as would be required in 1D. -/
theorem HolomorphicOn.eq_of_locally_eq {f g : M → N} [T2Space N] {s : Set M}
    (fa : HolomorphicOn J K f s) (ga : HolomorphicOn J K g s) (sp : IsPreconnected s)
    (e : ∃ x, x ∈ s ∧ f =ᶠ[𝓝 x] g) : f =ᶠ[𝓝ˢ s] g := by
  set t := {x | f =ᶠ[𝓝 x] g}
  suffices h : s ⊆ interior t
  · simp only [subset_interior_iff_mem_nhdsSet, ← Filter.eventually_iff] at h
    exact h.mp (eventually_of_forall fun _ e ↦ e.self)
  apply sp.relative_clopen; · exact e
  · intro x ⟨_, xt⟩; rw [mem_interior_iff_mem_nhds]; exact xt.eventually_nhds
  · intro x ⟨xs, xt⟩; rw [mem_closure_iff_frequently] at xt
    have ex' : ∃ᶠ y in 𝓝 x, f y = g y := xt.mp (eventually_of_forall fun _ e ↦ e.self)
    have ex : f x = g x :=
      tendsto_nhds_unique_of_frequently_eq (fa _ xs).continuousAt (ga _ xs).continuousAt ex'
    generalize hd : (fun y : E ↦
      extChartAt K (f x) (f ((extChartAt J x).symm y)) -
        extChartAt K (g x) (g ((extChartAt J x).symm y))) = d
    generalize hz : extChartAt J x x = z
    suffices h : d =ᶠ[𝓝 z] 0
    · simp only [← hz, ← extChartAt_map_nhds' J x, Filter.eventually_map, Filter.EventuallyEq] at h
      refine'
        h.mp (((isOpen_extChartAt_source J x).eventually_mem (mem_extChartAt_source J x)).mp _)
      apply ((fa _ xs).continuousAt.eventually_mem (isOpen_extChartAt_source _ _)
          (mem_extChartAt_source K (f x))).mp
      apply ((ga _ xs).continuousAt.eventually_mem (isOpen_extChartAt_source _ _)
          (mem_extChartAt_source K (g x))).mp
      refine' eventually_of_forall fun y gm fm m e ↦ _
      rw [← hd, Pi.zero_apply, sub_eq_zero, (extChartAt J x).left_inv m, ex] at e
      rw [ex] at fm; exact (extChartAt K (g x)).injOn fm gm e
    have d0 : ∃ᶠ y in 𝓝 z, d =ᶠ[𝓝 y] 0 := by
      rw [← hz]
      have xt' : ∃ᶠ y in 𝓝 x, (extChartAt J x).symm (extChartAt J x y) ∈ t := by
        apply xt.mp
        apply ((isOpen_extChartAt_source J x).eventually_mem (mem_extChartAt_source J x)).mp
        refine' eventually_of_forall fun y m e ↦ _; rw [(extChartAt J x).left_inv m]; exact e
      apply (Filter.Tendsto.frequently (p := fun y ↦ (extChartAt J x).symm y ∈ t)
          (continuousAt_extChartAt J x) xt').mp
      apply ((extChartAt_open_target J x).eventually_mem (mem_extChartAt_target J x)).mp
      refine' eventually_of_forall fun y m e ↦ _; simp only at e
      apply ((continuousAt_extChartAt_symm'' J x m).eventually e).mp
      refine' eventually_of_forall fun z e ↦ _; simp only at e
      simp only [← hd, Pi.zero_apply, sub_eq_zero, ex, e]
    have da : AnalyticAt ℂ d z := by rw [← hd, ← hz]; exact (fa _ xs).2.sub (ga _ xs).2
    clear hd ex ex' xt t e fa ga f g xs hz x sp
    -- Forget about manifolds
    rcases da.ball with ⟨r, rp, da⟩
    rcases Filter.frequently_iff.mp d0 (isOpen_ball.mem_nhds (mem_ball_self rp)) with ⟨z0, m0, ze⟩
    refine' eventually_nhds_iff.mpr ⟨_, _, isOpen_ball, mem_ball_self rp⟩
    exact da.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected m0 ze

end EqOfLocallyEq
