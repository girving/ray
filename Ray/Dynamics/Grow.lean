module
public import Ray.Dynamics.BottcherNearM
public import Ray.Dynamics.Defs
public import Ray.Dynamics.Nice
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Tactic.Cases
import Mathlib.Topology.ExtendFrom
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Nice
import Ray.Dynamics.Postcritical
import Ray.Manifold.Analytic
import Ray.Manifold.Inverse
import Ray.Manifold.LocalInj
import Ray.Manifold.Nonseparating
import Ray.Misc.Connected
import Ray.Misc.Continuation
import Ray.Misc.Topology
import all Ray.Dynamics.Potential

/-!
## Analytic continuation of external rays for all postcritical values

After `BottcherNearM.lean` and `Potential.lean`, we have Böttcher coordinates
`s.bottcherNear : ℂ → S → ℂ` defined near `a`, and `s.potential : ℂ → S → ℝ` continuous everywhere
if `OnePreimage s`.  `s.bottcherNear` is invertible at any `(c,a)`, so near `a` we have an external
ray map `ray : ℂ → ℂ → S`.

We now grow these rays out to the critical potential `s.p c`, which will give a ray map analytic
throughout `s.post`.  We fix `c`, require `ray` to be analytic on a neighborhood of
`{c} ×ˢ closedBall 0 p`, and apply continuous induction to increase `p` from a small value up to
(right below) `s.p c`.  The resulting map is unique near any `c`, so we can stitch the continuations
for all `c` together into a single map (`Super.has_ray`).

A lot of the detail here is related to working with analytic functions in neighborhoods of points
and sets without using the heavier machinery of germs, stalks, and sheaves.  But I don't know that
machinery well, so I'm sticking to the low tech approach for now.

The defining equation of external rays `r`, with `c` suppressed, is
  `bottcher (r x) = x`
However, we know `bottcher` only locally near `a`, specifically on `s.near`.  If we have `n` s.t.
`f^[n] z ∈ s.near`, we can map the above equation forward `n` times to get
  `bottcher (f^[n] (r x)) = bottcher (r x) ^ d ^ n = x ^ d ^ n`
-/

open Classical
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball mem_closedBall mem_ball_self)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {p : ℝ}
variable {s : Super f d a}
variable {r : ℂ → ℂ → S}

/-- `Eqn s n r (c,z)` means `r` looks locally like external rays near `z`, mapping forwards
    by `f c^[n]` to hit `s.near`. -/
public structure Eqn (s : Super f d a) (n : ℕ) (r : ℂ → ℂ → S) (x : ℂ × ℂ) : Prop where
  holo : ContMDiffAt II I ω (uncurry r) x
  near : (x.1, (f x.1)^[n] (r x.1 x.2)) ∈ s.near
  eqn : s.bottcherNear x.1 ((f x.1)^[n] (r x.1 x.2)) = x.2 ^ d ^ n

/-- `r` is an external ray map in a neighborhood of `{c} ×ˢ closedBall 0 p` -/
public structure Grow (s : Super f d a) (c : ℂ) (p : ℝ) (n : ℕ) (r : ℂ → ℂ → S) : Prop where
  nonneg : 0 ≤ p
  zero : r c 0 = a
  start : ∀ᶠ x : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear x.1 (r x.1 x.2) = x.2
  eqn : ∀ᶠ x : ℂ × ℂ in 𝓝ˢ ({c} ×ˢ closedBall 0 p), Eqn s n r x

/-- Construct `Eqn` using fewer `∀ᶠ` -/
public theorem eqn_near {s : Super f d a} {n : ℕ} {r : ℂ → ℂ → S} {c x : ℂ}
    (holo : ContMDiffAt II I ω (uncurry r) (c, x)) (mem : (c, (f c)^[n] (r c x)) ∈ s.near)
    (loc : ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), s.bottcherNear y.1 ((f y.1)^[n] (r y.1 y.2)) = y.2 ^ d ^ n) :
    ∀ᶠ y in 𝓝 (c, x), Eqn s n r y := by
  have m : ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), (y.1, (f y.1)^[n] (r y.1 y.2)) ∈ s.near := by
    refine ContinuousAt.eventually_mem ?_ (s.isOpen_near.mem_nhds mem)
    exact continuousAt_fst.prodMk (s.continuousAt_iter continuousAt_fst holo.continuousAt)
  apply holo.eventually.mp; apply loc.mp; apply m.mp
  exact .of_forall fun _ m l h ↦ ⟨h, m, l⟩

/-- `Eqn` is local -/
theorem Eqn.congr {x : ℂ × ℂ} {r0 r1 : ℂ → ℂ → S} (e : Eqn s n r0 x)
    (loc : uncurry r0 =ᶠ[𝓝 x] uncurry r1) : Eqn s n r1 x := by
  have s := loc.self_of_nhds; simp only [uncurry] at s
  exact
    { holo := e.holo.congr_of_eventuallyEq loc.symm
      near := by simp only [← s, e.near]
      eqn := by simp only [← s, e.eqn] }

/-- We can increase `n` in `Eqn` -/
theorem Eqn.mono {x : ℂ × ℂ} (e : Eqn s n r x) {m : ℕ} (nm : n ≤ m) : Eqn s m r x :=
  { holo := e.holo
    near := s.iter_stays_near' e.near nm
    eqn := by
      refine Nat.le_induction e.eqn ?_ m nm; intro k nk h
      simp only [h, Function.iterate_succ_apply',
        s.bottcherNear_eqn (s.iter_stays_near' e.near nk), pow_succ, pow_mul] }

/-- We can increase `n` in `Grow` -/
theorem Grow.mono (g : Grow s c p n r) {m : ℕ} (nm : n ≤ m) : Grow s c p m r :=
  { nonneg := g.nonneg
    zero := g.zero
    start := g.start
    eqn := g.eqn.mp (.of_forall fun _ e ↦ e.mono nm) }

/-- Centers `(c,0)` are in the domain -/
theorem mem_domain (c : ℂ) {p : ℝ} (p0 : 0 ≤ p) :
    (c, (0 : ℂ)) ∈ ({c} ×ˢ closedBall 0 p : Set (ℂ × ℂ)) :=
  mk_mem_prod rfl (Metric.mem_closedBall_self p0)

/-- The boundary is in the domain -/
public theorem mem_domain_self {c x : ℂ} :
    (c, x) ∈ ({c} ×ˢ closedBall 0 ‖x‖ : Set (ℂ × ℂ)) := by
  simp only [mem_prod_eq, mem_singleton_iff, mem_closedBall, Complex.dist_eq, sub_zero, true_and,
    le_refl]

/-- Our domain is preconnected -/
theorem domain_preconnected (c : ℂ) (p : ℝ) :
    IsPreconnected ({c} ×ˢ closedBall 0 p : Set (ℂ × ℂ)) :=
  isPreconnected_singleton.prod (convex_closedBall _ _).isPreconnected

/-- Our domain is monotonic in `p` -/
theorem domain_mono (c : ℂ) {p0 p1 : ℝ} (le : p0 ≤ p1) :
    ({c} ×ˢ closedBall 0 p0 : Set (ℂ × ℂ)) ⊆ {c} ×ˢ closedBall 0 p1 :=
  prod_mono_right (Metric.closedBall_subset_closedBall le)

/-- If `closedBall 0 p ⊆ t`, we can increase `p` bit without leaving `t` -/
theorem domain_open' {p : ℝ} {t : Set ℂ} (sub : closedBall (0 : ℂ) p ⊆ t) (ot : IsOpen t) :
    ∃ q, p < q ∧ closedBall 0 q ⊆ t := by
  set u := norm '' (closedBall 0 (p + 1) \ t)
  by_cases ne : u = ∅
  · refine ⟨p + 1, by bound, ?_⟩; rw [image_eq_empty, diff_eq_empty] at ne; exact ne
  replace ne := nonempty_iff_ne_empty.mpr ne
  have uc : IsClosed u :=
    (((isCompact_closedBall _ _).diff ot).image continuous_norm).isClosed
  have up : ∀ x : ℝ, x ∈ u → p < x := by
    intro x m; rcases m with ⟨z, ⟨_, mt⟩, e⟩; rw [← e]; contrapose mt
    simp only [not_lt] at mt ⊢
    apply sub; simp only [mem_closedBall, Complex.dist_eq, sub_zero, mt]
  have ub : BddBelow u := ⟨p, fun _ m ↦ (up _ m).le⟩
  have iu : sInf u ∈ u := IsClosed.csInf_mem uc ne ub
  rcases exists_between (up _ iu) with ⟨q, pq, qi⟩
  use min q (p + 1), lt_min pq (by linarith)
  intro z m; simp only [mem_closedBall, Complex.dist_eq, sub_zero, le_min_iff] at m
  rcases m with ⟨zq, zp⟩; have zi := lt_of_le_of_lt zq qi
  contrapose zi; simp only [not_lt]; refine csInf_le ub (mem_image_of_mem _ ?_)
  simp only [mem_diff, mem_closedBall, Complex.dist_eq, sub_zero]; use zp, zi

/-- If `{c} ×ˢ closedBall 0 p ⊆ t`, we can increase `p` bit without leaving `t` -/
theorem domain_open {p : ℝ} {t : Set (ℂ × ℂ)} (sub : {c} ×ˢ closedBall 0 p ⊆ t) (o : IsOpen t) :
    ∃ q, p < q ∧ {c} ×ˢ closedBall 0 q ⊆ t := by
  have sub : closedBall 0 p ⊆ {b | (c, b) ∈ t} := by
    intro z m; simp only [mem_setOf]; apply sub; exact ⟨mem_singleton _, m⟩
  rcases domain_open' sub (o.snd_preimage c) with ⟨q, pq, sub⟩
  use q, pq; intro ⟨e, z⟩ ⟨ec, m⟩; simp only [mem_singleton_iff] at ec
  replace m := sub m; simp only [← ec, mem_setOf] at m; exact m

/-- `Grow` is local -/
theorem Grow.congr {r0 r1 : ℂ → ℂ → S} (g : Grow s c p n r0)
    (e : uncurry r0 =ᶠ[𝓝ˢ ({c} ×ˢ closedBall 0 p)] uncurry r1) : Grow s c p n r1 :=
  { nonneg := g.nonneg
    zero := by
      have e := e.self_of_nhdsSet (mem_domain c g.nonneg)
      simp only [uncurry] at e; rw [← e]; exact g.zero
    start := by
      refine g.start.mp ((e.filter_mono (nhds_le_nhdsSet (mem_domain c g.nonneg))).mp ?_)
      refine .of_forall fun x e s ↦ ?_
      simp only [uncurry] at e; rw [← e]; exact s
    eqn := by
      have eqn := g.eqn; simp only [Filter.EventuallyEq, eventually_nhdsSet_iff_forall] at eqn e ⊢
      intro x m
      refine (eqn x m).mp ((e x m).eventually_nhds.mp (.of_forall fun y e eqn ↦ ?_))
      exact eqn.congr e }

/-- `s.potential (r x) = abs x`, if `Eqn s n r x` -/
public theorem Eqn.potential {x : ℂ × ℂ} (e : Eqn s n r x) :
    s.potential x.1 (r x.1 x.2) = ‖x.2‖ := by
  simp only [s.potential_eq e.near, e.eqn, norm_pow, ← Nat.cast_pow,
    Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ s.d0)]

/-- `Eqn` implies that `s.bottcherNearIter` is noncritical -/
theorem eqn_noncritical {x : ℂ × ℂ} (e : ∀ᶠ y in 𝓝 x, Eqn s n r y) (x0 : x.2 ≠ 0) :
    mfderiv I I (s.bottcherNearIter n x.1) (r x.1 x.2) ≠ 0 := by
  rcases x with ⟨c, x⟩; contrapose x0
  replace x0 : mfderiv I I (fun y ↦ s.bottcherNearIter n c (r c y)) x = 0 := by
    rw [←Function.comp_def,
      mfderiv_comp x
        ((s.bottcherNearIter_mAnalytic e.self_of_nhds.near).along_snd.mdifferentiableAt (by decide))
        (e.self_of_nhds.holo.along_snd.mdifferentiableAt (by decide)),
      x0, ContinuousLinearMap.zero_comp]
  have loc : (fun y ↦ s.bottcherNearIter n c (r c y)) =ᶠ[𝓝 x] fun y ↦ y ^ d ^ n :=
    ((continuousAt_const.prodMk continuousAt_id).eventually e).mp
      (.of_forall fun _ e ↦ e.eqn)
  rw [mfderiv_eq_fderiv, loc.fderiv_eq] at x0
  have d := (differentiableAt_pow (𝕜 := ℂ) (x := x) (d ^ n)).hasFDerivAt.hasDerivAt.deriv
  apply_fun (fun x ↦ x 1) at x0
  rw [x0] at d
  replace d := Eq.trans d (ContinuousLinearMap.zero_apply _)
  simp only [differentiableAt_fun_id, deriv_fun_pow, Nat.cast_pow, deriv_id'', mul_one, mul_eq_zero,
    pow_eq_zero_iff', Nat.cast_eq_zero, s.d0, ne_eq, false_and, false_or] at d
  exact d.1

/-- `p < 1` for any `p` in `Grow` -/
theorem Grow.p1 (g : Grow s c p n r) : p < 1 := by
  by_contra p1; simp only [not_lt] at p1
  have e := (g.eqn.filter_mono (nhds_le_nhdsSet (x := (c, 1)) ?_)).self_of_nhds
  · have lt := s.potential_lt_one (s.basin_iff_near.mpr ⟨_, e.near⟩)
    rw [e.potential, norm_one, lt_self_iff_false] at lt
    exact lt
  · simp only [p1, singleton_prod, mem_image, mem_closedBall_zero_iff, norm_one, Prod.mk_inj,
      true_and, exists_eq_right]

/-- `r` is analytic throughout the domain -/
theorem Grow.holo (g : Grow s c p n r) : ContMDiffOnNhd II I (uncurry r) ({c} ×ˢ closedBall 0 p) :=
  fun _ m ↦ (g.eqn.filter_mono (nhds_le_nhdsSet m)).self_of_nhds.holo

/-- `Grow` exists for small `p`, since small `p` is near `a` -/
theorem Super.grow_start (s : Super f d a) (c : ℂ) : ∃ p r, 0 < p ∧ Grow s c p 0 r := by
  have ba := s.bottcherNear_mAnalytic' (s.mem_near c)
  have nc := s.bottcherNear_mfderiv_ne_zero c
  rcases complex_inverse_fun ba nc with ⟨r, ra, rb, br⟩
  rw [s.bottcherNear_a] at ra br
  have rm : ∀ᶠ x : ℂ × ℂ in 𝓝 (c, 0), (x.1, r x.1 x.2) ∈ s.near := by
    refine (continuousAt_fst.prodMk ra.continuousAt).eventually_mem (s.isOpen_near.mem_nhds ?_)
    have r0 := rb.self_of_nhds; simp only [s.bottcherNear_a] at r0
    simp only [uncurry, r0]; exact s.mem_near c
  rcases eventually_nhds_iff.mp (ra.eventually.and (br.and rm)) with ⟨t, h, o, m⟩
  rcases Metric.isOpen_iff.mp o _ m with ⟨p, pp, sub⟩
  replace h := fun (x : ℂ × ℂ) m ↦ h x (sub m)
  have nb : ball (c, (0 : ℂ)) p ∈ 𝓝ˢ ({c} ×ˢ closedBall (0 : ℂ) (p / 2)) := by
    rw [isOpen_ball.mem_nhdsSet, ← ball_prod_same]; apply prod_mono
    rw [singleton_subset_iff]; exact mem_ball_self pp
    apply Metric.closedBall_subset_ball; exact half_lt_self pp
  use p / 2, r, half_pos pp
  exact
    { nonneg := (half_pos pp).le
      zero := by convert rb.self_of_nhds; simp only [s.bottcherNear_a]
      start := Filter.eventually_iff_exists_mem.mpr ⟨_, ball_mem_nhds _ pp, fun _ m ↦ (h _ m).2.1⟩
      eqn :=
        Filter.eventually_iff_exists_mem.mpr
          ⟨_, nb, fun _ m ↦
            { holo := (h _ m).1
              near := (h _ m).2.2
              eqn := by simp only [Function.iterate_zero_apply, pow_zero, pow_one, (h _ m).2.1] }⟩ }

/-- We can grow `p` and vary `c` a bit in `Grow` -/
theorem Grow.open (g : Grow s c p n r) : ∃ p', p < p' ∧ ∀ᶠ c' in 𝓝 c, Grow s c' p' n r := by
  have e := g.eqn; simp only [isCompact_singleton.nhdsSet_prod_eq (isCompact_closedBall _ _)] at e
  rcases Filter.mem_prod_iff.mp e with ⟨a', an, b', bn, sub⟩
  simp only [subset_setOf] at sub
  rcases eventually_nhds_iff.mp (nhdsSet_singleton.subst an) with ⟨a, aa, ao, am⟩
  rcases eventually_nhdsSet_iff_exists.mp bn with ⟨b, bo, bp, bb⟩
  rcases domain_open' bp bo with ⟨q, pq, qb⟩
  use q, pq
  have m : ∀ᶠ c' in 𝓝 c, (c', r c' 0) ∈ s.near := by
    refine (continuousAt_id.prodMk ?_).eventually_mem (s.isOpen_near.mem_nhds ?_)
    · exact (g.eqn.filter_mono (nhds_le_nhdsSet (mem_domain c
        g.nonneg))).self_of_nhds.holo.along_fst.continuousAt
    · simp only [id, g.zero, s.mem_near c]
  apply m.mp
  apply ((continuousAt_id.prodMk continuousAt_const).eventually g.start.eventually_nhds).mp
  refine eventually_nhds_iff.mpr ⟨a, ?_, ao, am⟩
  intro c' am' start m
  exact
    { nonneg := _root_.trans g.nonneg pq.le
      zero := by have e := start.self_of_nhds; simp only [id, s.bottcherNear_eq_zero m] at e; exact e
      start
      eqn := by
        refine eventually_nhdsSet_iff_exists.mpr ⟨a ×ˢ b, ao.prod bo, ?_, ?_⟩
        · exact prod_mono (singleton_subset_iff.mpr am') qb
        · intro x ⟨cm, xm⟩; exact sub x ⟨aa _ cm, bb _ xm⟩ }

/-- We can decrease `p` in `Grow` -/
theorem Grow.anti (g : Grow s c p n r) {q : ℝ} (nonneg : 0 ≤ q) (le : q ≤ p) : Grow s c q n r :=
  { nonneg
    zero := g.zero
    start := g.start
    eqn :=
      g.eqn.filter_mono (nhdsSet_mono (prod_mono_right (Metric.closedBall_subset_closedBall le))) }

/-- `Eqn` determines `r` locally, given equality at a point -/
public theorem eqn_unique {r0 r1 : ℂ → ℂ → S} {x : ℂ × ℂ} (e0 : ∀ᶠ y in 𝓝 x, Eqn s n r0 y)
    (e1 : ∀ᶠ y in 𝓝 x, Eqn s n r1 y) (r01 : r0 x.1 x.2 = r1 x.1 x.2) (x0 : x.2 ≠ 0) :
    uncurry r0 =ᶠ[𝓝 x] uncurry r1 := by
  have ba := s.bottcherNearIter_mAnalytic e0.self_of_nhds.near
  have inj := ba.local_inj' (eqn_noncritical e0 x0); nth_rw 2 [r01] at inj
  have t : Tendsto (fun x : ℂ × ℂ ↦ (x.1, r0 x.1 x.2, r1 x.1 x.2)) (𝓝 x)
      (𝓝 (x.1, r0 x.1 x.2, r1 x.1 x.2)) :=
    continuousAt_fst.prodMk
      (e0.self_of_nhds.holo.continuousAt.prodMk e1.self_of_nhds.holo.continuousAt)
  apply (t.eventually inj).mp
  refine e0.mp (e1.mp (.of_forall fun x e1 e0 inj ↦ ?_))
  specialize inj _
  simp only [Super.bottcherNearIter, e0.eqn, e1.eqn]
  exact inj

/-- The property that we will use to define valid germs in analytic continuation.
    This is normally just `Eqn`, but requiring `=ᶠ[𝓝 (c,0)]` if we're at the origin
    since there `Eqn` uniqueness breaks down. -/
structure Eqns (s : Super f d a) (n : ℕ) (r0 r : ℂ → ℂ → S) (x : ℂ × ℂ) : Prop where
  eqn : ∀ᶠ y in 𝓝 x, Eqn s n r y
  start : x.2 = 0 → uncurry r =ᶠ[𝓝 x] uncurry r0

/-- `Eqns` implies `r` is analytic -/
theorem Eqns.holo {r0 r : ℂ → ℂ → S} {x : ℂ × ℂ} (e : Eqns s n r0 r x) :
    ContMDiffAt II I ω (uncurry r) x :=
  e.eqn.self_of_nhds.holo

/-- `Eqns` is local -/
theorem Eqns.congr {x : ℂ × ℂ} {r0 r1 r2 : ℂ → ℂ → S} (e1 : Eqns s n r0 r1 x)
    (loc : uncurry r1 =ᶠ[𝓝 x] uncurry r2) : Eqns s n r0 r2 x :=
  { eqn := e1.eqn.mp (loc.eventually_nhds.mp (.of_forall fun _ loc e ↦ e.congr loc))
    start := fun x0 ↦ loc.symm.trans (e1.start x0) }

variable [T2Space S]

/-- The equivalent of `Grow` on `{c} ×ˢ ball 0 p`, where the ball is open rather than closed.
    However, we use an `n` that covers the boundary at potential `p` as well, so that analytic
    continuation will work without changing `n`. -/
structure GrowOpen (s : Super f d a) (c : ℂ) (p : ℝ) (r : ℂ → ℂ → S) : Prop where
  pos : 0 < p
  post : p < s.p c
  zero : r c 0 = a
  start : ∀ᶠ x : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear x.1 (r x.1 x.2) = x.2
  eqn : ∀ᶠ x : ℂ × ℂ in 𝓝ˢ ({c} ×ˢ ball 0 p), Eqn s (s.np c p) r x

/-- We can analytically continue `r` to any point in the closure -/
theorem GrowOpen.point (g : GrowOpen s c p r) [OnePreimage s] {x : ℂ} (ax : ‖x‖ ≤ p) :
    ∃ r' : ℂ → ℂ → S,
      (∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), Eqn s (s.np c p) r' y) ∧
        ∃ᶠ y in 𝓝 x, y ∈ ball (0 : ℂ) p ∧ r' c y = r c y := by
  -- If z = a, we can use r
  by_cases za : ‖x‖ = 0
  · use r
    simp only [norm_eq_zero] at za
    simp only [za, and_true]
    constructor
    · refine g.eqn.filter_mono (nhds_le_nhdsSet ?_)
      exact mk_mem_prod rfl (mem_ball_self g.pos)
    · exact (isOpen_ball.eventually_mem (mem_ball_self g.pos)).frequently
  replace za := (Ne.symm za).lt_of_le (norm_nonneg _)
  -- Choose a value z = r' c x as a cluster point of r c at 𝓝[t] x
  set t := ball (0 : ℂ) p
  have xt : x ∈ closure t := by
    simp only [t, closure_ball _ g.pos.ne', mem_closedBall, Complex.dist_eq, sub_zero, ax]
  have ez : ∃ z : S, MapClusterPt z (𝓝[t] x) (r c) :=
    @exists_clusterPt_of_compactSpace _ _ _ _
      (Filter.map_neBot (hf := mem_closure_iff_nhdsWithin_neBot.mp xt))
  rcases ez with ⟨z, cp⟩
  have pz : s.potential c z = ‖x‖ := by
    refine eq_of_nhds_neBot (cp.map (Continuous.potential s).along_snd.continuousAt
      (Filter.tendsto_map' ?_))
    have e : ∀ y, y ∈ t → (s.potential c ∘ r c) y = ‖y‖ := by
      intro y m; simp only [Function.comp]; exact (g.eqn.self_of_nhdsSet (c, y) ⟨rfl, m⟩).potential
    exact tendsto_nhdsWithin_congr (fun t m ↦ (e t m).symm)
      continuous_norm.continuousWithinAt
  have nice := s.nice_np c (lt_of_lt_of_le g.post s.p_le_one)
  have ba := nice.contMDiffAt_bottcherNearIter (le_trans (le_of_eq pz) ax)
  have nc := nice.mfderiv_ne_zero (le_trans (le_of_eq pz) ax) (le_refl _)
  generalize hn : s.np c p = n
  rw [hn] at ba nc
  generalize hb : s.bottcherNearIter n = b
  have bz : b c z = x ^ d ^ n := by
    refine eq_of_nhds_neBot (cp.map ?_ (Filter.tendsto_map' ?_))
    · rw [← hb]
      exact ba.along_snd.continuousAt
    · have e : ∀ y, y ∈ t → (b c ∘ r c) y = y ^ d ^ n := by
        intro y m
        simp only [Function.comp, ← hb, ← hn]
        exact (g.eqn.self_of_nhdsSet (c, y) ⟨rfl, m⟩).eqn
      exact tendsto_nhdsWithin_congr (fun t m ↦ (e t m).symm) (continuous_pow _).continuousWithinAt
  have post : Postcritical s c z := lt_of_le_of_lt (_root_.trans (le_of_eq pz) ax) g.post
  rw [← pz] at za
  -- Invert s.bottcherNearIter at z
  replace nc := s.bottcherNearIter_mfderiv_ne_zero nc (post.not_precritical za.ne')
  rcases complex_inverse_fun ba nc with ⟨i, ia, ib, bi⟩
  simp only [hb, bz] at ia bi ib
  have pt : Tendsto (fun p : ℂ × ℂ ↦ (p.1, p.2 ^ d ^ n)) (𝓝 (c, x)) (𝓝 (c, x ^ d ^ n)) :=
    continuousAt_fst.prodMk (continuousAt_snd.pow _)
  have ian : ContMDiffAt II I ω (uncurry fun e y : ℂ ↦ i e (y ^ d ^ n)) (c, x) :=
    ia.comp₂_of_eq contMDiffAt_fst ((contMDiff_pow _).contMDiffAt.comp _ contMDiffAt_snd) rfl
  use fun e y ↦ i e (y ^ d ^ n); constructor
  · -- We satisfy eqn near x
    apply eqn_near ian
    · simp only [← bz]
      rw [ib.self_of_nhds, ← hn]
      exact nice.near (le_trans (le_of_eq pz) ax)
    · refine (pt.eventually bi).mp (.of_forall ?_)
      intro _ bi; simp only [← hb] at bi; exact bi
  · -- We frequently match r, by local injectivity of b
    have ne : MapClusterPt (z, z) (𝓝[t] x) fun y ↦ (r c y, i c (y ^ d ^ n)) := by
      apply cp.prod; refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
      have ic := ian.along_snd.continuousAt
      simp only [ContinuousAt, ←bz] at ic; rw [ib.self_of_nhds] at ic
      exact ic
    have inj := (@Filter.Eventually.frequently _ _ ne _
            (Filter.Eventually.filter_mono inf_le_left (ba.along_snd.local_inj nc))).filter_mono
        inf_le_right
    simp only [Filter.frequently_map, frequently_nhdsWithin_iff] at inj
    apply inj.mp
    apply ((continuousAt_const.prodMk (continuousAt_pow _ _)).eventually bi).mp
    refine .of_forall ?_; simp only [← hb, ← hn]; intro x bi ⟨inj, m⟩
    refine ⟨m, (inj ?_).symm⟩; simp only [bi]
    exact (g.eqn.self_of_nhdsSet ⟨c, x⟩ (mk_mem_prod rfl m)).eqn

/-- `Eqns` determines `r` once one point is fixed -/
theorem eqns_unique {r0 r1 r2 : ℂ → ℂ → S} {t : Set (ℂ × ℂ)}
    (pre : IsPreconnected t) (e1 : ∀ x, x ∈ t → Eqns s n r0 r1 x)
    (e2 : ∀ x, x ∈ t → Eqns s n r0 r2 x) (ne : ∃ x, x ∈ t ∧ uncurry r1 x = uncurry r2 x) :
    EqOn (uncurry r1) (uncurry r2) t := by
  -- The set on which r0 = r1 is both relatively open and closed, so it's everything
  set u := {x | uncurry r1 x = uncurry r2 x}
  replace ne : (t ∩ u).Nonempty := ne
  have op : t ∩ u ⊆ interior u := by
    intro ⟨c, x⟩ ⟨mt, mu⟩; rw [mem_interior_iff_mem_nhds]
    by_cases x0 : x = 0; exact ((e1 _ mt).start x0).trans ((e2 _ mt).start x0).symm
    exact eqn_unique (e1 _ mt).eqn (e2 _ mt).eqn mu x0
  have cl : t ∩ closure u ⊆ u := by
    intro x ⟨mt, mu⟩; simp only [mem_closure_iff_frequently] at mu ⊢
    exact tendsto_nhds_unique_of_frequently_eq (e1 _ mt).holo.continuousAt
      (e2 _ mt).holo.continuousAt mu
  exact _root_.trans (pre.relative_clopen ne op cl) interior_subset

/-- `r` is unique in `Grow` -/
theorem Grow.unique {r0 r1 : ℂ → ℂ → S} {p0 p1 : ℝ} {n0 n1 : ℕ} (g0 : Grow s c p0 n0 r0)
    (g1 : Grow s c p1 n1 r1) (p01 : p0 ≤ p1) :
    uncurry r0 =ᶠ[𝓝ˢ ({c} ×ˢ closedBall 0 p0)] uncurry r1 := by
  -- Reduce to equality near (c,0)
  by_cases pos : p0 < 0
  · simp only [Metric.closedBall_eq_empty.mpr pos, singleton_prod, image_empty, nhdsSet_empty,
      Filter.EventuallyEq, Filter.eventually_bot]
  have m : (c, (0 : ℂ)) ∈ {c} ×ˢ closedBall (0 : ℂ) p0 := mem_domain c (not_lt.mp pos)
  refine ContMDiffOnNhd.eq_of_locally_eq g0.holo (g1.holo.mono (domain_mono _ p01))
      (domain_preconnected _ _) ⟨(c, 0), m, ?_⟩
  -- Injectivity of s.bottcherNear gives us the rest
  have t : ContinuousAt (fun x : ℂ × ℂ ↦ (x.1, r0 x.1 x.2, r1 x.1 x.2)) (c, 0) :=
    continuousAt_fst.prodMk
      ((g0.eqn.filter_mono (nhds_le_nhdsSet m)).self_of_nhds.holo.continuousAt.prodMk
        (g1.eqn.filter_mono (nhds_le_nhdsSet (domain_mono c p01 m))).self_of_nhds.holo.continuousAt)
  simp only [ContinuousAt, g0.zero, g1.zero] at t
  have inj := (s.bottcherNear_mAnalytic' (s.mem_near c)).local_inj'
    (s.bottcherNear_mfderiv_ne_zero c)
  refine ((t.eventually inj).and (g0.start.and g1.start)).mp (.of_forall ?_)
  intro ⟨e, y⟩ ⟨inj, s0, s1⟩; exact inj (s0.trans s1.symm)

/-- Given `GrowOpen _ _ p`, we can analytically continue to the boundary to get `Grow _ _ p` -/
theorem GrowOpen.grow (g : GrowOpen s c p r) [OnePreimage s] : ∃ r', Grow s c p (s.np c p) r' := by
  set n := s.np c p
  have b : Base (fun f x ↦ Eqns s n r (curry f) x) ({c} ×ˢ ball (0 : ℂ) p) (uncurry r) :=
    { convex := (convex_singleton c).prod (convex_ball 0 p)
      compact := by
        simp only [closure_prod_eq, closure_ball _ g.pos.ne', closure_singleton]
        exact isCompact_singleton.prod (isCompact_closedBall _ _)
      congr := by intro r0 r1 x e0 r01; exact e0.congr (by simp only [Function.uncurry_curry, r01])
      start := by
        simp only [Filter.eventually_iff]; rw [mem_nhdsSet_iff_forall]; intro x m
        exact (g.eqn.filter_mono (nhds_le_nhdsSet m)).eventually_nhds.mp
          (.of_forall fun y e ↦
          { eqn := e
            start := by
              simp only [Function.curry_uncurry, Filter.EventuallyEq.refl, imp_true_iff] })
      point := by
        intro ⟨c', x⟩ m
        simp only [closure_prod_eq, closure_ball _ g.pos.ne', closure_singleton, mem_prod_eq,
          mem_singleton_iff, mem_closedBall, Complex.dist_eq, sub_zero] at m
        have ct : Tendsto (fun x ↦ (c, x)) (𝓝 x) (𝓝 (c, x)) :=
          continuousAt_const.prodMk continuousAt_id
        by_cases x0 : x ≠ 0
        · rw [m.1]; rcases g.point m.2 with ⟨r', e, rr⟩
          use uncurry r'; constructor
          · have t : ContinuousAt (fun y : ℂ × ℂ ↦ y.2) (c, x) := continuousAt_snd
            refine e.eventually_nhds.mp ((t.eventually_ne x0).mp (.of_forall ?_))
            intro y y0 e
            exact
              { eqn := e
                start := fun h ↦ (y0 h).elim }
          · refine ct.frequently (rr.mp (.of_forall ?_)); intro x ⟨m, e⟩
            simp only [mem_prod_eq, mem_singleton_iff, true_and]; use m, e
        · use uncurry r; simp only [not_not] at x0
          simp only [m.1, x0, and_true] at ct ⊢; constructor
          · refine
              (g.eqn.filter_mono (nhds_le_nhdsSet ?_)).eventually_nhds.mp
                (.of_forall fun y e ↦ ?_)
            use rfl, mem_ball_self g.pos; simp only [Function.curry_uncurry]
            exact
              { eqn := e
                start := by
                  simp only [Filter.EventuallyEq.refl, imp_true_iff] }
          · refine ct.frequently (Filter.Eventually.frequently ?_)
            simp only [mem_prod_eq, mem_singleton_iff, true_and]
            exact isOpen_ball.eventually_mem (mem_ball_self g.pos)
      unique := by
        intro r0 r1 t _ pre e0 e1 r01
        have u := eqns_unique pre e0 e1 ?_
        simp only [Function.uncurry_curry] at u; exact u
        simp only [Function.uncurry_curry]; exact r01 }
  have m0 : (c, (0 : ℂ)) ∈ ({c} ×ˢ ball 0 p : Set (ℂ × ℂ)) := by
    simp only [mem_prod_eq, mem_singleton_iff, true_and, mem_ball_self g.pos]
  use curry b.u
  exact
    { nonneg := g.pos.le
      zero := by rw [curry, b.uf.self_of_nhdsSet m0, uncurry, g.zero]
      start := by
        refine g.start.mp ((b.uf.filter_mono (nhds_le_nhdsSet m0)).mp (.of_forall ?_))
        intro x e b; simp only [curry, uncurry, Prod.mk.eta] at e ⊢; rw [e]; exact b
      eqn := by
        have fp := b.up
        simp only [closure_prod_eq, closure_singleton, closure_ball _ g.pos.ne'] at fp
        exact fp.mp (.of_forall fun x e ↦ e.eqn.self_of_nhds) }

/-- Given a increasing sequence of `p`s with corresponding `r`s and `Grow`s, we can piece together
    a single, globally consistent `r`. -/
theorem join_r (s : Super f d a) {p : ℕ → ℝ} {n : ℕ → ℕ} {ps : ℝ} {r : ℕ → ℂ → ℂ → S}
    (g : ∀ k, Grow s c (p k) (n k) (r k)) (mono : Monotone p)
    (tend : Tendsto p atTop (𝓝 ps)) :
    ∃ rs : ℂ → ℂ → S, ∀ (k) (x : ℂ), ‖x‖ < p k → uncurry rs =ᶠ[𝓝 (c, x)] uncurry (r k) := by
  have above : ∀ k, p k ≤ ps := fun k ↦ mono.ge_of_tendsto tend k
  generalize hrs : (fun e x : ℂ ↦
    if h : ‖x‖ < ps then r (Nat.find (tend.exists_lt h)) e x else a) = rs
  use rs
  -- rs is locally each r, via induction
  have loc : ∀ k, ∀ᶠ e in 𝓝 c, ∀ x : ℂ, ‖x‖ < p k → rs e x = r k e x := by
    intro k; induction' k with k h
    · refine .of_forall fun e x x0 ↦ ?_
      have xe : ∃ k, ‖x‖ < p k := ⟨0, x0⟩
      simp only [← hrs, lt_of_lt_of_le x0 (above _), dif_pos, (Nat.find_eq_zero xe).mpr x0]
    · have eq := (g k).unique (g (k + 1)) (mono (Nat.lt_succ_self _).le)
      simp only [isCompact_singleton.nhdsSet_prod_eq (isCompact_closedBall _ _)] at eq
      apply h.mp
      rcases Filter.mem_prod_iff.mp eq with ⟨u0, n0, u1, n1, eq⟩
      simp only [nhdsSet_singleton] at n0
      refine Filter.eventually_of_mem n0 fun e eu h x xk1 ↦ ?_
      by_cases xk0 : ‖x‖ < p k
      · have m : (e, x) ∈ u0 ×ˢ u1 := by
          refine mk_mem_prod eu (subset_of_mem_nhdsSet n1 ?_)
          simp only [mem_closedBall, Complex.dist_eq, sub_zero, xk0.le]
        specialize eq m; simp only [mem_setOf, uncurry] at eq
        rw [h _ xk0, eq]
      · have xe : ∃ k, ‖x‖ < p k := ⟨k + 1, xk1⟩
        have n := (Nat.find_eq_iff xe).mpr ⟨xk1, ?_⟩
        simp only [← hrs, lt_of_lt_of_le xk1 (above _), dif_pos, n]
        intro j jk; simp only [not_lt, Nat.lt_succ_iff] at jk xk0 ⊢
        exact _root_.trans (mono jk) xk0
  -- rs is locally each r, final form
  intro k x xk
  rcases eventually_nhds_iff.mp (loc k) with ⟨u, eq, uo, uc⟩
  have m : u ×ˢ ball (0 : ℂ) (p k) ∈ 𝓝 (c, x) := by
    refine prod_mem_nhds (uo.mem_nhds uc) (isOpen_ball.mem_nhds ?_)
    simp only [mem_ball, Complex.dist_eq, sub_zero, xk]
  apply Filter.eventually_of_mem m; intro ⟨e, y⟩ ⟨m0, m1⟩
  simp only [mem_ball, Complex.dist_eq, sub_zero] at m1
  exact eq _ m0 _ m1

/-- If we can `Grow` up to any `q < p`, we get a `GrowOpen` up to `p` -/
theorem joined_growOpen (s : Super f d a) {p : ℕ → ℝ} {ps : ℝ} {r : ℕ → ℂ → ℂ → S} {rs : ℂ → ℂ → S}
    (g : ∀ k, Grow s c (p k) (s.np c ps) (r k)) (tend : Tendsto p atTop (𝓝 ps))
    (post : ps < s.p c) (pos : 0 < ps)
    (loc : ∀ (k) (x : ℂ), ‖x‖ < p k → uncurry rs =ᶠ[𝓝 (c, x)] uncurry (r k)) :
    GrowOpen s c ps rs :=
  { pos
    post
    zero := by
      rcases tend.exists_lt pos with ⟨k, pos⟩
      have e := (loc k 0 (by simp only [norm_zero, pos])).self_of_nhds
      simp only [uncurry] at e; simp only [e, (g k).zero]
    start := by
      rcases tend.exists_lt pos with ⟨k, pos⟩
      apply (g k).start.mp
      apply (loc k 0 (by simp only [norm_zero, pos])).mp
      refine .of_forall fun ⟨e, x⟩ loc start ↦ ?_
      simp only [uncurry] at loc start ⊢; simp only [start, loc]
    eqn := by
      apply mem_nhdsSet_iff_forall.mpr; intro ⟨c', x⟩ lt
      simp only [mem_prod_eq, mem_singleton_iff, mem_ball, Complex.dist_eq, sub_zero] at lt
      simp only [lt.1, true_and, ← Filter.eventually_iff] at lt ⊢; clear c'
      rcases tend.exists_lt lt with ⟨k, ltp⟩
      have m : (c, x) ∈ {c} ×ˢ closedBall (0 : ℂ) (p k) := by
        simp only [mem_prod_eq, mem_singleton_iff, Metric.mem_closedBall, true_and, Complex.dist_eq,
          sub_zero, ltp.le]
      have lt' : ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x), ‖y.2‖ < ps :=
        (continuous_norm.continuousAt.comp continuousAt_snd).eventually_lt
          continuousAt_const lt
      apply ((g k).eqn.filter_mono (nhds_le_nhdsSet m)).mp
      apply (loc _ _ ltp).eventually_nhds.mp
      apply lt'.mp
      refine .of_forall fun ⟨e, y⟩ _ loc eq ↦ ?_
      exact eq.congr (Filter.EventuallyEq.symm loc) }

/-- We can grow up to the postcritical value `s.p c` -/
theorem Super.grow (s : Super f d a) [OnePreimage s] :
    ∀ p, 0 ≤ p → p < s.p c → ∃ r, Grow s c p (s.np c p) r := by
  set t : Set ℝ := {p | 0 ≤ p ∧ ∀ q, 0 ≤ q → q ≤ p → ∃ r, Grow s c q (s.np c q) r}
  have self : ∀ {p}, p ∈ t → ∃ r, Grow s c p (s.np c p) r := fun {p} m ↦ m.2 _ m.1 (le_refl _)
  have t1 : ∀ p : ℝ, p ∈ t → p < 1 := by intro p m; rcases self m with ⟨r, g⟩; exact g.p1
  have above : BddAbove t := bddAbove_def.mpr ⟨1, fun p m ↦ (t1 p m).le⟩
  rcases s.grow_start c with ⟨p0, r0, pos0, g0⟩
  have start : p0 ∈ t := by
    use g0.nonneg; intro q q0 qp; use r0; exact (g0.anti q0 qp).mono (Nat.zero_le _)
  have ne : t.Nonempty := ⟨p0, start⟩
  have pos : 0 < sSup t := lt_csSup_of_lt above start pos0
  by_cases missing : sSup t ∈ t
  · -- Contradict by growing a bit beyond Sup t
    rcases self missing with ⟨r, g⟩; rcases g.open with ⟨p, sp, g'⟩
    suffices m : p ∈ t by linarith [le_csSup above m]
    use g'.self_of_nhds.nonneg
    intro q q0 qp; by_cases le : q ≤ sSup t; exact missing.2 _ q0 le
    use r; simp only [not_le] at le
    exact (g'.self_of_nhds.anti q0 qp).mono (s.np_mono c le.le (lt_of_le_of_lt qp g'.self_of_nhds.p1))
  by_cases post : sSup t < s.p c
  · exfalso; apply missing; use pos.le; intro q q0 le
    -- q < Sup t is trivial
    by_cases lt : q < sSup t
    · rcases exists_lt_of_lt_csSup ne lt with ⟨q', ⟨_, m⟩, qq⟩
      exact m _ q0 qq.le
    have eq := le_antisymm le (not_lt.mp lt); rw [eq]; clear eq lt le q0 q
    -- Piece together a single r that works < Sup t, then close to Sup t
    rcases exists_seq_tendsto_sSup ne above with ⟨p, mono, tend, sub⟩
    simp only [mem_setOf, t] at sub
    set pr := fun k ↦ choose (self (sub k))
    have pg : ∀ k, Grow s c (p k) (s.np c (sSup t)) (pr k) := fun k ↦
      (choose_spec (self (sub k))).mono
        (s.np_mono c (le_csSup above (sub k)) (lt_of_lt_of_le post s.p_le_one))
    rcases join_r s pg mono tend with ⟨r, loc⟩
    exact (joined_growOpen s pg tend post pos loc).grow
  -- Finish!
  simp only [not_lt] at post
  intro p p0 lt
  rcases exists_lt_of_lt_csSup ne (lt_of_lt_of_le lt post) with ⟨q, m, pq⟩
  exact m.2 _ p0 pq.le

/-- There is a single `r` that achieves all `Grow`s for all `c` and `p < s.p c`.

    That is, there exists a map on `𝓝ˢ ({c} ×ˢ ball 0 (s.p c))` which everywhere looks
    like an inverse to Böttcher coordinates, and thus defines external rays up to the
    critical potential `s.p c`. -/
public theorem Super.has_ray (s : Super f d a) [OnePreimage s] :
    ∃ r : ℂ → ℂ → S, ∀ c p, 0 ≤ p → p < s.p c → Grow s c p (s.np c p) r := by
  generalize hr : (fun {c p} (h : 0 ≤ p ∧ p < s.p c) ↦ choose (s.grow _ h.1 h.2)) = r
  have g : ∀ {c p} (h : 0 ≤ p ∧ p < s.p c), Grow s c p (s.np c p) (r h) := by
    intro c p h; rw [← hr]; exact choose_spec _
  clear hr
  generalize hray : (fun c x : ℂ ↦
    if h : ‖x‖ < s.p c then r ⟨norm_nonneg _, h⟩ c x else a) = ray
  have loc : ∀ {c p} (h : 0 ≤ p ∧ p < s.p c),
      uncurry ray =ᶠ[𝓝ˢ ({c} ×ˢ closedBall 0 p)] uncurry (r h) := by
    intro c p h
    rcases(g h).open with ⟨q', pq', gh⟩
    rcases exists_between (lt_min pq' h.2) with ⟨q, pq, qlo⟩
    rcases lt_min_iff.mp qlo with ⟨qq', qs⟩
    have q0 : 0 ≤ q := _root_.trans h.1 pq.le
    replace gh := gh.mp (.of_forall fun c' g ↦ g.anti q0 qq'.le)
    clear qlo qq' pq' q'
    rcases eventually_nhds_iff.mp gh with ⟨t0, gh, ot0, ct0⟩
    rcases eventually_nhds_iff.mp (s.lowerSemicontinuous_p _ _ qs) with ⟨t1, lo, ot1, ct1⟩
    refine eventually_nhdsSet_iff_exists.mpr
        ⟨(t0 ∩ t1) ×ˢ ball 0 q, (ot0.inter ot1).prod isOpen_ball, ?_, ?_⟩
    · exact prod_mono (singleton_subset_iff.mpr ⟨ct0, ct1⟩) (Metric.closedBall_subset_ball pq)
    · intro ⟨e, x⟩ ⟨⟨et0, et1⟩, xq⟩; simp only [uncurry] at et0 et1 xq ⊢
      simp only [mem_ball, Complex.dist_eq, sub_zero] at xq
      have hx : 0 ≤ ‖x‖ ∧ ‖x‖ < s.p e := ⟨norm_nonneg _, _root_.trans xq (lo _ et1)⟩
      simp only [← hray, dif_pos hx.2]
      refine ((g hx).unique (gh _ et0) xq.le).self_of_nhdsSet (x := ⟨e, x⟩) ⟨rfl, ?_⟩
      simp only [mem_closedBall, Complex.dist_eq, sub_zero, le_refl]
  use ray; intro c p p0 h
  exact (g ⟨p0, h⟩).congr (loc ⟨p0, h⟩).symm
