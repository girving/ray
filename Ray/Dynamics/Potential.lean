module
public import Ray.Dynamics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Tactic.Cases
import Mathlib.Topology.AlexandrovDiscrete
import Ray.Dynamics.BottcherNear
import Ray.Dynamics.BottcherNearM
import Ray.Manifold.Analytic
import Ray.Manifold.Inverse
import Ray.Manifold.Nontrivial
import Ray.Manifold.OneDimension
import Ray.Misc.Topology

/-!
## The potential map for a superattracting fixpoint

Let `s : Super f d a`, so that `a` is a superattracting fixpoint of `f c` of order d.
`Bottcher.lean` defines local Böttcher coordinates `s.bottcherNear` near `a`.

Throughout the basin of attraction of `f` to `a`, we define a `[0,1)`-valued `s.potential`
function that measures how fast `f`-iteration converges to `a`.  We define `s.potential c z = 1`
if `z` doesn't attract to `a`, to give a `[0,1]`-valued map defined everywhere in the manifold.
`s.potential` is `ℝ`-valued rather than `ℂ`-valued since it is defined via iterated `d`th roots,
which may not have globally continuously definable argument.

If `a` has no preimages under `f c` besides itself (`OnePreimage s`), then `s.potential` is
continuous everywhere.  This is true for the Mandelbrot and Multibrot sets, but is not true
for the Newton fractal of `z ↦ z^3 - 1` for example: `s.potential c z = 0` if `z` is an exact
iterated preimage of `a`, but such points cluster near `z = 0` with `s.potential c 0 = 1`.

## Removing the one preimage constraint

The `OnePreimage s` can be replaced by restricting to the basin of attraction.  This is mostly
straightforward, but requires working over noncompact manifolds, using compactness of levelsets
of `s.potential`.
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}

/-- If we're in the basin, we have a stable potential value -/
lemma Super.exists_potential (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∃ p : ℝ, 0 ≤ p ∧ ∀ᶠ n in atTop, ‖s.bottcherNear c ((f c)^[n] z)‖ = p ^ d ^ n := by
  obtain ⟨n,a⟩ := s.basin_iff_near.mp m
  generalize hb : ‖s.bottcherNear c ((f c)^[n] z)‖ = b
  have b0 : 0 ≤ b := by bound
  refine ⟨b ^ ((d : ℝ) ^ n)⁻¹, by bound, Filter.eventually_atTop.mpr ⟨n, fun k nk ↦ ?_⟩⟩
  rw [← Nat.sub_add_cancel nk, Function.iterate_add_apply]
  simp only [s.bottcherNear_eqn_iter a, hb, norm_pow, ← Real.rpow_natCast, Nat.cast_pow,
    ← Real.rpow_mul b0, ← div_eq_inv_mul, ← Real.rpow_sub (Nat.cast_pos.mpr s.dp),
    Nat.cast_add, add_sub_cancel_right]

/-- `potential` in terms of any `s.near` iterate -/
theorem Super.potential_eq (s : Super f d a) (m : (c, (f c)^[n] z) ∈ s.near) :
    s.potential c z = ‖s.bottcherNear c ((f c)^[n] z)‖ ^ (d ^ n : ℝ)⁻¹ := by
  have mb : (c, z) ∈ s.basin := s.basin_iff_near.mpr ⟨_, m⟩
  have ep := s.exists_potential mb
  simp only [Super.potential, mb, ep, true_and, dite_eq_left]
  obtain ⟨p0, ph⟩ := choose_spec ep
  generalize hp : choose ep = p at ph p0
  clear hp ep
  obtain ⟨k, ph⟩ := Filter.eventually_atTop.mp ph
  have e : ‖s.bottcherNear c ((f c)^[n] z)‖ ^ d ^ k = p ^ d ^ (k + n) := by
    refine Eq.trans ?_ (ph _ (by omega))
    rw [Function.iterate_add_apply, s.bottcherNear_eqn_iter m, norm_pow]
  generalize hb : ‖s.bottcherNear c ((f c)^[n] z)‖ = b at e
  have b0 : 0 ≤ b := by bound
  trans (p ^ d ^ (k + n)) ^ (d ^ (k + n) : ℝ)⁻¹
  · simp only [← Real.rpow_natCast (x := p), ← Real.rpow_mul p0, Nat.cast_pow]
    rw [mul_inv_cancel₀ (by simp [s.d0]), Real.rpow_one]
  · have d0 : (d ^ k : ℝ) ≠ 0 := by simp [s.d0]
    rw [← e, ← Real.rpow_natCast (x := b), ← Real.rpow_mul b0, Nat.cast_pow, pow_add]
    field_simp [d0]

/-- `‖bottcherNear‖` in terms of `potential` -/
theorem Super.norm_bottcherNear (s : Super f d a) {n : ℕ} (r : (c, (f c)^[n] z) ∈ s.near) :
    ‖s.bottcherNear c ((f c)^[n] z)‖ = s.potential c z ^ d ^ n := by
  rw [s.potential_eq r, ← Real.rpow_natCast, ← Real.rpow_mul (by bound), Nat.cast_pow,
    inv_mul_cancel₀ (by simp [s.d0]), Real.rpow_one]

/-- `potential a = 0` -/
public theorem Super.potential_a (s : Super f d a) : s.potential c a = 0 := by
  have r : (c, (f c)^[0] a) ∈ s.near := by simp only [Function.iterate_zero, s.mem_near, id]
  simp only [s.potential_eq r, Function.iterate_zero, id, s.bottcherNear_a,
    norm_zero, pow_zero, inv_one, Real.rpow_one]

/-- If `z` isn't in the basin, `potential = 1` -/
public theorem Super.potential_eq_one (s : Super f d a) (a : (c, z) ∉ s.basin) :
    s.potential c z = 1 := by
  simp [Super.potential, a]

/-- If `z` is in the basin, `potential < 1` -/
public theorem Super.potential_lt_one (s : Super f d a) (a : (c, z) ∈ s.basin) :
    s.potential c z < 1 := by
  obtain ⟨n, r⟩ := s.basin_iff_near.mp a
  simp only [s.potential_eq r]
  exact Real.rpow_lt_one (norm_nonneg _) (s.bottcherNear_lt_one r) (by bound)

/-- `z` is in the basin iff `potential < 1` -/
public theorem Super.potential_lt_one_iff (s : Super f d a) :
    s.potential c z < 1 ↔ (c, z) ∈ s.basin := by
  refine ⟨fun h ↦ ?_, s.potential_lt_one⟩
  contrapose h
  simp only [s.potential_eq_one h, lt_self_iff_false, not_false_iff]

/-- `potential ≤ 1` -/
@[bound] public theorem Super.potential_le_one (s : Super f d a) : s.potential c z ≤ 1 := by
  by_cases a : (c, z) ∈ s.basin
  exact (s.potential_lt_one a).le
  exact le_of_eq (s.potential_eq_one a)

/-- `0 ≤ potential` -/
@[bound] public theorem Super.potential_nonneg (s : Super f d a) : 0 ≤ s.potential c z := by
  by_cases r : (c, z) ∈ s.basin
  · rcases s.basin_iff_near.mp r with ⟨n, r⟩
    simp only [s.potential_eq r]; bound
  · simp only [s.potential_eq_one r, zero_le_one]

/-- The defining equation of `s.potential` -/
public theorem Super.potential_eqn (s : Super f d a) :
    s.potential c (f c z) = s.potential c z ^ d := by
  by_cases a : (c, z) ∈ s.basin
  · rcases s.basin_iff_near.mp a with ⟨n, a⟩
    have a' : (c, (f c)^[n] (f c z)) ∈ s.near := by
      simp only [← Function.iterate_succ_apply, Function.iterate_succ', s.stays_near a,
        Function.comp]
    simp only [s.potential_eq a, s.potential_eq a', ← Function.iterate_succ_apply,
      Function.iterate_succ', s.bottcherNear_eqn a, norm_pow, ← Real.rpow_natCast, ←
      Real.rpow_mul (norm_nonneg _), mul_comm, Function.comp]
  · have a' : (c, f c z) ∉ s.basin := by
      contrapose a
      simp only [s.basin_iff_near, ← Function.iterate_succ_apply] at a ⊢
      rcases a with ⟨n, a⟩; exact ⟨n + 1, a⟩
    simp only [s.potential_eq_one a, s.potential_eq_one a', one_pow]

/-- The potential equation, iterated -/
public theorem Super.potential_eqn_iter (s : Super f d a) (n : ℕ) :
    s.potential c ((f c)^[n] z) = s.potential c z ^ d ^ n := by
  induction' n with n h
  · simp only [Function.iterate_zero, id, pow_zero, pow_one]
  · simp only [Function.iterate_succ', Super.potential_eqn, h, ← pow_mul, ← pow_succ,
      Function.comp]

/-- Our standard iteration is analytic -/
theorem Super.iter_mAnalytic' (s : Super f d a) (n : ℕ) :
    ContMDiff II I ω fun p : ℂ × S ↦ (f p.1)^[n] p.2 := by
  intro p; induction' n with n h; simp [Function.iterate_zero, contMDiffAt_snd]
  simp only [Function.iterate_succ', Function.comp_def]
  exact (s.fa _).comp₂ contMDiffAt_fst h

theorem Super.iter_mAnalytic (s : Super f d a) (n : ℕ) :
    ContMDiff II II ω fun p : ℂ × S ↦ (p.1, (f p.1)^[n] p.2) := by
  intro p; apply contMDiffAt_fst.prodMk; apply s.iter_mAnalytic'

/-- `s.potential` is continuous where we attract -/
theorem ContinuousAt.potential_of_reaches (s : Super f d a) (a : (c, z) ∈ s.basin) :
    ContinuousAt (uncurry s.potential) (c, z) := by
  obtain ⟨n,a⟩ := s.basin_iff_near.mp a
  have e : uncurry s.potential =ᶠ[𝓝 (c, z)]
      fun p : ℂ × S ↦ ‖s.bottcherNear p.1 ((f p.1)^[n] p.2)‖ ^ (d ^ n : ℝ)⁻¹ := by
    have a' : ∀ᶠ p : ℂ × S in 𝓝 (c, z), (p.1, (f p.1)^[n] p.2) ∈ s.near :=
      (s.iter_mAnalytic n _).continuousAt.eventually_mem (s.isOpen_near.mem_nhds a)
    refine a'.mp (.of_forall fun p h ↦ ?_)
    simp only [uncurry, s.potential_eq h]
  simp only [continuousAt_congr e]
  refine ContinuousAt.rpow ?_ continuousAt_const ?_
  · apply continuous_norm.continuousAt.comp
    refine ((s.bottcherNear_mAnalytic' ?_).comp _ (s.iter_mAnalytic n (c, z))).continuousAt
    exact a
  · bound

/-- `s.potential = 0` exactly on iterated preimages of `a` -/
theorem Super.potential_eq_zero (s : Super f d a) : s.potential c z = 0 ↔ ∃ n, (f c)^[n] z = a := by
  constructor
  · intro h
    by_cases r : (c, z) ∈ s.basin
    · rcases s.basin_iff_near.mp r with ⟨n, r⟩
      simp only [s.potential_eq r, Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _), norm_eq_zero,
        s.bottcherNear_eq_zero r] at h
      use n, h.1
    · simp only [s.potential_eq_one r, one_ne_zero] at h
  · intro p; rcases p with ⟨n, p⟩
    have nz : d^n > 0 := pow_pos s.dp _
    rw [← pow_eq_zero_iff nz.ne', ← s.potential_eqn_iter n, p, s.potential_a]

/-- `s.potential` is upper semicontinuous unconditionally -/
theorem UpperSemicontinuous.potential (s : Super f d a) :
    UpperSemicontinuous (uncurry s.potential) := by
  intro ⟨c, z⟩
  by_cases r : (c, z) ∈ s.basin
  · exact (ContinuousAt.potential_of_reaches s r).upperSemicontinuousAt
  · simp only [uncurry, SemicontinuousAt, s.potential_eq_one r]
    exact fun y y1 ↦ .of_forall fun p ↦ lt_of_le_of_lt s.potential_le_one y1

theorem Super.preimage_eq' (s : Super f d a) [o : OnePreimage s] : f c z = a ↔ z = a := by
  have e := o.eq_a c z; refine ⟨e, ?_⟩; intro e; simp only [e, s.f0]

public theorem Super.preimage_eq (s : Super f d a) [o : OnePreimage s] {n : ℕ} :
    (f c)^[n] z = a ↔ z = a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply', s.preimage_eq', h]

public theorem Super.potential_eq_zero_of_onePreimage (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.potential c z = 0 ↔ z = a := by
  constructor
  · intro h; rw [s.potential_eq_zero] at h; rcases h with ⟨n, h⟩; rw [s.preimage_eq] at h; exact h
  · intro h; simp only [h, s.potential_a]

public theorem Super.potential_ne_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.potential c z ≠ 0 ↔ z ≠ a := by simp only [Ne, s.potential_eq_zero_of_onePreimage]

public theorem Super.potential_pos (s : Super f d a) [OnePreimage s] (c : ℂ) :
    0 < s.potential c z ↔ z ≠ a := by
  rw [← s.potential_ne_zero c]
  use ne_of_gt, fun ne ↦ ne.symm.lt_of_le s.potential_nonneg

/-- `f` can't get from far from `(c,a)` to arbitrarily close to `(c,a)` in one step -/
theorem Super.no_jump (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ) (n : Set (ℂ × S))
    (no : IsOpen n) (na : (c, a) ∈ n) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), ∀ q, p = s.fp q → q ∈ n := by
  have h : ∀ q : ℂ × S, f q.1 q.2 = a → q.2 = a := fun _ ↦ by simp only [s.preimage_eq', imp_self]
  contrapose h
  simp only [Filter.not_eventually, not_forall, exists_prop] at h
  set t := s.fp '' (closedBall c 1 ×ˢ univ ∩ nᶜ)
  have tc : IsClosed t := by
    refine (IsCompact.image ?_ s.fpa.continuous).isClosed
    exact ((isCompact_closedBall _ _).prod isCompact_univ).inter_right no.isClosed_compl
  have th : ∃ᶠ p in 𝓝 (c, a), p ∈ t := by
    have mb : ∀ᶠ p : ℂ × S in 𝓝 (c, a), p.1 ∈ closedBall c 1 :=
      continuousAt_fst.eventually_mem_nhd (Metric.closedBall_mem_nhds _ zero_lt_one)
    refine (h.and_eventually mb).mp (.of_forall fun p i ↦ ?_)
    rcases i with ⟨⟨q, qp, m⟩, b⟩
    simp only [Prod.ext_iff] at qp; simp only [qp.1] at b
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_prod_eq, Set.mem_univ,
      and_true, Prod.ext_iff, t]
    use q, ⟨b, m⟩, qp.1.symm, qp.2.symm
  have m := th.mem_of_closed tc
  rcases(Set.mem_image _ _ _).mp m with ⟨p, m, pa⟩
  simp only [Super.fp, Prod.mk_inj] at pa
  simp only [not_forall]; use p, pa.2
  contrapose m
  rw [← @Prod.mk.eta _ _ p, pa.1, m]
  simp only [Set.mem_inter_iff, Set.prodMk_mem_set_prod_eq, Metric.mem_closedBall, dist_self,
    zero_le_one, Set.mem_univ, Set.mem_compl_iff, true_and, not_not, na]

/-- A barrier is a compact, annular region around `a` (but not containing it) such that
    outside points must pass through it to reach `a`. -/
structure Barrier (s : Super f d a) (c : ℂ) (n t : Set (ℂ × S)) : Prop where
  compact : IsCompact t
  tn : t ⊆ n
  near : t ⊆ s.near
  hole : ∀ e, (e, a) ∉ t
  barrier : ∀ᶠ e in 𝓝 c, ∀ z, (e, z) ∉ n → Attracts (f e) z a → ∃ n, (e, (f e)^[n] z) ∈ t

/-- `f` can't get from far from `(c,a)` to close to `(c,a)` without passing through a barrier -/
theorem Super.barrier (s : Super f d a) [OnePreimage s] [T2Space S] (n : Set (ℂ × S))
    (no : IsOpen n) (na : (c, a) ∈ n) : ∃ t : Set (ℂ × S), Barrier s c n t := by
  set n' := n ∩ s.near
  have nn' : n' ∈ 𝓝 (c, a) :=
    Filter.inter_mem (no.mem_nhds na) (s.isOpen_near.mem_nhds (s.mem_near c))
  rcases (Filter.hasBasis_iff.mp (compact_basis_nhds (c, a)) n').mp nn' with ⟨u, ⟨un, uc⟩, us⟩
  simp only [Set.subset_inter_iff, n'] at us
  rcases eventually_nhds_iff.mp
      (s.no_jump c (interior u) isOpen_interior (mem_interior_iff_mem_nhds.mpr un)) with
    ⟨i, ih, io, ia⟩
  rcases mem_nhds_prod_iff'.mp (Filter.inter_mem un (io.mem_nhds ia)) with
    ⟨i0, i1, i0o, i0m, i1o, i1m, ii⟩
  simp only [Set.subset_inter_iff] at ii
  set t := u \ univ ×ˢ i1
  have ta : ∀ e, (e, a) ∉ t := fun e ↦
    Set.notMem_sdiff_of_mem (Set.mk_mem_prod (Set.mem_univ _) i1m)
  use t
  refine ⟨uc.diff (isOpen_univ.prod i1o), subset_trans sdiff_subset us.1,
      subset_trans sdiff_subset us.2, ta, ?_⟩
  rw [eventually_nhds_iff]; use i0; refine ⟨?_, i0o, i0m⟩
  intro e em z zm za
  rcases tendsto_atTop_nhds.mp za i1 i1m i1o with ⟨m, mh⟩
  have en : ∃ n, (f e)^[n] z ∈ i1 := ⟨m, mh m (le_refl _)⟩
  set n := Nat.find en
  use n - 1
  have ni1 : (f e)^[n] z ∈ i1 := Nat.find_spec en
  have n0 : n ≠ 0 := by
    contrapose zm
    simp only [zm, Function.iterate_zero, id_eq] at ni1
    exact us.1 (ii.1 (Set.mk_mem_prod em ni1))
  have nt : (f e)^[n-1] z ∉ i1 := Nat.find_min en (Nat.pred_lt n0)
  apply Set.mem_sdiff_of_mem
  · apply interior_subset; apply ih (e, (f e)^[n] z) (ii.2 (Set.mk_mem_prod em ni1))
    simp only [Super.fp]; rw [← Function.iterate_succ_apply' (f e) (n - 1)]
    simp only [Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.pos_of_ne_zero n0))]
  · contrapose nt
    simp only [Set.prodMk_mem_set_prod_eq] at nt ⊢
    exact nt.2

/-- `s.potential` is large on barriers (because they are compact) -/
theorem Barrier.potential_large {s : Super f d a} [OnePreimage s] {n t : Set (ℂ × S)}
    (b : Barrier s c n t) : ∃ r : ℝ, r > 0 ∧ ∀ e z, (e, z) ∈ t → r ≤ s.potential e z := by
  by_cases t0 : t = ∅
  · use 1, zero_lt_one
    simp only [t0, Set.mem_empty_iff_false, IsEmpty.forall_iff, forall_const, imp_true_iff]
  simp only [← ne_eq, ← Set.nonempty_iff_ne_empty] at t0
  have pc : ContinuousOn (uncurry s.potential) t := by
    refine ContinuousOn.mono ?_ b.near
    intro ⟨c, z⟩ m; apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.potential_of_reaches s
    simp only [s.basin_iff_near]
    use 0
    simpa only [Function.iterate_zero_apply]
  rcases b.compact.exists_isMinOn t0 pc with ⟨⟨e, z⟩, ps, pm⟩
  use s.potential e z; constructor
  · have h := b.hole e; contrapose h; simp only [not_lt] at h
    have h' := le_antisymm h s.potential_nonneg
    simp only [s.potential_eq_zero, s.preimage_eq, exists_const] at h'
    simp only [← h', ps]
  · intro e z m; simp only [isMinOn_iff, uncurry] at pm ⊢; exact pm _ m

/-- The first `n` preimages of a barrier -/
@[nolint unusedArguments]
def Barrier.fast {s : Super f d a} {n t : Set (ℂ × S)} (_ : Barrier s c n t) (m : ℕ) :
    Set (ℂ × S) :=
  ⋃ k : Fin m, (fun p : ℂ × S ↦ (p.1, (f p.1)^[k] p.2)) ⁻¹' t

theorem Barrier.closed_fast {s : Super f d a} [T2Space S] {n t : Set (ℂ × S)} (b : Barrier s c n t)
    (m : ℕ) : IsClosed (b.fast m) := by
  apply isClosed_iUnion_of_finite; intro k; refine IsClosed.preimage ?_ b.compact.isClosed
  apply continuous_fst.prodMk; generalize hn : (k : ℕ) = n; clear k hn; induction' n with n h
  simp only [Function.iterate_zero_apply]; exact continuous_snd
  simp only [Function.iterate_succ_apply']; exact s.fa.continuous.comp (continuous_fst.prodMk h)

theorem Barrier.mem_fast {s : Super f d a} {n t : Set (ℂ × S)} (b : Barrier s c n t) {m : ℕ} {e : ℂ}
    {z : S} : (e, z) ∈ b.fast m ↔ ∃ n, n < m ∧ (e, (f e)^[n] z) ∈ t := by
  simp only [Barrier.fast, Set.mem_iUnion, Set.mem_preimage]; constructor
  intro h; rcases h with ⟨n, h⟩; use n, Fin.is_lt _, h
  intro h; rcases h with ⟨n, nm, h⟩; use⟨n, nm⟩, h

theorem Barrier.fast_reaches {s : Super f d a} {n t : Set (ℂ × S)} (b : Barrier s c n t) {m : ℕ}
    {e : ℂ} {z : S} (q : (e, z) ∈ b.fast m) : ∃ n, (e, (f e)^[n] z) ∈ s.near := by
  rw [b.mem_fast] at q; rcases q with ⟨n, _, q⟩; exact ⟨n, b.near q⟩

/-- `s.potential` is everywhere lower semicontinuous (and thus continuous) if `OnePreimage s` -/
public theorem Continuous.potential (s : Super f d a) [OnePreimage s] [T2Space S] :
    Continuous (uncurry s.potential) := by
  -- Reduce to showing that nearby bounded potential means reaches
  refine continuous_iff_lower_upperSemicontinuous.mpr ⟨?_, UpperSemicontinuous.potential s⟩
  intro ⟨c, z⟩
  by_cases re : (c, z) ∈ s.basin
  · exact (ContinuousAt.potential_of_reaches s re).lowerSemicontinuousAt
  intro y y1
  simp only [uncurry, s.potential_eq_one re] at y1 ⊢
  contrapose re
  simp only [Filter.not_eventually, not_lt] at re
  -- Construct a barrier separating (c,z) from (c,a)
  by_cases za : z = a
  · simp only [s.basin_iff_near]
    use 0
    simp only [za, Function.iterate_zero_apply, s.mem_near c]
  have sn : {(c, a)}ᶜ ∈ 𝓝 (c, z) :=
    compl_singleton_mem_nhds (by simp only [za, Ne, Prod.mk_inj, and_false, not_false_iff])
  rcases (Filter.hasBasis_iff.mp (compact_basis_nhds (c, z)) ({(c, a)}ᶜ)).mp sn with
    ⟨u, ⟨un, uc⟩, ua⟩
  simp only [Set.subset_compl_singleton_iff] at ua
  rcases s.barrier (uᶜ) uc.isClosed.isOpen_compl (Set.mem_compl ua) with ⟨t, b⟩
  rcases b.potential_large with ⟨r, rp, rt⟩
  -- `potential ≤ y →` reaches the barrier quickly
  have en : ∃ n, ∀ᶠ e in 𝓝 c, ∀ z, (e, z) ∈ u → s.potential e z ≤ y → (e, z) ∈ b.fast n := by
    -- Find n s.t. y ^ (d^n) < r
    rcases exists_pow_lt_of_lt_one rp y1 with ⟨k, ky⟩
    rcases Filter.exists_le_of_tendsto_atTop (tendsto_pow_atTop_atTop_of_one_lt s.d1) 0 k
      with ⟨n, _, nk⟩
    use n
    -- Our upper bound on `potential e z`, plus on our lower bound on `t`,
    -- implies that `z` reaches near quickly
    refine b.barrier.mp (.of_forall fun e h z m py ↦ ?_)
    have za : Attracts (f e) z a := by
      by_cases r : (e, z) ∈ s.basin
      · rcases s.basin_iff_near.mp r with ⟨n, r⟩; exact s.attracts r
      · rw [s.potential_eq_one r] at py; linarith
    rcases h z (notMem_compl_iff.mpr m) za with ⟨o, oh⟩
    by_cases no : n ≤ o
    · have pyo : s.potential e z ^ d ^ o ≤ y ^ d ^ o := by bound
      rw [← s.potential_eqn_iter o] at pyo
      have ryo : r ≤ y ^ d ^ o := _root_.trans (rt _ _ oh) pyo
      have kdo : k ≤ d ^ o := _root_.trans nk (Nat.pow_le_pow_right s.dp no)
      have ryk : r ≤ y ^ k :=
        _root_.trans ryo (pow_le_pow_of_le_one (_root_.trans s.potential_nonneg py) y1.le kdo)
      linarith
    · simp only [not_le] at no; rw [b.mem_fast]; use o, no, oh
  -- Now that we've bounded n, (c,z) must reach near
  rcases en with ⟨n, h⟩
  rcases eventually_nhds_iff.mp h with ⟨v, vh, vo, vc⟩
  have ev : ∀ᶠ p : ℂ × S in 𝓝 (c, z), p ∈ u ∩ v ×ˢ univ := by
    simp only [Filter.eventually_iff, Set.ofPred_mem_eq]
    exact Filter.inter_mem un ((vo.prod isOpen_univ).mem_nhds (Set.mk_mem_prod vc (Set.mem_univ _)))
  have ef : ∃ᶠ p in 𝓝 (c, z), p ∈ b.fast n := by
    refine (re.and_eventually ev).mp (.of_forall ?_)
    intro ⟨e, z⟩ ⟨zy, m⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true] at m
    exact vh e m.2 z m.1 zy
  rcases b.mem_fast.mp (ef.mem_of_closed (b.closed_fast _)) with ⟨n, _, r⟩
  exact s.basin_iff_near.mpr ⟨n, b.near r⟩

/-- potential levelsets form a neighborhood basis at `a` (open version) -/
theorem Super.potential_basis' (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ) {t : Set S}
    (n : t ∈ 𝓝 a) (o : IsOpen t) :
    ∃ p, 0 < p ∧ {z | s.potential c z < p} ⊆ t := by
  by_cases ne : tᶜ = ∅
  · use 1, zero_lt_one; simp only [compl_empty_iff] at ne; rw [ne]; exact subset_univ _
  replace ne := Set.Nonempty.image (s.potential c) (nonempty_iff_ne_empty.mpr ne)
  have pos : ∀ p : ℝ, p ∈ s.potential c '' tᶜ → 0 ≤ p := by
    intro p m; simp only [mem_image] at m; rcases m with ⟨z, _, e⟩; rw [← e]
    exact s.potential_nonneg
  have below : BddBelow (s.potential c '' tᶜ) := bddBelow_def.mpr ⟨0, pos⟩
  generalize hq : sInf (s.potential c '' tᶜ) = q
  have qt : ∀ z, s.potential c z < q → z ∈ t := by
    intro z i; contrapose i; simp only [not_lt, ← hq]; apply csInf_le below
    simp only [mem_image]; use z, i
  have qp : 0 < q := by
    simp only [← hq]
    have mc := csInf_mem_closure ne below
    rw [IsClosed.closure_eq] at mc
    · simp only [mem_image] at mc; rcases mc with ⟨z, m, e⟩
      rw [← e]; contrapose m
      replace m := le_antisymm (not_lt.mp m) s.potential_nonneg
      rw [s.potential_eq_zero_of_onePreimage] at m; simp only [m, notMem_compl_iff]
      exact mem_of_mem_nhds n
    · exact (o.isClosed_compl.isCompact.image (Continuous.potential s).along_snd).isClosed
  use q, qp, qt

/-- potential levelsets form a neighborhood basis at `a` (general version) -/
public theorem Super.potential_basis (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ)
    {t : Set S} (n : t ∈ 𝓝 a) : ∃ p, 0 < p ∧ {z | s.potential c z < p} ⊆ t := by
  rcases mem_nhds_iff.mp n with ⟨t', tt, o, m⟩
  rcases s.potential_basis' c (o.mem_nhds m) o with ⟨p, pp, sub⟩
  use p, pp, _root_.trans sub tt
