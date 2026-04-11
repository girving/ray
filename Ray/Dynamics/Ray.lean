module
public import Ray.Dynamics.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Tactic.Cases
import Ray.Dynamics.Grow
import Ray.Dynamics.Postcritical
import Ray.Dynamics.Potential
import Ray.Manifold.Analytic
import Ray.Manifold.LocalInj
import Ray.Manifold.Nontrivial
import Ray.Manifold.OneDimension
import Ray.Manifold.OpenMapping
import Ray.Misc.Connected
import Ray.Misc.Topology

/-
## The external ray map

We define the external ray map `s.ray` on all postcritical points `(c,z)` (points where
`s.potential c z < s.potential c w` for all non-`a` critical points `w` of `f c`).

The existence of `s.ray` was proven in `Grow.lean` as `Super.has_ray`.  Here we define the
map, write down its basic properties, and prove that `(c,y) ↦ (c, s.ray c y)` is a
bijection from `s.ext` to `s.post`, where `s.ext = {(c,y) | abs y < s.p c}`.

Note that while our `s.ray` map is defined for all `c`, we are working in dynamical space:
the key varying coordinate is `z`.  In particular, our bijection result is equivalent to
`s.ray c` being a bijection from `ball 0 (s.p c)` to `{z | s.potential c z < s.p c}` for all `c`.

We still haven't defined Böttcher coordinates except near `a`, but their existence is immediate
from bijectivity of `s.ray`; see `Bottcher.lean`.
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
variable {c x : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {s : Super f d a}
variable {y : ℂ × ℂ}

/-- The `c`-slice of `s.ext` is `ball 0 (s.p c)` -/
theorem Super.ext_slice (s : Super f d a) (c : ℂ) :
    {x | (c, x) ∈ s.ext} = ball (0 : ℂ) (s.p c) := by
  apply Set.ext; intro x; simp only [Super.ext, mem_ball, mem_setOf, Complex.dist_eq, sub_zero]

variable [T2Space S]

/-- The external ray map: `s.ray c y` is moving in external ray space from the superattractor `a`
    out by `y`.  `s.ray` is well behaved for all postcritical values `(c,y) ∈ s.ext` (see below). -/
public def Super.ray (s : Super f d a) [OnePreimage s] : ℂ → ℂ → S :=
  choose s.has_ray

/-- `s.ext` is open -/
public theorem Super.isOpen_ext (s : Super f d a) [OnePreimage s] : IsOpen s.ext := by
  set f := fun y : ℂ × ℂ ↦ s.p y.1 - ‖y.2‖
  have fc : LowerSemicontinuous f :=
    (s.lowerSemicontinuous_p.comp continuous_fst).add
      (continuous_norm.comp continuous_snd).neg.lowerSemicontinuous
  have e : s.ext = f ⁻¹' Ioi 0 :=
    Set.ext fun _ ↦ by simp only [Super.ext, mem_setOf, mem_preimage, mem_Ioi, sub_pos, f]
  rw [e]; exact fc.isOpen_preimage _

/-- `(c,0) ∈ s.ext` -/
@[simp] public theorem Super.mem_ext (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (c, (0 : ℂ)) ∈ s.ext := by
  simp only [Super.ext, mem_setOf, norm_zero, s.p_pos c]

/-- `c`-slices of `s.ext` are connected -/
public theorem Super.ext_slice_connected (s : Super f d a) [OnePreimage s] (c : ℂ) :
    IsConnected {x | (c, x) ∈ s.ext} := by
  rw [s.ext_slice c]
  exact ⟨⟨(0 : ℂ), mem_ball_self (s.p_pos c)⟩, (convex_ball (0 : ℂ) (s.p c)).isPreconnected⟩

/-- `s.ext` is connected (since `c`-slices and `univ ×ˢ {0}` are connected) -/
public theorem Super.ext_connected (s : Super f d a) [OnePreimage s] : IsConnected s.ext := by
  refine ⟨⟨(0, 0), s.mem_ext 0⟩, isPreconnected_of_forall (0, 0) ?_⟩; intro ⟨c, x⟩ m
  use(fun x ↦ (c, x)) '' {x | (c, x) ∈ s.ext} ∪ univ ×ˢ {0}
  simp only [mem_image, mem_union, union_subset_iff, mem_setOf, mem_prod_eq, mem_univ, true_and,
    mem_singleton_iff, or_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y n; simp only [mem_image, mem_setOf] at n; rcases n with ⟨x, m, e⟩; rw [e] at m; exact m
  · intro ⟨c, x⟩ m; simp only [mem_prod_eq, mem_singleton_iff] at m; rw [m.2]; exact s.mem_ext c
  · left; exact ⟨x, m, rfl⟩
  · refine IsPreconnected.union (c, 0) ?_ ?_ ?_ ?_
    · use 0, s.mem_ext c
    · exact mk_mem_prod (mem_univ _) rfl
    · exact IsPreconnected.image (s.ext_slice_connected c).isPreconnected _
        (Continuous.prodMk_right _).continuousOn
    · exact isPreconnected_univ.prod isPreconnected_singleton

/-- `s.ray` satisfies `Grow` (it looks like a local inverse to Böttcher coordinates) -/
lemma Super.ray_spec (s : Super f d a) [OnePreimage s] :
    ∀ {c p}, 0 ≤ p → p < s.p c → Grow s c p (s.np c p) s.ray :=
  fun {c p} ↦ choose_spec s.has_ray c p

/-- `s.ray` satisfies `Eqn` -/
lemma Super.ray_eqn_self (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    Eqn s (s.np c ‖x‖) s.ray (c, x) :=
  (s.ray_spec (norm_nonneg _) post).eqn.self_of_nhdsSet _ mem_domain_self

/-- `s.ray` is analytic on `s.ext` (up to the critical potential for each `c`) -/
public theorem Super.ray_mAnalytic (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    ContMDiffAt II I ω (uncurry s.ray) (c, x) :=
  (s.ray_eqn_self post).holo

/-- `s.ray c` is analytic up to the critical potential (that is, on `ball 0 (s.p c)`) -/
theorem Super.ray_mAnalytic_slice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ContMDiffOnNhd I I (s.ray c) {x | (c, x) ∈ s.ext} := fun _ m ↦ (s.ray_mAnalytic m).along_snd

/-- `s.ray` is analytic on `s.ext` (up to the critical potential for each `c`) -/
public theorem Super.ray_mAnalyticOn (s : Super f d a) [OnePreimage s] :
    ContMDiffOnNhd II I (uncurry s.ray) s.ext := by intro ⟨c, x⟩ m; exact s.ray_mAnalytic m

/-- Rays start at `a`: `s.ray c 0 = a` -/
@[simp] public theorem Super.ray_zero (s : Super f d a) [OnePreimage s] (c : ℂ) : s.ray c 0 = a :=
  (s.ray_spec (le_refl _) (s.p_pos c)).zero

/-- `s.ray` maps `s.ext` into `s.basin` -/
public theorem Super.ray_basin (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, s.ray c x) ∈ s.basin :=
  s.basin_iff_near.mpr ⟨_, (s.ray_eqn_self post).near⟩

/-- `s.ray` maps into `s.near` with if we iterate `s.np c ‖x‖` times -/
theorem Super.ray_near (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, (f c)^[s.np c ‖x‖] (s.ray c x)) ∈ s.near :=
  (s.ray_eqn_self post).near

/-- `s.ray` inverts `s.bottcherNear` near 0 -/
public theorem Super.ray_eqn_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ∀ᶠ y : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear y.1 (s.ray y.1 y.2) = y.2 :=
  (s.ray_spec (le_refl _) (s.p_pos c)).start

/-- `s.ray` inverts `s.bottcherNear` after iteration -/
theorem Super.ray_eqn_iter' (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x),
      s.bottcherNearIter (s.np c ‖x‖) y.1 (s.ray y.1 y.2) = y.2 ^ d ^ s.np c ‖x‖ :=
  ((s.ray_spec (norm_nonneg _) post).eqn.filter_mono (nhds_le_nhdsSet mem_domain_self)).mp
    (.of_forall fun _ e ↦ e.eqn)

/-- `s.ray` sends absolute value to potential -/
public theorem Super.ray_potential (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    s.potential c (s.ray c x) = ‖x‖ :=
  (s.ray_eqn_self post).potential

/-- `s.ray` maps `s.ext` into `s.post` -/
public theorem Super.ray_post (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, s.ray c x) ∈ s.post := by
  simp only [Super.post, Postcritical, mem_setOf, s.ray_potential post]; exact post

/-- `s.ray` is noncritical at 0 -/
theorem Super.ray_noncritical_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    mfderiv I I (s.ray c) 0 ≠ 0 := by
  have h : mfderiv I I (s.bottcherNear c ∘ s.ray c) 0 ≠ 0 := by
    have e : s.bottcherNear c ∘ s.ray c =ᶠ[𝓝 0] id :=
      (continuousAt_const.prodMk continuousAt_id).eventually (s.ray_eqn_zero c)
    rw [e.mfderiv_eq]; exact id_mderiv_ne_zero
  contrapose h
  have hb : MDifferentiableAt I I (s.bottcherNear c) (s.ray c 0) := by
    rw [s.ray_zero]
    exact (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd.mdifferentiableAt (by decide)
  have hr : MDifferentiableAt I I (s.ray c) 0 :=
    (s.ray_mAnalytic (s.mem_ext c)).along_snd.mdifferentiableAt (by decide)
  rw [mfderiv_comp 0 hb hr, h, ContinuousLinearMap.comp_zero]
  rfl

-- `s.ray` is noncritical everywhere in `s.ext`
public theorem Super.ray_noncritical (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    mfderiv I I (s.ray c) x ≠ 0 := by
  by_cases x0 : x = 0; rw [x0]; exact s.ray_noncritical_zero c
  set n := s.np c ‖x‖
  have h : mfderiv I I (s.bottcherNearIter n c ∘ s.ray c) x ≠ 0 := by
    have e : s.bottcherNearIter n c ∘ s.ray c =ᶠ[𝓝 x] fun x ↦ x ^ d ^ n :=
      (continuousAt_const.prodMk continuousAt_id).eventually (s.ray_eqn_iter' post)
    rw [e.mfderiv_eq]; contrapose x0
    rw [mfderiv_eq_fderiv] at x0
    have hd := (differentiableAt_pow (x := x) (d ^ n)).hasFDerivAt.hasDerivAt.deriv
    apply_fun (fun x ↦ x 1) at x0
    rw [x0] at hd
    have hd0 : deriv (fun y ↦ y ^ d ^ n) x = 0 := by
      exact hd.trans rfl
    simp only [differentiableAt_fun_id, deriv_fun_pow, Nat.cast_pow, deriv_id'', mul_one,
      mul_eq_zero, pow_eq_zero_iff', Nat.cast_eq_zero, s.d0, ne_eq, false_and, false_or] at hd0
    exact hd0.1
  have d := mfderiv_comp x
      ((s.bottcherNearIter_mAnalytic (s.ray_near post)).along_snd.mdifferentiableAt (by decide))
      ((s.ray_mAnalytic post).along_snd.mdifferentiableAt (by decide))
  simp only [Function.comp_def, n] at d h
  intro hx
  apply h
  rw [d, hx, ContinuousLinearMap.comp_zero]
  rfl

/-- `s.ray` is nontrivial, since it is noncritical at 0 and `s.ext` is connected -/
public theorem Super.ray_nontrivial (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    NontrivialMAnalyticAt (s.ray c) x :=
  (nontrivialMAnalyticAt_of_mfderiv_ne_zero (s.ray_mAnalytic (s.mem_ext c)).along_snd
        (s.ray_noncritical_zero c)).on_preconnected
    (s.ray_mAnalytic_slice c).contMDiffOn (s.mem_ext c) (s.isOpen_ext.snd_preimage c)
    (s.ext_slice_connected c).isPreconnected _ post

/-- `s.ray c` is injective, or alternately `(c,x) ↦ (c, s.ray c x)` is injective on `s.ext`.

    We prove this by continuous induction on potential:
    1. `s.ray c` is injective for small potentials, since it is noncritical at (c,0)`
    2. If `s.ray c x0 = s.ray c x1`, we can use the fact that `s.ray` is a local inverse
       to `s.bottcherNear` to find a slightly smaller `t < 1` where
       `s.ray c (t*x0) = s.ray c (t*x1)`
    3. (1) + (2) is a contradiction, since we can walk all the down to `t ≈ 0`. -/
public theorem Super.ray_inj (s : Super f d a) [OnePreimage s] {x0 x1 : ℂ} :
    (c, x0) ∈ s.ext → (c, x1) ∈ s.ext → s.ray c x0 = s.ray c x1 → x0 = x1 := by
  -- Preliminaries
  intro p0 p1 e
  have ax : ‖x0‖ = ‖x1‖ := by simp only [← s.ray_potential p0, ← s.ray_potential p1, e]
  by_cases x00 : x0 = 0
  · simp only [x00, norm_zero] at ax ⊢; exact (norm_eq_zero.mp ax.symm).symm
  have tc : ∀ (x : ℂ) (t), ContinuousAt (fun t : ℝ ↦ ↑t * x) t := fun x t ↦
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have pt : ∀ {x : ℂ} {t : ℝ}, (c, x) ∈ s.ext → t ∈ Ioc (0 : ℝ) 1 → (c, ↑t * x) ∈ s.ext := by
    intro x t p m
    simp only [Super.ext, mem_setOf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos m.1] at p ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) m.2) p
  -- It suffices to show that the set of t's where the x0 and x1 rays match
  -- is relatively clopen in Ioc 0 1
  set u : Set ℝ := {t : ℝ | s.ray c (t * x0) = s.ray c (t * x1)}
  suffices h : Ioc (0 : ℝ) 1 ⊆ interior u by
    replace h := _root_.trans h interior_subset
    replace tc := (tc x0 0).prodMk (tc x1 0)
    simp only [ContinuousAt, Complex.ofReal_zero, MulZeroClass.zero_mul] at tc
    have inj := tc.eventually ((s.ray_mAnalytic (s.mem_ext c)).along_snd.local_inj
      (s.ray_noncritical_zero c))
    rcases Metric.eventually_nhds_iff.mp inj with ⟨r, rp, inj⟩
    simp only [Real.dist_eq, sub_zero] at inj
    set t := min 1 (r / 2)
    have t0 : 0 < t := lt_min zero_lt_one (half_pos rp)
    have t01 : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc.mpr ⟨t0, min_le_left _ _⟩
    specialize @inj t (by simp only [t, abs_of_pos t0, min_lt_of_right_lt (half_lt_self rp)])
      (h t01)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr t0.ne') inj
  refine isPreconnected_Ioc.relative_clopen ?_ ?_ ?_
  · use 1, right_mem_Ioc.mpr zero_lt_one
    simp only [mem_setOf, Complex.ofReal_one, one_mul, e, u]
  · intro t ⟨m, e⟩
    simp only [mem_interior_iff_mem_nhds] at e ⊢
    generalize hn : s.np c ‖↑t * x0‖ = n
    have t0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr m.1.ne'
    have pe : ‖↑t * x0‖ = ‖↑t * x1‖ := by
      simp only [mem_setOf_eq, u] at e
      simp only [← s.ray_potential (pt p0 m), e, ← s.ray_potential (pt p1 m)]
    have e0 := (s.ray_spec (norm_nonneg _) (pt p0 m)).eqn.filter_mono
      (nhds_le_nhdsSet mem_domain_self)
    have e1 := (s.ray_spec (norm_nonneg _) (pt p1 m)).eqn.filter_mono
      (nhds_le_nhdsSet mem_domain_self)
    simp only [← pe, hn] at e0 e1
    have de : (↑t * x0) ^ d ^ n = (↑t * x1) ^ d ^ n := by
      have e0 := e0.self_of_nhds.eqn
      have e1 := e1.self_of_nhds.eqn
      simp only [mem_setOf_eq, u] at e
      simp only [← e] at e0 e1
      exact e0.symm.trans e1
    simp only [mul_pow] at de
    replace de := mul_left_cancel₀ (pow_ne_zero _ t0) de
    generalize hr : (fun e x ↦ s.ray e (x1 / x0 * x)) = r
    have xe : x1 / x0 * (↑t * x0) = ↑t * x1 := by
      rw [← mul_assoc, mul_comm _ (t:ℂ), mul_assoc, div_mul_cancel₀ _ x00]
    have er : ∀ᶠ y in 𝓝 (c, ↑t * x0), Eqn s n r y := by
      rw [← hr]; apply eqn_near
      exact (s.ray_mAnalytic (pt p1 m)).comp₂_of_eq contMDiffAt_fst
          (contMDiffAt_const.mul contMDiffAt_snd) (by simp [xe])
      rw [xe]; exact e1.self_of_nhds.near
      have xc : ContinuousAt (fun y : ℂ × ℂ ↦ (y.1, x1 / x0 * y.2)) (c, ↑t * x0) :=
        continuousAt_fst.prodMk (continuousAt_const.mul continuousAt_snd)
      simp only [ContinuousAt] at xc
      rw [← mul_assoc, mul_comm _ (t:ℂ), mul_assoc, div_mul_cancel₀ _ x00] at xc
      refine (xc.eventually e1).mp (.of_forall ?_); intro ⟨e, x⟩ e1
      exact _root_.trans e1.eqn (by
        simp only [mul_pow, div_pow, ← de, div_self (pow_ne_zero _ x00), one_mul])
    refine ((continuousAt_const.prodMk (Complex.continuous_ofReal.continuousAt.mul
        continuousAt_const)).eventually
        (eqn_unique e0 er ?_ (mul_ne_zero t0 x00))).mp (.of_forall fun u e ↦ ?_)
    · rw [← hr]
      change s.ray c (↑t * x0) = s.ray c (x1 / x0 * (↑t * x0))
      rw [xe]
      simpa [u] using e
    · rw [← hr] at e; simp only [uncurry] at e
      have xeu : x1 / x0 * (↑u * x0) = ↑u * x1 := by
        rw [← mul_assoc, mul_comm _ (u : ℂ), mul_assoc, div_mul_cancel₀ _ x00]
      simpa [xeu] using e
  · intro t ⟨m, e⟩; simp only [mem_closure_iff_frequently] at e ⊢
    have rc : ∀ {x : ℂ}, (c, x) ∈ s.ext → ContinuousAt (fun t : ℝ ↦ s.ray c (↑t * x)) t :=
      fun {x} p ↦
      (s.ray_mAnalytic (pt p m)).along_snd.continuousAt.comp_of_eq
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const) rfl
    exact tendsto_nhds_unique_of_frequently_eq (rc p0) (rc p1) e

/-- Special case of injectivity: `s.ray c x = a` iff `x = 0` -/
@[simp] public lemma Super.ray_eq_a_iff (s : Super f d a) [OnePreimage s] {x : ℂ}
    (m : (c, x) ∈ s.ext) : s.ray c x = a ↔ x = 0 := by
  constructor
  · intro e
    nth_rw 2 [← s.ray_zero (c := c)] at e
    exact s.ray_inj m (s.mem_ext c) e
  · intro e
    simp only [e, s.ray_zero]

/-- `s.ray` surjects from `s.ext` to `s.post`

    We prove this by continuous induction on potential, but phrased in terms of explicit sets.
    Fixing `c`, we have
    1. The image of `s.ray c` is open (by the Open Mapping Theorem)
    2. The image of `s.ray c` restricted to `s.potential c z ≤ p` is closed.
    3. By picking `p` greater than any particular postcritical potential, we cover `s.post`. -/
public theorem Super.ray_surj (s : Super f d a) [OnePreimage s] :
    ∀ {z}, (c, z) ∈ s.post → ∃ x, (c, x) ∈ s.ext ∧ s.ray c x = z := by
  intro z0 m0
  by_contra i0; simp only [not_exists, not_and] at i0
  set p0 := s.potential c z0
  simp only [Super.post, mem_setOf, Postcritical] at m0
  rcases exists_between m0 with ⟨p1, p01, post⟩
  set i := s.ray c '' {x | (c, x) ∈ s.ext}
  set j := {z | s.potential c z ≤ p1} ∩ i
  set u := {z | s.potential c z ≤ p1} \ i
  have pc : Continuous (s.potential c) := (Continuous.potential s).along_snd
  have io : IsOpen i := by
    rw [isOpen_iff_eventually]; intro z ⟨x, m, xz⟩
    have eq := (s.ray_nontrivial m).nhds_eq_map_nhds; rw [xz] at eq
    rw [eq, Filter.eventually_map]
    exact ((s.isOpen_ext.snd_preimage c).eventually_mem m).mp
      (.of_forall fun x m ↦ ⟨x, m, rfl⟩)
  have jc : IsClosed j := by
    have e : j = s.ray c '' closedBall 0 p1 := by
      refine Set.ext fun z ↦ ?_
      simp only [mem_inter_iff, mem_setOf, mem_image, mem_closedBall, Complex.dist_eq, sub_zero, j]
      constructor
      · intro ⟨zp1, x, xp, xz⟩; rw [← xz, s.ray_potential xp] at zp1; use x, zp1, xz
      · intro ⟨x, xp, xz⟩; have zp1 := lt_of_le_of_lt xp post; rw [← xz, s.ray_potential zp1]
        use xp, x, zp1
    rw [e]; refine (IsCompact.image_of_continuousOn (isCompact_closedBall _ _) ?_).isClosed
    intro x m; simp only [mem_closedBall, Complex.dist_eq, sub_zero] at m
    exact (s.ray_mAnalytic (lt_of_le_of_lt m post)).along_snd.continuousAt.continuousWithinAt
  have uc : IsCompact u := ((isClosed_le pc continuous_const).sdiff io).isCompact
  have z0u : z0 ∈ u := by
    simp only [mem_diff, mem_setOf, u]; use p01.le; contrapose i0
    simp only [not_not, not_forall, exists_prop] at i0 ⊢; exact i0
  have ne : u.Nonempty := ⟨z0, z0u⟩
  rcases uc.exists_isMinOn ne pc.continuousOn with ⟨z, zu, zm⟩
  simp only [mem_diff, mem_setOf, u] at zu
  replace zm : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w := by
    have m : z ∈ jᶜ := by rw [compl_inter]; right; exact zu.2
    have lt : s.potential c z < p1 := lt_of_le_of_lt (zm z0u) p01
    apply (jc.isOpen_compl.eventually_mem m).mp
    apply ((Continuous.potential s).along_snd.continuousAt.eventually_lt continuousAt_const lt).mp
    refine .of_forall fun w lt m ↦ ?_
    rw [compl_inter] at m; cases' m with m m
    · simp only [compl_setOf, mem_setOf, not_le] at m; linarith
    · apply zm; simp only [mem_diff, mem_setOf, u]; use lt.le, m
  simp only [mem_setOf, mem_image, not_exists, not_and, i] at zu
  have za := s.potential_minima_only_a (lt_of_le_of_lt zu.1 post) zm
  have h := zu.2 0 (s.mem_ext c); simp only [s.ray_zero] at h; exact h za.symm

/-- `s.ray` is bijective from `s.ext` to `s.post`, accounting for `c` -/
public theorem Super.ray_bij (s : Super f d a) [OnePreimage s] :
    BijOn (fun y : ℂ × ℂ ↦ (y.1, s.ray y.1 y.2)) s.ext s.post := by
  refine ⟨fun _ m ↦ s.ray_post m, ?_, ?_⟩
  · intro ⟨c0, x0⟩ m0 ⟨c1, x1⟩ m1 e; simp only [Prod.ext_iff] at e ⊢; rcases e with ⟨ec, ex⟩
    rw [ec] at m0 ex; use ec, s.ray_inj m0 m1 ex
  · intro ⟨c, x⟩ m; simp only [mem_image, Prod.ext_iff]
    rcases s.ray_surj m with ⟨x, m, e⟩; use⟨c, x⟩, m, rfl, e
