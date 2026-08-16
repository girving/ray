module
public import Ray.Dynamics.Ray
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Tactic.Cases
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Postcritical
import Ray.Dynamics.Potential
import Ray.Dynamics.Ray
import Ray.Manifold.Analytic
import Ray.Manifold.GlobalInverse
import Ray.Manifold.Nontrivial
import Ray.Manifold.OpenMapping
import Ray.Misc.Topology

/-!
## The Böttcher map for all postcritical points

We define analytic Böttcher coordinates everywhere in `s.post` (the set of all postcritical points),
as the global inverse of the external ray map `s.ray`.  Since `Ray.lean` has already shown that
`s.ray` is bijective, it immediately has a global inverse, and the Böttcher equation follows easily:

  `s.bottcher c (f c z) = s.bottcher c z ^ d`

Combining `s.ray` and `s.bottcher`, we have an analytic bijection `s.homeomorphSlice` between
postcritical points `{z | s.potential c z < s.p c}` and the disk `ball 0 (s.p c)` (or equivalently
an all-`c` bijection `s.homeomorph` between `s.post` and `s.ext`).

To make `s.bottcher` easier to work with later, define it nonanalytically everywhere on `ℂ × S`
such that the defining equation always holds.  In particular, this means that
`s.potential c z = abs (s.bottcher c z)` unconditionally.  It is analytic only on `s.post`,
since for higher potentials we choose roots arbitrarily.
-/

open Classical
open Complex
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball mem_closedBall mem_ball_self)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [T3Space S] [ChartedSpace ℂ S]
  [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c x : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {s : Super f d a}
variable {y : ℂ × ℂ}

/-- `s.ray` has a global inverse -/
theorem Super.ray_inv (s : Super f d a) [OnePreimage s] : ∃ b : ℂ → S → ℂ,
    ContMDiffOnNhd II I (uncurry b) s.post ∧
      ∀ y : ℂ × ℂ, y ∈ s.ext → b y.1 (s.ray y.1 y.2) = y.2 := by
  rw [← s.ray_bij.image_eq]
  exact global_complex_inverse_fun_open s.ray_mAnalyticOn.contMDiffOn
      (fun _ m ↦ s.ray_noncritical m) s.ray_bij.injOn s.isOpen_ext

/-- The bottcher map throughout `s.post` -/
def Super.bottcherPost (s : Super f d a) [OnePreimage s] : ℂ → S → ℂ :=
  choose s.ray_inv

/-- The bottcher map tweaked so the defining equation holds even where it isn't continuous.

    On `s.post`, `s.bottcher` is analytic.  Otherwise, we iterate until we reach `s.post` and
    pull back the value using an arbitrary `d^n`th root (or use 1 outside `s.basin`). -/
public def Super.bottcher (s : Super f d a) [OnePreimage s] : ℂ → S → ℂ := fun c z ↦
  if h : ∃ n, (c, (f c)^[n] z) ∈ s.post then
    let n := Nat.find h
    (fun w ↦ w ^ (d : ℂ)⁻¹)^[n] (s.bottcherPost c ((f c)^[n] z))
  else
    1

/-- `bottcher = bottcherPost` on `s.post` -/
theorem Super.bottcher_eq_bottcherPost (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    s.bottcher c z = s.bottcherPost c z := by
  have h : ∃ n, (c, (f c)^[n] z) ∈ s.post := ⟨0, by simpa only [Function.iterate_zero_apply]⟩
  have h0 := (Nat.find_eq_zero h).mpr m
  simp only [Super.bottcher, h, dif_pos, h0, Function.iterate_zero_apply]

/-- `bottcher = bottcherPost` on `s.post` -/
theorem Super.eqOn_bottcher_bottcherPost (s : Super f d a) [OnePreimage s] :
    EqOn (uncurry s.bottcher) (uncurry s.bottcherPost) s.post := fun _ m ↦
  s.bottcher_eq_bottcherPost m

/-- `s.bottcher` is analytic on `s.post` -/
public theorem Super.bottcher_mAnalyticOn (s : Super f d a) [OnePreimage s] :
    ContMDiffOnNhd II I (uncurry s.bottcher) s.post := by
  intro ⟨c, z⟩ m; apply ((choose_spec s.ray_inv).1 _ m).congr_of_eventuallyEq
  exact (s.eqOn_bottcher_bottcherPost.symm.eventuallyEq_of_mem (s.isOpen_post.mem_nhds m)).symm

/-- `s.bottcher` is the left inverse of `s.ray` -/
public theorem Super.bottcher_ray (s : Super f d a) [OnePreimage s] (m : (c, x) ∈ s.ext) :
    s.bottcher c (s.ray c x) = x := by
  rw [s.bottcher_eq_bottcherPost (s.ray_post m)]; exact (choose_spec s.ray_inv).2 _ m

/-- `s.bottcher` is the right inverse of `s.ray` -/
public theorem Super.ray_bottcher (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    s.ray c (s.bottcher c z) = z := by
  rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m]

/-- `s.bottcher` maps `s.post` to `s.ext` -/
public theorem Super.bottcher_ext (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    (c, s.bottcher c z) ∈ s.ext := by
  rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m]; exact m

/-- `s.bottcher` is `s.bottcherNear` near `a` -/
public theorem Super.bottcher_eq_bottcherNear (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ∀ᶠ z in 𝓝 a, s.bottcher c z = s.bottcherNear c z := by
  have eq := (s.ray_nontrivial (s.mem_ext c)).nhds_eq_map_nhds; simp only [s.ray_zero] at eq
  simp only [eq, Filter.eventually_map]
  apply ((continuousAt_const.prodMk continuousAt_id).eventually (s.ray_eqn_zero c)).mp
  refine ((s.isOpen_ext.snd_preimage c).eventually_mem (s.mem_ext c)).mp
    (.of_forall fun z m e ↦ ?_)
  simp only [s.bottcher_ray m]; exact e.symm

/-- `s.ext` and `s.post` are (analytically) bijective -/
def Super.equiv (s : Super f d a) [OnePreimage s] : PartialEquiv (ℂ × ℂ) (ℂ × S) where
  toFun := fun y : ℂ × ℂ ↦ (y.1, s.ray y.1 y.2)
  invFun := fun y : ℂ × S ↦ (y.1, s.bottcher y.1 y.2)
  source := s.ext
  target := s.post
  map_source' := by intro ⟨c, x⟩ m; exact s.ray_post m
  map_target' := by intro ⟨c, z⟩ m; exact s.bottcher_ext m
  left_inv' := by intro ⟨c, x⟩ m; simp only [s.bottcher_ray m]
  right_inv' := by intro ⟨c, z⟩ m; simp only [s.ray_bottcher m]

/-- `s.ext` and `s.post` are (analytically) homeomorphic -/
def Super.homeomorph (s : Super f d a) [OnePreimage s] : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × S) where
  toPartialEquiv := s.equiv
  open_source := s.isOpen_ext
  open_target := s.isOpen_post
  continuousOn_toFun := continuousOn_fst.prodMk s.ray_mAnalyticOn.continuousOn
  continuousOn_invFun := continuousOn_fst.prodMk s.bottcher_mAnalyticOn.continuousOn

/-- `c`-slices of `s.ext` and `s.post` are (analytically) bijective -/
def Super.equivSlice (s : Super f d a) [OnePreimage s] (c : ℂ) : PartialEquiv ℂ S where
  toFun := s.ray c
  invFun := s.bottcher c
  source := {x | (c, x) ∈ s.ext}
  target := {z | (c, z) ∈ s.post}
  map_source' _ m := s.ray_post m
  map_target' _ m := s.bottcher_ext m
  left_inv' _ m := by simp only [s.bottcher_ray m]
  right_inv' _ m := by simp only [s.ray_bottcher m]

/-- `c`-slices of `s.ext` and `s.post` are (analytically) homeomorphic -/
public def Super.homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    OpenPartialHomeomorph ℂ S where
  toPartialEquiv := s.equivSlice c
  open_source := s.isOpen_ext.snd_preimage c
  open_target := s.isOpen_post.snd_preimage c
  continuousOn_toFun _ m := (s.ray_mAnalytic m).along_snd.continuousAt.continuousWithinAt
  continuousOn_invFun _ m := (s.bottcher_mAnalyticOn _ m).along_snd.continuousAt.continuousWithinAt

@[simp] public lemma Super.toFun_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.homeomorphSlice c = s.ray c := by rfl
@[simp] public lemma Super.invFun_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (s.homeomorphSlice c).symm = s.bottcher c := by rfl
@[simp] public lemma Super.source_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (s.homeomorphSlice c).source = {x | (c, x) ∈ s.ext} := by rfl
@[simp] public lemma Super.target_homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    (s.homeomorphSlice c).target = {z | (c, z) ∈ s.post} := by rfl

/-- `s.post` is connected -/
public theorem Super.post_connected (s : Super f d a) [OnePreimage s] : IsConnected s.post := by
  have e : s.post = s.homeomorph '' s.ext := s.homeomorph.image_source_eq_target.symm
  rw [e]; exact s.ext_connected.image _ s.homeomorph.continuousOn

/-- `c`-slices of `s.post` are connected -/
theorem Super.post_slice_connected (s : Super f d a) [OnePreimage s] (c : ℂ) :
    IsConnected {z | (c, z) ∈ s.post} := by
  have e : {z | (c, z) ∈ s.post} = s.homeomorphSlice c '' {x | (c, x) ∈ s.ext} :=
    (s.homeomorphSlice c).image_source_eq_target.symm
  rw [e]; exact (s.ext_slice_connected c).image _ (s.homeomorphSlice c).continuousOn

/-- Outside of the basin, `bottcher = 1` for simplicity -/
theorem Super.bottcher_not_basin (s : Super f d a) [OnePreimage s] (m : (c, z) ∉ s.basin) :
    s.bottcher c z = 1 := by
  have p : ¬∃ n, (c, (f c)^[n] z) ∈ s.post := by
    contrapose m; rcases m with ⟨n, m⟩
    rcases s.basin_iff_near.mp (s.post_basin m) with ⟨k, m⟩
    simp only [← Function.iterate_add_apply] at m
    exact s.basin_iff_near.mpr ⟨k + n, m⟩
  simp only [Super.bottcher, p]; rw [dif_neg]; exact not_false

/-- `s.bottcher` satifies the Böttcher equation everywhere

    1. It satisfies it near `a`, since it matches `s.bottcherNear` there
    2. It satisfies it throughout `s.post` since `s.post` is connected
    3. It satisfies it everywhere since we've defined it that way -/
public theorem Super.bottcher_eqn (s : Super f d a) [OnePreimage s] :
    s.bottcher c (f c z) = s.bottcher c z ^ d := by
  have h0 : ∀ {c z}, (c, z) ∈ s.post → s.bottcher c (f c z) = s.bottcher c z ^ d := by
    intro c z m
    suffices e : ∀ᶠ w in 𝓝 a, s.bottcher c (f c w) = s.bottcher c w ^ d by
      refine (ContMDiffOnNhd.eq_of_locally_eq ?_ (fun z m ↦
        ((contMDiff_pow _).contMDiffAt.comp _ (s.bottcher_mAnalyticOn (c, z) m).along_snd))
        (s.post_slice_connected c).isPreconnected ⟨a, s.post_a c, e⟩).self_of_nhdsSet m
      intro z m
      exact (s.bottcher_mAnalyticOn _ (s.stays_post m)).along_snd.comp _ (s.fa _).along_snd
    have e := s.bottcher_eq_bottcherNear c
    have fc := (s.fa (c, a)).along_snd.continuousAt; simp only [ContinuousAt, s.f0] at fc
    apply e.mp; apply (fc.eventually e).mp
    apply ((s.isOpen_near.snd_preimage c).eventually_mem (s.mem_near c)).mp
    refine .of_forall fun w m e0 e1 ↦ ?_
    simp only [e0, e1]; exact s.bottcherNear_eqn m
  by_cases p : (c, z) ∈ s.post; simp only [h0 p]
  by_cases m : (c, z) ∈ s.basin
  · have e0 : ∃ n, (c, (f c)^[n] z) ∈ s.post := s.basin_post m
    have e1 : ∃ n, (c, (f c)^[n] (f c z)) ∈ s.post := by
      rcases e0 with ⟨n, e0⟩; use n
      simp only [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact s.stays_post e0
    simp only [Super.bottcher, e0, e1, dif_pos]
    generalize hk0 : Nat.find e0 = k0
    generalize hk1 : Nat.find e1 = k1
    have kk : k0 = k1 + 1 := by
      rw [← hk0, ← hk1]; apply le_antisymm
      · apply Nat.find_le; simp only [Function.iterate_succ_apply]
        exact Nat.find_spec e1
      · rw [Nat.succ_le_iff, Nat.lt_find_iff]; intro n n1
        contrapose n1; simp only [not_le] at n1 ⊢
        have n0 : n ≠ 0 := by
          contrapose p
          simp only [p, Function.iterate_zero_apply] at n1; exact n1
        rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← Nat.sub_add_cancel (Nat.pos_of_ne_zero n0)]
        apply Nat.succ_le_succ; apply Nat.find_le
        simp only [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
          Nat.sub_add_cancel (Nat.pos_of_ne_zero n0), n1, zero_add]
    simp only [kk, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [Complex.cpow_nat_inv_pow _ s.d0]
  have m1 : (c, f c z) ∉ s.basin := by
    contrapose m
    obtain ⟨n, m⟩ := s.basin_iff_near.mp m
    refine s.basin_iff_near.mpr ⟨n + 1, ?_⟩
    rwa [Function.iterate_succ_apply]
  simp only [s.bottcher_not_basin m, s.bottcher_not_basin m1, one_pow]

/-- `s.bottcher` satisfies the iterated Böttcher equation -/
public theorem Super.bottcher_eqn_iter (s : Super f d a) [OnePreimage s] (n : ℕ) :
    s.bottcher c ((f c)^[n] z) = s.bottcher c z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  simp only [Function.iterate_succ_apply', s.bottcher_eqn, h, ← pow_mul, pow_succ]

/-- `abs (s.bottcher c z) = s.potential c z` -/
public theorem Super.norm_bottcher (s : Super f d a) [OnePreimage s] :
    ‖s.bottcher c z‖ = s.potential c z := by
  have base : ∀ {c z}, (c, z) ∈ s.post → ‖s.bottcher c z‖ = s.potential c z := by
    intro c z m; rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m, s.ray_potential m]
  by_cases m : (c, z) ∈ s.basin
  · rcases s.basin_post m with ⟨n, p⟩
    rw [← Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero n s.d0), ←
      norm_pow, ← s.bottcher_eqn_iter n, base p, s.potential_eqn_iter,
      Real.pow_rpow_inv_natCast s.potential_nonneg (pow_ne_zero n s.d0)]
  · simp only [s.bottcher_not_basin m, norm_one, s.potential_eq_one m]

/-- `abs (s.bottcher c z) < 1` on `s.post` -/
public theorem Super.bottcher_lt_one (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    ‖s.bottcher c z‖ < 1 := by
  replace m := s.bottcher_ext m
  simp only [Super.ext, mem_ofPred] at m
  exact lt_of_lt_of_le m s.p_le_one

/-- Functional equation for `s.ray` -/
public lemma Super.ray_eqn (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    f c (s.ray c x) = s.ray c (x ^ d) := by
  generalize hz : s.ray c x = z
  rw [← s.bottcher_ray post, ← s.bottcher_eqn, s.ray_bottcher, hz]
  exact s.stays_post (s.ray_post post)

omit [T3Space S] in
/-- Raising to powers stays in `s.ext` -/
public lemma Super.pow_ext (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) (n : ℕ) :
    (c, x ^ d ^ n) ∈ s.ext := by
  simp only [ext, mem_ofPred_eq, norm_pow] at post ⊢
  refine lt_of_le_of_lt (pow_le_of_le_one (by bound) ?_ (by simp [s.d0])) post
  exact le_trans post.le s.p_le_one

/-- Functional equation for `s.ray`, iterated -/
public lemma Super.ray_eqn_iter (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) (n : ℕ) :
    (f c)^[n] (s.ray c x) = s.ray c (x ^ d ^ n) := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  · rw [Function.iterate_succ_apply', h, pow_succ, pow_mul, s.ray_eqn (s.pow_ext post n)]

/-- `s.bottcher c` is injective (pulling it out of `s.homeomorphSlice c`) -/
public lemma Super.bottcher_inj (s : Super f d a) [OnePreimage s] (c : ℂ) :
    InjOn (s.bottcher c) {z | (c, z) ∈ s.post} :=
  (s.homeomorphSlice c).symm.injOn

/-- `s.bottcher c` sends the fixpoint to 0 -/
@[simp] public lemma Super.bottcher_a (s : Super f d a) [OnePreimage s] (c : ℂ) :
    s.bottcher c a = 0 := by
  rw [← norm_eq_zero]
  have lt : ‖s.bottcher c a‖ < 1 := s.bottcher_lt_one (s.post_a c)
  have e := s.f0 _ ▸ s.bottcher_eqn (c := c) (z := a)
  replace e : ‖s.bottcher c a‖ ^ d = ‖s.bottcher c a‖ := by rw [← norm_pow, ← e]
  contrapose e
  simp only [norm_eq_zero, ne_eq, ← norm_pos_iff] at e
  exact (pow_lt_self_of_lt_one₀ e lt s.d1).ne
