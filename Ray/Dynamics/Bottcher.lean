import Ray.AnalyticManifold.GlobalInverse
import Ray.Dynamics.Ray

/-!
## The Böttcher map for all postcritical points

We define analytic Böttcher coordinates everywhere in `s.post` (the set of all postcritical points),
as the global inverse of the external ray map `s.ray`.  Since `Ray.lean` has already shown that
`s.ray` is bijective, it immediately has a global inverse, and the Böttcher equation follows easily:

  `s.bottcher c (f c z) = s.bottcher c z ^ d`

Combining `s.ray` and `s.bottcher`, we have an analytic bijection `s.homeomorphSlice` between
postcritical points `{z | s.potential c z < s.p c}` and the disk `ball 0 (s.p c)` (or equivalently
an all-`c` bijection `s.homeomorph` between `s.post` and `s.ext`).

To make `s.bottcher` easier to work with later, define it nonholomorphically everywhere on `ℂ × S`
such that the defining equation always holds.  In particular, this means that
`s.potential c z = abs (s.bottcher c z)` unconditionally.  It is holomorphic only on `s.post`,
since for higher potentials we choose roots arbitrarily.
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Classical
open Complex (abs)
open Filter (Tendsto atTop eventually_of_forall)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball mem_closedBall mem_ball_self)
open OneDimension
open Set
open scoped Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [T3Space S] [ChartedSpace ℂ S]
  [AnalyticManifold I S]
variable {f : ℂ → S → S}
variable {c x : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {s : Super f d a}
variable {y : ℂ × ℂ}

/-- `s.ray` has a global inverse -/
theorem Super.ray_inv (s : Super f d a) [OnePreimage s] : ∃ b : ℂ → S → ℂ,
    HolomorphicOn II I (uncurry b) s.post ∧
      ∀ y : ℂ × ℂ, y ∈ s.ext → b y.1 (s.ray y.1 y.2) = y.2 := by
  rw [← s.ray_bij.image_eq]
  exact global_complex_inverse_fun_open s.ray_holomorphicOn (fun _ m ↦ s.ray_noncritical m)
      s.ray_bij.injOn s.isOpen_ext

/-- The bottcher map throughout `s.post` -/
def Super.bottcherPost (s : Super f d a) [OnePreimage s] : ℂ → S → ℂ :=
  choose s.ray_inv

/-- The bottcher map tweaked so the defining equation holds even where it isn't continuous.

    On `s.post`, `s.bottcher` is holomorphic.  Otherwise, we iterate until we reach `s.post` and
    pull back the value using an arbitrary `d^n`th root (or use 1 outside `s.basin`). -/
def Super.bottcher (s : Super f d a) [OnePreimage s] : ℂ → S → ℂ := fun c z ↦
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
  simp only [Super.bottcher, h, dif_pos, h0, Function.iterate_zero_apply, pow_zero, inv_one,
    Complex.cpow_one]

/-- `bottcher = bottcherPost` on `s.post` -/
theorem Super.eqOn_bottcher_bottcherPost (s : Super f d a) [OnePreimage s] :
    EqOn (uncurry s.bottcher) (uncurry s.bottcherPost) s.post := fun _ m ↦
  s.bottcher_eq_bottcherPost m

/-- `s.bottcher` is holomorphic on `s.post` -/
theorem Super.bottcher_holomorphicOn (s : Super f d a) [OnePreimage s] :
    HolomorphicOn II I (uncurry s.bottcher) s.post := by
  intro ⟨c, z⟩ m; apply ((choose_spec s.ray_inv).1 _ m).congr
  exact s.eqOn_bottcher_bottcherPost.symm.eventuallyEq_of_mem (s.isOpen_post.mem_nhds m)

/-- `s.bottcher` is the left inverse of `s.ray` -/
theorem Super.bottcher_ray (s : Super f d a) [OnePreimage s] (m : (c, x) ∈ s.ext) :
    s.bottcher c (s.ray c x) = x := by
  rw [s.bottcher_eq_bottcherPost (s.ray_post m)]; exact (choose_spec s.ray_inv).2 _ m

/-- `s.bottcher` is the right inverse of `s.ray` -/
theorem Super.ray_bottcher (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    s.ray c (s.bottcher c z) = z := by
  rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m]

/-- `s.bottcher` maps `s.post` to `s.ext` -/
theorem Super.bottcher_ext (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    (c, s.bottcher c z) ∈ s.ext := by
  rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m]; exact m

/-- `s.bottcher` is `s.bottcherNear` near `a` -/
theorem Super.bottcher_eq_bottcherNear (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ∀ᶠ z in 𝓝 a, s.bottcher c z = s.bottcherNear c z := by
  have eq := (s.ray_nontrivial (s.mem_ext c)).nhds_eq_map_nhds; simp only [s.ray_zero] at eq
  simp only [eq, Filter.eventually_map]
  apply ((continuousAt_const.prod continuousAt_id).eventually (s.ray_eqn_zero c)).mp
  refine ((s.isOpen_ext.snd_preimage c).eventually_mem (s.mem_ext c)).mp
    (eventually_of_forall fun z m e ↦ ?_)
  simp only [s.bottcher_ray m]; exact e.symm

/-- `s.ext` and `s.post` are (analytically) bijective -/
def Super.equiv (s : Super f d a) [OnePreimage s] : LocalEquiv (ℂ × ℂ) (ℂ × S) where
  toFun := fun y : ℂ × ℂ ↦ (y.1, s.ray y.1 y.2)
  invFun := fun y : ℂ × S ↦ (y.1, s.bottcher y.1 y.2)
  source := s.ext
  target := s.post
  map_source' := by intro ⟨c, x⟩ m; exact s.ray_post m
  map_target' := by intro ⟨c, z⟩ m; exact s.bottcher_ext m
  left_inv' := by intro ⟨c, x⟩ m; simp only [s.bottcher_ray m]
  right_inv' := by intro ⟨c, z⟩ m; simp only [s.ray_bottcher m]

/-- `s.ext` and `s.post` are (analytically) homeomorphic -/
def Super.homeomorph (s : Super f d a) [OnePreimage s] : LocalHomeomorph (ℂ × ℂ) (ℂ × S) where
  toLocalEquiv := s.equiv
  open_source := s.isOpen_ext
  open_target := s.isOpen_post
  continuous_toFun := continuousOn_fst.prod s.ray_holomorphicOn.continuousOn
  continuous_invFun := continuousOn_fst.prod s.bottcher_holomorphicOn.continuousOn

/-- `c`-slices of `s.ext` and `s.post` are (analytically) bijective -/
def Super.equivSlice (s : Super f d a) [OnePreimage s] (c : ℂ) : LocalEquiv ℂ S where
  toFun := s.ray c
  invFun := s.bottcher c
  source := {x | (c, x) ∈ s.ext}
  target := {z | (c, z) ∈ s.post}
  map_source' _ m := s.ray_post m
  map_target' _ m := s.bottcher_ext m
  left_inv' _ m := by simp only [s.bottcher_ray m]
  right_inv' _ m := by simp only [s.ray_bottcher m]

/-- `c`-slices of `s.ext` and `s.post` are (analytically) homeomorphic -/
def Super.homeomorphSlice (s : Super f d a) [OnePreimage s] (c : ℂ) : LocalHomeomorph ℂ S where
  toLocalEquiv := s.equivSlice c
  open_source := s.isOpen_ext.snd_preimage c
  open_target := s.isOpen_post.snd_preimage c
  continuous_toFun _ m := (s.ray_holomorphic m).along_snd.continuousAt.continuousWithinAt
  continuous_invFun _ m := (s.bottcher_holomorphicOn _ m).along_snd.continuousAt.continuousWithinAt

/-- `s.post` is connected -/
theorem Super.post_connected (s : Super f d a) [OnePreimage s] : IsConnected s.post := by
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
    contrapose m; simp only [not_not] at m ⊢; rcases m with ⟨n, m⟩
    rcases s.post_basin m with ⟨k, m⟩
    simp only [← Function.iterate_add_apply] at m; exact ⟨k + n, m⟩
  simp only [Super.bottcher, p]; rw [dif_neg]; exact not_false

/-- `s.bottcher` satifies the Böttcher equation everywhere

    1. It satisfies it near `a`, since it matches `s.bottcherNear` there
    2. It satisfies it throughout `s.post` since `s.post` is connected
    3. It satisfies it everywhere since we've defined it that way -/
theorem Super.bottcher_eqn (s : Super f d a) [OnePreimage s] :
    s.bottcher c (f c z) = s.bottcher c z ^ d := by
  have h0 : ∀ {c z}, (c, z) ∈ s.post → s.bottcher c (f c z) = s.bottcher c z ^ d := by
    intro c z m
    suffices e : ∀ᶠ w in 𝓝 a, s.bottcher c (f c w) = s.bottcher c w ^ d
    · refine'
        (HolomorphicOn.eq_of_locally_eq _ (fun z m ↦ (s.bottcher_holomorphicOn (c, z) m).along_snd.pow)
          (s.post_slice_connected c).isPreconnected ⟨a, s.post_a c, e⟩).self_of_nhdsSet m
      exact fun z m ↦ (s.bottcher_holomorphicOn _ (s.stays_post m)).along_snd.comp (s.fa _).along_snd
    have e := s.bottcher_eq_bottcherNear c
    have fc := (s.fa (c, a)).along_snd.continuousAt; simp only [ContinuousAt, s.f0] at fc
    apply e.mp; apply (fc.eventually e).mp
    apply ((s.isOpen_near.snd_preimage c).eventually_mem (s.mem_near c)).mp
    refine' eventually_of_forall fun w m e0 e1 ↦ _; simp only at m e0 e1
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
        contrapose n1; simp only [not_not, not_le] at n1 ⊢
        have n0 : n ≠ 0 := by
          contrapose p; simp only [not_not] at p ⊢
          simp only [p, Function.iterate_zero_apply] at n1; exact n1
        rw [← Nat.succ_le_iff, Nat.succ_eq_add_one, ← Nat.sub_add_cancel (Nat.pos_of_ne_zero n0)]
        apply Nat.succ_le_succ; apply Nat.find_le
        simp only [← Function.iterate_succ_apply, Nat.succ_eq_add_one,
          Nat.sub_add_cancel (Nat.pos_of_ne_zero n0), n1, zero_add]
    simp only [kk, ← Function.iterate_succ_apply, Function.iterate_succ_apply']
    rw [Complex.cpow_nat_inv_pow _ s.d0]
  have m1 : (c, f c z) ∉ s.basin := by
    contrapose m; simp only [not_not] at m ⊢
    rcases m with ⟨n, m⟩; use n + 1; simp only at m ⊢; rwa [Function.iterate_succ_apply]
  simp only [s.bottcher_not_basin m, s.bottcher_not_basin m1, one_pow]

/-- `s.bottcher` satisfies the iterated Böttcher equation -/
theorem Super.bottcher_eqn_iter (s : Super f d a) [OnePreimage s] (n : ℕ) :
    s.bottcher c ((f c)^[n] z) = s.bottcher c z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  simp only [Function.iterate_succ_apply', s.bottcher_eqn, h, ← pow_mul, pow_succ']

/-- `abs (s.bottcher c z) = s.potential c z` -/
theorem Super.abs_bottcher (s : Super f d a) [OnePreimage s] :
    abs (s.bottcher c z) = s.potential c z := by
  have base : ∀ {c z}, (c, z) ∈ s.post → abs (s.bottcher c z) = s.potential c z := by
    intro c z m; rcases s.ray_surj m with ⟨x, m, e⟩; rw [← e, s.bottcher_ray m, s.ray_potential m]
  by_cases m : (c, z) ∈ s.basin
  · rcases s.basin_post m with ⟨n, p⟩
    rw [← Real.pow_nat_rpow_nat_inv (Complex.abs.nonneg _) (pow_ne_zero n s.d0), ←
      Complex.abs.map_pow, ← s.bottcher_eqn_iter n, base p, s.potential_eqn_iter,
      Real.pow_nat_rpow_nat_inv s.potential_nonneg (pow_ne_zero n s.d0)]
  · have m' := m; simp only [Super.basin, not_exists, mem_setOf] at m'
    simp only [s.bottcher_not_basin m, Complex.abs.map_one, s.potential_eq_one m']

/-- `abs (s.bottcher c z) < 1` on `s.post` -/
theorem Super.bottcher_lt_one (s : Super f d a) [OnePreimage s] (m : (c, z) ∈ s.post) :
    abs (s.bottcher c z) < 1 := by
  replace m := s.bottcher_ext m
  simp only [Super.ext, mem_setOf] at m
  exact lt_of_lt_of_le m s.p_le_one
