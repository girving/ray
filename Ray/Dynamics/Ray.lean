import Ray.Dynamics.Grow

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

/-- The external ray map: `s.ray c y` is moving in external ray space from the superattractor `a`
    out by `y`.  `s.ray` is well behaved for all postcritical values `(c,y) ∈ s.ext` (see below). -/
def Super.ray (s : Super f d a) [OnePreimage s] : ℂ → ℂ → S :=
  choose s.has_ray

/-- The domain on which `s.ray` is well behaved: `{(c,z) | s.potential c z < s.p c}`. -/
def Super.ext (s : Super f d a) : Set (ℂ × ℂ) :=
  {y : ℂ × ℂ | abs y.2 < s.p y.1}

/-- The `c`-slice of `s.ext` is `ball 0 (s.p c)` -/
theorem Super.ext_slice (s : Super f d a) (c : ℂ) :
    {x | (c, x) ∈ s.ext} = ball (0 : ℂ) (s.p c) := by
  apply Set.ext; intro x; simp only [Super.ext, mem_ball, mem_setOf, Complex.dist_eq, sub_zero]

/-- `s.ext` is open -/
theorem Super.isOpen_ext (s : Super f d a) [OnePreimage s] : IsOpen s.ext := by
  set f := fun y : ℂ × ℂ ↦ s.p y.1 - abs y.2
  have fc : LowerSemicontinuous f :=
    (s.lowerSemicontinuous_p.comp continuous_fst).add
      (Complex.continuous_abs.comp continuous_snd).neg.lowerSemicontinuous
  have e : s.ext = f ⁻¹' Ioi 0 :=
    Set.ext fun _ ↦ by simp only [Super.ext, mem_setOf, mem_preimage, mem_Ioi, sub_pos]
  rw [e]; exact fc.isOpen_preimage _

/-- `(c,0) ∈ s.ext` -/
theorem Super.mem_ext (s : Super f d a) [OnePreimage s] (c : ℂ) : (c, (0 : ℂ)) ∈ s.ext := by
  simp only [Super.ext, mem_setOf, Complex.abs.map_zero, s.p_pos c]

/-- `c`-slices of `s.ext` are connected -/
theorem Super.ext_slice_connected (s : Super f d a) [OnePreimage s] (c : ℂ) :
    IsConnected {x | (c, x) ∈ s.ext} := by
  rw [s.ext_slice c]
  exact ⟨⟨(0 : ℂ), mem_ball_self (s.p_pos c)⟩, (convex_ball (0 : ℂ) (s.p c)).isPreconnected⟩

/-- `s.ext` is connected (since `c`-slices and `univ ×ˢ {0}` are connected) -/
theorem Super.ext_connected (s : Super f d a) [OnePreimage s] : IsConnected s.ext := by
  refine ⟨⟨(0, 0), s.mem_ext 0⟩, isPreconnected_of_forall (0, 0) ?_⟩; intro ⟨c, x⟩ m
  use(fun x ↦ (c, x)) '' {x | (c, x) ∈ s.ext} ∪ univ ×ˢ {0}
  simp only [mem_image, mem_union, union_subset_iff, mem_setOf, mem_prod_eq, mem_univ,
    true_and_iff, mem_singleton_iff, eq_self_iff_true, or_true_iff]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro y n; simp only [mem_image, mem_setOf] at n; rcases n with ⟨x, m, e⟩; rw [e] at m; exact m
  · intro ⟨c, x⟩ m; simp only [mem_prod_eq, mem_singleton_iff] at m; rw [m.2]; exact s.mem_ext c
  · left; exact ⟨x, m, rfl⟩
  · refine' IsPreconnected.union (c, 0) _ _ _ _
    use 0, s.mem_ext c; exact mk_mem_prod (mem_univ _) rfl
    · exact IsPreconnected.image (s.ext_slice_connected c).isPreconnected _
        (Continuous.Prod.mk _).continuousOn
    · exact isPreconnected_univ.prod isPreconnected_singleton

/-- `s.ray` satisfies `Grow` (it looks like a local inverse to Böttcher coordinates) -/
lemma Super.ray_spec (s : Super f d a) [OnePreimage s] :
    ∀ {c p}, 0 ≤ p → p < s.p c → Grow s c p (s.np c p) s.ray :=
  fun {c p} ↦ choose_spec s.has_ray c p

/-- `s.ray` satisfies `Eqn` -/
lemma Super.ray_eqn_self (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    Eqn s (s.np c (abs x)) s.ray (c, x) :=
  (s.ray_spec (Complex.abs.nonneg _) post).eqn.self_of_nhdsSet _ mem_domain_self

/-- `s.ray` is holomorphic on `s.ext` (up to the critical potential for each `c`) -/
theorem Super.ray_holomorphic (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    HolomorphicAt II I (uncurry s.ray) (c, x) :=
  (s.ray_eqn_self post).holo

/-- `s.ray c` is holomorphic up to the critical potential (that is, on `ball 0 (s.p c)`) -/
theorem Super.ray_holomorphic_slice (s : Super f d a) [OnePreimage s] (c : ℂ) :
    HolomorphicOn I I (s.ray c) {x | (c, x) ∈ s.ext} := fun _ m ↦ (s.ray_holomorphic m).in2

/-- `s.ray` is holomorphic on `s.ext` (up to the critical potential for each `c`) -/
theorem Super.ray_holomorphicOn (s : Super f d a) [OnePreimage s] :
    HolomorphicOn II I (uncurry s.ray) s.ext := by intro ⟨c, x⟩ m; exact s.ray_holomorphic m

/-- Rays start at `a`: `s.ray c 0 = a` -/
theorem Super.ray_zero (s : Super f d a) [OnePreimage s] (c : ℂ) : s.ray c 0 = a :=
  (s.ray_spec (le_refl _) (s.p_pos c)).zero

/-- `s.ray` maps `s.ext` into `s.basin` -/
theorem Super.ray_basin (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, s.ray c x) ∈ s.basin :=
  ⟨_, (s.ray_eqn_self post).near⟩

/-- `s.ray` maps into `s.near` with if we iterate `s.np c (abs x)` times -/
theorem Super.ray_near (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, (f c)^[s.np c (abs x)] (s.ray c x)) ∈ s.near :=
  (s.ray_eqn_self post).near

/-- `s.ray` inverts `s.bottcherNear` near 0 -/
theorem Super.ray_eqn_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    ∀ᶠ y : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear y.1 (s.ray y.1 y.2) = y.2 :=
  (s.ray_spec (le_refl _) (s.p_pos c)).start

/-- `s.ray` inverts `s.bottcherNear` after iteration -/
theorem Super.ray_eqn_iter (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    ∀ᶠ y : ℂ × ℂ in 𝓝 (c, x),
      s.bottcherNearIter (s.np c (abs x)) y.1 (s.ray y.1 y.2) = y.2 ^ d ^ s.np c (abs x) :=
  ((s.ray_spec (Complex.abs.nonneg _) post).eqn.filter_mono (nhds_le_nhdsSet mem_domain_self)).mp
    (eventually_of_forall fun _ e ↦ e.eqn)

/-- `s.ray` sends absolute value to potential -/
theorem Super.ray_potential (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    s.potential c (s.ray c x) = abs x :=
  (s.ray_eqn_self post).potential

/-- `s.ray` maps `s.ext` into `s.post` -/
theorem Super.ray_post (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    (c, s.ray c x) ∈ s.post := by
  simp only [Super.post, Postcritical, mem_setOf, s.ray_potential post]; exact post

/-- `s.ray` is noncritical at 0 -/
theorem Super.ray_noncritical_zero (s : Super f d a) [OnePreimage s] (c : ℂ) :
    mfderiv I I (s.ray c) 0 ≠ 0 := by
  have h : mfderiv I I (s.bottcherNear c ∘ s.ray c) 0 ≠ 0 := by
    have e : s.bottcherNear c ∘ s.ray c =ᶠ[𝓝 0] id :=
      (continuousAt_const.prod continuousAt_id).eventually (s.ray_eqn_zero c)
    rw [e.mfderiv_eq]; exact id_mderiv_ne_zero
  contrapose h; simp only [not_not] at h ⊢
  have hb : MDifferentiableAt I I (s.bottcherNear c) (s.ray c 0) := by
    rw [s.ray_zero]; exact (s.bottcherNear_holomorphic _ (s.mem_near c)).in2.mdifferentiableAt
  have hr : MDifferentiableAt I I (s.ray c) 0 :=
    (s.ray_holomorphic (s.mem_ext c)).in2.mdifferentiableAt
  rw [mfderiv_comp 0 hb hr, h, ContinuousLinearMap.comp_zero]

-- `s.ray` is noncritical everywhere in `s.ext`
theorem Super.ray_noncritical (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    mfderiv I I (s.ray c) x ≠ 0 := by
  by_cases x0 : x = 0; rw [x0]; exact s.ray_noncritical_zero c
  set n := s.np c (abs x)
  have h : mfderiv I I (s.bottcherNearIter n c ∘ s.ray c) x ≠ 0 := by
    have e : s.bottcherNearIter n c ∘ s.ray c =ᶠ[𝓝 x] fun x ↦ x ^ d ^ n :=
      (continuousAt_const.prod continuousAt_id).eventually (s.ray_eqn_iter post)
    rw [e.mfderiv_eq]; contrapose x0; simp only [not_not] at x0 ⊢
    rw [mfderiv_eq_fderiv] at x0
    have d := (differentiableAt_pow (x := x) (d ^ n)).hasFDerivAt.hasDerivAt.deriv
    apply_fun (fun x ↦ x 1) at x0
    rw [x0] at d
    replace d := Eq.trans d (ContinuousLinearMap.zero_apply _)
    rw [deriv_pow, mul_eq_zero, Nat.cast_eq_zero, pow_eq_zero_iff', pow_eq_zero_iff'] at d
    simp only [s.d0, false_and_iff, false_or_iff] at d; exact d.1
  simp only [mfderiv_comp x
      (s.bottcherNearIter_holomorphic (s.ray_near post)).in2.mdifferentiableAt
      (s.ray_holomorphic post).in2.mdifferentiableAt,
    Ne.def, mderiv_comp_eq_zero_iff, not_or] at h
  exact h.2

/-- `s.ray` is nontrivial, since it is noncritical at 0 and `s.ext` is connected -/
theorem Super.ray_nontrivial (s : Super f d a) [OnePreimage s] (post : (c, x) ∈ s.ext) :
    NontrivialHolomorphicAt (s.ray c) x :=
  (nontrivialHolomorphicAt_of_mfderiv_ne_zero (s.ray_holomorphic (s.mem_ext c)).in2
        (s.ray_noncritical_zero c)).on_preconnected
    (s.ray_holomorphic_slice c) (s.mem_ext c) (s.isOpen_ext.snd_preimage c)
    (s.ext_slice_connected c).isPreconnected _ post

/-- `s.ray c` is injective, or alternately `(c,x) ↦ (c, s.ray c x)` is injective on `s.ext`.

    We prove this by continuous induction on potential:
    1. `s.ray c` is injective for small potentials, since it is noncritical at (c,0)`
    2. If `s.ray c x0 = s.ray c x1`, we can use the fact that `s.ray` is a local inverse
       to `s.bottcherNear` to find a slightly smaller `t < 1` where
       `s.ray c (t*x0) = s.ray c (t*x1)`
    3. (1) + (2) is a contradiction, since we can walk all the down to `t ≈ 0`. -/
theorem Super.ray_inj (s : Super f d a) [OnePreimage s] {x0 x1 : ℂ} :
    (c, x0) ∈ s.ext → (c, x1) ∈ s.ext → s.ray c x0 = s.ray c x1 → x0 = x1 := by
  -- Preliminaries
  intro p0 p1 e
  have ax : abs x0 = abs x1 := by simp only [← s.ray_potential p0, ← s.ray_potential p1, e]
  by_cases x00 : x0 = 0
  · simp only [x00, Complex.abs.map_zero] at ax ⊢; exact (Complex.abs.eq_zero.mp ax.symm).symm
  have tc : ∀ (x : ℂ) (t), ContinuousAt (fun t : ℝ ↦ ↑t * x) t := fun x t ↦
    Complex.continuous_ofReal.continuousAt.mul continuousAt_const
  have pt : ∀ {x : ℂ} {t : ℝ}, (c, x) ∈ s.ext → t ∈ Ioc (0 : ℝ) 1 → (c, ↑t * x) ∈ s.ext := by
    intro x t p m
    simp only [Super.ext, mem_setOf, Complex.abs.map_mul, Complex.abs_ofReal, abs_of_pos m.1] at p ⊢
    exact lt_of_le_of_lt (mul_le_of_le_one_left (Complex.abs.nonneg _) m.2) p
  -- It suffices to show that the set of t's where the x0 and x1 rays match
  -- is relatively clopen in Ioc 0 1
  set u : Set ℝ := {t : ℝ | s.ray c (t * x0) = s.ray c (t * x1)}
  suffices h : Ioc (0 : ℝ) 1 ⊆ interior u
  · replace h := _root_.trans h interior_subset
    replace tc := (tc x0 0).prod_mk (tc x1 0); simp only [← nhds_prod_eq] at tc
    simp only [ContinuousAt, Complex.ofReal_zero, MulZeroClass.zero_mul] at tc
    have inj := tc.eventually ((s.ray_holomorphic (s.mem_ext c)).in2.local_inj
      (s.ray_noncritical_zero c))
    rcases Metric.eventually_nhds_iff.mp inj with ⟨r, rp, inj⟩
    simp only [Real.dist_eq, sub_zero] at inj
    set t := min 1 (r / 2)
    have t0 : 0 < t := lt_min zero_lt_one (half_pos rp)
    have t01 : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc.mpr ⟨t0, min_le_left _ _⟩
    specialize @inj t (by simp only [abs_of_pos t0, min_lt_of_right_lt (half_lt_self rp)]) (h t01)
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr t0.ne') inj
  refine' isPreconnected_Ioc.relative_clopen _ _ _
  · use 1, right_mem_Ioc.mpr zero_lt_one
    simp only [mem_setOf, Complex.ofReal_one, one_mul, e]
  · intro t ⟨m, e⟩
    simp only [mem_setOf, mem_interior_iff_mem_nhds, ← Filter.eventually_iff] at e ⊢
    generalize hn : s.np c (abs (↑t * x0)) = n
    have t0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr m.1.ne'
    have pe : abs (↑t * x0) = abs (↑t * x1) := by
      simp only [← s.ray_potential (pt p0 m), ← s.ray_potential (pt p1 m), e]
    have e0 := (s.ray_spec (Complex.abs.nonneg _) (pt p0 m)).eqn.filter_mono
      (nhds_le_nhdsSet mem_domain_self)
    have e1 := (s.ray_spec (Complex.abs.nonneg _) (pt p1 m)).eqn.filter_mono
      (nhds_le_nhdsSet mem_domain_self)
    simp only [← pe, hn] at e0 e1
    have de : (↑t * x0) ^ d ^ n = (↑t * x1) ^ d ^ n := by
      have e0 := e0.self_of_nhds.eqn; have e1 := e1.self_of_nhds.eqn; simp only [hn, ← pe, ← e] at e0 e1
      exact e0.symm.trans e1
    simp only [mul_pow] at de
    replace de := mul_left_cancel₀ (pow_ne_zero _ t0) de
    generalize hr : (fun e x ↦ s.ray e (x1 / x0 * x)) = r
    have xe : x1 / x0 * (↑t * x0) = ↑t * x1 := by
      rw [← mul_assoc, mul_comm _ (t:ℂ), mul_assoc, div_mul_cancel _ x00]
    have er : ∀ᶠ y in 𝓝 (c, ↑t * x0), Eqn s n r y := by
      rw [← hr]; apply eqn_near
      exact (s.ray_holomorphic (pt p1 m)).comp₂_of_eq holomorphicAt_fst
          (holomorphicAt_const.mul holomorphicAt_snd) (by simp only [xe])
      rw [xe]; exact e1.self_of_nhds.near
      have xc : ContinuousAt (fun y : ℂ × ℂ ↦ (y.1, x1 / x0 * y.2)) (c, ↑t * x0) :=
        continuousAt_fst.prod (continuousAt_const.mul continuousAt_snd)
      simp only [ContinuousAt] at xc
      rw [← mul_assoc, mul_comm _ (t:ℂ), mul_assoc, div_mul_cancel _ x00] at xc
      refine' (xc.eventually e1).mp (eventually_of_forall _); intro ⟨e, x⟩ e1
      exact _root_.trans e1.eqn (by
        simp only [mul_pow, div_pow, ← de, div_self (pow_ne_zero _ x00), one_mul])
    refine ((continuousAt_const.prod (Complex.continuous_ofReal.continuousAt.mul
        continuousAt_const)).eventually
        (eqn_unique e0 er ?_ (mul_ne_zero t0 x00))).mp (eventually_of_forall fun u e ↦ ?_)
    · simp only [← hr]; rw [xe]; exact e
    · rw [← hr] at e; simp only [uncurry] at e
      rw [← mul_assoc, mul_comm _ (u:ℂ), mul_assoc, div_mul_cancel _ x00] at e
      exact e
  · intro t ⟨m, e⟩; simp only [mem_setOf, mem_closure_iff_frequently] at e ⊢
    have rc : ∀ {x : ℂ}, (c, x) ∈ s.ext → ContinuousAt (fun t : ℝ ↦ s.ray c (↑t * x)) t :=
      fun {x} p ↦
      (s.ray_holomorphic (pt p m)).in2.continuousAt.comp_of_eq
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const) rfl
    exact tendsto_nhds_unique_of_frequently_eq (rc p0) (rc p1) e

/-- `s.ray` surjects from `s.ext` to `s.post`

    We prove this by continuous induction on potential, but phrased in terms of explicit sets.
    Fixing `c`, we have
    1. The image of `s.ray c` is open (by the Open Mapping Theorem)
    2. The image of `s.ray c` restricted to `s.potential c z ≤ p` is closed.
    3. By picking `p` greater than any particular postcritical potential, we cover `s.post`. -/
theorem Super.ray_surj (s : Super f d a) [OnePreimage s] :
    ∀ {z}, (c, z) ∈ s.post → ∃ x, (c, x) ∈ s.ext ∧ s.ray c x = z := by
  intro z0 m0
  by_contra i0; simp only [not_forall, not_exists, not_and] at i0
  set p0 := s.potential c z0
  simp only [Super.post, mem_setOf, Postcritical] at m0
  rcases exists_between m0 with ⟨p1, p01, post⟩
  set i := s.ray c '' {x | (c, x) ∈ s.ext}
  set j := {z | s.potential c z ≤ p1} ∩ i
  set u := {z | s.potential c z ≤ p1} \ i
  have pc : Continuous (s.potential c) := (Continuous.potential s).in2
  have io : IsOpen i := by
    rw [isOpen_iff_eventually]; intro z ⟨x, m, xz⟩
    have eq := (s.ray_nontrivial m).nhds_eq_map_nhds; rw [xz] at eq
    rw [eq, Filter.eventually_map]
    exact ((s.isOpen_ext.snd_preimage c).eventually_mem m).mp
      (eventually_of_forall fun x m ↦ ⟨x, m, rfl⟩)
  have jc : IsClosed j := by
    have e : j = s.ray c '' closedBall 0 p1 := by
      refine Set.ext fun z ↦ ?_
      simp only [mem_inter_iff, mem_setOf, mem_image, mem_closedBall, Complex.dist_eq, sub_zero,
        Super.ext]
      constructor
      intro ⟨zp1, x, xp, xz⟩; rw [← xz, s.ray_potential xp] at zp1; use x, zp1, xz
      intro ⟨x, xp, xz⟩; have zp1 := lt_of_le_of_lt xp post; rw [← xz, s.ray_potential zp1]
      use xp, x, zp1
    rw [e]; refine' (IsCompact.image_of_continuousOn (isCompact_closedBall _ _) _).isClosed
    intro x m; simp only [mem_closedBall, Complex.dist_eq, sub_zero] at m
    exact (s.ray_holomorphic (lt_of_le_of_lt m post)).in2.continuousAt.continuousWithinAt
  have uc : IsCompact u := ((isClosed_le pc continuous_const).sdiff io).isCompact
  have z0u : z0 ∈ u := by
    simp only [mem_diff, mem_setOf]; use p01.le; contrapose i0
    simp only [not_not, mem_image, mem_setOf, not_forall, exists_prop] at i0 ⊢; exact i0
  have ne : u.Nonempty := ⟨z0, z0u⟩
  rcases uc.exists_isMinOn ne pc.continuousOn with ⟨z, zu, zm⟩
  simp only [mem_diff, mem_setOf] at zu
  replace zm : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w
  · have m : z ∈ jᶜ := by rw [compl_inter]; right; exact zu.2
    have lt : s.potential c z < p1 := lt_of_le_of_lt (zm z0u) p01
    apply (jc.isOpen_compl.eventually_mem m).mp
    apply ((Continuous.potential s).in2.continuousAt.eventually_lt continuousAt_const lt).mp
    refine' eventually_of_forall fun w lt m ↦ _
    rw [compl_inter] at m; cases' m with m m
    · simp only [compl_setOf, mem_setOf, not_le] at m; linarith
    · apply zm; simp only [mem_diff, mem_setOf]; use lt.le, m
  simp only [mem_setOf, mem_image, not_exists, not_and] at zu
  have za := s.potential_minima_only_a (lt_of_le_of_lt zu.1 post) zm
  have h := zu.2 0 (s.mem_ext c); simp only [s.ray_zero] at h; exact h za.symm

/-- `s.ray` is bijective from `s.ext` to `s.post`, accounting for `c` -/
theorem Super.ray_bij (s : Super f d a) [OnePreimage s] :
    BijOn (fun y : ℂ × ℂ ↦ (y.1, s.ray y.1 y.2)) s.ext s.post := by
  refine ⟨fun _ m ↦ s.ray_post m, ?_, ?_⟩
  · intro ⟨c0, x0⟩ m0 ⟨c1, x1⟩ m1 e; simp only [Prod.ext_iff] at e ⊢; rcases e with ⟨ec, ex⟩
    rw [ec] at m0 ex; use ec, s.ray_inj m0 m1 ex
  · intro ⟨c, x⟩ m; simp only [mem_image, Prod.ext_iff]
    rcases s.ray_surj m with ⟨x, m, e⟩; use⟨c, x⟩, m, rfl, e
