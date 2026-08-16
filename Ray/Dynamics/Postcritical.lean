module
public import Ray.Dynamics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Tactic.Cases
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Nice
import Ray.Dynamics.Potential
import Ray.Manifold.Nontrivial
import Ray.Manifold.OpenMapping
import Ray.Misc.Bounds
import Ray.Misc.Topology

/-!
## Postcritical points

A postcritical point w.r.t. a superattracting fixpoint `a` of `f : ℂ → S → S` is a point `z`
with potential smaller than any critical point of `f` other than `a` (in this file we assume
`OnePotential s`, so `a` is the only preimage of `a` under `f`).  Postcritical points are
special because the Böttcher can be analytically continued through all of them, which we
show in `Grow.lean`.  Roughly, this is true because

1. Postcritical points stay postcritical under iteration, since iteration decreases `s.potential`
2. Thus, postcritical points are never precritical
3. Postcritical points form a simply connected set (indeed, a disk), so analytic continuation works

This file has definitions and continuity results only, which are then used by `Grow.lean`,
`Ray.lean`, and `Bottcher.lean` to construct the analytic continuations.
-/

open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z z0 z1 : S}
variable {d n : ℕ}
variable {s : Super f d a}

/-- `s.ps c` is nonempty (since it contains 1) -/
public theorem Super.nonempty_ps (s : Super f d a) : (s.ps c).Nonempty :=
  ⟨1, by simp only [Super.ps, mem_ofPred, true_or]⟩

/-- `s.ps c` is compact -/
public theorem Super.compact_ps (s : Super f d a) [OnePreimage s] [T2Space S] :
    IsCompact (s.ps c) := by
  have pc : Continuous (s.potential c) := (Continuous.potential s).along_snd
  have c1 : IsCompact {(1 : ℝ)} := isCompact_singleton
  convert c1.union ((s.isClosed_critical_not_a.snd_preimage c).isCompact.image pc)
  apply Set.ext; intro p
  simp only [mem_ofPred, Super.ps, mem_singleton_iff, mem_union, mem_image, Ne, ←
    s.potential_eq_zero_of_onePreimage c]
  apply or_congr_right; constructor
  intro ⟨p0, z, e, c⟩; rw [← e] at p0; exact ⟨z, ⟨c, p0⟩, e⟩
  intro ⟨z, ⟨c, p0⟩, e⟩; rw [e] at p0; exact ⟨p0, z, e, c⟩

/-- `s.ps c` has positive members only, since we exclude the critical point at `a` -/
theorem Super.ps_pos (s : Super f d a) (c : ℂ) {p : ℝ} (m : p ∈ s.ps c) : 0 < p := by
  cases' m with m m; simp only [m, zero_lt_one]; rcases m with ⟨p0, z, e, c⟩; rw [← e] at p0 ⊢
  exact p0.symm.lt_of_le s.potential_nonneg

/-- `s.ps c` is bounded below -/
theorem Super.bddBelow_ps (s : Super f d a) : BddBelow (s.ps c) :=
  bddBelow_def.mpr ⟨0, fun _ m ↦ (s.ps_pos c m).le⟩

/-- `s.ps c` attains its infimum -/
theorem Super.mem_ps (s : Super f d a) (c : ℂ) [OnePreimage s] [T2Space S] : s.p c ∈ s.ps c := by
  rw [← s.compact_ps.isClosed.closure_eq]; exact csInf_mem_closure s.nonempty_ps s.bddBelow_ps

/-- `s.p c` is positive, since it is the infimum of a compact set of positive numbers -/
public theorem Super.p_pos (s : Super f d a) (c : ℂ) [OnePreimage s] [T2Space S] : 0 < s.p c :=
  s.ps_pos c (s.mem_ps c)

/-- `s.p c ≤ 1` -/
@[bound] public theorem Super.p_le_one (s : Super f d a) : s.p c ≤ 1 :=
  csInf_le s.bddBelow_ps (Or.inl rfl)

/-- `s.p` doesn't jump down locally as a function of `c`.

    Intuitively, this is because if `c` varies a little bit, critical points might suddenly
    disappear (if we're at the furthest `c` extent of a critical surface) but they can't suddenly
    appear as the set of critical points is closed. -/
public theorem Super.lowerSemicontinuous_p (s : Super f d a) [OnePreimage s] [T2Space S] :
    LowerSemicontinuous s.p := by
  intro c p h; contrapose h
  simp only [not_lt, Filter.not_eventually] at h ⊢
  -- Add a bit of slack
  apply le_of_forall_gt
  intro q' pq'
  rcases exists_between pq' with ⟨q, pq, qq⟩; refine lt_of_le_of_lt ?_ qq; clear qq pq' q'
  by_cases q1 : 1 ≤ q; exact _root_.trans s.p_le_one q1
  simp only [not_le] at q1
  -- Use closedness of the set of non-a critical points
  set t : Set (ℂ × S) := {x | s.potential x.1 x.2 ≤ q ∧ Critical (f x.1) x.2 ∧ x.2 ≠ a}
  have ct : IsClosed t :=
    (isClosed_le (Continuous.potential s) continuous_const).inter s.isClosed_critical_not_a
  set u := Prod.fst '' t
  have cu : IsClosed u := isClosedMap_fst_of_compactSpace _ ct
  suffices m : c ∈ u by
    rcases(mem_image _ _ _).mp m with ⟨⟨c', z⟩, ⟨zp, zc, za⟩, cc⟩
    simp only at cc za zc zp; simp only [cc] at za zc zp; clear cc c'
    simp only [Ne, ← s.potential_eq_zero_of_onePreimage c] at za
    refine _root_.trans (csInf_le s.bddBelow_ps ?_) zp; right; use za, z, rfl, zc
  refine Filter.Frequently.mem_of_closed ?_ cu
  refine h.mp (.of_forall fun e h ↦ ?_)
  rcases exists_lt_of_csInf_lt s.nonempty_ps (lt_of_le_of_lt h pq) with ⟨r, m, rq⟩
  cases' m with m m; linarith; rcases m with ⟨r0, z, zr, zc⟩
  rw [← zr, Ne, s.potential_eq_zero_of_onePreimage] at r0; rw [mem_image]
  refine ⟨(e, z), ⟨?_, zc, r0⟩, rfl⟩; simp only [zr]; exact rq.le

/-- Postcritical points are in the basin, since they have `s.potential c z < s.p c ≤ 1` -/
theorem Postcritical.basin (p : Postcritical s c z) : (c, z) ∈ s.basin :=
  s.potential_lt_one_iff.mp (lt_of_lt_of_le p s.p_le_one)

/-- If `s.potential c z0 ≤ s.potential c z1` and `z1` is postcritical, then `z0` is postcritical -/
theorem Postscritical.mono (p : Postcritical s c z1) (z01 : s.potential c z0 ≤ s.potential c z1) :
    Postcritical s c z0 :=
  lt_of_le_of_lt z01 p

/-- Postcritical points are not precritical, since iteration decreases potential (except for `a`) -/
public theorem Postcritical.not_precritical (p : Postcritical s c z) (p0 : s.potential c z ≠ 0) :
    ¬Precritical (f c) z := by
  contrapose p; simp only [Postcritical, not_lt] at p ⊢
  rcases p with ⟨n, p⟩; trans s.potential c ((f c)^[n] z)
  · refine csInf_le s.bddBelow_ps (Or.inr ⟨?_, (f c)^[n] z, rfl, p⟩)
    simp only [s.potential_eqn_iter]; exact pow_ne_zero _ p0
  · simp only [s.potential_eqn_iter]
    exact pow_le_of_le_one s.potential_nonneg s.potential_le_one (pow_ne_zero _ s.d0)

/-- Postcritical points are not precritical, since iteration decreases potential (except for `a`) -/
theorem Postcritical.not_precritical' (p : Postcritical s c z) (za : z ≠ a) [OnePreimage s] :
    ¬Precritical (f c) z := by
  apply p.not_precritical; simp only [Ne, s.potential_eq_zero_of_onePreimage]; exact za

/-- `s.post` is open -/
public theorem Super.isOpen_post (s : Super f d a) [OnePreimage s] [T2Space S] : IsOpen s.post := by
  set f := fun x : ℂ × S ↦ s.p x.1 - s.potential x.1 x.2
  have fc : LowerSemicontinuous f :=
    (s.lowerSemicontinuous_p.comp continuous_fst).add
      (Continuous.potential s).neg.lowerSemicontinuous
  have e : s.post = f ⁻¹' Ioi 0 :=
    Set.ext fun _ ↦ by
      simp only [Super.post, mem_ofPred, Postcritical, mem_preimage, mem_Ioi, sub_pos, f]
  rw [e]; exact fc.isOpen_preimage _

/-- Postcritical holds locally -/
theorem Postcritical.eventually (p : Postcritical s c z) [OnePreimage s] [T2Space S] :
    ∀ᶠ p : ℂ × S in 𝓝 (c, z), Postcritical s p.1 p.2 := by
  refine (s.isOpen_post.eventually_mem ?_).mp (.of_forall fun _ m ↦ m); exact p

/-- Postcritical points are in the basin -/
public theorem Super.post_basin (s : Super f d a) : s.post ⊆ s.basin := fun _ m ↦
  Postcritical.basin m

/-- `p ∈ s.post` means `p` is postcritical -/
theorem Super.postPostcritical (s : Super f d a) {p : ℂ × S} (m : p ∈ s.post) :
    Postcritical s p.1 p.2 := m

/-- `a` is postcritical -/
@[simp] public lemma Super.post_a (s : Super f d a) [OnePreimage s] [T2Space S] (c : ℂ) :
    (c, a) ∈ s.post := by
  simp only [Super.post, Postcritical, s.potential_a, mem_ofPred]; exact s.p_pos c

/-- `f` maps `s.post` into itself -/
public theorem Super.stays_post (s : Super f d a) {p : ℂ × S} (m : p ∈ s.post) :
    (p.1, f p.1 p.2) ∈ s.post := by
  rcases p with ⟨c, z⟩; simp only [Super.post, mem_ofPred, Postcritical, s.potential_eqn]
  exact lt_of_le_of_lt (pow_le_of_le_one s.potential_nonneg s.potential_le_one s.d0) m

/-- Iterating `f` maps `s.post` into itself -/
public theorem Super.iter_stays_post (s : Super f d a) {p : ℂ × S} (m : p ∈ s.post) (n : ℕ) :
    (p.1, (f p.1)^[n] p.2) ∈ s.post := by
  induction' n with n h; simp only [Function.iterate_zero_apply]; exact m
  simp only [Function.iterate_succ_apply']; exact s.stays_post h

/-- We can get from `s.basin` to `s.post` with enough iterations -/
public theorem Super.basin_post (s : Super f d a) [OnePreimage s] [T2Space S]
    (m : (c, z) ∈ s.basin) : ∃ n, (c, (f c)^[n] z) ∈ s.post := by
  rcases tendsto_atTop_nhds.mp (s.basin_attracts m) {z | (c, z) ∈ s.post} (s.post_a c)
      (s.isOpen_post.snd_preimage c) with ⟨n, h⟩
  specialize h n (le_refl n); simp only [mem_ofPred] at h; use n, h

/-- `s.potential` has postcritical minima only at `z = a` -/
public theorem Super.potential_minima_only_a (s : Super f d a) [OnePreimage s] [T2Space S]
    (p : Postcritical s c z) (m : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w) : z = a := by
  contrapose m; simp only [Filter.not_eventually, not_le]
  have nice := s.nice_nz p.basin
  set f : S → ℂ := s.bottcherNearIter (s.nz c z) c
  have o : 𝓝 (f z) = Filter.map f (𝓝 z) := (nontrivialMAnalyticAt_of_mfderiv_ne_zero
      (nice.contMDiffAt_bottcherNearIter (le_refl _)).along_snd
      (s.bottcherNearIter_mfderiv_ne_zero (nice.mfderiv_ne_zero (le_refl _) (le_refl _))
        (p.not_precritical ((s.potential_ne_zero _).mpr m)))).nhds_eq_map_nhds
  have e : ∃ᶠ x : ℂ in 𝓝 (f z), ‖x‖ < ‖f z‖ := by
    apply frequently_smaller
    contrapose m
    rwa [nice.bottcherNear_eq_zero (le_refl _), s.preimage_eq] at m
  rw [o, Filter.frequently_map] at e
  apply e.mp
  filter_upwards [nice.norm_bottcherNear' (le_refl _)] with w wp lt
  simp only [f, Super.bottcherNearIter, nice.norm_bottcherNear (le_refl _), wp] at lt
  rwa [pow_lt_pow_iff_left₀ (by bound) (by bound) (by simp [s.d0])] at lt
