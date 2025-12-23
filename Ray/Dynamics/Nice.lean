module
public import Ray.Dynamics.BottcherNearM
public import Ray.Dynamics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Tactic.Cases
import Mathlib.Topology.AlexandrovDiscrete
import Ray.Manifold.Analytic
import Ray.Manifold.Inverse
import Ray.Manifold.Nontrivial
import Ray.Manifold.OneDimension
import Ray.Misc.Topology
import all Ray.Dynamics.Potential

/-!
## An `n` which maps whole potential levelsets to `s.near`
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
variable {c : ℂ} {p : ℝ}
variable {a z : S}
variable {d n n0 n1 k : ℕ}
variable {s : Super f d a}

/-- Fix `c`, and let `p < 1`.  Then `u = s.potential c ⁻¹' Icc 0 p` is closed, and thus compact,
    and thus there is a fixed `n` s.t. `f c^[n] '' u ⊆ s.near`.  This lets us work with fixed `n`
    more of the time. -/
public def Super.IsNiceN (s : Super f d a) (c : ℂ) (p : ℝ) (n : ℕ) :=
  ∀ z, s.potential c z ≤ p →
    (c, (f c)^[n] z) ∈ s.near ∧ ∀ k, n ≤ k → mfderiv I I (s.bottcherNear c) ((f c)^[k] z) ≠ 0

public lemma Super.IsNiceN.near (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p) :
    (c, (f c)^[n] z) ∈ s.near :=
  (nice z le).1

public theorem Super.isNice_zero (s : Super f d a) (c : ℂ) [OnePreimage s] : s.IsNiceN c 0 0 := by
  intro z zp
  have za := le_antisymm zp s.potential_nonneg
  simp only [s.potential_eq_zero_of_onePreimage] at za
  rw [za, Function.iterate_zero_apply]; use s.mem_near c
  intro k _; rw [s.iter_a]; exact s.bottcherNear_mfderiv_ne_zero c

public theorem Super.isNiceN_mono (s : Super f d a) (nice : s.IsNiceN c p n0) (n01 : n0 ≤ n1) :
    s.IsNiceN c p n1 := by
  intro z zp; rcases nice z zp with ⟨m, nc⟩
  use s.iter_stays_near' m n01, fun k n1k ↦ nc k (_root_.trans n01 n1k)

variable [T2Space S]

public theorem Super.has_nice_n (s : Super f d a) (c : ℂ) (p1 : p < 1) [op : OnePreimage s] :
    ∃ n, s.IsNiceN c p n := by
  have et : ∀ᶠ z in 𝓝 a, (c, z) ∈ s.near ∧ mfderiv I I (s.bottcherNear c) z ≠ 0 := by
    apply
      (mfderiv_ne_zero_eventually (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd
          (s.bottcherNear_mfderiv_ne_zero c)).mp
    apply ((s.isOpen_near.snd_preimage c).eventually_mem (s.mem_near c)).mp
    refine .of_forall fun z m nc ↦ ?_; use m, nc
  rcases et.exists_mem with ⟨t, m, h⟩
  rcases s.potential_basis c m with ⟨q, qp, qt⟩; clear et m
  rcases exists_pow_lt_of_lt_one qp p1 with ⟨n, pq⟩
  use n; intro z m
  replace m : ∀ k, n ≤ k → s.potential c ((f c)^[k] z) < q := by
    intro k nk; refine lt_of_le_of_lt ?_ pq; simp only [s.potential_eqn_iter]
    have dn := (Nat.lt_pow_self s.d1 (n := k)).le
    apply _root_.trans (pow_le_pow_of_le_one s.potential_nonneg s.potential_le_one dn)
    refine _root_.trans (pow_le_pow_left₀ s.potential_nonneg m _) ?_
    exact pow_le_pow_of_le_one (_root_.trans s.potential_nonneg m) p1.le nk
  use(h _ (qt (m n (le_refl _)))).1, fun k nk ↦ (h _ (qt (m k nk))).2

/-- An `n` such that `(f c)^[n]` sends everything with potential < `p` to `s.near` -/
public def Super.np (s : Super f d a) (c : ℂ) (p : ℝ) : ℕ :=
  if q : p < 1 ∧ OnePreimage s then Nat.find (s.has_nice_n c q.1 (op := q.2)) else 0

public theorem Super.nice_np (s : Super f d a) (c : ℂ) (p1 : p < 1) [op : OnePreimage s] :
    s.IsNiceN c p (s.np c p) := by
  have q : p < 1 ∧ OnePreimage s := ⟨p1, op⟩
  simp only [Super.np, q, true_and, dif_pos]
  exact Nat.find_spec (s.has_nice_n c p1)

theorem Super.np_zero (s : Super f d a) (c : ℂ) [op : OnePreimage s] : s.np c 0 = 0 := by
  simp only [Super.np, zero_lt_one, op, true_and, dif_pos, Nat.find_eq_zero, Super.isNice_zero]

public theorem Super.np_mono (s : Super f d a) (c : ℂ) {p0 p1 : ℝ} (le : p0 ≤ p1) (p11 : p1 < 1)
    [op : OnePreimage s] : s.np c p0 ≤ s.np c p1 := by
  have p01 : p0 < 1 := lt_of_le_of_lt le p11
  have e : s.np c p0 = Nat.find (s.has_nice_n c p01) := by
    simp only [Super.np, p01, op, true_and, dif_pos]
  rw [e]; apply Nat.find_min'; exact fun z zp ↦ s.nice_np c p11 _ (_root_.trans zp le)

/-- An `n` such that `(f c)^[n]` sends everything with potential < `s.potential c z` to `s.near` -/
public def Super.nz (s : Super f d a) (c : ℂ) (z : S) : ℕ :=
  s.np c (s.potential c z)

public lemma Super.nice_nz (s : Super f d a) (m : (c, z) ∈ s.basin) [OnePreimage s] :
    s.IsNiceN c (s.potential c z) (s.nz c z) :=
  s.nice_np c (s.potential_lt_one m)

/-!
## Nice properties that don't depend on `s.near`, since that isn't in `Defs.lean`
-/

namespace Super.IsNiceN
omit [T2Space S]

public lemma contMDiffAt_bottcherNearIter (nice : s.IsNiceN c p n)
    (le : s.potential c z ≤ p) : ContMDiffAt II I ω (uncurry (s.bottcherNearIter n)) (c, z) :=
  s.bottcherNearIter_mAnalytic (nice z le).1

public lemma bottcherNear_eq_zero (nice : s.IsNiceN c p n)
    (le : s.potential c z ≤ p) : s.bottcherNearIter n c z = 0 ↔ (f c)^[n] z = a :=
  s.bottcherNear_eq_zero (nice z le).1

public lemma mfderiv_ne_zero (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p)
    (nk : n ≤ k) : mfderiv I I (s.bottcherNear c) ((f c)^[k] z) ≠ 0 :=
  (nice z le).2 _ nk

public lemma norm_bottcherNear' (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p) :
    ∀ᶠ w in 𝓝 z, ‖s.bottcherNear c ((f c)^[n] w)‖ = s.potential c w ^ d ^ n := by
  filter_upwards [((s.isOpen_preimage _).snd_preimage c).eventually_mem (nice z le).1] with w m
  exact s.norm_bottcherNear m

public lemma norm_bottcherNear (nice : s.IsNiceN c p n) (le : s.potential c z ≤ p) :
    ‖s.bottcherNear c ((f c)^[n] z)‖ = s.potential c z ^ d ^ n :=
  (nice.norm_bottcherNear' le).self_of_nhds
