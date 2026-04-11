module
public import Ray.Dynamics.Bottcher
public import Ray.Multibrot.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Cases
import Ray.Analytic.Analytic
import Ray.Dynamics.BottcherNear
import Ray.Dynamics.BottcherNearM
import Ray.Dynamics.Potential
import Ray.Manifold.Analytic
import Ray.Manifold.Nontrivial
import Ray.Manifold.OneDimension
import Ray.Manifold.OpenMapping
import Ray.Misc.Bound
import Ray.Misc.Bounds
import Ray.Misc.Cobounded
import Ray.Misc.Connected
import Ray.Misc.Topology
import Ray.Multibrot.D

/-!
## The Multibrot sets and their basic properties

We define the Multibrot set as points `c` where `z ↦ z^d + c` does not escape to `∞` starting from
`c` (or 0), both as a subset of `ℂ` and of the Riemann sphere `𝕊`.  We then lift the dynamical
results from `Ray.lean` and `Bottcher.lean` about fixed `c` behavior into parameter results about
the Multibrot set.  This file contains only basics; see
`Multibrot/{Iterates,Potential,Postcritical,Bottcher}.lean` for effective bounds and
`Multibrot/Isomorphism.lean`, `Multibrot/Connected.lean`, and `Mandelbrot.lean` for the main
theoretical results.

In detail, this file contains:

1. Definitions of the Multibrot set and complement, and their `potential` and `bottcher` functions.
2. Superattraction from the fixpoint at `∞`, in an effective region of `∞`.
3. An initial exponential growth bound on iterates (`iter_large`).
4. Specific points that are inside or out of the Multibrot set, including all points with
   `2 < abs c` (`multibrot_two_lt`), points that repeat, etc.
5. Analyticity and surjectivity of `bottcher`.
6. Ineffective estimates for `bottcher` and `potential` near `∞`.
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall mem_ball_self mem_ball mem_closedBall)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped ContDiff OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
## Basic properties of the sets
-/

-- Basic properties of multibrot_ext
@[simp] public theorem multibrotExt_inf {d : ℕ} : (∞ : 𝕊) ∈ multibrotExt d :=
  subset_union_right rfl
public theorem multibrotExt_coe {d : ℕ} {c : ℂ} : ↑c ∈ multibrotExt d ↔ c ∉ multibrot d := by
  simp only [multibrotExt, mem_union, mem_singleton_iff, coe_eq_inf_iff, or_false, mem_image,
    mem_compl_iff, coe_eq_coe, not_iff_not]
  constructor; intro ⟨x, m, e⟩; rw [e] at m; exact m; intro m; use c, m
public theorem coe_preimage_multibrotExt {d : ℕ} :
    (fun z : ℂ ↦ (z : 𝕊)) ⁻¹' multibrotExt d = (multibrot d)ᶜ := by
  apply Set.ext; intro z; simp only [mem_compl_iff, mem_preimage, multibrotExt_coe]

/-!
## Basic properties of the iteration `f`
-/

theorem deriv_f' {d : ℕ} {z : ℂ} : deriv (f' d c) z = d * z ^ (d - 1) := by
  have h : HasDerivAt (f' d c) (d * z ^ (d - 1) + 0) z :=
    (hasDerivAt_pow _ _).add (hasDerivAt_const _ _)
  simp only [add_zero] at h; exact h.deriv

/-- Bound on `(1 + z)⁻¹ - 1` used in `superNearF` -/
lemma inv_sub_one_le {z : ℂ} {b : ℝ} (zb : ‖z‖ ≤ b / (1 + b)) (b0 : 0 ≤ b) :
    ‖(1 + z)⁻¹ - 1‖ ≤ b := by
  have z1 : ‖z‖ < 1 := lt_of_le_of_lt zb (by bound)
  have a0 : 1 + z ≠ 0 := by contrapose z1; simp [(by grind : z = -1)]
  nth_rw 2 [← div_self a0]
  simp only [← one_div, ← sub_div, sub_add_cancel_left, Complex.norm_div, norm_neg,
    div_le_iff₀ (norm_pos_iff.mpr a0), ge_iff_le]
  trans b * (‖(1 : ℂ)‖ - ‖z‖)
  · simp only [norm_one]
    suffices h : ‖z‖ * (1 + b) ≤ b by grind
    rwa [← le_div_iff₀ (by linarith)]
  · bound

/-- The set of `z`s for which `superNearF` holds -/
@[expose] public def superNearT (d : ℕ) (c : ℂ) : Set ℂ :=
  {z | ‖z‖ < 1 / 3 ∧ ‖c‖ * ‖z‖ ^ d < 2 / 5}

/-- An explicit bound on the near region near `∞`, giving an explicit region where the
    infinite product formula for `s.bottcher` will hold -/
public theorem superNearF (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    SuperNear (fl (f d) ∞ c) d (superNearT d c) (1 / 3) (2 / 3) := by
  set s := superF d
  have zb : ∀ {z}, z ∈ superNearT d c → ‖z‖ < 1 / 3 := by
    intro z m; simp [superNearT] at m ⊢; linarith
  have cz : ∀ {z}, z ∈ superNearT d c → ‖c * z ^ d‖ ≤ 2 / 5 := by
    intro z m; simp [superNearT] at m ⊢; linarith
  have cz1 : ∀ {z}, z ∈ superNearT d c → 3 / 5 ≤ ‖1 + c * z ^ d‖ := by
    intro z m
    trans ‖(1 : ℂ)‖ - ‖c * z ^ d‖
    · specialize cz m
      simp only [norm_one] at cz ⊢
      linarith
    · bound
  exact
    { d2 := two_le_d d
      a1 := by norm_num
      b0 := by norm_num
      b1 := by norm_num
      c1' := by norm_num
      fa0 := (s.fla c).along_snd
      fd := fd_f
      fc := fc_f
      o := by
        simp only [← norm_pow, ← norm_mul, superNearT]
        apply IsOpen.inter
        · exact isOpen_lt continuous_norm continuous_const
        · exact isOpen_lt (continuous_norm.comp (by continuity)) continuous_const
      t0 := by
        simp only [superNearT, one_div, mem_setOf_eq, norm_zero, inv_pos, Nat.ofNat_pos,
          zero_pow (d_ne_zero d), mul_zero, div_pos_iff_of_pos_left, and_self]
      t2 := fun {z} m ↦ le_trans (zb m).le (by norm_num)
      fa := by
        intro z m
        rw [fl_f]
        refine (analyticAt_id.pow _).div (analyticAt_const.add
          (analyticAt_const.mul (analyticAt_id.pow _))) ?_
        specialize cz m
        contrapose cz
        norm_num [(by grind : c * z ^ d = -1)]
      ft := by
        intro z m
        specialize cz1 m
        specialize zb m
        simp only [fl_f, mem_setOf, norm_div, norm_pow, superNearT] at m ⊢
        have le : ‖z‖ ^ d / ‖1 + c * z ^ d‖ ≤ 5 / 27 := by
          calc ‖z‖ ^ d / ‖1 + c * z ^ d‖
            _ ≤ (1 / 3) ^ d / (3 / 5) := by bound
            _ ≤ (1 / 3) ^ 2 / (3 / 5) := by bound
            _ = 5 / 27 := by norm_num
        refine ⟨by linarith, ?_⟩
        have le1 : ‖z‖ ^ d / ‖1 + c * z ^ d‖ ≤ 1 := by linarith
        calc ‖c‖ * (‖z‖ ^ d / ‖1 + c * z ^ d‖) ^ d
          _ ≤ ‖c‖ * (‖z‖ ^ d / ‖1 + c * z ^ d‖) ^ 2 := by bound
          _ = ‖c‖ * ‖z‖ ^ d * (‖z‖ ^ d / ‖1 + c * z ^ d‖ / ‖1 + c * z ^ d‖) := by ring
          _ ≤ ‖c‖ * ‖z‖ ^ d * (5 / 27 / (3 / 5)) := by bound
          _ ≤ ‖c‖ * ‖z‖ ^ d := mul_le_of_le_one_right (by bound) (by norm_num)
          _ < 2 / 5 := by bound
      gs' := by
        intro z z0 m
        simp only [fl_f, div_div_cancel_left' (pow_ne_zero d z0)]
        refine inv_sub_one_le ?_ (by norm_num)
        norm_num
        simpa using cz m }

/-- `0, ∞` are the only critical points of `f` -/
theorem critical_f {z : 𝕊} : Critical (f d c) z ↔ z = 0 ∨ z = (∞ : 𝕊) := by
  induction' z using OnePoint.rec with z
  · simp only [(superF d).critical_a, or_true]
  · simp only [Critical, mfderiv, (mAnalyticAt_f (c, z)).along_snd.mdifferentiableAt (by decide),
      if_pos, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ,
      writtenInExtChartAt_coe_f, RiemannSphere.extChartAt_coe, coePartialEquiv_symm_apply,
      toComplex_coe, coe_eq_zero, coe_eq_inf_iff, or_false, ← toSpanSingleton_deriv, deriv_f']
    constructor
    · intro h
      have h0 : ContinuousLinearMap.toSpanSingleton ℂ (↑d * z ^ (d - 1)) =
          ContinuousLinearMap.toSpanSingleton ℂ 0 := by simpa using h
      have h' := ContinuousLinearMap.toSpanSingleton_inj.mp h0
      have hz : z ^ (d - 1) = 0 := by
        simpa only [mul_eq_zero, Nat.cast_eq_zero, d_ne_zero, false_or] using h'
      exact (pow_eq_zero_iff ((d_minus_one_pos _).ne')).mp hz
    · intro h
      subst h
      rw [zero_pow (d_minus_one_pos _).ne', mul_zero, ContinuousLinearMap.toSpanSingleton_zero]
      rfl

/-- The multibrot set is all `c`'s s.t. `0` doesn't reach `∞` -/
theorem multibrot_basin' : c ∈ multibrot d ↔ (c, (c : 𝕊)) ∉ (superF d).basin := by
  simp only [multibrot, mem_setOf, Super.basin_iff_attracts, Attracts]

theorem multibrot_basin : c ∈ multibrot d ↔ (c, (0 : 𝕊)) ∉ (superF d).basin := by
  set s := superF d
  simp only [multibrot_basin', not_iff_not, Super.basin, mem_setOf]
  have e : ∀ n, (f d c)^[n] c = (f d c)^[n + 1] 0 := by
    intro n; induction' n with n h
    · simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one, f_0]
    · simp only [Function.iterate_succ_apply', h]
  simp only [e]
  apply Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ (f d c)^[n] 0))

/-- The critical potential is the potential of 0 (as 0 is the only nontrivial critical point) -/
public theorem multibrot_p : (superF d).p c = (superF d).potential c 0 := by
  set s := superF d
  have e : s.ps c = {1, s.potential c 0} := by
    apply Set.ext; intro p
    simp only [Super.ps, mem_singleton_iff, mem_setOf, critical_f, Ne, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · intro h; cases' h with h h; left; exact h; right; rcases h with ⟨p0, z, e, h⟩
      cases' h with h h; rw [h] at e; exact e.symm
      rw [h, s.potential_a] at e; exfalso; exact p0 e.symm
    · intro h; cases' h with h h; left; exact h; right; constructor
      · simp only [h, s.potential_ne_zero]; exact inf_ne_zero.symm
      · use 0, h.symm, Or.inl rfl
  simp only [Super.p, e, csInf_pair]
  exact inf_of_le_right s.potential_le_one

/-- `(c,c)` is postcritical for `c` outside multibrot -/
public theorem multibrotPost (m : c ∉ multibrot d) : Postcritical (superF d) c c := by
  set s := superF d
  simp only [Postcritical, multibrot_p, ← f_0 d, s.potential_eqn]
  simp only [multibrot_basin, not_not] at m
  exact pow_lt_self_of_lt_one₀ ((s.potential_pos c).mpr inf_ne_zero.symm)
    (s.potential_lt_one m) (d_gt_one d)

/-!
## The diagonal Böttcher map
-/

-- `bottcher` at `ℂ` and `∞`
public theorem bottcher_coe {c : ℂ} : bottcher d c = bottcher' d c := by
  simp only [bottcher, fill_coe, bottcher']
@[simp] public theorem bottcher_inf : bottcher d ∞ = 0 := by simp only [bottcher, fill_inf]

/-!
## Exponential lower and upper bounds on iterates
-/

/-- A warmup exponential lower bound on iterates -/
public lemma iter_large (d : ℕ) [Fact (2 ≤ d)] (b : ℝ) {c z : ℂ} (b2 : 2 ≤ b) (bz : b ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) : (b-1)^n * ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  induction' n with n h
  · simp only [pow_zero, one_mul, Function.iterate_zero_apply, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (f' d c)^[n] z = w; rw [hw] at h; clear hw
    have z1 : 1 ≤ ‖z‖ := le_trans (by norm_num) (le_trans b2 bz)
    have b1 : 1 ≤ b - 1 := by linarith
    have b0 : 0 ≤ b - 1 := by linarith
    have nd : n + 1 ≤ n * d + 1 := by bound
    calc ‖w ^ d + c‖
      _ ≥ ‖w ^ d‖ - ‖c‖ := by bound
      _ = ‖w‖ ^ d - ‖c‖ := by rw [norm_pow]
      _ ≥ ((b-1) ^ n * ‖z‖) ^ d - ‖c‖ := by bound
      _ = (b-1) ^ (n*d) * ‖z‖ ^ d - ‖c‖ := by rw [mul_pow, pow_mul]
      _ ≥ (b-1) ^ (n*d) * ‖z‖ ^ 2 - ‖c‖ := by bound
      _ = (b-1) ^ (n*d) * (‖z‖ * ‖z‖) - ‖c‖ := by rw [pow_two]
      _ ≥ (b-1) ^ (n*d) * (b * ‖z‖) - ‖c‖ := by bound
      _ = (b-1) ^ (n*d) * (b-1) * ‖z‖ + ((b-1) ^ (n*d) * ‖z‖ - ‖c‖) := by ring
      _ = (b-1) ^ (n*d + 1) * ‖z‖ + ((b-1) ^ (n * d) * ‖z‖ - ‖c‖) := by rw [pow_succ]
      _ ≥ (b-1) ^ (n + 1) * ‖z‖ + (1 * ‖z‖ - ‖c‖) := by bound
      _ = (b-1) ^ (n + 1) * ‖z‖ + (‖z‖ - ‖c‖) := by rw [one_mul]
      _ ≥ (b-1) ^ (n + 1) * ‖z‖ := by bound

/-- Ap exponential upper bound on a single iteration -/
public lemma iter_small (d : ℕ) (c z : ℂ) : ‖(f' d c z)‖ ≤ ‖z‖ ^ d + ‖c‖ := by
  calc ‖z ^ d + c‖
    _ ≤ ‖z ^ d‖ + ‖c‖ := by bound
    _ ≤ ‖z‖ ^ d + ‖c‖ := by rw [norm_pow]

/-!
## Explicit points that are inside or outside the Multibrot set
-/

/-- Multibrot membership in terms of the `ℂ → ℂ` iteration `f'`, not `f` -/
public theorem f_f'_iter {d : ℕ} (n : ℕ) {z : ℂ} : (f d c)^[n] ↑z = ↑((f' d c)^[n] z) := by
  induction' n with n h; simp only [Function.iterate_zero, id]
  simp only [h, Function.iterate_succ_apply']
  simp only [f, lift_coe']

public theorem multibrot_coe {d : ℕ} :
    c ∈ multibrot d ↔ ¬Tendsto (fun n ↦ (f' d c)^[n] c) atTop (cobounded ℂ) := by
  simp only [multibrot, mem_setOf, f_f'_iter, tendsto_inf_iff_tendsto_cobounded]

/-- Closed Julia sets are not outside radius `max 2 (abs c)` -/
public theorem julia_two_lt {z : ℂ} (z2 : 2 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    (c,↑z) ∈ (superF d).basin := by
  simp only [(superF d).basin_iff_attracts, Attracts, f_f'_iter, tendsto_inf_iff_tendsto_cobounded,
    tendsto_cobounded_iff_norm_tendsto_atTop] at z2 ⊢
  apply Filter.tendsto_atTop_mono (iter_large d ‖z‖ z2.le (le_refl _) cz)
  refine Filter.Tendsto.atTop_mul_pos (by linarith) ?_ tendsto_const_nhds
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

/-- Closed Julia sets are inside radius `max 2 (abs c)` -/
public theorem julia_le_two {z : ℂ} (m : (c,↑z) ∉ (superF d).basin) (cz : ‖c‖ ≤ ‖z‖) : ‖z‖ ≤ 2 := by
  contrapose m
  simp only [not_le] at m ⊢
  exact julia_two_lt m cz

/-- `0 < s.potential` at finite values -/
@[bound] public lemma potential_pos {z : ℂ} : 0 < (superF d).potential c z :=
  ((superF d).potential_pos _).mpr RiemannSphere.coe_ne_inf

/-- `s.potential < 1` outside radius `max 2 (abs c)` -/
public lemma potential_lt_one_of_two_lt {z : ℂ} (z2 : 2 < ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    (superF d).potential c z < 1 :=
  (superF d).potential_lt_one (julia_two_lt z2 cz)

/-- The Multibrot set is inside radius 2 -/
public theorem multibrot_le_two (m : c ∈ multibrot d) : ‖c‖ ≤ 2 := by
  rw [multibrot_basin' (d := d)] at m
  exact julia_le_two m (le_refl _)

/-- The Multibrot set is a subset of `closedBall 0 2` -/
public theorem multibrot_subset_closedBall : multibrot d ⊆ closedBall 0 2 := by
  intro c m; simp only [mem_closedBall, Complex.dist_eq, sub_zero]; exact multibrot_le_two m

/-- Points with absolute value `> 2` are not in the Multibrot set -/
public theorem multibrot_two_lt (a : 2 < ‖c‖) : c ∉ multibrot d := by
  contrapose a; simp only [not_lt] at a ⊢; exact multibrot_le_two a

/-- If the iteration repeats, we're in the Multibrot set -/
public theorem multibrot_of_repeat {d a b : ℕ} (ab : a < b) (h : (f d c)^[a] c = (f d c)^[b] c) :
    c ∈ multibrot d := by
  generalize hg : (fun n ↦ (f' d c)^[n] c) = g
  replace hg : ∀ n, (f' d c)^[n] c = g n := fun n ↦ by rw [← hg]
  simp only [f_f'_iter, coe_eq_coe, hg] at h
  have lo : ∀ n : ℕ, ∃ k, k ≤ b ∧ g n = g k := by
    intro n; induction' n with n h
    · use 0, Nat.zero_le _
    · rcases h with ⟨k, kb, nk⟩
      by_cases e : k = b; use a + 1, Nat.succ_le_iff.mpr ab
      rw [← hg, ← hg, Function.iterate_succ_apply', Function.iterate_succ_apply', hg, hg, nk, e, h]
      use k + 1, Nat.succ_le_iff.mpr (Ne.lt_of_le e kb)
      rw [← hg, ← hg, Function.iterate_succ_apply', Function.iterate_succ_apply', hg, hg, nk]
  simp only [multibrot_coe, hasBasis_cobounded_norm_lt.tendsto_right_iff, true_imp_iff, not_forall,
    Filter.not_eventually, mem_setOf, not_lt, hg]
  use partialSups (fun k ↦ ‖g k‖) b
  refine .of_forall ?_; intro k; rcases lo k with ⟨l, lb, kl⟩
  rw [kl]; exact le_partialSups_of_le (fun k ↦ ‖g k‖) lb

/-- If the iteration hits zero, we're in the Multibrot set -/
public theorem multibrot_of_zero {n : ℕ} (h : (f d c)^[n] c = 0) : c ∈ multibrot d := by
  have i0 : (f d c)^[0] c = c := by rw [Function.iterate_zero_apply]
  have i1 : (f d c)^[n + 1] c = c := by simp only [Function.iterate_succ_apply', h, f_0]
  exact multibrot_of_repeat (Nat.zero_lt_succ _) (_root_.trans i0 i1.symm)

/-- `0 ∈ multbrot d` -/
@[simp] public theorem multibrot_zero : (0 : ℂ) ∈ multibrot d := by
  apply multibrot_of_zero; rw [Function.iterate_zero_apply, coe_zero]

/-- `0 ∉ multibrotExt d` -/
@[simp] public theorem multibrotExt_zero : (0 : 𝕊) ∉ multibrotExt d := by
  simp only [← coe_zero, multibrotExt_coe, not_not, multibrot_zero]

theorem not_multibrot_of_two_lt {n : ℕ} (h : 2 < ‖(f' d c)^[n] c‖) : c ∉ multibrot d := by
  by_cases c2 : 2 < ‖c‖; exact multibrot_two_lt c2
  simp only [multibrot_coe, not_not]; simp only [not_lt] at c2
  generalize hs : ‖((f' d c)^[n] c)‖ = s; rw [hs] at h
  have s1 : 1 ≤ s := by linarith
  have s1' : 1 ≤ s - 1 := by linarith
  have s0 : 0 ≤ s := by linarith
  have b : ∀ k, s * (s - 1) ^ k ≤ ‖(f' d c)^[k + n] c‖ := by
    intro k; induction' k with k p
    · simp only [pow_zero, mul_one, zero_add, hs, le_refl]
    · simp only [Nat.succ_add, Function.iterate_succ_apply']
      generalize hz : (f' d c)^[k + n] c = z; rw [hz] at p
      have ss1 : 1 ≤ s * (s - 1) ^ k := by bound
      have k2 : k ≤ k * 2 := by linarith
      calc ‖(f' d c z)‖
        _ = ‖z ^ d + c‖ := rfl
        _ ≥ ‖z ^ d‖ - ‖c‖ := by bound
        _ = ‖z‖ ^ d - ‖c‖ := by rw [norm_pow]
        _ ≥ (s * (s - 1) ^ k) ^ d - 2 := by bound
        _ ≥ (s * (s - 1) ^ k) ^ 2 - 2 := by bound
        _ = s ^ 2 * (s - 1) ^ (k * 2) - 2 * 1 := by rw [mul_pow, pow_mul, mul_one]
        _ ≥ s ^ 2 * (s - 1) ^ k - s * (s - 1) ^ k := by bound
        _ = s * ((s - 1) ^ k * (s - 1)) := by ring
        _ = s * (s - 1) ^ (k + 1) := by rw [pow_succ]
  simp only [tendsto_cobounded_iff_norm_tendsto_atTop]
  rw [← Filter.tendsto_add_atTop_iff_nat n]; apply Filter.tendsto_atTop_mono b
  refine Filter.Tendsto.pos_mul_atTop (by linarith) tendsto_const_nhds ?_
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

theorem multibrot_eq_le_two :
    multibrot d = ⋂ n : ℕ, (fun c : ℂ ↦ (f' d c)^[n] c) ⁻¹' closedBall 0 2 := by
  apply Set.ext; intro c
  simp only [mem_iInter, mem_preimage, mem_closedBall, Complex.dist_eq, sub_zero]
  constructor; · intro m n; contrapose m; simp only [not_le] at m; exact not_multibrot_of_two_lt m
  · intro h; contrapose h
    simp only [multibrot_coe, tendsto_cobounded_iff_norm_tendsto_atTop, not_not, not_forall, not_le,
      Filter.tendsto_atTop, not_exists] at h ⊢
    rcases(h 3).exists with ⟨n, h⟩; use n; linarith

/-- `multibrot d` is compact -/
public theorem isCompact_multibrot : IsCompact (multibrot d) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall _ _) ?_ multibrot_subset_closedBall
  rw [multibrot_eq_le_two]; apply isClosed_iInter; intro n
  refine IsClosed.preimage ?_ Metric.isClosed_closedBall
  induction' n with n h; simp only [Function.iterate_zero_apply]; exact continuous_id
  simp only [Function.iterate_succ_apply']; rw [continuous_iff_continuousAt]; intro c
  exact (analytic_f' _ (mem_univ _)).continuousAt.comp₂ continuousAt_id h.continuousAt

/-- The exterior of the Multibrot set is open -/
public theorem isOpen_multibrotExt : IsOpen (multibrotExt d) := by
  rw [OnePoint.isOpen_iff_of_mem']
  simp only [coe_preimage_multibrotExt, compl_compl]
  use isCompact_multibrot, isCompact_multibrot.isClosed.isOpen_compl
  exact multibrotExt_inf

/-!
## Analyticity of our Böttcher coordinates
-/

lemma mem_superNearT {c : ℂ} (lo : 3 < ‖c‖) : c⁻¹ ∈ superNearT d c := by
  simp only [superNearT, one_div, mem_setOf_eq, norm_inv, inv_pow]
  refine ⟨by bound, ?_⟩
  calc ‖c‖ * (‖c‖ ^ d)⁻¹
    _ ≤ ‖c‖ * (‖c‖ ^ 2)⁻¹ := by bound
    _ = ‖c‖⁻¹ := by grind
    _ < 3⁻¹ := by bound
    _ < 2 / 5 := by norm_num

def superK : ℝ :=
  Real.exp (2 * (psg (2 / 3) 2⁻¹ * (2 / 3) / 2))

/-- `bottcher' d c` is small for large `c` -/
theorem bottcher_bound {c : ℂ} (lo : 3 < ‖c‖) : ‖bottcher' d c‖ ≤ superK * ‖c⁻¹‖ := by
  set s := superF d
  generalize hg : fl (f d) ∞ c = g
  -- Facts about c and f
  have ct : c⁻¹ ∈ superNearT d c := mem_superNearT lo
  have mem : c ∉ multibrot d := multibrot_two_lt (lt_trans (by norm_num) lo)
  have nz : ∀ n, (f d c)^[n] c ≠ 0 := by
    intro n; contrapose mem; exact multibrot_of_zero mem
  have iter : ∀ n, ((f d c)^[n] ↑c)⁻¹ = ↑(g^[n] c⁻¹) := by
    intro n; induction' n with n h
    have cp : c ≠ 0 := norm_ne_zero_iff.mp (lt_trans (by norm_num) lo).ne'
    simp only [Function.iterate_zero_apply, inv_coe cp]
    have e : (f d c)^[n] ↑c = ((g^[n] c⁻¹ : ℂ) : 𝕊)⁻¹ := by rw [← h, inv_inv]
    simp only [Function.iterate_succ_apply', e]
    generalize hz : g^[n] c⁻¹ = z
    simp only [← hg, fl, extChartAt_inf, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply,
      invEquiv_apply, RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, sub_zero,
      Function.comp_def, add_zero, PartialEquiv.coe_trans_symm, PartialEquiv.symm_symm,
      coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm]
    rw [coe_toComplex]
    simp only [Ne, inv_eq_inf, ← hz, ← h, inv_inv, ← Function.iterate_succ_apply' (f d c)]
    apply nz
  -- Find an n that gets us close enough to ∞ for s.bottcher = bottcher_near
  have b := mem
  simp only [multibrot_basin', not_not] at b
  have attracts := (s.basin_attracts b).eventually (s.bottcher_eq_bottcherNear c)
  rcases (attracts.and (s.basin_stays b)).exists with ⟨n, eq, _⟩; clear attracts b
  simp only [Super.bottcherNear, extChartAt_inf, PartialEquiv.trans_apply,
    coePartialEquiv_symm_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, RiemannSphere.inv_inf,
    toComplex_zero, sub_zero, Super.fl, hg, iter, toComplex_coe] at eq
  -- Translate our bound across n iterations
  have e0 : s.bottcher c ((f d c)^[n] ↑c) = bottcher' d c ^ d ^ n := s.bottcher_eqn_iter n
  have e1 : bottcherNear g d (g^[n] c⁻¹) = bottcherNear g d c⁻¹ ^ d ^ n := by
    rw [← hg]; exact bottcherNear_eqn_iter (superNearF d c) ct n
  rw [e0, e1] at eq; clear e0 e1 iter
  have ae : ‖bottcher' d c‖ = ‖bottcherNear g d c⁻¹‖ := by
    apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _)
      (pow_ne_zero n (d_ne_zero d))).mp
    simp only [← norm_pow, eq]
  simpa only [ae, ← hg, SuperNear.k, SuperNear.kt, superK] using bottcherNear_le (superNearF d c) ct

/-- `bottcher' d c → 0` as `c → ∞` -/
theorem bottcher_tendsto_zero : Tendsto (bottcher' d) (cobounded ℂ) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro r rp
  rw [hasBasis_cobounded_norm_lt.eventually_iff]
  use max 3 (superK / r)
  simp only [true_and, mem_setOf, Complex.dist_eq, sub_zero, max_lt_iff]
  intro z ⟨lo, rz⟩; apply lt_of_le_of_lt (bottcher_bound lo)
  rw [div_lt_iff₀ rp] at rz
  rw [norm_inv, mul_inv_lt_iff₀ (lt_trans (by norm_num) lo)]
  linarith

/-- `bottcher' d` is analytic outside the Multibrot set -/
public theorem bottcher_analytic : AnalyticOnNhd ℂ (bottcher' d) (multibrot d)ᶜ := by
  set s := superF d
  intro c m
  apply ContMDiffAt.analyticAt I I
  exact (s.bottcher_mAnalyticOn (c, c) (multibrotPost m)).comp₂_of_eq contMDiffAt_id
    (mAnalytic_coe _) rfl

/-- `bottcher d` is analytic outside the Multibrot set -/
public theorem bottcherMAnalytic (d : ℕ) [Fact (2 ≤ d)] :
    ContMDiffOnNhd I I (bottcher d) (multibrotExt d) := by
  intro c m; induction c using OnePoint.rec
  · refine mAnalyticAt_fill_inf ?_ bottcher_tendsto_zero
    rw [hasBasis_cobounded_norm_lt.eventually_iff]; use 2
    simp only [true_and, mem_setOf]
    intro z a; exact (bottcher_analytic _ (multibrot_two_lt a)).mAnalyticAt I I
  · simp only [multibrotExt_coe] at m
    exact mAnalyticAt_fill_coe ((bottcher_analytic (d := d) _ m).mAnalyticAt I I)

/-!
## The Multibrot potential map
-/

/-- The potential map on 𝕊, defined as the diagonal of `s.potential` -/
public def potential (d : ℕ) [Fact (2 ≤ d)] : 𝕊 → ℝ :=
  fill (fun c ↦ (superF d).potential c c) 0

public theorem norm_bottcher {c : 𝕊} : ‖bottcher d c‖ = potential d c := by
  set s := superF d
  induction c using OnePoint.rec
  · simp only [bottcher, potential, fill_inf, norm_zero]
  · simp only [bottcher, potential, fill_coe]; exact s.norm_bottcher

public theorem potential_continuous : Continuous (potential d) := by
  set s := superF d; rw [continuous_iff_continuousAt]; intro c; induction c using OnePoint.rec
  · have e : potential d =ᶠ[𝓝 (∞ : 𝕊)] fun c ↦ ‖bottcher d c‖ := by
      refine .of_forall fun c ↦ ?_; rw [← norm_bottcher]
    rw [continuousAt_congr e]
    exact continuous_norm.continuousAt.comp
      (bottcherMAnalytic d _ multibrotExt_inf).continuousAt
  · exact continuousAt_fill_coe ((Continuous.potential s).comp₂
      continuous_id continuous_coe).continuousAt

@[simp, bound] public lemma potential_le_one {c : 𝕊} : potential d c ≤ 1 := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, zero_le_one]
  · simp only [potential, fill_coe, (superF d).potential_le_one]

public theorem potential_lt_one {c : 𝕊} : potential d c < 1 ↔ c ∈ multibrotExt d := by
  set s := superF d
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, zero_lt_one, multibrotExt_inf]
  · constructor
    · intro h; contrapose h
      simp only [not_not, not_lt, multibrot_basin', potential, fill_coe, Super.basin,
        mem_setOf, multibrotExt_coe] at h ⊢
      rw [s.potential_eq_one]; exact h
    · intro m; rw [← norm_bottcher]; simp only [bottcher, fill_coe]
      simp only [multibrotExt_coe] at m
      exact s.bottcher_lt_one (multibrotPost m)

@[simp, bound] public theorem potential_nonneg {c : 𝕊} : 0 ≤ potential d c := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, le_refl]
  · simp only [potential, fill_coe]; exact (superF d).potential_nonneg

public theorem potential_eq_zero {c : 𝕊} : potential d c = 0 ↔ c = (∞ : 𝕊) := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf]
  · simp only [potential, fill_coe, (superF d).potential_eq_zero_of_onePreimage]

public theorem potential_eq_one {c : ℂ} : potential d c = 1 ↔ c ∈ multibrot d := by
  contrapose
  simp only [← multibrotExt_coe, ← potential_lt_one]
  have le : potential d c ≤ 1 := by bound
  grind

/-!
## Dynamical space bottcher facts
-/

@[simp] public lemma spotential_coe_ne_zero {z : ℂ} : (superF d).potential c z ≠ 0 := by
  simp [(superF d).potential_eq_zero_of_onePreimage]

@[simp] public lemma sbottcher_coe_ne_zero {z : ℂ} : (superF d).bottcher c z ≠ 0 := by
  rw [← norm_ne_zero_iff, (superF d).norm_bottcher]
  exact spotential_coe_ne_zero

/-!
## Surjectivity of `bottcher d`
-/

/-- `bottcher d` is nontrivial everywhere in `multibrotExt`,
    as otherwise trivality spreads throughout `𝕊` -/
public theorem bottcherNontrivial {c : 𝕊} (m : c ∈ multibrotExt d) :
    NontrivialMAnalyticAt (bottcher d) c := by
  by_cases h : ∃ᶠ e in 𝓝 c, bottcher d e ≠ bottcher d c
  exact
    { mAnalyticAt := bottcherMAnalytic d _ m
      nonconst := h }
  exfalso; simp only [Filter.not_frequently, not_not] at h
  set b := bottcher d c
  have b1 : ‖b‖ < 1 := by simp only [norm_bottcher, potential_lt_one, m, b]
  -- From bottcher d c = y near a point, show that bottcher d c = y everywhere in 𝕊
  set t := {c | c ∈ multibrotExt d ∧ ∀ᶠ e in 𝓝 c, bottcher d e = b}
  have tu : t = univ := by
    refine IsClopen.eq_univ ?_ ⟨c, m, h⟩; constructor
    · rw [isClosed_iff_frequently]; intro x e; by_contra xt
      have pb : potential d x = ‖b‖ := by
        apply tendsto_nhds_unique_of_frequently_eq potential_continuous.continuousAt
          continuousAt_const
        refine e.mp (.of_forall ?_); intro z ⟨_, h⟩; rw [← h.self_of_nhds, norm_bottcher]
      rw [← pb, potential_lt_one] at b1
      have e' : ∃ᶠ y in 𝓝[{x}ᶜ] x, y ∈ t := by
        simp only [frequently_nhdsWithin_iff, mem_compl_singleton_iff]
        refine e.mp (.of_forall fun z zt ↦ ⟨zt, ?_⟩)
        contrapose xt; rwa [← xt]
      contrapose xt; clear xt; use b1
      cases' ContMDiffAt.eventually_eq_or_eventually_ne (bottcherMAnalytic d _ b1)
        contMDiffAt_const with h h
      use h; contrapose h; simp only [Filter.not_eventually, not_not] at h ⊢
      exact e'.mp (.of_forall fun y yt ↦ yt.2.self_of_nhds)
    · rw [isOpen_iff_eventually]; intro e ⟨m, h⟩
      apply (isOpen_multibrotExt.eventually_mem m).mp
      apply (eventually_eventually_nhds.mpr h).mp
      exact .of_forall fun f h m ↦ ⟨m, h⟩
  -- Contradiction!
  have m0 : (0 : 𝕊) ∈ multibrotExt d :=
    haveI m : (0 : 𝕊) ∈ t := by simp only [tu, mem_univ]
    m.1
  simp only [← coe_zero, multibrotExt_coe, multibrot_zero, not_true] at m0

/-- `bottcher d` surjects onto `ball 0 1` -/
public theorem bottcher_surj (d : ℕ) [Fact (2 ≤ d)] : bottcher d '' multibrotExt d = ball 0 1 := by
  set s := superF d
  apply subset_antisymm
  · intro w; simp only [mem_image]; intro ⟨c, m, e⟩; rw [← e]; clear e w
    induction c using OnePoint.rec
    · simp only [bottcher, fill_inf]; exact mem_ball_self one_pos
    · simp only [multibrotExt_coe] at m
      simp only [bottcher, fill_coe, bottcher', mem_ball, Complex.dist_eq, sub_zero]
      exact s.bottcher_lt_one (multibrotPost m)
  · refine _root_.trans ?_ interior_subset
    refine IsPreconnected.relative_clopen (convex_ball _ _).isPreconnected ?_ ?_ ?_
    · use 0, mem_ball_self one_pos, ∞
      simp only [multibrotExt_inf, bottcher, fill_inf, true_and]
    · -- Relative openness
      rw [IsOpen.interior_eq]; exact inter_subset_right
      rw [isOpen_iff_eventually]; intro z ⟨c, m, e⟩
      rw [← e, (bottcherNontrivial m).nhds_eq_map_nhds, Filter.eventually_map]
      exact
        (isOpen_multibrotExt.eventually_mem m).mp (.of_forall fun e m ↦ by use e, m)
    · -- Relative closedness
      intro x ⟨x1, m⟩; simp only [mem_ball, Complex.dist_eq, sub_zero] at x1
      rcases exists_between x1 with ⟨b, xb, b1⟩
      set t := {e | potential d e ≤ b}
      have ct : IsCompact t := (isClosed_le potential_continuous continuous_const).isCompact
      have ts : t ⊆ multibrotExt d := by
        intro c m; rw [← potential_lt_one]; exact lt_of_le_of_lt m b1
      have mt : x ∈ closure (bottcher d '' t) := by
        rw [mem_closure_iff_frequently] at m ⊢; apply m.mp
        have lt : ∀ᶠ y : ℂ in 𝓝 x, ‖y‖ < b :=
          continuous_norm.continuousAt.eventually_lt continuousAt_const xb
        refine lt.mp (.of_forall fun y lt m ↦ ?_)
        rcases m with ⟨c, _, cy⟩; rw [← cy]; rw [← cy, norm_bottcher] at lt
        exact ⟨c, lt.le, rfl⟩
      apply image_mono ts; rw [IsClosed.closure_eq] at mt; exact mt
      apply IsCompact.isClosed; apply IsCompact.image_of_continuousOn ct
      refine ContinuousOn.mono ?_ ts; exact (bottcherMAnalytic d).continuousOn

/-!
### Ineffective approximations
-/

/-- `s.bottcher c z ~ z⁻¹` for large `z` -/
public theorem bottcher_large_approx (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).bottcher c z * z) (cobounded ℂ) (𝓝 1) := by
  set s := superF d
  have e : ∀ᶠ z : ℂ in cobounded ℂ, s.bottcher c z * z = s.bottcherNear c z * z := by
    suffices e : ∀ᶠ z : ℂ in cobounded ℂ, s.bottcher c z = s.bottcherNear c z by
      exact e.mp (.of_forall fun z e ↦ by rw [e])
    refine coe_tendsto_inf.eventually (p := fun z ↦ s.bottcher c z = s.bottcherNear c z) ?_
    apply s.bottcher_eq_bottcherNear
  rw [Filter.tendsto_congr' e]; clear e
  have m := bottcherNear_monic (s.superNearC.s (mem_univ c))
  simp only [hasDerivAt_iff_tendsto, sub_zero, bottcherNear_zero, smul_eq_mul, mul_one,
    Metric.tendsto_nhds_nhds, Real.dist_eq, Complex.dist_eq] at m
  simp only [Metric.tendsto_nhds, hasBasis_cobounded_norm_lt.eventually_iff, true_and, mem_setOf,
    Complex.dist_eq]
  intro e ep; rcases m e ep with ⟨r, rp, h⟩; use 1 / r; intro z zr
  have az0 : ‖z‖ ≠ 0 := (lt_trans (one_div_pos.mpr rp) zr).ne'
  have z0 : z ≠ 0 := norm_ne_zero_iff.mp az0
  have zir : ‖z⁻¹‖ < r := by
    simp only [one_div, norm_inv] at zr ⊢; exact inv_lt_of_inv_lt₀ rp zr
  specialize @h z⁻¹ zir
  simp only [norm_inv, inv_inv, ← norm_mul, sub_mul, inv_mul_cancel₀ z0, abs_norm,
    mul_comm z _] at h
  simp only [Super.bottcherNear, extChartAt_inf, PartialEquiv.trans_apply,
    coePartialEquiv_symm_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, RiemannSphere.inv_inf,
    toComplex_zero, sub_zero, inv_coe z0, toComplex_coe]
  exact h

/-- `s.potential c z ~ ‖z‖⁻¹` for large `z` -/
public theorem potential_tendsto (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).potential c z * ‖z‖) (cobounded ℂ) (𝓝 1) := by
  set s := superF d
  have c := continuous_norm.continuousAt.tendsto.comp (bottcher_large_approx d c)
  simpa only [s.norm_bottcher, norm_mul, norm_one, Function.comp_def] using c
