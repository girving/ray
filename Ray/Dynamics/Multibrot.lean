import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Lhopital
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Ray.Analytic.Holomorphic
import Ray.AnalyticManifold.RiemannSphere
import Ray.Dynamics.Bottcher
import Ray.Dynamics.Multiple
import Ray.Misc.AtInf
import Ray.Tactic.Bound

/-!
## The Multibrot set and its basic properties

We define the Multibrot set as points `c` where `z ↦ z^d + c` does not escape to `∞` starting from
`c` (or 0), both as a subset of `ℂ` and of the Riemann sphere `𝕊`.  We then lift the dynamical
results from `Ray.lean` and `Bottcher.lean` about fixed `c` behavior into parameter results about
the Multibrot set.  Some key results are

1. `(c,c)` is postcritical for each `c` not in the Multibrot set.  To see this, note that `0` and
   `∞` are the only critical points of `f z = z^d + c`, and `c` is postcritical since it is the
   image of `0` (and thus has smaller potential).
2. Therefore, the diagonal Böttcher map `bottcher d c = s.bottcher c c` is holomorphic throughout
   the exterior of the Multibrot set.
3. `bottcher d` is nontrivial throughout the exterior of the Multibrot set, as otherwise triviality
   spreads throughout `𝕊`.
4. `bottcher d` bijects from the exterior of the Multibrot set to `ball 0 1`.
5. There is an explicit, analytic homeomorphism `bottcherHomeomorph d` from the exterior of the
   Multibrot set to `ball 0 1`.

Connectivity of the Multibrot set and its complement are easy consequences of (5); see
`MultibrotConnected.lean` and `Mandelbrot.lean`.

An unfortunate amount of explicit calculation is required in this file.  These calculations mainly
serve to show that our diagonal Böttcher `bottcher d c` is holomorphic with derivative 1 at `∞`, by
showing that the analytically continued map is given by the infinite product for large `c`.  This
does not follow immediately from our dynamical work, which covers only finite `c : ℂ`.  I'm uneasy
that I've missed some basic conceptual arguments that would make these calculations unnecessary,
though it's not a disaster: they may prove useful in downstream numerical calculations.  Here are
some example effective results that we prove:

1. The Multibrot set is inside radius 2.
2. For `16 < abs c`, `abs (bottcher' d c) ≤ 3 * abs c⁻¹`.
   In particular, `bottcher' c d → 0` as `c → ∞`
3. Iterates escape exponentially fast: if `3 ≤ abs c ≤ abs z`, `2^n * abs z ≤ abs (f c^[n] z)`
4. Iterates grow roughly as `z^d^n` for large `c,z`: if `3 ≤ abs c ≤ abs z`, then
   `|log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤ 8 / (d * abs z ^ (d - 1))`
5. `s.potential c z = 1/abs z + o(1/abs z)`: if `4 ≤ abs c ≤ abs z`, then
   `|s.potential c z - 1 / abs z| ≤ 24 / (d * abs z ^ (d - 1) * log (abs z))`
6. If `exp 48 ≤ abs c ≤ abs z`, then `z` is postcritical (`(c,z) ∈ s.post`)
7. If `exp 48 ≤ abs c ≤ abs z`, `s.bottcher = bottcherNear`, and thus the infinite produce holds
8. If `exp 48 ≤ abs c ≤ abs z`, `abs (s.bottcher c z - z⁻¹) ≤ 16 * (abs z)⁻¹^2`
9. `bottcher d` is monic at `∞` (has derivative 1 there)
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Complex (abs)
open Filter (eventually_of_forall Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]
theorem two_le_d [h : Fact (2 ≤ d)] : 2 ≤ d := h.elim
theorem d_pos : 0 < d := lt_trans (by norm_num) two_le_d
theorem d_ne_zero : d ≠ 0 := d_pos.ne'
theorem d_minus_one_pos : 0 < d - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le one_lt_two two_le_d)
theorem d_minus_one_ge_one : 1 ≤ d - 1 := Nat.succ_le_iff.mpr d_minus_one_pos
theorem d_gt_one : 1 < d := lt_of_lt_of_le (by norm_num) two_le_d
theorem d_ge_one : 1 ≤ d := d_gt_one.le

/-!
## The defining iteration, the Multibrot set, and its complement
-/

/-- The Multibrot iteration, `ℂ → ℂ` version -/
def f' (d : ℕ) (c z : ℂ) : ℂ :=
  z ^ d + c

/-- The Multibrot iteration, `𝕊 → 𝕊` version -/
def f (d : ℕ) : ℂ → 𝕊 → 𝕊 :=
  lift' (f' d) ∞

/-- The Multibrot set is those points that do not escape to `∞` -/
def multibrot (d : ℕ) : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ (f d c)^[n] ↑c) atTop (𝓝 ∞)}

/-- The complement of the Multibrot set, including `∞` -/
def multibrotExt (d : ℕ) : Set 𝕊 :=
  ((fun z : ℂ ↦ (z : 𝕊)) '' multibrot d)ᶜ ∪ {∞}

-- Basic properties of multibrot_ext
theorem multibrotExt_inf : ∞ ∈ multibrotExt d :=
  subset_union_right _ _ rfl
theorem multibrotExt_coe {c : ℂ} : ↑c ∈ multibrotExt d ↔ c ∉ multibrot d := by
  simp only [multibrotExt, mem_union, mem_singleton_iff, coe_eq_inf_iff, or_false_iff, mem_image,
    mem_compl_iff, coe_eq_coe, not_iff_not]
  constructor; intro ⟨x, m, e⟩; rw [e] at m; exact m; intro m; use c, m
theorem coe_preimage_multibrotExt : (fun z : ℂ ↦ (z : 𝕊)) ⁻¹' multibrotExt d = (multibrot d)ᶜ := by
  apply Set.ext; intro z; simp only [mem_compl_iff, mem_preimage, multibrotExt_coe]

/-!
## Basic properties of the iteration `f`

In particular, we show that `f d` has a superattracting fixpoint at `∞`.
-/

-- Basic properties of f
theorem f_0' (d : ℕ) [Fact (2 ≤ d)] : f' d c 0 = c := by
  simp only [lift_coe', f', zero_pow d_pos, zero_add]

theorem f_0 (d : ℕ) [Fact (2 ≤ d)] : f d c 0 = c := by
  simp only [f, ← coe_zero, lift_coe', f', zero_pow d_pos, zero_add]

theorem analytic_f' : AnalyticOn ℂ (uncurry (f' d)) univ := fun _ _ ↦
  (analyticAt_snd.pow _).add analyticAt_fst

theorem deriv_f' {z : ℂ} : deriv (f' d c) z = d * z ^ (d - 1) := by
  have h : HasDerivAt (f' d c) (d * z ^ (d - 1) + 0) z :=
    (hasDerivAt_pow _ _).add (hasDerivAt_const _ _)
  simp only [add_zero] at h; exact h.deriv

theorem tendsto_f'_atInf (c : ℂ) : Tendsto (uncurry (f' d)) (𝓝 c ×ˢ atInf) atInf := by
  simp only [atInf_basis.tendsto_right_iff, Complex.norm_eq_abs, Set.mem_setOf_eq,
    forall_true_left, uncurry, Metric.eventually_nhds_prod_iff]
  intro r; use 1, zero_lt_one, fun z ↦ max r 0 + abs c + 1 < abs z; constructor
  · refine' (eventually_atInf (max r 0 + abs c + 1)).mp (eventually_of_forall fun w h ↦ _)
    simp only [Complex.norm_eq_abs] at h; exact h
  · intro e ec z h; simp only [Complex.dist_eq] at ec
    have zz : abs z ≤ abs (z ^ d) := by
      rw [Complex.abs.map_pow]; refine' le_self_pow _ d_ne_zero
      exact le_trans (le_add_of_nonneg_left (add_nonneg (le_max_right _ _) (Complex.abs.nonneg _)))
        h.le
    calc abs (f' d e z)
      _ = abs (z ^ d + e) := rfl
      _ = abs (z ^ d + (c + (e - c))) := by ring_nf
      _ ≥ abs (z ^ d) - abs (c + (e - c)) := by bound
      _ ≥ abs (z ^ d) - (abs c + abs (e - c)) := by bound
      _ ≥ abs z - (abs c + 1) := by bound [zz]
      _ > max r 0 + abs c + 1 - (abs c + 1) := by bound
      _ = max r 0 := by ring_nf
      _ ≥ r := le_max_left _ _

theorem holomorphicF : Holomorphic II I (uncurry (f d)) :=
  holomorphicLift' analytic_f' tendsto_f'_atInf

theorem writtenInExtChartAt_coe_f {z : ℂ} : writtenInExtChartAt I I (z : 𝕊) (f d c) = f' d c := by
  simp only [writtenInExtChartAt, f, Function.comp, lift_coe', RiemannSphere.extChartAt_coe,
    LocalEquiv.symm_symm, coeLocalEquiv_apply, coeLocalEquiv_symm_apply, toComplex_coe]

theorem fl_f : fl (f d) ∞ = fun c z : ℂ ↦ z^d / (1 + c * z^d) := by
  funext c z
  simp only [fl, RiemannSphere.extChartAt_inf, Function.comp, invEquiv_apply,
    LocalEquiv.trans_apply, Equiv.toLocalEquiv_apply, LocalEquiv.coe_trans_symm,
    coeLocalEquiv_symm_apply, LocalEquiv.symm_symm, coeLocalEquiv_apply,
    Equiv.toLocalEquiv_symm_apply, invEquiv_symm, inv_inf, toComplex_zero, add_zero, sub_zero]
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', f, lift_inf', inv_inf, toComplex_zero, zero_pow d_pos,
      zero_div]
  simp only [f, f', inv_coe z0, lift_coe', inv_pow]
  have zd := pow_ne_zero d z0
  by_cases h : (z ^ d)⁻¹ + c = 0
  · simp only [h, coe_zero, inv_zero', toComplex_inf]
    simp only [← add_eq_zero_iff_neg_eq.mp h, neg_mul, inv_mul_cancel zd, ← sub_eq_add_neg,
      sub_self, div_zero]
  rw [inv_coe h, toComplex_coe, eq_div_iff, inv_mul_eq_iff_eq_mul₀ h, right_distrib,
    inv_mul_cancel zd]
  contrapose h; rw [not_not]
  rw [not_not, add_comm, add_eq_zero_iff_eq_neg, ← eq_div_iff zd, neg_div, ←
    inv_eq_one_div, ← add_eq_zero_iff_eq_neg, add_comm] at h
  exact h

/-- `f` near `∞` with the `z^d` factor removed -/
def gl (d : ℕ) (c z : ℂ) :=
  (1 + c * z ^ d)⁻¹

theorem gl_f {z : ℂ} : g (fl (f d) ∞ c) d z = gl d c z := by
  simp only [fl_f, gl, g]
  by_cases z0 : z = 0
  simp only [if_pos, z0, zero_pow d_pos, MulZeroClass.mul_zero, add_zero, inv_one]
  rw [if_neg z0, div_eq_mul_inv _ (_ + _), mul_comm, mul_div_assoc, div_self (pow_ne_zero _ z0),
    mul_one]

theorem analyticAt_gl : AnalyticAt ℂ (gl d c) 0 := by
  apply (analyticAt_const.add (analyticAt_const.mul ((analyticAt_id _ _).pow _))).inv
  simp only [zero_pow d_pos, MulZeroClass.mul_zero]; norm_num

theorem fl_f' : fl (f d) ∞ = fun c z : ℂ ↦ (z - 0) ^ d • gl d c z := by
  funext c z; simp only [fl_f, gl, sub_zero, Algebra.id.smul_eq_mul, div_eq_mul_inv]

theorem gl_zero : gl d c 0 = 1 := by simp only [gl, zero_pow d_pos, MulZeroClass.mul_zero]; norm_num

theorem gl_frequently_ne_zero : ∃ᶠ z in 𝓝 0, gl d c z ≠ 0 := by
  refine' (analyticAt_gl.continuousAt.eventually_ne _).frequently; simp only [gl_zero]
  exact one_ne_zero

theorem fc_f : leadingCoeff (fl (f d) ∞ c) 0 = 1 := by
  rw [fl_f', analyticAt_gl.monomial_mul_leadingCoeff gl_frequently_ne_zero, leadingCoeff_of_ne_zero]
  exact gl_zero; rw [gl_zero]; exact one_ne_zero

theorem fd_f : orderAt (fl (f d) ∞ c) 0 = d := by
  rw [fl_f', analyticAt_gl.monomial_mul_orderAt gl_frequently_ne_zero, orderAt_eq_zero, add_zero]
  rw [gl_zero]; exact one_ne_zero

theorem f_inf : f d c ∞ = ∞ := by simp only [f, f', lift_inf', eq_self_iff_true, imp_true_iff]

-- f has a superattracting fixpoint at ∞
theorem superF (d : ℕ) [Fact (2 ≤ d)] : Super (f d) d ∞ :=
  { d2 := two_le_d
    fa := holomorphicF
    fc := fun _ ↦ fc_f
    fd := fun _ ↦ fd_f
    f0 := fun _ ↦ f_inf }

/-- An explicit bound on the near region near `∞`, giving an explicit region where the
    infinite product formula for `s.bottcher` will hold -/
theorem superNearF (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    SuperNear (fl (f d) ∞ c) d {z | abs z < (max 16 (abs c / 2))⁻¹} := by
  set s := superF d
  generalize ht : {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹} = t
  have cz : ∀ {z}, z ∈ t → abs (c * z ^ d) ≤ 1 / 8 := by
    intro z m; simp only [← ht, mem_setOf] at m
    simp only [Complex.abs.map_mul, Complex.abs.map_pow]
    trans abs c * (max 16 (abs c / 2))⁻¹ ^ d; bound
    rw [inv_pow, mul_inv_le_iff]; swap; bound
    rw [mul_one_div]; rw [le_div_iff, mul_comm]; swap; norm_num
    refine' le_trans _ (pow_le_pow (le_max_of_le_left (by norm_num)) two_le_d)
    by_cases cb : abs c / 2 ≤ 16
    rw [max_eq_left cb, pow_two]; linarith
    rw [max_eq_right (not_le.mp cb).le, pow_two]; nlinarith
  have cz1 : ∀ {z}, z ∈ t → 7 / 8 ≤ abs (1 + c * z ^ d) := by
    intro z m
    calc abs (1 + c * z ^ d)
      _ ≥ Complex.abs 1 - abs (c * z ^ d) := by bound
      _ ≥ Complex.abs 1 - 1 / 8 := by linarith [cz m]
      _ = 7 / 8 := by norm_num
  have zb : ∀ {z}, z ∈ t → abs z ≤ 1 / 8 := by
    intro z m; rw [← ht] at m; refine le_trans (le_of_lt m) ?_
    rw [one_div]; exact inv_le_inv_of_le (by norm_num) (le_trans (by norm_num) (le_max_left _ _))
  exact
    { d2 := two_le_d
      fa0 := (s.fla c).in2
      fd := fd_f
      fc := fc_f
      o := by rw [← ht]; exact isOpen_lt Complex.continuous_abs continuous_const
      t0 := by simp only [← ht, mem_setOf, Complex.abs.map_zero]; bound
      t2 := fun {z} m ↦ le_trans (zb m) (by norm_num)
      fa := by
        intro z m; rw [fl_f]
        refine ((analyticAt_id _ _).pow _).div (analyticAt_const.add
          (analyticAt_const.mul ((analyticAt_id _ _).pow _))) ?_
        rw [← Complex.abs.ne_zero_iff]; exact (lt_of_lt_of_le (by norm_num) (cz1 m)).ne'
      ft := by
        intro z m; specialize cz1 m; specialize zb m
        simp only [fl_f, mem_setOf, map_div₀, Complex.abs.map_pow, ← ht] at m ⊢
        refine lt_of_le_of_lt ?_ m; rw [div_le_iff (lt_of_lt_of_le (by norm_num) cz1)]
        refine le_trans (pow_le_pow_of_le_one (Complex.abs.nonneg _)
          (le_trans zb (by norm_num)) two_le_d) ?_
        rw [pow_two]; refine' mul_le_mul_of_nonneg_left _ (Complex.abs.nonneg _)
        exact le_trans zb (le_trans (by norm_num) cz1)
      gs' := by
        intro z z0 m; simp only [fl_f, div_div_cancel_left' (pow_ne_zero d z0)]
        specialize cz1 m
        have czp : 0 < abs (1 + c * z ^ d) := lt_of_lt_of_le (by norm_num) cz1
        refine' le_of_mul_le_mul_right _ czp
        rw [← Complex.abs.map_mul, mul_sub_right_distrib, one_mul,
          inv_mul_cancel (Complex.abs.ne_zero_iff.mp czp.ne'), ← sub_sub, sub_self, zero_sub,
          Complex.abs.map_neg]
        exact le_trans (cz m) (le_trans (by norm_num)
          (mul_le_mul_of_nonneg_left cz1 (by norm_num))) }

/-- `f` has one preimage of `∞` -/
instance onePreimageF : OnePreimage (superF d) where
  eq_a := by
    intro c z; induction z using OnePoint.rec
    · simp only [eq_self_iff_true, imp_true_iff]
    · simp only [f, lift_coe', coe_eq_inf_iff]

/-- `0, ∞` are the only critical points of `f` -/
theorem critical_f {z : 𝕊} : Critical (f d c) z ↔ z = 0 ∨ z = ∞ := by
  induction' z using OnePoint.rec with z
  · simp only [(superF d).critical_a, or_true]
  · simp only [Critical, mfderiv, (holomorphicF (c, z)).in2.mdifferentiableAt, if_pos,
      ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ, writtenInExtChartAt_coe_f,
      RiemannSphere.extChartAt_coe, coeLocalEquiv_symm_apply, toComplex_coe, coe_eq_zero,
      coe_eq_inf_iff, or_false_iff, ← deriv_fderiv, deriv_f', ContinuousLinearMap.ext_iff,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, Algebra.id.smul_eq_mul,
      one_mul, ContinuousLinearMap.zero_apply, mul_eq_zero, Nat.cast_eq_zero, d_ne_zero,
      false_or_iff, pow_eq_zero_iff d_minus_one_pos]
    dsimp [TangentSpace]
    simp only [ge_iff_le, mul_eq_zero, Nat.cast_eq_zero, d_ne_zero, tsub_pos_iff_lt,
      pow_eq_zero_iff d_minus_one_pos, false_or]
    constructor
    · intro h; specialize h 1
      simp only [one_mul, mul_eq_zero, one_ne_zero, false_or_iff] at h
      exact h
    · exact fun h x ↦ Or.inr h

/-- The multibrot set is all `c`'s s.t. `0` doesn't reach `∞` -/
theorem multibrot_basin' : c ∈ multibrot d ↔ (c, (c : 𝕊)) ∉ (superF d).basin := by
  simp only [multibrot, mem_setOf, Super.basin_iff_attracts, Attracts]

theorem multibrot_basin : c ∈ multibrot d ↔ (c, (0 : 𝕊)) ∉ (superF d).basin := by
  set s := superF d
  simp only [multibrot_basin', not_iff_not, Super.basin, mem_setOf]
  have e : ∀ n, (f d c)^[n] c = (f d c)^[n + 1] 0 := by
    intro n; induction' n with n h
    · simp only [Function.iterate_zero_apply, zero_add, Function.iterate_one, f_0, Nat.zero_eq]
    · simp only [Function.iterate_succ_apply', h]
  simp only [e]; constructor
  · intro ⟨n, h⟩; exact ⟨n + 1, h⟩
  · intro ⟨n, h⟩; use n; simp only [Function.iterate_succ_apply']; exact s.stays_near h

/-- The critical potential is the potential of 0 (as 0 is the only nontrivial critical point) -/
theorem multibrot_p : (superF d).p c = (superF d).potential c 0 := by
  set s := superF d
  have e : s.ps c = {1, s.potential c 0} := by
    apply Set.ext; intro p
    simp only [Super.ps, mem_singleton_iff, mem_setOf, critical_f, Ne.def, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · intro h; cases' h with h h; left; exact h; right; rcases h with ⟨p0, z, e, h⟩
      cases' h with h h; rw [h] at e; exact e.symm
      rw [h, s.potential_a] at e; exfalso; exact p0 e.symm
    · intro h; cases' h with h h; left; exact h; right; constructor
      · simp only [h, ← Ne.def, s.potential_ne_zero]; exact inf_ne_zero.symm
      · use 0, h.symm, Or.inl rfl
  simp only [Super.p, e, csInf_pair]; exact inf_of_le_right s.potential_le_one

/-- `(c,c)` is postcritical for `c` outside multibrot -/
theorem multibrotPost (m : c ∉ multibrot d) : Postcritical (superF d) c c := by
  set s := superF d
  simp only [Postcritical, multibrot_p, ← f_0 d, s.potential_eqn]
  simp only [multibrot_basin, not_not] at m
  exact pow_lt_self_of_lt_one ((s.potential_pos c).mpr inf_ne_zero.symm)
    (s.potential_lt_one m) d_gt_one

/-!
## The diagonal Böttcher map
-/

/-- The Böttcher map for the Multibrot set is the diagonal of the dynamical map (`ℂ → ℂ` version) -/
def bottcher' (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) : ℂ :=
  (superF d).bottcher c c

/-- The Böttcher map for the Multibrot set is the diagonal of the dynamical map (`𝕊 → ℂ` version) -/
def bottcher (d : ℕ) [Fact (2 ≤ d)] : 𝕊 → ℂ :=
  fill (bottcher' d) 0

-- `bottcher` at `ℂ` and `∞`
theorem bottcher_coe {c : ℂ} : bottcher d c = bottcher' d c := rfl
theorem bottcher_inf : bottcher d ∞ = 0 := rfl

/-!
## Explicit points that are inside or outside the Multibrot set
-/

/-- Multibrot membership in terms of the `ℂ → ℂ` iteration `f'`, not `f` -/
theorem f_f'_iter (n : ℕ) {z : ℂ} : (f d c)^[n] ↑z = ↑((f' d c)^[n] z) := by
  induction' n with n h; simp only [Function.iterate_zero, id]
  simp only [h, Function.iterate_succ_apply']
  simp only [f, lift', rec_coe]

theorem multibrot_coe : c ∈ multibrot d ↔ ¬Tendsto (fun n ↦ (f' d c)^[n] c) atTop atInf := by
  simp only [multibrot, mem_setOf, f_f'_iter, not_iff_not, tendsto_inf_iff_tendsto_atInf]

/-- The Multibrot set is inside radius 2 -/
theorem multibrot_le_two (m : c ∈ multibrot d) : abs c ≤ 2 := by
  set s := abs c
  contrapose m
  simp only [multibrot_coe, not_le, not_not] at m ⊢
  have s1 : 1 ≤ s := le_trans (by norm_num) m.le
  have s1' : 1 ≤ s - 1 := by linarith
  have a : ∀ z : ℂ, 1 ≤ abs z → abs z ^ 2 - s ≤ abs (f' d c z) := by
    intro z z1; simp only [f']; refine le_trans (sub_le_sub_right ?_ _) (Complex.abs.le_add _ _)
    simp only [Complex.abs.map_pow]; exact pow_le_pow z1 two_le_d
  have b : ∀ n, s * (s - 1) ^ n ≤ abs ((f' d c)^[n] c) := by
    intro n; induction' n with n h
    · simp only [pow_zero, mul_one, Function.iterate_zero_apply, le_refl]
    · simp only [Function.iterate_succ_apply', le_refl]
      refine le_trans ?_ (a _ ?_)
      trans (s * (s - 1) ^ n) ^ 2 - s
      · calc (s * (s - 1) ^ n) ^ 2 - s
          _ = s ^ 2 * ((s - 1) ^ n) ^ 2 - s := by ring
          _ = s ^ 2 * (s - 1) ^ (n * 2) - s := by rw [pow_mul]
          _ ≥ s ^ 2 * (s - 1) ^ (n * 2) - s * (s - 1) ^ (n * 2) := by bound
          _ = s * ((s - 1) ^ 1 * (s - 1) ^ (n * 2)) := by ring
          _ = s * (s - 1) ^ (1 + n * 2) := by rw [pow_add]
          _ ≥ s * (s - 1) ^ (1 + n * 1) := by bound [pow_le_pow]
          _ = s * (s - 1) ^ (n + 1) := by ring_nf
      · bound
      · exact le_trans (Left.one_le_mul_of_le_of_le s1 (one_le_pow_of_one_le s1' _) (by linarith)) h
  simp only [tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs]
  apply Filter.tendsto_atTop_mono b
  refine' Filter.Tendsto.mul_atTop (by linarith) tendsto_const_nhds _
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

/-- The Multibrot set is a subset of `closedBall 0 2` -/
theorem multibrot_subset_closedBall : multibrot d ⊆ closedBall 0 2 := by
  intro c m; simp only [mem_closedBall, Complex.dist_eq, sub_zero]; exact multibrot_le_two m

/-- Points with absolute value `> 2` are not in the Multibrot set -/
theorem multibrot_two_lt (a : 2 < abs c) : c ∉ multibrot d := by
  contrapose a; simp only [not_lt, not_not] at a ⊢; exact multibrot_le_two a

/-- If the iteration repeats, we're in the Multibrot set -/
theorem multibrot_of_repeat {a b : ℕ} (ab : a < b) (h : (f d c)^[a] c = (f d c)^[b] c) :
    c ∈ multibrot d := by
  generalize hg : (fun n ↦ (f' d c)^[n] c) = g
  replace hg : ∀ n, (f' d c)^[n] c = g n := fun n ↦ by rw [← hg]
  simp only [f_f'_iter, ← coe_zero, coe_eq_coe, hg] at h
  have lo : ∀ n : ℕ, ∃ k, k ≤ b ∧ g n = g k := by
    intro n; induction' n with n h
    · use 0, Nat.zero_le _
    · rcases h with ⟨k, kb, nk⟩
      by_cases e : k = b; use a + 1, Nat.succ_le_iff.mpr ab
      rw [← hg, ← hg, Function.iterate_succ_apply', Function.iterate_succ_apply', hg, hg, nk, e, h]
      use k + 1, Nat.succ_le_iff.mpr (Ne.lt_of_le e kb)
      rw [← hg, ← hg, Function.iterate_succ_apply', Function.iterate_succ_apply', hg, hg, nk]
  simp only [multibrot_coe, atInf_basis.tendsto_right_iff, true_imp_iff, not_forall,
    Filter.not_eventually, mem_setOf, not_lt, Complex.norm_eq_abs, hg]
  use partialSups (fun k ↦ Complex.abs (g k)) b
  apply Filter.frequently_of_forall; intro k; rcases lo k with ⟨l, lb, kl⟩
  rw [kl]; exact le_partialSups_of_le (fun k ↦ abs (g k)) lb

/-- If the iteration hits zero, we're in the Multibrot set -/
theorem multibrot_of_zero {n : ℕ} (h : (f d c)^[n] c = 0) : c ∈ multibrot d := by
  have i0 : (f d c)^[0] c = c := by rw [Function.iterate_zero_apply]
  have i1 : (f d c)^[n + 1] c = c := by simp only [Function.iterate_succ_apply', h, f_0]
  exact multibrot_of_repeat (Nat.zero_lt_succ _) (_root_.trans i0 i1.symm)

/-- `0 ∈ multbrot d` -/
theorem multibrot_zero : (0 : ℂ) ∈ multibrot d := by
  apply multibrot_of_zero; rw [Function.iterate_zero_apply, coe_zero]

theorem not_multibrot_of_two_lt {n : ℕ} (h : 2 < abs ((f' d c)^[n] c)) : c ∉ multibrot d := by
  by_cases c2 : 2 < abs c; exact multibrot_two_lt c2
  simp only [multibrot_coe, not_not]; simp only [not_lt] at c2
  generalize hs : abs ((f' d c)^[n] c) = s; rw [hs] at h
  have s1 : 1 ≤ s := by linarith
  have s1' : 1 ≤ s - 1 := by linarith
  have s0 : 0 ≤ s := by linarith
  have b : ∀ k, s * (s - 1) ^ k ≤ abs ((f' d c)^[k + n] c) := by
    intro k; induction' k with k p
    · simp only [pow_zero, mul_one, zero_add, Nat.zero_eq, hs, le_refl]
    · simp only [Nat.succ_add, Function.iterate_succ_apply']
      generalize hz : (f' d c)^[k + n] c = z; rw [hz] at p
      have ss1 : 1 ≤ s * (s - 1) ^ k := by bound [one_le_mul_of_one_le_of_one_le]
      have k2 : k ≤ k * 2 := by linarith
      calc abs (f' d c z)
        _ = abs (z ^ d + c) := rfl
        _ ≥ abs (z ^ d) - abs c := by bound
        _ = abs z ^ d - abs c := by rw [Complex.abs.map_pow]
        _ ≥ (s * (s - 1) ^ k) ^ d - 2 := by bound [pow_le_pow_of_le_left]
        _ ≥ (s * (s - 1) ^ k) ^ 2 - 2 := by bound [pow_le_pow, two_le_d]
        _ = s ^ 2 * (s - 1) ^ (k * 2) - 2 * 1 := by rw [mul_pow, pow_mul, mul_one]
        _ ≥ s ^ 2 * (s - 1) ^ k - s * (s - 1) ^ k := by bound [pow_le_pow, one_le_pow_of_one_le]
        _ = s * ((s - 1) ^ k * (s - 1)) := by ring
        _ = s * (s - 1) ^ (k + 1) := by rw [pow_succ']
  simp only [tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs]
  rw [← Filter.tendsto_add_atTop_iff_nat n]; apply Filter.tendsto_atTop_mono b
  refine' Filter.Tendsto.mul_atTop (by linarith) tendsto_const_nhds _
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

theorem multibrot_eq_le_two :
    multibrot d = ⋂ n : ℕ, (fun c : ℂ ↦ (f' d c)^[n] c) ⁻¹' closedBall 0 2 := by
  apply Set.ext; intro c
  simp only [mem_iInter, mem_preimage, mem_closedBall, Complex.dist_eq, sub_zero]
  constructor; · intro m n; contrapose m; simp only [not_le] at m; exact not_multibrot_of_two_lt m
  · intro h; contrapose h
    simp only [multibrot_coe, tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs,
      not_not, not_forall, not_le, Filter.tendsto_atTop, not_exists] at h ⊢
    rcases(h 3).exists with ⟨n, h⟩; use n; linarith

/-- `multibrot d` is compact -/
theorem isCompact_multibrot : IsCompact (multibrot d) := by
  refine' IsCompact.of_isClosed_subset (isCompact_closedBall _ _) _ multibrot_subset_closedBall
  rw [multibrot_eq_le_two]; apply isClosed_iInter; intro n
  refine' IsClosed.preimage _ Metric.isClosed_ball
  induction' n with n h; simp only [Function.iterate_zero_apply]; exact continuous_id
  simp only [Function.iterate_succ_apply']; rw [continuous_iff_continuousAt]; intro c
  exact (analytic_f' _ (mem_univ _)).continuousAt.comp₂ continuousAt_id h.continuousAt

/-- The exterior of the Multibrot set is open -/
theorem isOpen_multibrotExt : IsOpen (multibrotExt d) := by
  rw [OnePoint.isOpen_iff_of_mem']
  simp only [coe_preimage_multibrotExt, compl_compl]
  use isCompact_multibrot, isCompact_multibrot.isClosed.isOpen_compl
  exact multibrotExt_inf

/-!
## Analyticity of our Böttcher coordinates
-/

/-- `bottcher' d c` is small for large `c` -/
theorem bottcher_bound {c : ℂ} (lo : 16 < abs c) : abs (bottcher' d c) ≤ 3 * abs c⁻¹ := by
  set s := superF d
  generalize hg : fl (f d) ∞ c = g
  -- Facts about c and f
  have ct : c⁻¹ ∈ {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹} := by
    simp only [mem_setOf, map_inv₀]
    apply inv_lt_inv_of_lt; bound; refine max_lt lo (half_lt_self (lt_trans (by norm_num) lo))
  have mem : c ∉ multibrot d := multibrot_two_lt (lt_trans (by norm_num) lo)
  have nz : ∀ n, (f d c)^[n] c ≠ 0 := by
    intro n; contrapose mem; simp only [not_not] at mem ⊢; exact multibrot_of_zero mem
  have iter : ∀ n, ((f d c)^[n] ↑c)⁻¹ = ↑(g^[n] c⁻¹) := by
    intro n; induction' n with n h
    have cp : c ≠ 0 := Complex.abs.ne_zero_iff.mp (lt_trans (by norm_num) lo).ne'
    simp only [Function.iterate_zero_apply, inv_coe cp, toComplex_coe]
    have e : (f d c)^[n] ↑c = ((g^[n] c⁻¹ : ℂ) : 𝕊)⁻¹ := by rw [← h, inv_inv]
    simp only [Function.iterate_succ_apply', e]
    generalize hz : g^[n] c⁻¹ = z
    simp only [← hg, fl, extChartAt_inf, LocalEquiv.trans_apply, Equiv.toLocalEquiv_apply,
      invEquiv_apply, inv_inf, coeLocalEquiv_symm_apply, toComplex_zero, sub_zero,
      Function.comp, add_zero, LocalEquiv.coe_trans_symm, LocalEquiv.symm_symm,
      coeLocalEquiv_apply, Equiv.toLocalEquiv_symm_apply, invEquiv_symm]
    rw [coe_toComplex]
    simp only [Ne.def, inv_eq_inf, ← hz, ← h, inv_inv, ← Function.iterate_succ_apply' (f d c)]
    apply nz
  -- Find an n that gets us close enough to ∞ for s.bottcher = bottcher_near
  have b := mem
  simp only [multibrot_basin', not_not] at b
  have attracts := (s.basin_attracts b).eventually (s.bottcher_eq_bottcherNear c)
  rcases (attracts.and (s.basin_stays b)).exists with ⟨n, eq, _⟩; clear attracts b
  simp only [Super.bottcherNear, extChartAt_inf, LocalEquiv.trans_apply,
    coeLocalEquiv_symm_apply, Equiv.toLocalEquiv_apply, invEquiv_apply, inv_inf, toComplex_zero,
    sub_zero, Super.fl, hg, iter, toComplex_coe] at eq
  -- Translate our bound across n iterations
  have e0 : s.bottcher c ((f d c)^[n] ↑c) = bottcher' d c ^ d ^ n := s.bottcher_eqn_iter n
  have e1 : bottcherNear g d (g^[n] c⁻¹) = bottcherNear g d c⁻¹ ^ d ^ n := by
    rw [← hg]; exact bottcherNear_eqn_iter (superNearF d c) ct n
  rw [e0, e1] at eq; clear e0 e1 iter
  have ae : abs (bottcher' d c) = abs (bottcherNear g d c⁻¹) := by
    apply (pow_left_inj (Complex.abs.nonneg _) (Complex.abs.nonneg _)
      (pow_pos d_pos n : 0 < d ^ n)).mp
    simp only [← Complex.abs.map_pow, eq]
  rw [ae, ← hg]; exact bottcherNear_le (superNearF d c) ct

/-- `bottcher' d c → 0` as `c → ∞` -/
theorem bottcher_tendsto_zero : Tendsto (bottcher' d) atInf (𝓝 0) := by
  rw [Metric.tendsto_nhds]; intro r rp; rw [atInf_basis.eventually_iff]
  use max 16 (3 / r)
  simp only [true_and_iff, mem_setOf, Complex.dist_eq, sub_zero, Complex.norm_eq_abs, max_lt_iff]
  intro z ⟨lo, rz⟩; apply lt_of_le_of_lt (bottcher_bound lo)
  rw [div_lt_iff rp] at rz; rw [map_inv₀, mul_inv_lt_iff (lt_trans (by norm_num) lo)]; exact rz

/-- `bottcher' d` is holomorphic outside the Multibrot set -/
theorem bottcher_analytic : AnalyticOn ℂ (bottcher' d) (multibrot d)ᶜ := by
  set s := superF d; intro c m; apply HolomorphicAt.analyticAt I I
  exact (s.bottcher_holomorphicOn (c, c) (multibrotPost m)).comp₂_of_eq holomorphicAt_id
    (holomorphic_coe _) rfl

/-- `bottcher d` is holomorphic outside the Multibrot set -/
theorem bottcherHolomorphic (d : ℕ) [Fact (2 ≤ d)] :
    HolomorphicOn I I (bottcher d) (multibrotExt d) := by
  intro c m; induction c using OnePoint.rec
  · refine' holomorphicAt_fill_inf _ bottcher_tendsto_zero
    rw [atInf_basis.eventually_iff]; use 2
    simp only [true_and_iff, mem_setOf, Complex.norm_eq_abs]
    intro z a; exact (bottcher_analytic _ (multibrot_two_lt a)).holomorphicAt I I
  · simp only [multibrotExt_coe] at m
    exact holomorphicAt_fill_coe ((bottcher_analytic (d := d) _ m).holomorphicAt I I)

/-!
## The Multibrot potential map
-/

/-- The potential map on 𝕊, defined as the diagonal of `s.potential` -/
def potential (d : ℕ) [Fact (2 ≤ d)] : 𝕊 → ℝ :=
  fill (fun c ↦ (superF d).potential c c) 0

theorem abs_bottcher {c : 𝕊} : abs (bottcher d c) = potential d c := by
  set s := superF d
  induction c using OnePoint.rec
  · simp only [bottcher, potential, fill_inf, Complex.abs.map_zero]
  · simp only [bottcher, potential, fill_coe]; exact s.abs_bottcher

theorem potential_continuous : Continuous (potential d) := by
  set s := superF d; rw [continuous_iff_continuousAt]; intro c; induction c using OnePoint.rec
  · have e : potential d =ᶠ[𝓝 ∞] fun c ↦ abs (bottcher d c) := by
      refine' eventually_of_forall fun c ↦ _; rw [← abs_bottcher]
    rw [continuousAt_congr e]
    exact Complex.continuous_abs.continuousAt.comp
      (bottcherHolomorphic d _ multibrotExt_inf).continuousAt
  · exact continuousAt_fill_coe ((Continuous.potential s).comp₂
      continuous_id continuous_coe).continuousAt

theorem potential_lt_one {c : 𝕊} : potential d c < 1 ↔ c ∈ multibrotExt d := by
  set s := superF d
  induction c using OnePoint.rec
  · simp only [potential, bottcher, fill_inf, zero_lt_one, multibrotExt_inf]
  · constructor
    · intro h; contrapose h
      simp only [not_not, not_lt, multibrot_basin', potential, fill_coe, Super.basin,
        mem_setOf, not_exists, multibrotExt_coe] at h ⊢
      rw [s.potential_eq_one]; exact h
    · intro m; rw [← abs_bottcher]; simp only [bottcher, fill_coe]
      simp only [multibrotExt_coe] at m
      exact s.bottcher_lt_one (multibrotPost m)

theorem potential_nonneg {c : 𝕊} : 0 ≤ potential d c := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, le_refl]
  · simp only [potential, fill_coe]; exact (superF d).potential_nonneg

theorem potential_eq_zero {c : 𝕊} : potential d c = 0 ↔ c = ∞ := by
  induction c using OnePoint.rec
  · simp only [potential, fill_inf, eq_self_iff_true]
  · simp only [potential, fill_coe, (superF d).potential_eq_zero_of_onePreimage]

/-!
## Surjectivity of `bottcher d`
-/

/-- `bottcher d` is nontrivial everywhere in `multibrotExt`,
    as otherwise trivality spreads throughout `𝕊` -/
theorem bottcherNontrivial {c : 𝕊} (m : c ∈ multibrotExt d) :
    NontrivialHolomorphicAt (bottcher d) c := by
  by_cases h : ∃ᶠ e in 𝓝 c, bottcher d e ≠ bottcher d c
  exact
    { holomorphicAt := bottcherHolomorphic d _ m
      nonconst := h }
  exfalso; simp only [Filter.not_frequently, not_not] at h
  set b := bottcher d c
  have b1 : abs b < 1 := by simp only [abs_bottcher, potential_lt_one, m]
  -- From bottcher d c = y near a point, show that bottcher d c = y everywhere in 𝕊
  set t := {c | c ∈ multibrotExt d ∧ ∀ᶠ e in 𝓝 c, bottcher d e = b}
  have tu : t = univ := by
    refine' IsClopen.eq_univ _ ⟨c, m, h⟩; constructor
    · rw [isOpen_iff_eventually]; intro e ⟨m, h⟩
      apply (isOpen_multibrotExt.eventually_mem m).mp
      apply (eventually_eventually_nhds.mpr h).mp
      exact eventually_of_forall fun f h m ↦ ⟨m, h⟩
    · rw [isClosed_iff_frequently]; intro x e; by_contra xt
      have pb : potential d x = abs b := by
        apply tendsto_nhds_unique_of_frequently_eq potential_continuous.continuousAt
          continuousAt_const
        refine' e.mp (eventually_of_forall _); intro z ⟨_, h⟩; rw [← h.self, abs_bottcher]
      rw [← pb, potential_lt_one] at b1
      have e' : ∃ᶠ y in 𝓝[{x}ᶜ] x, y ∈ t := by
        simp only [frequently_nhdsWithin_iff, mem_compl_singleton_iff]
        refine' e.mp (eventually_of_forall fun z zt ↦ ⟨zt, _⟩)
        contrapose xt; simp only [not_not] at xt ⊢; rwa [← xt]
      contrapose xt; simp only [not_not]; use b1
      cases' HolomorphicAt.eventually_eq_or_eventually_ne (bottcherHolomorphic d _ b1)
        holomorphicAt_const with h h
      use h; contrapose h; simp only [Filter.not_eventually, not_not] at h ⊢
      exact e'.mp (eventually_of_forall fun y yt ↦ yt.2.self)
  -- Contradiction!
  have m0 : (0 : 𝕊) ∈ multibrotExt d :=
    haveI m : (0 : 𝕊) ∈ t := by simp only [tu, mem_univ]
    m.1
  simp only [← coe_zero, multibrotExt_coe, multibrot_zero, not_true] at m0

/-- `bottcher d` surjects onto `ball 0 1` -/
theorem bottcher_surj (d : ℕ) [Fact (2 ≤ d)] : bottcher d '' multibrotExt d = ball 0 1 := by
  set s := superF d
  apply subset_antisymm
  · intro w; simp only [mem_image]; intro ⟨c, m, e⟩; rw [← e]; clear e w
    induction c using OnePoint.rec
    · simp only [bottcher, fill_inf]; exact mem_ball_self one_pos
    · simp only [multibrotExt_coe] at m
      simp only [bottcher, fill_coe, bottcher', mem_ball, Complex.dist_eq, sub_zero]
      exact s.bottcher_lt_one (multibrotPost m)
  · refine _root_.trans ?_ interior_subset
    refine' IsPreconnected.relative_clopen (convex_ball _ _).isPreconnected _ _ _
    · use 0, mem_ball_self one_pos, ∞
      simp only [multibrotExt_inf, bottcher, fill_inf, true_and_iff]
    · -- Relative openness
      rw [IsOpen.interior_eq]; exact inter_subset_right _ _
      rw [isOpen_iff_eventually]; intro z ⟨c, m, e⟩
      rw [← e, (bottcherNontrivial m).nhds_eq_map_nhds, Filter.eventually_map]
      exact
        (isOpen_multibrotExt.eventually_mem m).mp (eventually_of_forall fun e m ↦ by use e, m)
    · -- Relative closedness
      intro x ⟨x1, m⟩; simp only [mem_ball, Complex.dist_eq, sub_zero] at x1
      rcases exists_between x1 with ⟨b, xb, b1⟩
      set t := {e | potential d e ≤ b}
      have ct : IsCompact t := (isClosed_le potential_continuous continuous_const).isCompact
      have ts : t ⊆ multibrotExt d := by
        intro c m; rw [← potential_lt_one]; exact lt_of_le_of_lt m b1
      have mt : x ∈ closure (bottcher d '' t) := by
        rw [mem_closure_iff_frequently] at m ⊢; apply m.mp
        have lt : ∀ᶠ y : ℂ in 𝓝 x, abs y < b :=
          Complex.continuous_abs.continuousAt.eventually_lt continuousAt_const xb
        refine' lt.mp (eventually_of_forall fun y lt m ↦ _)
        rcases m with ⟨c, _, cy⟩; rw [← cy]; rw [← cy, abs_bottcher] at lt
        exact ⟨c, lt.le, rfl⟩
      apply image_subset _ ts; rw [IsClosed.closure_eq] at mt; exact mt
      apply IsCompact.isClosed; apply IsCompact.image_of_continuousOn ct
      refine' ContinuousOn.mono _ ts; exact (bottcherHolomorphic d).continuousOn

/-!
## Effective bounds on iterates and Böttcher coordinates
-/

/-- A warmup exponential lower bound on iterates -/
theorem iter_large (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (cb : 3 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ) :
    (2:ℝ)^n * abs z ≤ abs ((f' d c)^[n] z) := by
  induction' n with n h
  · simp only [pow_zero, one_mul, Function.iterate_zero_apply, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (f' d c)^[n] z = w; rw [hw] at h; clear hw
    have z4 : 3 ≤ abs z := le_trans cb cz
    have z1 : 1 ≤ abs z := le_trans (by norm_num) z4
    have d1 : 1 ≤ d := d_ge_one
    have nd : n + 1 ≤ n * d + 1 := by bound [le_mul_of_one_le_right]
    calc abs (w ^ d + c)
      _ ≥ abs (w ^ d) - abs c := by bound
      _ = abs w ^ d - abs c := by rw [Complex.abs.map_pow]
      _ ≥ ((2:ℝ) ^ n * abs z) ^ d - abs c := by bound
      _ = (2:ℝ) ^ (n*d) * abs z ^ d - abs c := by rw [mul_pow, pow_mul]
      _ ≥ (2:ℝ) ^ (n*d) * abs z ^ 2 - abs c := by bound [pow_le_pow z1 two_le_d]
      _ = (2:ℝ) ^ (n*d) * (abs z * abs z) - abs c := by rw [pow_two]
      _ ≥ (2:ℝ) ^ (n*d) * (3 * abs z) - abs c := by bound
      _ = (2:ℝ) ^ (n*d) * 2 * abs z + ((2:ℝ) ^ (n * d) * abs z - abs c) := by ring
      _ = (2:ℝ) ^ (n*d + 1) * abs z + ((2:ℝ) ^ (n * d) * abs z - abs c) := by rw [pow_succ']
      _ ≥ (2:ℝ) ^ (n + 1) * abs z + (1 * abs z - abs c) := by bound [pow_le_pow]
      _ = (2:ℝ) ^ (n + 1) * abs z + (abs z - abs c) := by rw [one_mul]
      _ ≥ (2:ℝ) ^ (n + 1) * abs z := by bound

/-- Iterates tend to infinity for large `c, z` -/
theorem tendsto_iter_atInf (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z) :
    Tendsto (fun n ↦ (f' d c)^[n] z) atTop atInf := by
  simp only [tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs]
  refine' Filter.tendsto_atTop_mono (iter_large d c3 cz) _
  exact Filter.Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- The approximate change of `log (log (abs z))` across one iterate -/
theorem f_approx {c z : ℂ} (cb : 3 ≤ abs c) (cz : abs c ≤ abs z) :
    |log (log (abs (z ^ d + c))) - log (log (abs z)) - log d| ≤ 4 / ↑d / abs z ^ (d - 1) := by
  have dp : 0 < d := d_pos
  have d0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr d_ne_zero
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have z3 : 3 ≤ abs z := le_trans cb cz
  have z1 : 1 ≤ abs z := le_trans (by norm_num) z3
  have z0' : 0 < abs z := lt_of_lt_of_le (by norm_num) z3
  have zd : 3 ≤ abs z ^ (d - 1) := by
    calc abs z ^ (d - 1)
      _ ≥ (3:ℝ) ^ (d - 1) := by bound [pow_mono z1]
      _ ≥ (3:ℝ) ^ 1 := by bound [pow_le_pow _ d_minus_one_ge_one]
      _ = 3 := by norm_num
  have z0 : z ≠ 0 := Complex.abs.ne_zero_iff.mp (z0'.ne')
  have zd0 : z ^ d ≠ 0 := pow_ne_zero _ z0
  have zc0 : z ^ d + c ≠ 0 := by
    rw [← Complex.abs.ne_zero_iff]; apply ne_of_gt
    calc abs (z ^ d + c)
      _ ≥ abs (z ^ d) - abs c := by bound
      _ = abs z ^ d - abs c := by rw [Complex.abs.map_pow]
      _ ≥ abs z ^ 2 - abs z := by bound [pow_le_pow _ two_le_d]
      _ = abs z * (abs z - 1) := by ring
      _ ≥ 3 * (3 - 1) := by bound
      _ > 0 := by norm_num
  have cz : abs (c / z ^ d) ≤ 1 / abs z ^ (d - 1) := by
    have d1 : z^d = z^(d - 1 + 1) := by rw [Nat.sub_add_cancel d_ge_one]
    simp only [d1, map_div₀, Complex.abs.map_pow, pow_succ, Complex.abs.map_mul, div_mul_eq_div_div]
    bound
  have czs : abs (c / z ^ d) ≤ 1 / 2 := by
    apply le_trans cz
    calc 1 / abs z ^ (d - 1)
      _ ≤ 1 / 3 := by bound
      _ ≤ 1 / 2 := by norm_num
  have l0s : 1 ≤ log (abs z) := by
    rw [Real.le_log_iff_exp_le z0']; exact le_trans Real.exp_one_lt_3.le z3
  have l0 : 0 < log (abs z) := lt_of_lt_of_le (by norm_num) l0s
  have l1 : 0 < ↑d * log (abs z) := by bound
  have l2 : |log (abs (1 + c / z ^ d))| ≤ 2 / abs z ^ (d - 1) := by
    nth_rw 1 [← Complex.log_re]
    refine le_trans (Complex.abs_re_le_abs _) (le_trans (log1p_small czs) ?_)
    calc 2 * abs (c / z ^ d)
      _ ≤ 2 * (1 / abs z ^ (d - 1)) := by bound
      _ = 2 / abs z ^ (d - 1) := by rw [← mul_div_assoc, mul_one]
  have l3 : 0 < ↑d * log (abs z) + log (abs (1 + c / z ^ d)) := by
    suffices h : -log (abs (1 + c / z ^ d)) < ↑d * log (abs z); linarith
    apply lt_of_le_of_lt (neg_le_neg_iff.mpr (abs_le.mp l2).1); simp only [neg_neg]
    trans (1 : ℝ)
    · calc 2 / abs z ^ (d - 1)
        _ ≤ 2 / 3 := by bound
        _ < 1 := by norm_num
    · calc ↑d * log (abs z)
        _ ≥ 2 * 1 := by bound
        _ > 1 := by norm_num
  rw [log_abs_add (z ^ d) c zd0 zc0, Complex.abs.map_pow, Real.log_pow, log_add _ _ l1 l3,
    Real.log_mul (Nat.cast_ne_zero.mpr d_ne_zero) l0.ne']
  generalize hw : log (1 + log (abs (1 + c / z ^ d)) / (d * log (abs z))) = w
  ring_nf; rw [← hw]; clear hw w
  have inner : |log (abs (1 + c / z ^ d)) / (d * log (abs z))| ≤ 2 / d / abs z ^ (d - 1) := by
    simp only [abs_div, abs_of_pos l1, div_le_iff l1]; apply le_trans l2
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, mul_comm _ (d:ℝ),
      mul_comm _ (d:ℝ)⁻¹, ← mul_assoc, ← mul_assoc, mul_inv_cancel d0, one_mul]
    exact le_mul_of_one_le_right (by bound) l0s
  have weak : 2 / ↑d / abs z ^ (d - 1) ≤ 1 / 2 := by
    calc 2 / ↑d / abs z ^ (d - 1)
      _ ≤ 2 / 2 / 3 := by bound
      _ ≤ 1 / 2 := by norm_num
  apply le_trans (Real.log1p_small (le_trans inner weak))
  simp only [(by norm_num : (4 : ℝ) = 2 * 2), ←mul_assoc _ (2:ℝ) (2:ℝ), mul_comm _ (2:ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  simp only [← mul_assoc, ← mul_div_assoc, ← div_eq_mul_inv, div_right_comm _ _ (d:ℝ), inv_pow,
    inner]

/-- Absolute values of iterates grow roughly as `z^d^n` for large `c,z` -/
theorem iter_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ) :
    |log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤
      8 / (d * abs z ^ (d - 1)) := by
  have z3 : 3 ≤ abs z := le_trans c3 cz
  have z0 : 0 < abs z := lt_of_lt_of_le (by linarith) z3
  have d0 : 0 < d := d_pos
  have d1' : 0 < d-1 := d_minus_one_pos
  -- Strengthen to get something we can prove by induction
  suffices h : |log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤
      8 * (1 - (1 / 2 : ℝ) ^ n) / (d * abs z ^ (d - 1)) by
    apply le_trans h; rw [div_le_div_right]
    · bound
    · bound
  induction' n with n h
  · simp only [Function.iterate_zero_apply, sub_self, Nat.cast_zero, MulZeroClass.zero_mul,
      abs_zero, pow_zero, zero_div, MulZeroClass.mul_zero, le_refl]
  -- Generalize away the iteration
  simp only [Function.iterate_succ_apply', Nat.cast_succ, right_distrib, one_mul,
    sub_add_eq_sub_sub _ _ (log d), ← sub_add_eq_sub_sub _ _ (↑n * log d)]
  generalize hw : (f' d c)^[n] z = w
  generalize hb : log (log (abs z)) + n * log d = b
  have rw : (2:ℝ) ^ n * abs z ≤ abs w := by
    trans (2:ℝ) ^ n * abs z; bound; rw [← hw]; exact iter_large d c3 cz n
  rw [← sub_add_eq_sub_sub, hw, hb] at h; clear hw hb
  have cw : abs c ≤ abs w := by
    refine le_trans cz (le_trans ?_ rw); bound [le_mul_of_one_le_left, one_le_pow_of_one_le]
  -- Do the main calculation
  have e : log (log (abs (w ^ d + c))) - b - log d =
      log (log (abs (w ^ d + c))) - log (log (abs w)) - log d + (log (log (abs w)) - b) := by abel
  rw [f', e]; refine le_trans (abs_add _ _) (le_trans (add_le_add (f_approx c3 cw) h) ?_); clear e h
  rw [← div_mul_eq_div_div, ← le_sub_iff_add_le, ← sub_div, ← mul_sub, ← sub_add,
    sub_sub_cancel_left, neg_add_eq_sub, pow_succ, ← one_sub_mul, sub_half, ← mul_assoc,
    (by norm_num : (8 : ℝ) * (1 / 2) = 4), div_pow, one_pow, ← mul_div_assoc, mul_one, ←
    div_mul_eq_div_div, ← mul_assoc, mul_comm _ (d:ℝ), mul_assoc (d:ℝ) _ _]
  refine div_le_div_of_le_left (by norm_num) (by bound) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by bound)
  calc abs w ^ (d - 1)
    _ ≥ ((2:ℝ) ^ n * abs z) ^ (d - 1) := by bound
    _ = ((2:ℝ) ^ n) ^ (d - 1) * abs z ^ (d - 1) := by rw [mul_pow]
    _ ≥ (2:ℝ) ^ n * abs z ^ (d - 1) := by bound [one_le_pow_of_one_le]

/-- A lower bound-only, non-log version of `iter_approx` -/
theorem iter_bounds (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z) (n : ℕ) :
    abs z ^ ((d:ℝ) ^ n / exp (8 / (d * abs z ^ (d - 1)))) ≤ abs ((f' d c)^[n] z) ∧
      abs ((f' d c)^[n] z) ≤ abs z ^ ((d:ℝ) ^ n * exp (8 / (d * abs z ^ (d - 1)))) := by
  have z1 : 1 < abs z := lt_of_lt_of_le (by norm_num) (le_trans c3 cz)
  have z0 : 0 < abs z := lt_trans (by norm_num) z1
  have d0 : 0 < (d : ℝ) := Nat.cast_pos.mpr d_pos
  have f1 : 1 < abs ((f' d c)^[n] z) :=
    lt_of_lt_of_le (one_lt_mul (one_le_pow_of_one_le one_le_two _) z1) (iter_large d c3 cz n)
  have f0 : 0 < abs ((f' d c)^[n] z) := lt_trans zero_lt_one f1
  have l0 : 0 < log (abs ((f' d c)^[n] z)) := Real.log_pos f1
  rcases abs_le.mp (iter_approx d c3 cz n) with ⟨lo, hi⟩
  simp only [sub_le_iff_le_add', le_sub_iff_add_le] at lo hi
  simp only [neg_add_eq_sub, sub_add_eq_add_sub, Real.log_le_iff_le_exp l0,
    Real.le_log_iff_exp_le l0, Real.log_le_iff_le_exp f0, Real.le_log_iff_exp_le f0, Real.exp_add,
    Real.exp_sub, Real.exp_log (Real.log_pos z1), Real.exp_mul, Real.exp_log z0,
    mul_comm _ (log (abs z)), mul_div_assoc] at lo hi
  rw [← Real.exp_mul (↑n) (log ↑d), mul_comm (n:ℝ) _, Real.exp_mul (log ↑d) ↑n, Real.exp_log d0,
    Real.rpow_nat_cast] at lo hi
  use lo, hi

/-- `s.bottcher c z ~ 1/z` for large `z` -/
theorem bottcher_large_approx (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).bottcher c z * z) atInf (𝓝 1) := by
  set s := superF d
  have e : ∀ᶠ z : ℂ in atInf, s.bottcher c z * z = s.bottcherNear c z * z := by
    suffices e : ∀ᶠ z : ℂ in atInf, s.bottcher c z = s.bottcherNear c z
    exact e.mp (eventually_of_forall fun z e ↦ by rw [e])
    refine coe_tendsto_inf.eventually (p := fun z ↦ s.bottcher c z = s.bottcherNear c z) ?_
    apply s.bottcher_eq_bottcherNear
  rw [Filter.tendsto_congr' e]; clear e
  have m := bottcherNear_monic (s.superNearC.s (mem_univ c))
  simp only [hasDerivAt_iff_tendsto, sub_zero, bottcherNear_zero, smul_eq_mul, mul_one,
    Metric.tendsto_nhds_nhds, Real.dist_eq, Complex.norm_eq_abs, Complex.dist_eq, abs_mul,
    abs_of_nonneg (Complex.abs.nonneg _), abs_inv] at m
  simp only [Metric.tendsto_nhds, atInf_basis.eventually_iff, true_and_iff, mem_setOf,
    Complex.dist_eq, Complex.norm_eq_abs]
  intro e ep; rcases m e ep with ⟨r, rp, h⟩; use 1 / r; intro z zr
  have az0 : abs z ≠ 0 := (lt_trans (one_div_pos.mpr rp) zr).ne'
  have z0 : z ≠ 0 := Complex.abs.ne_zero_iff.mp az0
  have zir : abs (z⁻¹) < r := by
    simp only [one_div, map_inv₀] at zr ⊢; exact inv_lt_of_inv_lt rp zr
  specialize @h z⁻¹ zir
  simp only [map_inv₀, inv_inv, ← Complex.abs.map_mul, sub_mul, inv_mul_cancel z0,
    mul_comm z _] at h
  simp only [Super.bottcherNear, extChartAt_inf, LocalEquiv.trans_apply,
    coeLocalEquiv_symm_apply, Equiv.toLocalEquiv_apply, invEquiv_apply, inv_inf, toComplex_zero,
    sub_zero, inv_coe z0, toComplex_coe]
  exact h

/-- `s.potential c z ~ 1/abs z` for large `z` -/
theorem potential_tendsto (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).potential c z * abs z) atInf (𝓝 1) := by
  set s := superF d
  simp only [← s.abs_bottcher, ← Complex.abs.map_mul, ← Complex.abs.map_one]
  exact Complex.continuous_abs.continuousAt.tendsto.comp (bottcher_large_approx d c)

-- The derivative of `x → exp (-exp x)`, for use in approximating `s.potential` -/
theorem hasDerivAt_exp_neg_exp (x : ℝ) :
    HasDerivAt (fun x ↦ exp (-exp x)) (-exp (x - exp x)) x := by
  have h : HasDerivAt (fun x ↦ exp (-exp x)) (exp (-exp x) * -exp x) x :=
    HasDerivAt.exp (Real.hasDerivAt_exp x).neg
  simp only [mul_neg, ← Real.exp_add, neg_add_eq_sub] at h; exact h

theorem deriv_exp_neg_exp (x : ℝ) : deriv (fun x ↦ exp (-exp x)) x = -exp (x - exp x) :=
  (hasDerivAt_exp_neg_exp x).deriv

/-- This is a weak bound, but it's all we use below -/
theorem deriv_exp_neg_exp_le (x : ℝ) : ‖deriv (fun x ↦ exp (-exp x)) x‖ ≤ exp (-x) := by
  rw [deriv_exp_neg_exp]
  simp only [Real.norm_eq_abs, abs_le]; constructor
  · rw [neg_le_neg_iff, Real.exp_le_exp]
    suffices h : 2 * x ≤ exp x; linarith
    by_cases x1 : x ≤ 1
    exact le_trans (by linarith) (Real.add_one_le_exp _)
    exact le_trans (by nlinarith) (Real.quadratic_le_exp_of_nonneg (by linarith))
  · rw [neg_le]; refine (lt_trans ?_ (Real.exp_pos _)).le; rw [neg_lt_zero]; exact Real.exp_pos _

/-- `potential` is the limit of roots of iterates -/
theorem tendsto_potential (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c3 : 3 ≤ abs c) (cz : abs c ≤ abs z) :
    Tendsto (fun n ↦ abs ((f' d c)^[n] z) ^ (-((d ^ n : ℕ) : ℝ)⁻¹)) atTop
      (𝓝 ((superF d).potential c z)) := by
  set s := superF d
  have p0 : s.potential c z ≠ 0 := by rw [s.potential_ne_zero]; exact coe_ne_inf
  suffices h : Tendsto (fun n ↦ (abs ((f' d c)^[n] z) *
      s.potential c ↑((f' d c)^[n] z)) ^ (-((d ^ n : ℕ) : ℝ)⁻¹))
      atTop (𝓝 1) by
    replace h := h.mul_const (s.potential c z)
    simp only [div_mul_cancel _ p0, one_mul, ← f_f'_iter, s.potential_eqn_iter,
      Real.mul_rpow (Complex.abs.nonneg _) (pow_nonneg s.potential_nonneg _),
      Real.pow_nat_rpow_nat_inv s.potential_nonneg (pow_ne_zero _ d_ne_zero),
      Real.rpow_neg (pow_nonneg s.potential_nonneg _), ← div_eq_mul_inv] at h
    exact h
  simp only [← s.abs_bottcher, ← Complex.abs.map_mul, mul_comm _ (s.bottcher _ _)]
  rw [Metric.tendsto_atTop]; intro r rp
  rcases Metric.tendsto_atTop.mp ((bottcher_large_approx d c).comp (tendsto_iter_atInf d c3 cz))
      (min (1 / 2) (r / 4)) (by bound) with ⟨n, h⟩
  use n; intro k nk; specialize h k nk
  generalize hw : (f' d c)^[k] z = w; generalize hp : s.bottcher c w * w = p
  simp only [hw, hp, Function.comp, Complex.dist_eq, Real.dist_eq] at h ⊢
  clear hp w hw nk n p0 s cz c3 z c
  generalize ha : abs p = a
  generalize hb : ((d ^ k : ℕ) : ℝ)⁻¹ = b
  have a1 : |a - 1| < min (1 / 2) (r / 4) := by
    rw [← ha]; refine lt_of_le_of_lt ?_ h
    rw [← Complex.abs.map_one]; apply Complex.abs.abs_abv_sub_le_abv_sub
  have am : a ∈ ball (1 : ℝ) (1 / 2) := by
    simp only [mem_ball, Real.dist_eq]; exact (lt_min_iff.mp a1).1
  have b0 : 0 ≤ b := by rw [← hb]; bound
  have b1 : b ≤ 1 := by
    rw [← hb]; exact inv_le_one (Nat.one_le_cast.mpr (one_le_pow_of_one_le d_ge_one _))
  have hd : ∀ x, x ∈ ball (1 : ℝ) (1 / 2) →
      HasDerivAt (fun x ↦ x ^ (-b)) (1 * -b * x ^ (-b - 1) + 0 * x ^ (-b) * log x) x := by
    intro x m; apply HasDerivAt.rpow (hasDerivAt_id _) (hasDerivAt_const _ _)
    simp only [mem_ball, Real.dist_eq, id] at m ⊢; linarith [abs_lt.mp m]
  simp only [MulZeroClass.zero_mul, add_zero, one_mul] at hd
  have bound : ∀ x, x ∈ ball (1 : ℝ) (1 / 2) → ‖deriv (fun x ↦ x ^ (-b)) x‖ ≤ 4 := by
    intro x m
    simp only [(hd x m).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg b0]
    simp only [mem_ball, Real.dist_eq, abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add] at m
    norm_num at m
    have x0 : 0 < x := by linarith
    calc b * |x ^ (-b - 1)|
      _ ≤ 1 * |x| ^ (-b - 1) := by bound [Real.abs_rpow_le_abs_rpow]
      _ = (x ^ (b + 1))⁻¹ := by rw [← Real.rpow_neg x0.le, neg_add', one_mul, abs_of_pos x0]
      _ ≤ ((1 / 2 : ℝ) ^ (b + 1))⁻¹ := by bound [m.1.le]
      _ = (2:ℝ) ^ (b + 1) := by rw [one_div, Real.inv_rpow zero_le_two, inv_inv]
      _ ≤ (2:ℝ) ^ (1 + 1 : ℝ) := by bound [Real.rpow_le_rpow_of_exponent_le]
      _ ≤ 4 := by norm_num
  have le := Convex.norm_image_sub_le_of_norm_deriv_le (fun x m ↦ (hd x m).differentiableAt) bound
      (convex_ball _ _) (mem_ball_self (by norm_num)) am
  simp only [Real.norm_eq_abs, Real.one_rpow] at le
  calc |a ^ (-b) - 1|
    _ ≤ 4 * |a - 1| := le
    _ < 4 * (r / 4) := by linarith [(lt_min_iff.mp a1).2]
    _ = r := by ring

/-- For large `c, z`, `s.potential = 1/abs z + o(1/abs z)` -/
theorem potential_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (c4 : 4 ≤ abs c) (cz : abs c ≤ abs z) :
    |(superF d).potential c z - 1 / abs z| ≤ 24 / (↑d * abs z ^ (d - 1) * log (abs z)) := by
  have d0 : 0 < d := d_pos
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have z4 : 4 ≤ abs z := le_trans c4 cz
  have z0 : 0 < abs z := lt_of_lt_of_le (by norm_num) z4
  have z1 : 1 < abs z := lt_of_lt_of_le (by norm_num) z4
  have c3 : 3 ≤ abs c := le_trans (by norm_num) c4
  have l2 : 0 < log (abs z) := Real.log_pos (by linarith)
  set s := superF d
  generalize hb : 24 / (↑d * abs z ^ (d - 1) * log (abs z)) = b
  -- Swap out potential for an iterate approximate
  suffices h : ∀ᶠ n in atTop, |abs ((f' d c)^[n] z) ^ (-((d ^ n : ℕ) : ℝ)⁻¹) - 1 / abs z| ≤ b
  · apply le_of_forall_pos_lt_add; intro e ep
    rcases(h.and (Metric.tendsto_nhds.mp (tendsto_potential d c3 cz) e ep)).exists with ⟨n, h, t⟩
    generalize hw : abs ((f' d c)^[n] z) ^ (-((d ^ n : ℕ) : ℝ)⁻¹) = w; rw [hw] at h t
    rw [Real.dist_eq, abs_sub_comm] at t; rw [add_comm]
    calc |s.potential c z - 1 / abs z|
      _ ≤ |s.potential c z - w| + |w - 1 / abs z| := abs_sub_le _ _ _
      _ < e + _ := add_lt_add_of_lt_of_le t h
  -- iter_approx does the rest
  apply eventually_of_forall
  intro n
  generalize hi : ((d ^ n : ℕ) : ℝ)⁻¹ = i
  have dn0 : 0 < ((d ^ n : ℕ) : ℝ) := Nat.cast_pos.mpr (pow_pos d_pos n)
  have i0 : 0 < i := by rw [← hi]; exact inv_pos.mpr dn0
  have f1 : 1 < abs ((f' d c)^[n] z) :=
    lt_of_lt_of_le (one_lt_mul (one_le_pow_of_one_le one_le_two _) z1) (iter_large d c3 cz n)
  have f0 : 0 < abs ((f' d c)^[n] z) := lt_trans zero_lt_one f1
  have l0 : 0 < log (abs ((f' d c)^[n] z)) := Real.log_pos f1
  have l1 : 0 < log (abs ((f' d c)^[n] z) ^ i) := by rw [Real.log_rpow f0]; bound
  have f1 : 0 < abs ((f' d c)^[n] z) ^ i := Real.rpow_pos_of_pos f0 i
  have h := iter_approx d c3 cz n
  rw [sub_sub, add_comm, ← sub_sub, ← Real.log_pow _ n, ← Nat.cast_pow, ←
    Real.log_div l0.ne' dn0.ne', div_eq_mul_inv, mul_comm, ← Real.log_rpow f0, hi] at h
  generalize hr : 8 / (↑d * abs z ^ (d - 1)) = r; rw [hr] at h
  have r0 : 0 < r := by rw [← hr]; bound
  have r1 : r ≤ 1 := by
    rw [← hr, div_le_one]; swap; bound
    calc ↑d * abs z ^ (d - 1)
      _ ≥ 2 * (4:ℝ) ^ (d - 1) := by bound
      _ ≥ 2 * 4 := by bound [le_self_pow _ (d_minus_one_pos : 0 < d - 1).ne']
      _ = 8 := by norm_num
  set t := closedBall (log (log (abs z))) r
  have yt : log (log (abs ((f' d c)^[n] z) ^ i)) ∈ t := by
    simp only [mem_closedBall, Real.dist_eq, h]
  have bound : ∀ x, x ∈ t → ‖deriv (fun x ↦ exp (-exp x)) x‖ ≤ 3 / log (abs z) := by
    intro x m; simp only [mem_closedBall, Real.dist_eq] at m
    replace m : -x ≤ 1 - log (log (abs z)) := by linarith [(abs_le.mp m).1]
    refine le_trans (deriv_exp_neg_exp_le _) (le_trans (Real.exp_le_exp.mpr m) ?_)
    simp only [Real.exp_sub, Real.exp_log l2]; bound [Real.exp_one_lt_3, l2]
  have m :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ ↦ (hasDerivAt_exp_neg_exp x).differentiableAt) bound (convex_closedBall _ _)
      (mem_closedBall_self r0.le) yt
  simp only [Real.norm_eq_abs] at m
  replace m := le_trans m (mul_le_mul_of_nonneg_left h (by bound))
  simp only [Real.exp_log l1, Real.exp_log l2, Real.exp_neg, Real.exp_log z0, Real.exp_log f1, ←
    Real.rpow_neg f0.le] at m
  rw [one_div]; refine le_trans m (le_of_eq ?_)
  rw [← hr, ← hb]; field_simp [l2.ne', z0.ne']; ring_nf

/-- For large `c`, large `z`'s are postcritical -/
theorem largePost {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z) :
    Postcritical (superF d) c z := by
  have d0 : 0 < d := d_pos
  have d1 : 0 < d-1 := d_minus_one_pos
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have c10 : 10 ≤ abs c := le_trans (by norm_num) (le_trans (Real.add_one_le_exp _) cb)
  have c4 : 4 ≤ abs c := le_trans (by norm_num) c10
  have c5 : 5 ≤ abs c := le_trans (by norm_num) c10
  have c0 : 0 < abs c := by linarith
  have lcb : 48 ≤ log (abs c) := (Real.le_log_iff_exp_le c0).mpr cb
  have lc : 0 < log (abs c) := lt_of_lt_of_le (by norm_num) lcb
  simp only [Postcritical, multibrot_p]
  set s := superF d
  rw [← Real.pow_nat_rpow_nat_inv s.potential_nonneg d0.ne', ←
    Real.pow_nat_rpow_nat_inv (s.potential_nonneg : 0 ≤ s.potential c 0) d0.ne']
  simp only [← s.potential_eqn]; refine Real.rpow_lt_rpow s.potential_nonneg ?_ (by bound)
  generalize hw : f' d c z = w
  have e : f d c z = w := by rw [f, lift_coe', hw]
  simp only [f_0, e]; clear e
  have cw2 : 4 * abs c ≤ abs w := by
    simp only [← hw, f']
    have z1 : 1 ≤ abs z := by linarith
    calc abs (z ^ d + c)
      _ ≥ abs (z ^ d) - abs c := by bound
      _ = abs z ^ d - abs c := by rw [Complex.abs.map_pow]
      _ ≥ abs z ^ 2 - abs c := by bound [pow_le_pow z1 two_le_d]
      _ ≥ abs c ^ 2 - abs c := by bound
      _ = abs c * abs c - abs c := by rw [pow_two]
      _ ≥ 5 * abs c - abs c := by bound
      _ = 4 * abs c := by ring
  have cw : abs c ≤ abs w := le_trans (by linarith) cw2
  have lcw : log (abs c) ≤ log (abs w) := (Real.log_le_log c0 (lt_of_lt_of_le c0 cw)).mpr cw
  have pw := sub_le_iff_le_add.mp (abs_le.mp (potential_approx d c4 cw)).2
  have pc := le_sub_iff_add_le.mp (abs_le.mp (potential_approx d c4 (le_refl _))).1
  refine' lt_of_le_of_lt pw (lt_of_lt_of_le _ pc)
  generalize hkc : 24 / (↑d * abs c ^ (d - 1) * log (abs c)) = kc
  generalize hkw : 24 / (↑d * abs w ^ (d - 1) * log (abs w)) = kw
  rw [neg_add_eq_sub, lt_sub_iff_add_lt, add_comm _ kc, ← add_assoc]
  have kcw : kw ≤ kc := by rw [← hkc, ← hkw]; bound
  have kcc : kc ≤ 1 / (4 * abs c) := by
    rw [← hkc]
    have c1 : 1 ≤ abs c := le_trans (by norm_num) cb
    calc 24 / (↑d * abs c ^ (d - 1) * log (abs c))
      _ ≤ 24 / (2 * abs c * 48) := by bound
      _ = 24 / (48 * 2) / abs c := by rw [mul_comm _ (48 : ℝ), ← mul_assoc, ← div_div]
      _ = 1 / 4 / abs c := by norm_num
      _ = 1 / (4 * abs c) := by rw [div_div]
  calc kc + kw + 1 / abs w
    _ ≤ kc + kc + 1 / (4 * abs c) := by bound
    _ = 2 * kc + 1 / (4 * abs c) := by ring
    _ ≤ 2 * (1 / (4 * abs c)) + 1 / (4 * abs c) := by linarith
    _ = 2 / 4 / abs c + 1 / 4 / abs c := by field_simp
    _ = 3 / 4 / abs c := by ring
    _ < 1 / abs c := (div_lt_div_right c0).mpr (by norm_num)

/-- `s.bottcher = bottcherNear` for large `c,z`.
    This means that `s.bottcher` is given by the infinite product formula from `BottcherNear.lean`
    for large `c,z`. -/
theorem bottcher_eq_bottcherNear_z {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z) :
    (superF d).bottcher c z = bottcherNear (fl (f d) ∞ c) d z⁻¹ := by
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (le_trans (Real.add_one_le_exp _) cb)
  have c0 : 0 < abs c := lt_trans (by norm_num) c16
  have z0 : 0 < abs z := lt_of_lt_of_le c0 cz
  set s := superF d
  set t := closedBall (0 : ℂ) (abs c)⁻¹
  suffices e : EqOn (fun z : ℂ ↦ s.bottcher c (z : 𝕊)⁻¹) (bottcherNear (fl (f d) ∞ c) d) t
  · have z0' : z ≠ 0 := Complex.abs.ne_zero_iff.mp z0.ne'
    convert @e z⁻¹ _; rw [inv_coe (inv_ne_zero z0'), inv_inv]
    simp only [mem_closedBall, Complex.dist_eq, sub_zero, map_inv₀, inv_le_inv z0 c0, cz]
  have a0 : HolomorphicOn I I (fun z : ℂ ↦ s.bottcher c (z : 𝕊)⁻¹) t := by
    intro z m
    refine' (s.bottcher_holomorphicOn _ _).in2.comp (holomorphic_inv.comp holomorphic_coe _)
    simp only [mem_closedBall, Complex.dist_eq, sub_zero] at m
    by_cases z0 : z = 0; simp only [z0, coe_zero, inv_zero']; exact s.post_a c
    rw [inv_coe z0]; apply largePost cb
    rwa [map_inv₀, le_inv c0]; exact Complex.abs.pos z0
  have a1 : HolomorphicOn I I (bottcherNear (fl (f d) ∞ c) d) t := by
    intro z m; apply AnalyticAt.holomorphicAt
    apply bottcherNear_analytic_z (superNearF d c)
    simp only [mem_setOf, mem_closedBall, Complex.dist_eq, sub_zero] at m ⊢
    refine' lt_of_le_of_lt m _
    refine' inv_lt_inv_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _
    exact max_lt c16 (half_lt_self (lt_trans (by norm_num) c16))
  refine' (a0.eq_of_locally_eq a1 (convex_closedBall _ _).isPreconnected _).self_set
  use 0, mem_closedBall_self (by bound)
  have e : ∀ᶠ z in 𝓝 0, bottcherNear (fl (f d) ∞ c) d z = s.bottcherNear c (z : 𝕊)⁻¹ := by
    simp only [Super.bottcherNear, extChartAt_inf_apply, inv_inv, toComplex_coe, inv_inf,
      toComplex_zero, sub_zero, Super.fl, eq_self_iff_true, Filter.eventually_true]
  refine' Filter.EventuallyEq.trans _ (Filter.EventuallyEq.symm e)
  have i : Tendsto (fun z : ℂ ↦ (z : 𝕊)⁻¹) (𝓝 0) (𝓝 ∞) := by
    have h : ContinuousAt (fun z : ℂ ↦ (z : 𝕊)⁻¹) 0 :=
      (RiemannSphere.continuous_inv.comp continuous_coe).continuousAt
    simp only [ContinuousAt, coe_zero, inv_zero'] at h; exact h
  exact i.eventually (s.bottcher_eq_bottcherNear c)

/-- `bottcher' = bottcherNear` for large `c` -/
theorem bottcher_eq_bottcherNear {c : ℂ} (cb : exp 48 ≤ abs c) :
    bottcher' d c = bottcherNear (fl (f d) ∞ c) d c⁻¹ :=
  bottcher_eq_bottcherNear_z cb (le_refl _)

/-- `z⁻¹` is in the `superNearC` region for large `c,z` -/
theorem inv_mem_t {c z : ℂ} (c16 : 16 < abs c) (cz : abs c ≤ abs z) :
    z⁻¹ ∈ {z : ℂ | abs z < (max 16 (abs c / 2))⁻¹} := by
  simp only [mem_setOf, map_inv₀]
  refine' inv_lt_inv_of_lt (lt_of_lt_of_le (by norm_num) (le_max_left _ _)) _
  exact lt_of_lt_of_le (max_lt c16 (half_lt_self (lt_trans (by norm_num) c16))) cz

/-- Terms in the `bottcherNear` product are close to 1 -/
theorem term_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (cb : exp 48 ≤ abs c) (cz : abs c ≤ abs z)
    (n : ℕ) : abs (term (fl (f d) ∞ c) d n z⁻¹ - 1) ≤ 2 * (1 / 2 : ℝ) ^ n * (abs z)⁻¹ := by
  set s := superF d
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (le_trans (Real.add_one_le_exp _) cb)
  have d2 : 2 ≤ (d : ℝ) := le_trans (by norm_num) (Nat.cast_le.mpr two_le_d)
  have z0 : abs z ≠ 0 := (lt_of_lt_of_le (lt_trans (by norm_num) c16) cz).ne'
  have i8 : (abs z)⁻¹ ≤ 1 / 8 := by
    rw [one_div]; apply inv_le_inv_of_le; norm_num
    exact le_trans (by norm_num) (le_trans c16.le cz)
  have i1 : (abs z)⁻¹ ≤ 1 := le_trans i8 (by norm_num)
  simp only [term]
  have wc := iterates_converge (superNearF d c) n (inv_mem_t c16 cz)
  generalize hw : (fl (f d) ∞ c)^[n] z⁻¹ = w; rw [hw] at wc
  replace wc : abs w ≤ (abs z)⁻¹
  · rw [map_inv₀] at wc
    exact le_trans wc (mul_le_of_le_one_left (inv_nonneg.mpr (Complex.abs.nonneg _)) (by bound))
  have cw : abs (c * w ^ d) ≤ (abs z)⁻¹ := by
    simp only [Complex.abs.map_mul, Complex.abs.map_pow]
    calc abs c * abs w ^ d
      _ ≤ abs z * (abs z)⁻¹ ^ d := by bound
      _ ≤ abs z * (abs z)⁻¹ ^ 2 := by bound [pow_le_pow_of_le_one, (two_le_d : 2 ≤ d)]
      _ = (abs z)⁻¹ := by rw [pow_two]; field_simp [z0]
  have cw2 : abs (c * w ^ d) ≤ 1 / 2 := le_trans cw (le_trans i8 (by norm_num))
  simp only [gl_f, gl]; rw [Complex.inv_cpow, ← Complex.cpow_neg]; swap
  · refine (lt_of_le_of_lt (le_abs_self _) (lt_of_le_of_lt ?_ (half_lt_self Real.pi_pos))).ne
    rw [Complex.abs_arg_le_pi_div_two_iff, Complex.add_re, Complex.one_re]
    calc 1 + (c * w ^ d).re
      _ ≥ 1 + -|(c * w ^ d).re| := by bound [neg_abs_le_self]
      _ = 1 - |(c * w ^ d).re| := by ring
      _ ≥ 1 - abs (c * w ^ d) := by bound [Complex.abs_re_le_abs]
      _ ≥ 1 - 1 / 2 := by linarith
      _ ≥ 0 := by norm_num
  · have dn : abs (-(1 / (d ^ (n + 1) : ℂ))) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
      simp only [one_div, Complex.abs.map_neg, map_inv₀, Nat.cast_pow, Complex.abs_of_nat, inv_pow,
        Complex.abs.map_pow]
      bound
    have d1 : abs (-(1 / (d ^ (n + 1) : ℂ))) ≤ 1 := le_trans dn (by bound)
    refine le_trans (pow_small ?_ d1) ?_
    · rw [add_sub_cancel']; exact cw2
    · rw [add_sub_cancel']
      calc 4 * abs (c * w ^ d) * abs (-(1 / (d ^ (n + 1) : ℂ)))
        _ ≤ 4 * (abs z)⁻¹ * (1/2 : ℝ) ^ (n + 1) := by bound
        _ ≤ 2 * (1/2 : ℝ) ^ n * (abs z)⁻¹ := by
          simp only [pow_succ, ←mul_assoc, mul_comm _ (1/2:ℝ)]; norm_num
          simp only [mul_comm _ ((2:ℝ)^n)⁻¹, ←mul_assoc, le_refl]

/-- `s.bottcher c z = z⁻¹ + O(z⁻¹^2)` -/
theorem bottcher_approx_z (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (cb : exp 48 ≤ abs c)
    (cz : abs c ≤ abs z) : abs ((superF d).bottcher c z - z⁻¹) ≤ (16:ℝ) * (abs z)⁻¹ ^ 2 := by
  set s := superF d
  have c16 : 16 < abs c := lt_of_lt_of_le (by norm_num) (le_trans (Real.add_one_le_exp _) cb)
  have i8 : (abs z)⁻¹ ≤ 1 / 8 := by
    rw [one_div]; apply inv_le_inv_of_le; norm_num
    exact le_trans (by norm_num) (le_trans c16.le cz)
  nth_rw 1 [← mul_one z⁻¹]
  simp only [bottcher_eq_bottcherNear_z cb cz, bottcherNear, Complex.abs.map_mul, ← mul_sub_one,
    pow_two, ← mul_assoc, map_inv₀, mul_comm (abs z)⁻¹]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Complex.abs.nonneg _))
  rcases term_prod_exists (superNearF d c) _ (inv_mem_t c16 cz) with ⟨p, h⟩
  rw [h.tprod_eq]; simp only [HasProd] at h
  apply le_of_tendsto' (Filter.Tendsto.comp Complex.continuous_abs.continuousAt (h.sub_const 1))
  clear h; intro A; simp only [Function.comp]
  rw [(by norm_num : (16 : ℝ) = 4 * 4), mul_assoc]
  refine dist_prod_one_le_abs_sum ?_ (by linarith)
  refine le_trans (Finset.sum_le_sum fun n _ ↦ term_approx d cb cz n) ?_
  simp only [mul_comm _ _⁻¹, ← mul_assoc, ← Finset.mul_sum]
  calc (abs z)⁻¹ * 2 * A.sum (fun n ↦ (1/2:ℝ)^n)
    _ ≤ (abs z)⁻¹ * 2 * (1 - 1 / 2)⁻¹ := by bound [partial_geometric_bound]
    _ = (abs z)⁻¹ * 4 := by ring

/-- `bottcher' d c = c⁻¹ + O(c⁻¹^2)` -/
theorem bottcher_approx (d : ℕ) [Fact (2 ≤ d)] {c : ℂ} (cb : exp 48 ≤ abs c) :
    abs (bottcher' d c - c⁻¹) ≤ 16 * (abs c)⁻¹ ^ 2 :=
  bottcher_approx_z d cb (le_refl _)

/-- bottcher is monic at `∞` (has derivative 1) -/
theorem bottcher_hasDerivAt_one : HasDerivAt (fun z : ℂ ↦ bottcher d (↑z)⁻¹) 1 0 := by
  simp only [HasDerivAt, HasDerivAtFilter, bottcher, HasFDerivAtFilter, coe_zero, inv_zero',
    fill_inf, sub_zero, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, mul_one]
  rw [Asymptotics.isLittleO_iff]
  intro k k0; rw [Metric.eventually_nhds_iff]
  refine ⟨min (exp 48)⁻¹ (k / 16), by bound, ?_⟩; intro z le
  simp only [Complex.dist_eq, sub_zero, lt_min_iff] at le; simp only [Complex.norm_eq_abs]
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', fill_inf, sub_zero, Complex.abs.map_zero,
      MulZeroClass.mul_zero, le_refl]
  simp only [inv_coe z0, fill_coe]
  have b : abs (bottcher' d z⁻¹ - z⁻¹⁻¹) ≤ (16:ℝ) * (abs z⁻¹)⁻¹ ^ 2 := bottcher_approx d ?_
  · simp only [inv_inv] at b; apply le_trans b
    simp only [map_inv₀, inv_inv, pow_two, ← mul_assoc]
    refine' mul_le_mul_of_nonneg_right _ (Complex.abs.nonneg _)
    calc 16 * abs z
      _ ≤ 16 * (k / 16) := by linarith [le.2]
      _ = k := by ring
  · rw [map_inv₀, le_inv (Real.exp_pos _) (Complex.abs.pos z0)]; exact le.1.le

/-- bottcher is nonsingular at `∞` -/
theorem bottcher_mfderiv_inf_ne_zero : mfderiv I I (bottcher d) ∞ ≠ 0 := by
  simp only [mfderiv, (bottcherHolomorphic d _ multibrotExt_inf).mdifferentiableAt, if_pos,
    writtenInExtChartAt, bottcher_inf, extChartAt_inf, extChartAt_eq_refl, Function.comp,
    LocalEquiv.refl_coe, id, LocalEquiv.trans_apply, Equiv.toLocalEquiv_apply, invEquiv_apply,
    inv_inf, coeLocalEquiv_symm_apply, toComplex_zero, LocalEquiv.coe_trans_symm,
    LocalEquiv.symm_symm, coeLocalEquiv_apply, Equiv.toLocalEquiv_symm_apply, invEquiv_symm,
    ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  rw [bottcher_hasDerivAt_one.hasFDerivAt.fderiv]
  rw [Ne.def, ContinuousLinearMap.ext_iff, not_forall]; use 1
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    Algebra.id.smul_eq_mul, mul_one, ContinuousLinearMap.zero_apply]
  convert one_ne_zero; exact NeZero.one

/-!
## Injectivity of Böttcher coordinates
-/

/-- `bottcher d` is injective.

    We use induction on potential down 0, expressed using closed sets of pairs.  Intuitively,
    1. Near 0, `bottcher d` is injective since it is noncritical.
    2. The set of potentials with an injectivity counterexample is open.
    3. A limit of counterexamples is either already a counterexample, or shows that `bottcher d`
       is critical at the limit.
    4. But every value is repeated near critical points of analytic functions, so in particular
       smaller values are repeated, which gives us a smaller potential counterexample. -/
theorem bottcher_inj : InjOn (bottcher d) (multibrotExt d) := by
  -- We operate by induction on potential down to 0, expressed using closed sets of pairs.
  -- Preliminaries first:
  by_contra bad
  simp only [InjOn, not_forall, ← Ne.def] at bad
  rcases bad with ⟨x, xm, y, ym, bxy, xy⟩
  generalize hb : potential d x = b
  have b1 : b < 1 := by rwa [← hb, potential_lt_one]
  set u := {c | potential d c ≤ b}
  set t0 := u ×ˢ u
  set t1 := {q : 𝕊 × 𝕊 | bottcher d q.1 = bottcher d q.2 ∧ q ∈ t0}
  set t2 := {q : 𝕊 × 𝕊 | q.1 ≠ q.2 ∧ q ∈ t1}
  have t2ne : t2.Nonempty := by
    refine ⟨⟨x, y⟩, xy, bxy, ?_, ?_⟩
    · simp only [mem_setOf, ← hb, le_refl]
    · simp only [mem_setOf, ← hb, ← abs_bottcher, bxy, le_refl]
  clear x xm y ym bxy xy hb
  have ue : u ⊆ multibrotExt d := by intro c m; rw [← potential_lt_one]; exact lt_of_le_of_lt m b1
  have t01 : t1 ⊆ t0 := inter_subset_right _ _
  have t12 : t2 ⊆ t1 := inter_subset_right _ _
  have uc : IsClosed u := isClosed_le potential_continuous continuous_const
  have t0c : IsClosed t0 := uc.prod uc
  have t1c : IsClosed t1 := by
    rw [isClosed_iff_frequently]; intro ⟨x, y⟩ f
    have m0 : (x, y) ∈ t0 :=
      Filter.Frequently.mem_of_closed (f.mp (eventually_of_forall fun _ m ↦ t01 m)) t0c
    refine ⟨tendsto_nhds_unique_of_frequently_eq ?_ ?_
      (f.mp (eventually_of_forall fun _ m ↦ m.1)), m0⟩
    · exact (bottcherHolomorphic d _ (ue m0.1)).continuousAt.comp continuousAt_fst
    · exact (bottcherHolomorphic d _ (ue m0.2)).continuousAt.comp continuousAt_snd
  have t12' : closure t2 ⊆ t1 := by rw [← t1c.closure_eq]; exact closure_mono t12
  have t2c' : IsCompact (closure t2) := isClosed_closure.isCompact
  have t2ne' : (closure t2).Nonempty := t2ne.closure
  -- Find the smallest potential which (almost) violates injectivity,
  -- and a pair (x,y) which realizes it
  have pc : Continuous fun q : 𝕊 × 𝕊 ↦ potential d q.1 := potential_continuous.comp continuous_fst
  rcases pc.continuousOn.compact_min t2c' t2ne' with ⟨⟨x, y⟩, m2, min⟩
  simp only [isMinOn_iff] at min
  generalize xp : potential d x = p; rw [xp] at min
  have m1 := t12' m2
  have pb : p ≤ b := by rw [← xp]; exact m1.2.1
  have xm : x ∈ multibrotExt d := ue m1.2.1
  have ym : y ∈ multibrotExt d := ue m1.2.2
  have yp : potential d y = p := by rw [← abs_bottcher, ← m1.1, abs_bottcher, xp]
  have p0i : p = 0 → x = ∞ ∧ y = ∞ := by intro p0; rw [p0, potential_eq_zero] at xp yp; use xp, yp
  -- Split into three cases to find a contradiction
  by_cases xy : x ≠ y
  · -- Case 1: If x ≠ y, we can move a bit downwards in potential
    have p0 : p ≠ 0 := by
      contrapose xy; simp only [not_not] at xy ⊢; rcases p0i xy with ⟨xi, yi⟩; rw [xi, yi]
    have f : ∃ᶠ q : ℂ × ℂ in Filter.map
        (fun q : 𝕊 × 𝕊 ↦ (bottcher d q.1, bottcher d q.2)) (𝓝 (x, y)),
        q.1 = q.2 ∧ abs q.1 < p := by
      rw [nhds_prod_eq, ← Filter.prod_map_map_eq, ← (bottcherNontrivial xm).nhds_eq_map_nhds, ←
        (bottcherNontrivial ym).nhds_eq_map_nhds, m1.1, ← nhds_prod_eq]
      apply (continuous_id.prod continuous_id).continuousAt.frequently
      simp only [eq_self_iff_true, true_and_iff, ← yp, ← abs_bottcher]; apply frequently_smaller
      rw [← Complex.abs.ne_zero_iff, abs_bottcher, yp]; exact p0
    simp only [Filter.frequently_map] at f
    rcases(f.and_eventually (Ne.eventually_ne xy)).exists with ⟨⟨v, w⟩, ⟨bvw, pv⟩, vw⟩
    simp only [not_lt, abs_bottcher] at vw bvw pv ⊢
    have pw : potential d w < p := by rwa [← abs_bottcher, ← bvw, abs_bottcher]
    have m : (v, w) ∈ t2 := ⟨vw, bvw, le_trans pv.le pb, le_trans pw.le pb⟩
    contrapose pv; simp only [not_lt]; exact min ⟨v, w⟩ (subset_closure m)
  -- x = y, so we're at a singular point
  simp only [not_not] at xy
  rw [← xy] at m1 m2 p0i; clear xy ym yp y
  have db : mfderiv I I (bottcher d) x = 0 := by
    contrapose m2; simp only [mem_closure_iff_frequently, Filter.not_frequently]
    refine' ((bottcherHolomorphic d _ xm).local_inj m2).mp (eventually_of_forall _)
    intro ⟨x, y⟩ inj ⟨xy, e, _⟩; simp only at xy e inj; exact xy (inj e)
  by_cases p0 : p ≠ 0
  · -- Case 2: At a singular point we're not locally injective,
    -- so we can find a smaller potential value
    rcases not_local_inj_of_mfderiv_zero (bottcherHolomorphic d _ xm) db with ⟨r, ra, rx, e⟩
    simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] at e
    rw [← xp, ← abs_bottcher, Complex.abs.ne_zero_iff] at p0
    have h := frequently_smaller p0
    rw [(bottcherNontrivial xm).nhds_eq_map_nhds, Filter.frequently_map] at h
    have m : ∃ᶠ z in 𝓝 x, potential d z < p ∧ (z, r z) ∈ t2 := by
      refine' h.mp (e.mp (eventually_of_forall fun z e lt ↦ _))
      have zx : z ≠ x := by
        contrapose lt; simp only [not_not, not_lt] at lt ⊢; simp only [lt, le_refl]
      rw [abs_bottcher, abs_bottcher, xp] at lt
      rcases e zx with ⟨rz, e⟩
      refine' ⟨lt, rz.symm, e.symm, le_trans lt.le pb, _⟩
      rw [← abs_bottcher, ← e, abs_bottcher] at lt; exact le_trans lt.le pb
    rcases m.exists with ⟨y, yp, m⟩
    linarith [min _ (subset_closure m)]
  · -- Case 1: x = ∞, which we know is nonsingular
    simp only [not_not] at p0; rw [(p0i p0).1] at db
    exact bottcher_mfderiv_inf_ne_zero db

/-!
## The external ray map, and `bottcherHomeomorph`
-/

lemma ray_exists (d : ℕ) [Fact (2 ≤ d)] :
    ∃ g, HolomorphicOn I I g (bottcher d '' multibrotExt d) ∧
      ∀ z : 𝕊, z ∈ multibrotExt d → g (bottcher d z) = z :=
  global_complex_inverse_fun_open' (bottcherHolomorphic d) bottcher_inj isOpen_multibrotExt

/-- The inverse to `bottcher d`, defining external rays throughout the exterior -/
def ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → 𝕊 :=
  Classical.choose (ray_exists d)

/-- `ray d` is holomorphic on `ball 0 1` -/
theorem rayHolomorphic (d : ℕ) [Fact (2 ≤ d)] : HolomorphicOn I I (ray d) (ball 0 1) := by
  rw [← bottcher_surj d]; exact (Classical.choose_spec (ray_exists d)).1

/-- `ray d` is the left inverse to `bottcher d` -/
theorem ray_bottcher {c : 𝕊} (m : c ∈ multibrotExt d) : ray d (bottcher d c) = c :=
  (Classical.choose_spec (ray_exists d)).2 _ m

/-- `ray d` is the right inverse to `bottcher d` -/
theorem bottcher_ray {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : bottcher d (ray d z) = z := by
  rw [← bottcher_surj d] at m; rcases m with ⟨c, m, cz⟩
  nth_rw 1 [← cz]; rw [ray_bottcher m]; exact cz

/-- `ray d` surjects from `ball 0 1` to the exterior of the Multibrot set -/
theorem ray_surj (d : ℕ) [Fact (2 ≤ d)] : ray d '' ball 0 1 = multibrotExt d := by
  rw [← bottcher_surj d]; apply Set.ext; intro c; simp only [← image_comp, mem_image]; constructor
  · intro ⟨e, m, ec⟩; simp only [Function.comp, ray_bottcher m] at ec; rwa [← ec]
  · intro m; use c, m, ray_bottcher m

/-- `bottcher d` as an (analytic) homeomorphism from `multibrotExt d` to `ball 0 1` -/
def bottcherHomeomorph (d : ℕ) [Fact (2 ≤ d)] : LocalHomeomorph 𝕊 ℂ where
  toFun := bottcher d
  invFun := ray d
  source := multibrotExt d
  target := ball 0 1
  map_source' := by intro c m; simp only [← bottcher_surj d]; exact mem_image_of_mem _ m
  map_target' := by intro z m; simp only [← ray_surj d]; exact mem_image_of_mem _ m
  left_inv' c m := ray_bottcher m
  right_inv' z m := bottcher_ray m
  open_source := isOpen_multibrotExt
  open_target := isOpen_ball
  continuous_toFun := (bottcherHolomorphic d).continuousOn
  continuous_invFun := (rayHolomorphic d).continuousOn
