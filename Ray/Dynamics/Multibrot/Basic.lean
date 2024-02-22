import Ray.AnalyticManifold.RiemannSphere
import Ray.Dynamics.Bottcher

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

open Complex (abs)
open Filter (eventually_of_forall Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall mem_ball_self mem_ball mem_closedBall)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]
lemma two_le_d (d : ℕ) [h : Fact (2 ≤ d)] : 2 ≤ d := h.elim
lemma d_pos (d : ℕ) [Fact (2 ≤ d)] : 0 < d := by linarith [two_le_d d]
lemma d_ne_zero (d : ℕ) [Fact (2 ≤ d)] : d ≠ 0 := (d_pos d).ne'
lemma d_gt_one (d : ℕ) [Fact (2 ≤ d)] : 1 < d := by linarith [two_le_d d]
lemma d_ge_one (d : ℕ) [Fact (2 ≤ d)] : 1 ≤ d := (d_gt_one _).le
lemma d_minus_one_pos (d : ℕ) [Fact (2 ≤ d)] : 0 < d - 1 := by have h := two_le_d d; omega
lemma one_le_d_minus_one (d : ℕ) [Fact (2 ≤ d)] : 1 ≤ d - 1 := by have h := two_le_d d; omega
lemma two_le_cast_d (d : ℕ) [Fact (2 ≤ d)] : (2 : ℝ) ≤ d :=
  le_trans (by norm_num) (Nat.cast_le.mpr (two_le_d d))

-- Teach `bound` about `d`
attribute [bound] two_le_d d_gt_one d_ge_one d_pos two_le_cast_d one_le_d_minus_one
attribute [aesop norm apply (rule_sets [Bound])] d_ne_zero  -- TODO: Make `@[bound]` work for this

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
  simp only [lift_coe', f', zero_pow (d_ne_zero _), zero_add]

theorem f_0 (d : ℕ) [Fact (2 ≤ d)] : f d c 0 = c := by
  simp only [f, ← coe_zero, lift_coe', f', zero_pow (d_ne_zero _), zero_add]

theorem analytic_f' : AnalyticOn ℂ (uncurry (f' d)) univ := fun _ _ ↦
  ((analyticAt_snd _).pow _).add (analyticAt_fst _)

theorem deriv_f' {z : ℂ} : deriv (f' d c) z = d * z ^ (d - 1) := by
  have h : HasDerivAt (f' d c) (d * z ^ (d - 1) + 0) z :=
    (hasDerivAt_pow _ _).add (hasDerivAt_const _ _)
  simp only [add_zero] at h; exact h.deriv

theorem tendsto_f'_atInf (c : ℂ) : Tendsto (uncurry (f' d)) (𝓝 c ×ˢ atInf) atInf := by
  simp only [atInf_basis.tendsto_right_iff, Complex.norm_eq_abs, Set.mem_setOf_eq,
    forall_true_left, uncurry, Metric.eventually_nhds_prod_iff]
  intro r; use 1, zero_lt_one, fun z ↦ max r 0 + abs c + 1 < abs z; constructor
  · refine (eventually_atInf (max r 0 + abs c + 1)).mp (eventually_of_forall fun w h ↦ ?_)
    simp only [Complex.norm_eq_abs] at h; exact h
  · intro e ec z h; simp only [Complex.dist_eq] at ec
    have zz : abs z ≤ abs (z ^ d) := by
      rw [Complex.abs.map_pow]
      refine le_self_pow ?_ (d_ne_zero _)
      exact le_trans (le_add_of_nonneg_left (add_nonneg (le_max_right _ _) (Complex.abs.nonneg _)))
        h.le
    calc abs (f' d e z)
      _ = abs (z ^ d + e) := rfl
      _ = abs (z ^ d + (c + (e - c))) := by ring_nf
      _ ≥ abs (z ^ d) - abs (c + (e - c)) := by bound
      _ ≥ abs (z ^ d) - (abs c + abs (e - c)) := by bound
      _ ≥ abs z - (abs c + 1) := by bound
      _ > max r 0 + abs c + 1 - (abs c + 1) := by bound
      _ = max r 0 := by ring_nf
      _ ≥ r := le_max_left _ _

theorem holomorphicF : Holomorphic II I (uncurry (f d)) :=
  holomorphicLift' analytic_f' tendsto_f'_atInf

theorem writtenInExtChartAt_coe_f {z : ℂ} : writtenInExtChartAt I I (z : 𝕊) (f d c) = f' d c := by
  simp only [writtenInExtChartAt, f, Function.comp, lift_coe', RiemannSphere.extChartAt_coe,
    PartialEquiv.symm_symm, coePartialEquiv_apply, coePartialEquiv_symm_apply, toComplex_coe]

theorem fl_f : fl (f d) ∞ = fun c z : ℂ ↦ z^d / (1 + c * z^d) := by
  funext c z
  simp only [fl, RiemannSphere.extChartAt_inf, Function.comp, invEquiv_apply,
    PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply, PartialEquiv.coe_trans_symm,
    coePartialEquiv_symm_apply, PartialEquiv.symm_symm, coePartialEquiv_apply,
    Equiv.toPartialEquiv_symm_apply, invEquiv_symm, RiemannSphere.inv_inf, toComplex_zero,
    add_zero, sub_zero]
  by_cases z0 : z = 0
  · simp only [z0, coe_zero, inv_zero', f, lift_inf', RiemannSphere.inv_inf, toComplex_zero,
      zero_pow (d_ne_zero _), zero_div]
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
  simp only [if_pos, z0, zero_pow (d_ne_zero _), MulZeroClass.mul_zero, add_zero, inv_one]
  rw [if_neg z0, div_eq_mul_inv _ (_ + _), mul_comm, mul_div_assoc, div_self (pow_ne_zero _ z0),
    mul_one]

theorem analyticAt_gl : AnalyticAt ℂ (gl d c) 0 := by
  apply (analyticAt_const.add (analyticAt_const.mul ((analyticAt_id _ _).pow _))).inv
  simp only [Pi.pow_apply, id_eq, Pi.add_apply, ne_eq, zero_pow (d_ne_zero _), mul_zero, add_zero,
    one_ne_zero, not_false_eq_true]

theorem fl_f' : fl (f d) ∞ = fun c z : ℂ ↦ (z - 0) ^ d • gl d c z := by
  funext c z; simp only [fl_f, gl, sub_zero, Algebra.id.smul_eq_mul, div_eq_mul_inv]

theorem gl_zero : gl d c 0 = 1 := by
  simp only [gl, zero_pow (d_ne_zero _), MulZeroClass.mul_zero]; norm_num

theorem gl_frequently_ne_zero : ∃ᶠ z in 𝓝 0, gl d c z ≠ 0 := by
  refine (analyticAt_gl.continuousAt.eventually_ne ?_).frequently; simp only [gl_zero]
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
  { d2 := two_le_d d
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
    refine le_trans ?_ (pow_le_pow_right (le_max_of_le_left (by norm_num)) (two_le_d d))
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
    { d2 := two_le_d d
      fa0 := (s.fla c).along_snd
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
          (le_trans zb (by norm_num)) (two_le_d d)) ?_
        rw [pow_two]; refine mul_le_mul_of_nonneg_left ?_ (Complex.abs.nonneg _)
        exact le_trans zb (le_trans (by norm_num) cz1)
      gs' := by
        intro z z0 m; simp only [fl_f, div_div_cancel_left' (pow_ne_zero d z0)]
        specialize cz1 m
        have czp : 0 < abs (1 + c * z ^ d) := lt_of_lt_of_le (by norm_num) cz1
        refine le_of_mul_le_mul_right ?_ czp
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
    · simp only [f, lift_coe', OnePoint.coe_ne_infty, IsEmpty.forall_iff]

/-- `0, ∞` are the only critical points of `f` -/
theorem critical_f {z : 𝕊} : Critical (f d c) z ↔ z = 0 ∨ z = ∞ := by
  induction' z using OnePoint.rec with z
  · simp only [(superF d).critical_a, or_true]
  · simp only [Critical, mfderiv, (holomorphicF (c, z)).along_snd.mdifferentiableAt, if_pos,
      ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ, writtenInExtChartAt_coe_f,
      RiemannSphere.extChartAt_coe, coePartialEquiv_symm_apply, toComplex_coe, coe_eq_zero,
      coe_eq_inf_iff, or_false_iff, ← deriv_fderiv, deriv_f', ContinuousLinearMap.ext_iff,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, Algebra.id.smul_eq_mul,
      one_mul, ContinuousLinearMap.zero_apply, mul_eq_zero, Nat.cast_eq_zero, d_ne_zero,
      false_or_iff, pow_eq_zero_iff (d_minus_one_pos d).ne']
    dsimp [TangentSpace]
    simp only [ge_iff_le, mul_eq_zero, Nat.cast_eq_zero, d_ne_zero, tsub_pos_iff_lt,
      pow_eq_zero_iff (d_minus_one_pos d).ne', false_or]
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
    (s.potential_lt_one m) (d_gt_one d)

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
## Exponential lower and upper bounds on iterates
-/

/-- A warmup exponential lower bound on iterates -/
lemma iter_large (d : ℕ) [Fact (2 ≤ d)] (b : ℝ) {c z : ℂ} (b2 : 2 ≤ b) (bz : b ≤ abs z)
    (cz : abs c ≤ abs z) (n : ℕ) : (b-1)^n * abs z ≤ abs ((f' d c)^[n] z) := by
  induction' n with n h
  · simp only [Nat.zero_eq, pow_zero, one_mul, Function.iterate_zero_apply, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (f' d c)^[n] z = w; rw [hw] at h; clear hw
    have z1 : 1 ≤ abs z := le_trans (by norm_num) (le_trans b2 bz)
    have b1 : 1 ≤ b - 1 := by linarith
    have b0 : 0 ≤ b - 1 := by linarith
    have nd : n + 1 ≤ n * d + 1 := by bound
    calc abs (w ^ d + c)
      _ ≥ abs (w ^ d) - abs c := by bound
      _ = abs w ^ d - abs c := by rw [Complex.abs.map_pow]
      _ ≥ ((b-1) ^ n * abs z) ^ d - abs c := by bound
      _ = (b-1) ^ (n*d) * abs z ^ d - abs c := by rw [mul_pow, pow_mul]
      _ ≥ (b-1) ^ (n*d) * abs z ^ 2 - abs c := by bound
      _ = (b-1) ^ (n*d) * (abs z * abs z) - abs c := by rw [pow_two]
      _ ≥ (b-1) ^ (n*d) * (b * abs z) - abs c := by bound
      _ = (b-1) ^ (n*d) * (b-1) * abs z + ((b-1) ^ (n*d) * abs z - abs c) := by ring
      _ = (b-1) ^ (n*d + 1) * abs z + ((b-1) ^ (n * d) * abs z - abs c) := by rw [pow_succ']
      _ ≥ (b-1) ^ (n + 1) * abs z + (1 * abs z - abs c) := by bound
      _ = (b-1) ^ (n + 1) * abs z + (abs z - abs c) := by rw [one_mul]
      _ ≥ (b-1) ^ (n + 1) * abs z := by bound

/-- Ap exponential upper bound on a single iteration -/
lemma iter_small (d : ℕ) (c z : ℂ) : abs (f' d c z) ≤ abs z ^ d + abs c := by
  calc abs (z^d + c)
    _ ≤ abs (z^d) + abs c := by bound
    _ ≤ abs z ^ d + abs c := by rw [Complex.abs.map_pow]

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

/-- Closed Julia sets are not outside radius `max 2 (abs c)` -/
theorem julia_two_lt {z : ℂ} (z2 : 2 < abs z) (cz : abs c ≤ abs z) : (c,↑z) ∈ (superF d).basin := by
  simp only [multibrot_coe, not_le, not_not, (superF d).basin_iff_attracts, Attracts, f_f'_iter,
    tendsto_inf_iff_tendsto_atInf, tendsto_atInf_iff_norm_tendsto_atTop,
    Complex.norm_eq_abs] at z2 ⊢
  apply Filter.tendsto_atTop_mono (iter_large d (abs z) z2.le (le_refl _) cz)
  refine Filter.Tendsto.atTop_mul (by linarith) ?_ tendsto_const_nhds
  apply tendsto_pow_atTop_atTop_of_one_lt; linarith

/-- Closed Julia sets are inside radius `max 2 (abs c)` -/
theorem julia_le_two {z : ℂ} (m : (c,↑z) ∉ (superF d).basin) (cz : abs c ≤ abs z) : abs z ≤ 2 := by
  contrapose m
  simp only [not_le, not_not] at m ⊢
  exact julia_two_lt m cz

/-- `0 < s.potential` at finite values -/
lemma potential_pos {z : ℂ} : 0 < (superF d).potential c z :=
  ((superF d).potential_pos _).mpr RiemannSphere.coe_ne_inf

/-- `s.potential < 1` outside radius `max 2 (abs c)` -/
lemma potential_lt_one_of_two_lt {z : ℂ} (z2 : 2 < abs z) (cz : abs c ≤ abs z) :
    (superF d).potential c z < 1 :=
  (superF d).potential_lt_one (julia_two_lt z2 cz)

/-- The Multibrot set is inside radius 2 -/
theorem multibrot_le_two (m : c ∈ multibrot d) : abs c ≤ 2 := by
  rw [multibrot_basin' (d := d)] at m
  exact julia_le_two m (le_refl _)

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
      have ss1 : 1 ≤ s * (s - 1) ^ k := by bound
      have k2 : k ≤ k * 2 := by linarith
      calc abs (f' d c z)
        _ = abs (z ^ d + c) := rfl
        _ ≥ abs (z ^ d) - abs c := by bound
        _ = abs z ^ d - abs c := by rw [Complex.abs.map_pow]
        _ ≥ (s * (s - 1) ^ k) ^ d - 2 := by bound
        _ ≥ (s * (s - 1) ^ k) ^ 2 - 2 := by bound
        _ = s ^ 2 * (s - 1) ^ (k * 2) - 2 * 1 := by rw [mul_pow, pow_mul, mul_one]
        _ ≥ s ^ 2 * (s - 1) ^ k - s * (s - 1) ^ k := by bound
        _ = s * ((s - 1) ^ k * (s - 1)) := by ring
        _ = s * (s - 1) ^ (k + 1) := by rw [pow_succ']
  simp only [tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs]
  rw [← Filter.tendsto_add_atTop_iff_nat n]; apply Filter.tendsto_atTop_mono b
  refine Filter.Tendsto.mul_atTop (by linarith) tendsto_const_nhds ?_
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
  refine IsCompact.of_isClosed_subset (isCompact_closedBall _ _) ?_ multibrot_subset_closedBall
  rw [multibrot_eq_le_two]; apply isClosed_iInter; intro n
  refine IsClosed.preimage ?_ Metric.isClosed_ball
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
    simp only [← hg, fl, extChartAt_inf, PartialEquiv.trans_apply, Equiv.toPartialEquiv_apply,
      invEquiv_apply, RiemannSphere.inv_inf, coePartialEquiv_symm_apply, toComplex_zero, sub_zero,
      Function.comp, add_zero, PartialEquiv.coe_trans_symm, PartialEquiv.symm_symm,
      coePartialEquiv_apply, Equiv.toPartialEquiv_symm_apply, invEquiv_symm]
    rw [coe_toComplex]
    simp only [Ne.def, inv_eq_inf, ← hz, ← h, inv_inv, ← Function.iterate_succ_apply' (f d c)]
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
  have ae : abs (bottcher' d c) = abs (bottcherNear g d c⁻¹) := by
    apply (pow_left_inj (Complex.abs.nonneg _) (Complex.abs.nonneg _)
      (pow_ne_zero n (d_ne_zero d))).mp
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
  · refine holomorphicAt_fill_inf ?_ bottcher_tendsto_zero
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
      refine eventually_of_forall fun c ↦ ?_; rw [← abs_bottcher]
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
    refine IsClopen.eq_univ ?_ ⟨c, m, h⟩; constructor
    · rw [isClosed_iff_frequently]; intro x e; by_contra xt
      have pb : potential d x = abs b := by
        apply tendsto_nhds_unique_of_frequently_eq potential_continuous.continuousAt
          continuousAt_const
        refine e.mp (eventually_of_forall ?_); intro z ⟨_, h⟩; rw [← h.self_of_nhds, abs_bottcher]
      rw [← pb, potential_lt_one] at b1
      have e' : ∃ᶠ y in 𝓝[{x}ᶜ] x, y ∈ t := by
        simp only [frequently_nhdsWithin_iff, mem_compl_singleton_iff]
        refine e.mp (eventually_of_forall fun z zt ↦ ⟨zt, ?_⟩)
        contrapose xt; simp only [not_not] at xt ⊢; rwa [← xt]
      contrapose xt; simp only [not_not]; use b1
      cases' HolomorphicAt.eventually_eq_or_eventually_ne (bottcherHolomorphic d _ b1)
        holomorphicAt_const with h h
      use h; contrapose h; simp only [Filter.not_eventually, not_not] at h ⊢
      exact e'.mp (eventually_of_forall fun y yt ↦ yt.2.self_of_nhds)
    · rw [isOpen_iff_eventually]; intro e ⟨m, h⟩
      apply (isOpen_multibrotExt.eventually_mem m).mp
      apply (eventually_eventually_nhds.mpr h).mp
      exact eventually_of_forall fun f h m ↦ ⟨m, h⟩
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
    refine IsPreconnected.relative_clopen (convex_ball _ _).isPreconnected ?_ ?_ ?_
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
        refine lt.mp (eventually_of_forall fun y lt m ↦ ?_)
        rcases m with ⟨c, _, cy⟩; rw [← cy]; rw [← cy, abs_bottcher] at lt
        exact ⟨c, lt.le, rfl⟩
      apply image_subset _ ts; rw [IsClosed.closure_eq] at mt; exact mt
      apply IsCompact.isClosed; apply IsCompact.image_of_continuousOn ct
      refine ContinuousOn.mono ?_ ts; exact (bottcherHolomorphic d).continuousOn

/-!
### Ineffective approximations
-/

/-- `s.bottcher c z ~ 1/z` for large `z` -/
theorem bottcher_large_approx (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).bottcher c z * z) atInf (𝓝 1) := by
  set s := superF d
  have e : ∀ᶠ z : ℂ in atInf, s.bottcher c z * z = s.bottcherNear c z * z := by
    suffices e : ∀ᶠ z : ℂ in atInf, s.bottcher c z = s.bottcherNear c z by
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
  simp only [Super.bottcherNear, extChartAt_inf, PartialEquiv.trans_apply,
    coePartialEquiv_symm_apply, Equiv.toPartialEquiv_apply, invEquiv_apply, RiemannSphere.inv_inf,
    toComplex_zero, sub_zero, inv_coe z0, toComplex_coe]
  exact h

/-- `s.potential c z ~ 1/abs z` for large `z` -/
theorem potential_tendsto (d : ℕ) [Fact (2 ≤ d)] (c : ℂ) :
    Tendsto (fun z : ℂ ↦ (superF d).potential c z * abs z) atInf (𝓝 1) := by
  set s := superF d
  simp only [← s.abs_bottcher, ← Complex.abs.map_mul, ← Complex.abs.map_one]
  exact Complex.continuous_abs.continuousAt.tendsto.comp (bottcher_large_approx d c)
