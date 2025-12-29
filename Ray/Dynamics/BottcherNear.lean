module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Ray.Dynamics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Cases
import Mathlib.Topology.Basic
import Ray.Analytic.Analytic
import Ray.Analytic.Products
import Ray.Hartogs.Hartogs
import Ray.Misc.Bound
import Ray.Misc.Bounds
import Ray.Misc.Pow
import Ray.Misc.Topology

/-!
## Böttcher map near a superattracting fixpoint

We define superattracting fixed points at `0` of a parameterized analytic map `f : ℂ → ℂ → ℂ`
(namely a fixed point of order `d ≥ 2`).  Near the fixpoint, Böttcher coordinates `bottcherNear`
conjugate `f c` to `z ^ d`:

  `bottcherNear c (f c z) = bottcherNear c z ^ d`

This file defines `bottcherNear` locally near `0` using the explicit infinite product formula.
Later in `Potential.lean` we lift to 1D complex manifolds, and `Grow.lean`, `Ray.lean`, and
`Bottcher.lean` analytically continue the map to all postcritical points.

One wart: we require not only that `f c` has a zero of order `d ≥ 2`, but also that `f c` is
"monic": that the leading coefficient of the Taylor series is `1`.  This slightly simplifies the
formulas, but is probably better to remove.
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open Set
open scoped NNReal Topology
noncomputable section

section Bottcher

-- All information for a monic superattracting fixed point at the origin
variable {f : ℂ → ℂ}
variable {d : ℕ}
variable {z : ℂ}
variable {t : Set ℂ}
variable {a b : ℝ}

-- Facts about d
public lemma SuperAt.d0 (s : SuperAt f d) : d ≠ 0 := by have h := s.d2; omega
public lemma SuperAt.dp (s : SuperAt f d) : 0 < d := lt_of_lt_of_le two_pos s.d2
public lemma SuperAt.drp (s : SuperAt f d) : 0 < (d : ℝ) := Nat.cast_pos.mpr s.dp
public lemma SuperAt.drz (s : SuperAt f d) : (d : ℝ) ≠ 0 := s.drp.ne'
public lemma SuperAt.dz (s : SuperAt f d) : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.dp.ne'
public lemma SuperAt.dr2 (s : SuperAt f d) : 2 ≤ (d : ℝ) :=
  le_trans (by norm_num) (Nat.cast_le.mpr s.d2)

-- Teach `bound` that `0 < d` and `2 ≤ d`
attribute [bound_forward] SuperAt.d2 SuperAt.dp SuperAt.dr2 SuperNear.toSuperAt SuperNear.b0
  SuperNear.b1

-- More basic inequalities
@[bound_forward] lemma SuperNear.a0 (s : SuperNear f d t a b) : 0 ≤ a := by
  simpa only [norm_zero] using s.t2 s.t0

/-- `c` is nonnegative -/
@[bound] public lemma SuperNear.c0 (s : SuperNear f d t a b) : 0 ≤ s.c := by
  simp only [SuperNear.c]
  bound
@[bound_forward, bound] public lemma SuperNear.c1 (s : SuperNear f d t a b) : s.c < 1 := s.c1'
@[bound] public lemma SuperNear.c_le_one (s : SuperNear f d t a b) : s.c ≤ 1 := by bound

/-- g 0 = 1 -/
theorem g0 {f : ℂ → ℂ} {d : ℕ} : g f d 0 = 1 := by simp only [g, if_true]

/-- Asymptotic bound on `f` based on the order `d` zero -/
theorem SuperAt.approx (s : SuperAt f d) : (fun z ↦ f z - z ^ d) =o[𝓝 0] fun z ↦ z ^ d := by
  have a := s.fa0.leading_approx
  simp only [s.fd, s.fc, sub_zero, smul_eq_mul, mul_one] at a
  exact a

/-- `f 0 = 0` -/
public theorem SuperAt.f0 (s : SuperAt f d) : f 0 = 0 :=
  haveI p : orderAt f 0 > 0 := by simp [s.fd, s.dp]
  s.fa0.zero_of_order_pos p

/-- `f = z^d g` -/
theorem SuperAt.fg (s : SuperAt f d) (z : ℂ) : f z = z ^ d * g f d z := by
  by_cases z0 : z = 0
  · simp only [z0, zero_pow s.d0, s.f0, MulZeroClass.zero_mul]
  · simp only [g, z0, if_false]; field_simp [z0]

/-- `g` is analytic where `f` is -/
theorem SuperAt.ga_of_fa (s : SuperAt f d) {c : ℂ} (fa : AnalyticAt ℂ f c) :
    AnalyticAt ℂ (g f d) c := by
  rcases fa.exists_ball_analyticOnNhd with ⟨r, rp, fa⟩
  have o : IsOpen (ball c r) := isOpen_ball
  generalize ht : ball c r = t
  rw [ht] at fa o
  suffices h : AnalyticOnNhd ℂ (g f d) t by rw [← ht] at h; exact h _ (mem_ball_self rp)
  have ga : DifferentiableOn ℂ (g f d) (t \ {0}) := by
    have e : ∀ z : ℂ, z ∈ t \ {0} → g f d z = f z / z ^ d := by
      intro z zs; simp only [Set.mem_diff, Set.mem_singleton_iff] at zs
      simp only [g, zs.2, if_false]
    rw [differentiableOn_congr e]
    apply DifferentiableOn.div (fa.mono diff_subset).differentiableOn
    exact (Differentiable.pow differentiable_id _).differentiableOn
    intro z zs; exact pow_ne_zero _ (Set.mem_diff_singleton.mp zs).2
  rw [Complex.analyticOnNhd_iff_differentiableOn o]
  by_cases t0 : (0 : ℂ) ∉ t; · rw [Set.diff_singleton_eq_self t0] at ga; exact ga
  simp only [Set.not_notMem] at t0
  have gc : ContinuousAt (g f d) 0 := by
    rw [Metric.continuousAt_iff]; intro e ep
    rcases Metric.eventually_nhds_iff.mp
        (Asymptotics.isBigOWith_iff.mp (s.approx.forall_isBigOWith (by linarith : e / 2 > 0))) with
      ⟨t, tp, h⟩
    use t, tp; intro z zs; specialize h zs
    simp only [g, Complex.dist_eq]
    by_cases z0 : z = 0; · simp only [z0, sub_self, norm_zero]; exact ep
    simp only [z0, if_false, if_true]
    calc ‖f z / z ^ d - 1‖
      _ = ‖f z * (z ^ d)⁻¹ - 1‖ := by rw [div_eq_mul_inv]
      _ = ‖(f z - z ^ d) * (z ^ d)⁻¹‖ := by
        rw [mul_sub_right_distrib, mul_inv_cancel₀ (pow_ne_zero d z0)]
      _ = ‖f z - z ^ d‖ * ‖z ^ d‖⁻¹ := by rw [norm_mul, norm_inv]
      _ ≤ e / 2 * ‖z ^ d‖ * ‖z ^ d‖⁻¹ := by bound
      _ = e / 2 * (‖z ^ d‖ * ‖z ^ d‖⁻¹) := by ring
      _ ≤ e / 2 * 1 := by bound
      _ = e / 2 := by ring
      _ < e := half_lt_self ep
  exact (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (o.mem_nhds t0)).mp ⟨ga, gc⟩

/-- `g` is analytic -/
theorem SuperNear.ga (s : SuperNear f d t a b) : AnalyticOnNhd ℂ (g f d) t := fun z m ↦
  s.ga_of_fa (s.fa z m)

/-- `SuperAt → SuperNear`, manual radius version: if we know a ball where `f` is analytic and
    the resulting `g` is small, then `SuperAt` becomes `SuperNear` -/
theorem SuperAt.super_on_ball (s : SuperAt f d) {r : ℝ} (rp : 0 < r) (r2 : r ≤ a) (a0 : 0 < a)
    (a1 : a < 1) (b0 : 0 ≤ b) (b1 : b < 1) (c1 : a * (1 + b) < 1)
    (fa : AnalyticOnNhd ℂ f (ball 0 r)) (gs : ∀ {z : ℂ}, ‖z‖ < r → ‖g f d z - 1‖ < b) :
    SuperNear f d (ball 0 r) a b :=
  haveI gs : ∀ {z : ℂ}, z ≠ 0 → z ∈ ball (0 : ℂ) r → ‖f z / z ^ d - 1‖ ≤ b := by
    intro z z0 zs
    simp only [mem_ball_zero_iff] at zs
    specialize gs zs
    simp only [g, z0, if_false] at gs
    exact gs.le
  { d2 := s.d2
    fa0 := s.fa0
    fd := s.fd
    fc := s.fc
    o := isOpen_ball
    t0 := mem_ball_self rp
    gs' := fun z0 ↦ gs z0
    a1 := a1
    b0 := b0
    b1 := b1
    c1' := c1
    fa := fa
    t2 := by
      intro z zs
      simp only [mem_ball_zero_iff] at zs
      exact le_trans zs.le r2
    ft := by
      intro z zs; simp only [mem_ball_zero_iff] at zs gs ⊢
      by_cases z0 : z = 0; · simp only [z0, s.f0, rp, norm_zero]
      by_cases f0 : f z = 0
      · simp only [f0, norm_zero, rp]
      · calc ‖f z‖
          _ = ‖f z / z ^ d‖ * ‖z‖ ^ d := by
            rw [← norm_pow, ← norm_mul, div_mul_cancel₀ _ (pow_ne_zero d z0)]
          _ < ‖f z / z ^ d‖ * r ^ d := by
            apply mul_lt_mul_of_pos_left (by bound)
            simp only [Complex.norm_div, norm_pow]
            positivity
          _ = ‖f z / z ^ d - 1 + 1‖ * r ^ d := by
            simp only [Complex.norm_div, norm_pow, sub_add_cancel]
          _ ≤ (‖f z / z ^ d - 1‖ + ‖(1 : ℂ)‖) * r ^ d := by bound
          _ ≤ (b + ‖(1 : ℂ)‖) * r ^ d := by bound [gs z0 zs]
          _ ≤ (1 + b) * r ^ (d - 1) * r := by
            simp only [mul_assoc, ← pow_succ, Nat.sub_add_cancel (le_trans one_le_two s.d2), norm_one,
              add_comm b, le_refl]
          _ ≤ (1 + b) * a ^ (d - 1) * r := by bound
          _ ≤ (1 + b) * a ^ (2 - 1) * r := by bound
          _ = a * (1 + b) * r := by ring
          _ ≤ r := by bound }

/-- `SuperAt → SuperNear`, automatic radius version: given `SuperAt`, we can find a ball where the
    smallness conditions needed for `SuperNear` hold. -/
public theorem SuperAt.superNear (s : SuperAt f d) : ∃ t, SuperNear f d t (1 / 2) (1 / 4) := by
  rcases s.fa0.exists_ball_analyticOnNhd with ⟨r0, r0p, fa⟩
  rcases Metric.continuousAt_iff.mp (s.ga_of_fa (fa 0 (mem_ball_self r0p))).continuousAt (1 / 4)
      (by norm_num) with
    ⟨r1, r1p, gs⟩
  set r := min r0 (min r1 (1 / 2))
  use ball 0 r
  have rp : 0 < r := by bound
  have r2 : r ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have rr1 : r ≤ r1 := le_trans (min_le_right r0 _) (min_le_left r1 _)
  simp only [g0, dist_zero_right, Complex.dist_eq] at gs
  exact s.super_on_ball rp r2 (b := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fa.mono (Metric.ball_subset_ball (min_le_left r0 _))) (fun {z} zr ↦
    gs (lt_of_lt_of_le zr rr1))

/-- `g` is small near 0 -/
theorem SuperNear.gs (s : SuperNear f d t a b) {z : ℂ} (zt : z ∈ t) : ‖g f d z - 1‖ ≤ b := by
  by_cases z0 : z = 0
  · simp only [z0, g0, sub_self, norm_zero, s.b0]
  · simp only [g, z0, if_false, s.gs' z0 zt]

/-- `g` is nonzero -/
theorem SuperNear.g_ne_zero (s : SuperNear f d t a b) {z : ℂ} (zt : z ∈ t) : g f d z ≠ 0 := by
  have h := s.gs zt; contrapose h; simp only [h]; norm_num [s.b1]

/-- `f` is zero only at zero -/
theorem SuperNear.f_ne_zero (s : SuperNear f d t a b) {z : ℂ} (zt : z ∈ t) (z0 : z ≠ 0) :
    f z ≠ 0 := by
  simp only [s.fg, mul_ne_zero (pow_ne_zero _ z0) (s.g_ne_zero zt), Ne, not_false_iff]

/-!
## The infinite product

To prove Bottcher's theorem for a monic, superattracting fixpoint, we start with

   `f z = z^d * g z`
   `g 0 = 1`

Ignoring multiple values when taking `d`th roots, we can derive the infinite product

  `(E n z)^(d^n) = f^[n] z`
  `E n z = (f^[n] z)^(1/d^n)`
  `E n z = (f (f^[n-1] z))^(1/d^n)`
  `E n z = (f ((E (n-1) z)^(d^(n-1))))^(1/d^n)`
  `E n z = ((E (n-1) z)^(d^n) * g ((E (n-1) z)^(d^(n-1))))^(1/d^n)`
  `E n z = E (n-1) z * (g ((E (n-1) z)^(d^(n-1))))^(1/d^n)`
  `E n z = E (n-1) z * (g (f^[n-1] z))^(1/d^n)`
  `E n z = z * prod_{1 < k ≤ n} (g (f^[k-1] z))^(1/d^k)`
-/

/-- `^d` shifts `term (n+1)` to `term n`:

    `(term n z)^d = (g (f^[n] z) ^ 1/d^(n+1))^d`
    `             = (g (f^[n-1] (f z)) ^ 1/d^n)`
    `             = term (n-1) (f z)` -/
theorem term_eqn (s : SuperNear f d t a b) : ∀ n, term f d n (f z) = term f d (n + 1) z ^ d := by
  intro n
  simp only [term, ← Function.iterate_succ_apply, pow_mul_nat, div_mul, pow_succ' _ (n + 1),
    mul_div_cancel_left₀ _ s.dz, Nat.succ_eq_add_one, Nat.cast_mul]

/-- The analogue of `term_eqn (-1)`:

    `(z * term 0 z)^d = (z * g z ^ 1/d)^d`
    `                 = z^d * g z`
    `                 = f z` -/
theorem term_base (s : SuperNear f d t a b) : f z = (z * term f d 0 z) ^ d := by
  rw [term]; simp only [Function.iterate_zero, id, one_div]
  rw [mul_pow, pow_mul_nat, zero_add, pow_one, inv_mul_cancel₀]
  · rw [s.fg]; simp only [Complex.cpow_one]
  · simp only [Ne, Nat.cast_eq_zero]
    have := s.d2
    omega

/-- `abs (f z) = abs (z^d * g z) ≤ c * (abs z)^d ≤ c * abs z` -/
theorem f_converges (s : SuperNear f d t a b) : z ∈ t → ‖f z‖ ≤ s.c * ‖z‖ := by
  intro zt
  simp only [s.fg, Complex.norm_mul, norm_pow]
  have gs : ‖g f d z‖ ≤ 1 + b := by
    calc ‖g f d z‖
      _ = ‖g f d z - 1 + 1‖ := by ring_nf
      _ ≤ ‖g f d z - 1‖ + ‖(1 : ℂ)‖ := by bound
      _ ≤ b + ‖(1 : ℂ)‖ := by linarith [s.gs zt]
      _ ≤ (1 + b) := by simp only [norm_one, add_comm, le_refl]
  have az1 : ‖z‖ ≤ 1 := le_trans (s.t2 zt) s.a1.le
  calc ‖z‖ ^ d * ‖g f d z‖
    _ ≤ ‖z‖ ^ 2 * (1 + b) := by bound
    _ = ‖z‖ * ‖z‖ * (1 + b) := by ring_nf
    _ ≤ a * ‖z‖ * (1 + b) := by bound [s.t2 zt]
    _ = a * (1 + b) * ‖z‖ := by ring

/-- Iterating f remains in t -/
theorem SuperNear.mapsTo (s : SuperNear f d t a b) (n : ℕ) : MapsTo f^[n] t t := by
  induction' n with n h; simp only [Set.mapsTo_id, Function.iterate_zero]
  rw [Function.iterate_succ']; exact s.ft.comp h

/-- `‖f^[n] z‖ ≤ s.c ^ n * ‖z‖` -/
public theorem iterates_converge (s : SuperNear f d t a b) :
    ∀ n, z ∈ t → ‖f^[n] z‖ ≤ s.c ^ n * ‖z‖ := by
  intro n zt
  induction' n with n nh
  · simp only [Function.iterate_zero, id, pow_zero, one_mul, le_refl]
  · rw [Function.iterate_succ']
    trans s.c * ‖f^[n] z‖
    · exact f_converges s (s.mapsTo n zt)
    · calc s.c * ‖f^[n] z‖
        _ ≤ s.c * (s.c ^ n * ‖z‖) := by bound
        _ = s.c * s.c ^ n * ‖z‖ := by ring
        _ = s.c ^ (n + 1) * ‖z‖ := by rw [← pow_succ']
        _ = s.c ^ n.succ * ‖z‖ := rfl

/-- Iterates are analytic -/
theorem iterates_analytic (s : SuperNear f d t a b) : ∀ n, AnalyticOnNhd ℂ f^[n] t := by
  intro n; induction' n with n h
  · simp only [Function.iterate_zero]
    exact analyticOnNhd_id
  · rw [Function.iterate_succ']
    intro z zt
    exact (s.fa _ (s.mapsTo n zt)).comp (h z zt)

/-- `term` is analytic close to 0 -/
theorem term_analytic (s : SuperNear f d t a b) : ∀ n, AnalyticOnNhd ℂ (term f d n) t := by
  intro n z zt
  refine AnalyticAt.cpow ?_ analyticAt_const ?_
  · exact (s.ga _ (s.mapsTo n zt)).comp (iterates_analytic s n z zt)
  · exact mem_slitPlane_of_near_one (lt_of_le_of_lt (s.gs (s.mapsTo n zt)) s.b1)

@[bound] public lemma SuperNear.kt_nonneg (s : SuperNear f d t a b) : 0 ≤ s.kt := by
  unfold kt; bound

/-- term converges to 1 exponentially: `‖term s n z - 1‖ = O((1 / 2) ^ n)` -/
theorem term_converges (s : SuperNear f d t a b) (n : ℕ) (zt : z ∈ t) :
    ‖term f d n z - 1‖ ≤ s.kt * (2⁻¹ : ℝ) ^ n := by
  rw [term]
  trans psg b 2⁻¹ * ‖g f d (f^[n] z) - 1‖ * ‖(1 / (d ^ (n + 1) : ℕ) : ℂ)‖
  · refine pow_small_general ?_ ?_ s.b1
    · exact s.gs (s.mapsTo n zt)
    · simp only [Nat.cast_pow, one_div, norm_inv, norm_pow, RCLike.norm_natCast]
      calc (d ^ (n + 1) : ℝ)⁻¹
        _ ≤ (2 ^ (n + 1))⁻¹ := by bound
        _ ≤ 2⁻¹ := by bound
  · simp only [Nat.cast_pow, one_div, ← div_eq_mul_inv, norm_inv, norm_pow, norm_natCast, inv_pow]
    calc psg b 2⁻¹ * ‖g f d (f^[n] z) - 1‖ / d ^ (n + 1)
      _ ≤ psg b 2⁻¹ * b / 2 ^ (n + 1) := by bound [s.gs (s.mapsTo n zt)]
      _ = s.kt / 2 ^ n := by simp only [SuperNear.kt, pow_succ']; ring

/-- `term` is nonzero, sufficiently close to 0 -/
theorem term_nonzero (s : SuperNear f d t a b) : ∀ n, z ∈ t → term f d n z ≠ 0 := by
  intro n zt
  simp [term, s.g_ne_zero (s.mapsTo n zt)]

/-- The `term` product exists and is analytic -/
theorem term_prod (s : SuperNear f d t a b) :
    ProdExistsOn (term f d) t ∧ AnalyticOnNhd ℂ (tprodOn (term f d)) t ∧
      ∀ z ∈ t, tprodOn (term f d) z ≠ 0 := by
  have a0 : 0 ≤ (2⁻¹ : ℝ) := by norm_num
  obtain ⟨p, a, nz⟩ := fast_products_converge_eventually' s.o a0 (by linarith) (term_analytic s)
    (.of_forall fun n z zt ↦ term_converges s n zt)
  exact ⟨p, a, fun z zt ↦ nz z zt (fun n ↦ term_nonzero s n zt)⟩

/-- The `term` product exists -/
public theorem term_prod_exists (s : SuperNear f d t a b) : ProdExistsOn (term f d) t :=
  (term_prod s).1

/-- The `term` product is analytic in `z` -/
theorem term_prod_analytic_z (s : SuperNear f d t a b) : AnalyticOnNhd ℂ (tprodOn (term f d)) t :=
  (term_prod s).2.1

/-- The `term` product is nonzero -/
theorem term_prod_ne_zero (s : SuperNear f d t a b) (zt : z ∈ t) : tprodOn (term f d) z ≠ 0 :=
  (term_prod s).2.2 _ zt

/-- `bottcherNear` satisfies `b (f z) = (b z)^d` near 0 -/
public theorem bottcherNear_eqn (s : SuperNear f d t a b) (zt : z ∈ t) :
    bottcherNear f d (f z) = bottcherNear f d z ^ d := by
  simp_rw [bottcherNear]
  have pe := (term_prod_exists s) z zt
  simp only [mul_pow, product_pow' pe]
  have pe : ProdExists fun n ↦ term f d n z ^ d := by
    rcases pe with ⟨g, hg⟩; exact ⟨_, product_pow d hg⟩
  simp only [product_split pe, ← term_eqn s, ← mul_assoc, ← mul_pow, ← term_base s]

/-- `bottcherNear_eqn`, iterated -/
public theorem bottcherNear_eqn_iter (s : SuperNear f d t a b) (zt : z ∈ t) (n : ℕ) :
    bottcherNear f d (f^[n] z) = bottcherNear f d z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero, id, pow_zero, pow_one]
  simp only [Function.comp, Function.iterate_succ', pow_succ, pow_mul,
    bottcherNear_eqn s (s.mapsTo n zt), h]

/-- `f^[n] 0 = 0` -/
theorem iterates_at_zero (s : SuperNear f d t a b) : ∀ n, f^[n] 0 = 0 := by
  intro n; induction' n with n h; simp only [Function.iterate_zero, id]
  simp only [Function.iterate_succ', Function.comp_apply, h, s.f0]

/-- `term s n 0 = 1` -/
theorem term_at_zero (s : SuperNear f d t a b) (n : ℕ) : term f d n 0 = 1 := by
  simp only [term, iterates_at_zero s, g0, Complex.one_cpow]

/-- `prod (term s _ 0) = 1` -/
theorem term_prod_at_zero (s : SuperNear f d t a b) : tprodOn (term f d) 0 = 1 := by
  simp_rw [tprodOn, term_at_zero s, tprod_one]

/-- `bottcherNear' 0 = 1` (so in particular `bottcherNear` is a local isomorphism) -/
public theorem bottcherNear_monic (s : SuperNear f d t a b) :
    HasDerivAt (bottcherNear f d) 1 0 := by
  have dz : HasDerivAt (fun z : ℂ ↦ z) 1 0 := hasDerivAt_id 0
  have db := HasDerivAt.mul dz (term_prod_analytic_z s 0 s.t0).differentiableAt.hasDerivAt
  simp only [one_mul, MulZeroClass.zero_mul, add_zero] at db
  rw [term_prod_at_zero s] at db; exact db

/-- `bottcherNear 0 = 0` -/
@[simp] public lemma bottcherNear_zero : bottcherNear f d 0 = 0 := by
  simp only [bottcherNear, MulZeroClass.zero_mul]

/-- `z ≠ 0 → bottcherNear z ≠ 0` -/
public theorem bottcherNear_ne_zero (s : SuperNear f d t a b) :
    z ∈ t → z ≠ 0 → bottcherNear f d z ≠ 0 :=
  fun zt z0 ↦ mul_ne_zero z0 (term_prod_ne_zero s zt)

/-- `bottcherNear` is analytic in `z` -/
public theorem bottcherNear_analytic_z (s : SuperNear f d t a b) :
    AnalyticOnNhd ℂ (bottcherNear f d) t :=
  analyticOnNhd_id.mul (term_prod_analytic_z s)

/-- `f^[n] z → 0` -/
public theorem iterates_tendsto (s : SuperNear f d t a b) (zt : z ∈ t) :
    Tendsto (fun n ↦ f^[n] z) atTop (𝓝 0) := by
  by_cases z0 : z = 0; simp only [z0, iterates_at_zero s, tendsto_const_nhds]
  rw [Metric.tendsto_atTop]; intro e ep
  simp only [Complex.dist_eq, sub_zero]
  have xp : e / ‖z‖ > 0 := div_pos ep (norm_pos_iff.mpr z0)
  rcases exists_pow_lt_of_lt_one xp s.c1 with ⟨N, Nb⟩
  simp only [lt_div_iff₀ (norm_pos_iff.mpr z0)] at Nb
  use N; intro n nN
  refine lt_of_le_of_lt (iterates_converge s n zt) (lt_of_le_of_lt ?_ Nb)
  bound

/-- `bottcherNear < 1` -/
public theorem bottcherNear_lt_one (s : SuperNear f d t a b) (zt : z ∈ t) :
    ‖bottcherNear f d z‖ < 1 := by
  rcases Metric.continuousAt_iff.mp (bottcherNear_analytic_z s _ s.t0).continuousAt 1 zero_lt_one
    with ⟨r, rp, rs⟩
  simp only [Complex.dist_eq, sub_zero, bottcherNear_zero] at rs
  have b' : ∀ᶠ n in atTop, ‖bottcherNear f d (f^[n] z)‖ < 1 := by
    refine (Metric.tendsto_nhds.mp (iterates_tendsto s zt) r rp).mp (.of_forall fun n h ↦ ?_)
    rw [Complex.dist_eq, sub_zero] at h; exact rs h
  rcases b'.exists with ⟨n, b⟩
  contrapose b; simp only [not_lt] at b ⊢
  simp only [bottcherNear_eqn_iter s zt n, norm_pow, one_le_pow₀ b]

/-- Linear bound on `bottcherNear` -/
public theorem bottcherNear_le (s : SuperNear f d t a b) (zt : z ∈ t) :
    ‖bottcherNear f d z‖ ≤ s.k * ‖z‖ := by
  simp only [bottcherNear, norm_mul]; rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases term_prod_exists s _ zt with ⟨p, h⟩; rw [h.tprod_eq]; simp only [HasProd] at h
  apply le_of_tendsto' (Filter.Tendsto.comp continuous_norm.continuousAt h)
  intro A
  clear h
  simp only [Function.comp, norm_prod]
  have tb : ∀ n, ‖term f d n z‖ ≤ 1 + s.kt * (1 / 2 : ℝ) ^ n := by
    intro n
    calc ‖term f d n z‖
      _ = ‖1 + (term f d n z - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖term f d n z - 1‖ := by bound
      _ = 1 + ‖term f d n z - 1‖ := by norm_num
      _ ≤ 1 + s.kt * (1 / 2 : ℝ) ^ n := by bound [term_converges s n zt]
  have p : ∀ n : ℕ, 0 < (1 : ℝ) + s.kt * (1 / 2 : ℝ) ^ n :=
    fun _ ↦ by apply add_pos_of_pos_of_nonneg <;> bound
  have lb : ∀ n : ℕ, Real.log ((1 : ℝ) + s.kt * (1 / 2 : ℝ) ^ n) ≤ s.kt * (1 / 2 : ℝ) ^ n :=
    fun n ↦ le_trans (Real.log_le_sub_one_of_pos (p n)) (le_of_eq (by ring))
  refine le_trans (Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) fun n _ ↦ tb n) ?_
  rw [← Real.exp_log (Finset.prod_pos fun n _ ↦ p n), Real.log_prod fun n _ ↦ (p n).ne']
  refine le_trans (Real.exp_le_exp.mpr (Finset.sum_le_sum fun n _ ↦ lb n)) ?_
  have geom := partial_scaled_geometric_bound (s.kt).toNNReal A one_half_pos.le
    one_half_lt_one
  simp only [Real.coe_toNNReal', s.kt_nonneg, sup_of_le_left,
    (by norm_num : (1 - 1 / 2 : ℝ)⁻¹ = 2)] at geom
  refine le_trans (Real.exp_le_exp.mpr geom) (le_of_eq ?_)
  simp only [SuperNear.k, mul_comm]

end Bottcher

-- Next we prove that everything is analytic in an additional function parameter
section BottcherC

variable {f : ℂ → ℂ → ℂ}
variable {d : ℕ}
variable {u : Set ℂ}
variable {t : Set (ℂ × ℂ)}
variable {a b : ℝ}

/-- `SuperNearC → SuperNear` at `p ∈ t` -/
theorem SuperNearC.ts (s : SuperNearC f d u t a b) {p : ℂ × ℂ} (m : p ∈ t) :
    SuperNear (f p.1) d {z | (p.1, z) ∈ t} a b :=
  s.s (s.tc m)

/-- The parameter set `u` is open -/
theorem SuperNearC.ou (s : SuperNearC f d u t a b) : IsOpen u := by
  have e : u = Prod.fst '' t := by
    ext c; simp only [Set.mem_image, Prod.exists, exists_and_right, exists_eq_right]
    exact ⟨fun m ↦ ⟨0, (s.s m).t0⟩, fun h ↦ Exists.elim h fun z m ↦ s.tc m⟩
  rw [e]; exact isOpenMap_fst _ s.o

/-- `SuperNearC → SuperAtC` -/
public theorem SuperNearC.superAtC (s : SuperNearC f d u t a b) : SuperAtC f d u :=
  { o := s.ou
    s := by
      intro c m; have s := s.s m
      exact
        { d2 := s.d2
          fa0 := s.fa0
          fd := s.fd
          fc := s.fc }
    fa := fun {c} m ↦ s.fa _ (s.s m).t0 }

/-- A Two-parameter version of `g` -/
def g2 (f : ℂ → ℂ → ℂ) (d : ℕ) := fun p : ℂ × ℂ ↦ g (f p.1) d p.2

/-- `g2` is jointly analytic where `f` is -/
theorem SuperAtC.ga_of_fa (s : SuperAtC f d u) {t : Set (ℂ × ℂ)} (o : IsOpen t)
    (fa : AnalyticOnNhd ℂ (uncurry f) t) (tc : ∀ {p : ℂ × ℂ}, p ∈ t → p.1 ∈ u) :
    AnalyticOnNhd ℂ (g2 f d) t := by
  refine Pair.hartogs o ?_ ?_
  · intro c z m
    simp only [g2, g]
    by_cases zero : z = 0; · simp only [zero, if_true]; exact analyticAt_const
    · simp only [zero, if_false]; refine AnalyticAt.div ?_ analyticAt_const (pow_ne_zero _ zero)
      refine (fa _ ?_).comp₂ analyticAt_id analyticAt_const; exact m
  · intro c z m; apply (s.s (tc m)).ga_of_fa
    refine (fa _ ?_).comp₂ analyticAt_const analyticAt_id; exact m

/-- `g2` is jointly analytic -/
theorem SuperNearC.ga (s : SuperNearC f d u t a b) : AnalyticOnNhd ℂ (g2 f d) t :=
  s.superAtC.ga_of_fa s.o s.fa fun {_} m ↦ s.tc m

/-- `SuperNearC` commutes with unions -/
theorem SuperNearC.union {I : Type} {u : I → Set ℂ} {t : I → Set (ℂ × ℂ)}
    (s : ∀ i, SuperNearC f d (u i) (t i) a b) : SuperNearC f d (⋃ i, u i) (⋃ i, t i) a b := by
  set tu := ⋃ i, t i
  have o : IsOpen tu := isOpen_iUnion fun i ↦ (s i).o
  have sm : ∀ {c z : ℂ},
      (c, z) ∈ tu → ∃ u, z ∈ u ∧ u ⊆ {z | (c, z) ∈ tu} ∧ SuperNear (f c) d u a b := by
    intro c z m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩; use{z | (c, z) ∈ t i}
    simp only [Set.mem_setOf_eq, m, Set.mem_iUnion, Set.setOf_subset_setOf, true_and, tu]
    constructor
    · exact fun z m ↦ ⟨i, m⟩
    · exact (s i).s ((s i).tc m)
  exact
    { o
      tc := by
        intro p m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩
        exact Set.subset_iUnion _ i ((s i).tc m)
      fa := by intro p m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩; exact (s i).fa _ m
      s := by
        intro c m; rcases Set.mem_iUnion.mp m with ⟨i, m⟩; have s := (s i).s m
        exact
          { d2 := s.d2
            fa0 := s.fa0
            fd := s.fd
            fc := s.fc
            o := o.snd_preimage c
            a1 := s.a1
            b0 := s.b0
            b1 := s.b1
            c1' := s.c1'
            t0 := Set.subset_iUnion _ i s.t0
            t2 := by intro z m; rcases sm m with ⟨u, m, _, s⟩; exact s.t2 m
            fa := by intro z m; rcases sm m with ⟨u, m, _, s⟩; exact s.fa _ m
            ft := by intro z m; rcases sm m with ⟨u, m, us, s⟩; exact us (s.ft m)
            gs' := by intro z z0 m; rcases sm m with ⟨u, m, _, s⟩; exact s.gs' z0 m } }

/-- `SuperAtC → SuperNearC`, staying inside `w` -/
public theorem SuperAtC.superNearC' (s : SuperAtC f d u) {w : Set (ℂ × ℂ)} (wo : IsOpen w)
    (wc : ∀ c, c ∈ u → (c, (0 : ℂ)) ∈ w) : ∃ t, t ⊆ w ∧ SuperNearC f d u t (1 / 2) (1 / 4) := by
  have h : ∀ c, c ∈ u →
      ∃ r, r > 0 ∧ ball c r ⊆ u ∧ ball (c, 0) r ⊆ w ∧
        SuperNearC f d (ball c r) (ball (c, 0) r) (1 / 2) (1 / 4) := by
    intro c m
    rcases(s.fa m).exists_ball_analyticOnNhd with ⟨r0, r0p, fa⟩
    rcases Metric.isOpen_iff.mp s.o c m with ⟨r1, r1p, rc⟩
    set r2 := min r0 r1
    have fa := fa.mono (Metric.ball_subset_ball (min_le_left r0 r1))
    have rc : ball c r2 ⊆ u := le_trans (Metric.ball_subset_ball (by bound)) rc
    have ga := s.ga_of_fa isOpen_ball fa
        (by intro p m; simp only [← ball_prod_same, Set.mem_prod] at m; exact rc m.1)
    rcases Metric.isOpen_iff.mp wo (c, 0) (wc c m) with ⟨r3, r3p, rw⟩
    rcases Metric.continuousAt_iff.mp (ga (c, 0) (mem_ball_self (by bound))).continuousAt
        (1 / 4) (by norm_num) with ⟨r4, r4p, gs⟩
    set r := min (min r2 r3) (min r4 (1 / 2))
    have rp : 0 < r := by bound
    have rh : r ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
    have rr4 : r ≤ r4 := le_trans (min_le_right _ _) (min_le_left r4 _)
    have rc : ball c r ⊆ u := le_trans (Metric.ball_subset_ball (by bound)) rc
    have rw : ball (c, 0) r ⊆ w :=
      _root_.trans (Metric.ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))) rw
    use r, rp, rc, rw
    exact
      { o := isOpen_ball
        tc := by
          intro p m; simp only [← ball_prod_same, Set.mem_prod] at m
          exact Metric.ball_subset_ball (by linarith) m.1
        s := by
          intro c' m; simp only [← ball_prod_same, Set.mem_prod, m, true_and]
          apply (s.s (rc m)).super_on_ball rp rh (by norm_num) (by norm_num) (by norm_num)
              (by norm_num) (by norm_num)
          · apply fa.comp₂ analyticOnNhd_const analyticOnNhd_id
            intro z zm; apply Metric.ball_subset_ball (by bound : r ≤ r2)
            simp only [← ball_prod_same, Set.mem_prod, m, true_and]; exact zm
          · simp only [Complex.dist_eq, Prod.dist_eq, sub_zero, max_lt_iff, and_imp, g2, g0] at gs
            simp only [Metric.mem_ball, Complex.dist_eq] at m
            intro z zr; exact @gs ⟨c', z⟩ (lt_of_lt_of_le m rr4) (lt_of_lt_of_le zr rr4)
        fa := fa.mono (Metric.ball_subset_ball (min_le_of_left_le (min_le_left _ _))) }
  set r := fun c : u ↦ choose (h _ c.mem)
  set v := fun c : u ↦ ball (c : ℂ) (r c)
  set t := fun c : u ↦ ball ((c : ℂ), (0 : ℂ)) (r c)
  use⋃ c : u, t c
  have e : u = ⋃ c : u, v c := by
    apply Set.ext; intro c; rw [Set.mem_iUnion]; constructor
    · intro m; use⟨c, m⟩; rcases choose_spec (h c m) with ⟨rp, _, _⟩
      exact mem_ball_self rp
    · intro m; rcases m with ⟨i, m⟩; rcases choose_spec (h _ i.mem) with ⟨_, us, _⟩
      exact us m
  have tw : (⋃ c : u, t c) ⊆ w := by
    apply Set.iUnion_subset; intro i; rcases choose_spec (h _ i.mem) with ⟨_, _, rw, _⟩; exact rw
  have si : ∀ c : u, SuperNearC f d (v c) (t c) (1 / 2) (1 / 4) := by
    intro i; rcases choose_spec (h _ i.mem) with ⟨_, _, _, s⟩; exact s
  have s := SuperNearC.union si; simp only at s; rw [← e] at s
  exact ⟨tw, s⟩

/-- `SuperAtC → SuperNearC` -/
theorem SuperAtC.superNearC (s : SuperAtC f d u) : ∃ t, SuperNearC f d u t (1 / 2) (1 / 4) := by
  rcases s.superNearC' isOpen_univ fun _ _ ↦ Set.mem_univ _ with ⟨t, _, s⟩; exact ⟨t, s⟩

theorem iterates_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (n : ℕ) (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ (f c)^[n] z) c := by
  induction' n with n nh; · simp only [Function.iterate_zero, id]; exact analyticAt_const
  · simp_rw [Function.iterate_succ']; simp only [Function.comp_apply]
    refine (s.fa _ ?_).comp (analyticAt_id.prod nh)
    exact (s.ts m).mapsTo n m

theorem term_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (n : ℕ) (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ term (f c) d n z) c := by
  refine AnalyticAt.cpow ?_ analyticAt_const ?_
  · have e : (fun c ↦ g (f c) d ((f c)^[n] z)) = fun c ↦ g2 f d (c, (f c)^[n] z) := rfl
    rw [e]
    refine (s.ga _ ?_).comp ?_
    · exact (s.ts m).mapsTo n m
    · apply analyticAt_id.prod (iterates_analytic_c s n m)
  · refine mem_slitPlane_of_near_one ?_
    exact lt_of_le_of_lt ((s.ts m).gs ((s.ts m).mapsTo n m)) (s.ts m).b1

/-- `term` prod is analytic in `c` -/
theorem term_prod_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ tprod fun n ↦ term (f c) d n z) c := by
  have a0 : 0 ≤ (2⁻¹ : ℝ) := by norm_num
  set t' := {c | (c, z) ∈ t}
  have o' : IsOpen t' := s.o.preimage (by continuity)
  refine (fast_products_converge_eventually' o' a0 (by linarith) ?_
    (.of_forall fun n c m ↦ term_converges (s.ts m) n m)).2.1 _ m
  exact fun n c m ↦ term_analytic_c s n m

/-- `term` prod is jointly analytic (using Hartogs's theorem for simplicity) -/
theorem term_prod_analytic (s : SuperNearC f d u t a b) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ tprod fun n ↦ term (f p.1) d n p.2) t := by
  refine Pair.hartogs s.o ?_ ?_
  · intro c z m; simp only; exact term_prod_analytic_c s m
  · intro c z m; simp only; exact term_prod_analytic_z (s.ts m) _ m

/-- `bottcherNear` is analytic in `c` -/
public theorem bottcherNear_analytic_c (s : SuperNearC f d u t a b) {c z : ℂ} (m : (c, z) ∈ t) :
    AnalyticAt ℂ (fun c ↦ bottcherNear (f c) d z) c :=
  analyticAt_const.mul (term_prod_analytic_c s m)

/-- `bottcherNear` is jointly analytic -/
public theorem bottcherNear_analytic (s : SuperNearC f d u t a b) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ ↦ bottcherNear (f p.1) d p.2) t := fun _ m ↦
  analyticAt_snd.mul (term_prod_analytic s _ m)

/-- `deriv f` is nonzero away from 0 -/
public theorem df_ne_zero (s : SuperNearC f d u t a b) {c : ℂ} (m : c ∈ u) :
    ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0), deriv (f p.1) p.2 = 0 ↔ p.2 = 0 := by
  have df : ∀ e z, (e, z) ∈ t →
      deriv (f e) z = ↑d * z ^ (d - 1) * g (f e) d z + z ^ d * deriv (g (f e) d) z := by
    intro e z m; apply HasDerivAt.deriv
    have fg : f e = fun z ↦ z ^ d * g (f e) d z := by funext; rw [(s.ts m).fg]
    nth_rw 1 [fg]
    apply HasDerivAt.mul; apply hasDerivAt_pow
    rw [hasDerivAt_deriv_iff]; exact ((s.ts m).ga _ m).differentiableAt
  have small : ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0),
      ‖p.2 * deriv (g (f p.1) d) p.2‖ < ‖↑d * g (f p.1) d p.2‖ := by
    have ga : AnalyticAt ℂ (uncurry fun c z ↦ g (f c) d z) (c, 0) := s.ga _ (s.s m).t0
    apply ContinuousAt.eventually_lt
    · exact continuous_norm.continuousAt.comp (continuousAt_snd.mul ga.deriv2.continuousAt)
    · exact continuous_norm.continuousAt.comp (continuousAt_const.mul ga.continuousAt)
    · simp only [g0, MulZeroClass.zero_mul, norm_zero, Complex.norm_natCast, mul_one, Nat.cast_pos]
      exact (s.s m).dp
  apply small.mp
  apply (s.o.eventually_mem (s.s m).t0).mp
  refine .of_forall ?_; clear small
  intro ⟨e, w⟩ m' small; simp only [df _ _ m'] at small ⊢
  nth_rw 4 [← Nat.sub_add_cancel (Nat.succ_le_of_lt (s.s m).dp)]
  simp only [pow_add, pow_one, mul_comm _ (w ^ (d - 1)), mul_assoc (w ^ (d - 1)) _ _, ←
    left_distrib, mul_eq_zero, pow_eq_zero_iff (Nat.sub_pos_of_lt (s.s m).d2).ne']
  exact or_iff_left (add_ne_zero_of_abs_lt small)

end BottcherC
