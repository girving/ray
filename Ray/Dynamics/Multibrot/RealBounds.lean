import Mathlib.Analysis.Complex.RealDeriv
import Ray.Dynamics.Multibrot.D
import Ray.Misc.Pow

/-!
## Real iteration bounds useful for `bottcher` bounds
-/

open Complex
open Metric (closedBall mem_closedBall mem_closedBall_self)
open Real (exp log)
open Set
open scoped Real Topology
noncomputable section

variable {c z : ℂ}
variable {𝕜 : Type} [NontriviallyNormedField 𝕜]

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
### Noniteration lemmas
-/

/-- Absorb a free `x` into `x⁻¹ ^ d` -/
lemma mul_inv_pow_d (d : ℕ) [Fact (2 ≤ d)] (x : 𝕜) : x * x⁻¹ ^ d = x⁻¹ ^ (d - 1) := by
  by_cases x0 : x = 0
  · simp only [x0, inv_zero, zero_mul]
    have d2 := two_le_d d
    rw [zero_pow (by omega)]
  · nth_rw 1 [← Nat.sub_add_cancel (d_ge_one d), pow_succ', ← mul_assoc, mul_inv_cancel₀ x0,
      one_mul]

/-- Loose bound on `c * x ^ d` -/
@[bound] lemma cxd_le (d : ℕ) [d2 : Fact (2 ≤ d)] (c x : ℝ) (c3 : 3 ≤ c) (x0 : 0 ≤ x)
    (x3 : x ≤ c⁻¹) : c * x ^ d ≤ 3⁻¹ := by
  have c3 : c⁻¹ ≤ 3⁻¹ := by bound
  calc c * x ^ d
    _ ≤ c * x ^ 2 := by bound
    _ = c * x * x := by ring
    _ ≤ c * c⁻¹ * x := by bound
    _ ≤ 1 * x := by bound
    _ ≤ 3⁻¹ := by bound
@[bound] lemma cxd_lt_1 (d : ℕ) [d2 : Fact (2 ≤ d)] (c x : ℝ) (c3 : 3 ≤ c) (x0 : 0 ≤ x)
    (x3 : x ≤ c⁻¹) : c * x ^ d < 1 := lt_of_le_of_lt (cxd_le d c x c3 x0 x3) (by norm_num)
@[bound] lemma cxd_le_1 (d : ℕ) [d2 : Fact (2 ≤ d)] (c x : ℝ) (c3 : 3 ≤ c) (x0 : 0 ≤ x)
    (x3 : x ≤ c⁻¹) : c * x ^ d ≤ 1 := (cxd_lt_1 d c x c3 x0 x3).le

/-!
### Multibrot real iteration bounds
-/

/-- Function we'll iterate in tight bounds below -/
def fb (d : ℕ) (b : ℝ) (x : ℝ) : ℝ := x ^ d / (1 - b * x ^ d)

/-- Real iterates are positive and small -/
lemma fb_nonneg_le (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ∈ Ioc 0 z⁻¹ := by
  have czi : z⁻¹ ≤ c⁻¹ := by bound
  have z3 : z⁻¹ ≤ 3⁻¹ := by bound
  induction' n with n h
  · simp
    linarith
  · simp only [Function.iterate_succ_apply']
    generalize hx : (fb d c)^[n] z⁻¹ = x at h
    simp only [fb]
    refine ⟨by bound, ?_⟩
    calc x ^ d / (1 - c * x ^ d)
      _ ≤ x ^ 2 / (1 - 3⁻¹) := by bound
      _ = x / (1 - 3⁻¹) * x := by ring
      _ ≤ 3⁻¹ / (1 - 3⁻¹) * z⁻¹ := by bound
      _ ≤ z⁻¹ := by bound

@[bound] lemma fb_nonneg (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    0 ≤ (fb d c)^[n] z⁻¹ := (fb_nonneg_le d c z c3 cz n).1.le
@[bound] lemma fb_pos (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    0 < (fb d c)^[n] z⁻¹ := (fb_nonneg_le d c z c3 cz n).1
@[bound] lemma fb_le_z (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ z⁻¹ := (fb_nonneg_le d c z c3 cz n).2
@[bound] lemma fb_le_c (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ c⁻¹ := le_trans (fb_le_z d c z c3 cz n) (by bound)
@[bound] lemma fb_le_3i (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ 3⁻¹ := le_trans (fb_le_z d c z c3 cz n) (by bound)
@[bound] lemma fb_le_1 (d : ℕ) [d2 : Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ 1 := le_trans (fb_le_z d c z c3 cz n) (by bound)

@[bound] lemma fb_mono_d (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (b3 : 3 ≤ b) (bx : b ≤ x) (n : ℕ) :
    b * (fb d b)^[n] x⁻¹ ^ d ≤ b * (fb 2 b)^[n] x⁻¹ ^ 2 := by
  have i3 : b⁻¹ ≤ 3⁻¹ := by bound
  have xb : x⁻¹ ≤ b⁻¹ := by bound
  induction' n with n uv
  · simp only [Function.iterate_zero, id_eq]
    bound
  · simp only [Function.iterate_succ_apply']
    generalize hu : (fb d b)^[n] x⁻¹ = u at uv
    generalize hv : (fb 2 b)^[n] x⁻¹ = v at uv
    refine mul_le_mul_of_nonneg_left ?_ (by bound)
    have u1 : u ^ d / (1 - b * u ^ d) ≤ 1 := by
      calc u ^ d / (1 - b * u ^ d)
        _ ≤ u / (1 - 3⁻¹) := by bound
        _ ≤ 3⁻¹ / (1 - 3⁻¹) := by bound
        _ ≤ 1 := by norm_num
    trans (fb d b u) ^ 2
    · simp only [fb]
      bound
    · simp only [fb]
      rw [mul_le_mul_iff_of_pos_left (by linarith)] at uv
      bound

@[bound] lemma fb_mono_d_weak (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (b3 : 3 ≤ b) (bx : b ≤ x) (n : ℕ) :
    (fb d b)^[n] x⁻¹ ^ d ≤ (fb 2 b)^[n] x⁻¹ ^ 2 := by
  have h := fb_mono_d d b x b3 bx n
  rwa [mul_le_mul_iff_of_pos_left (by bound)] at h

@[bound] lemma f_le_fb (d : ℕ) [Fact (2 ≤ d)] (c z : ℂ) (c3 : 3 ≤ ‖c‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖(fun z ↦ z ^ d / (1 + c * z ^ d))^[n] z⁻¹‖ ≤ (fb d ‖c‖)^[n] ‖z‖⁻¹ := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq, norm_inv, le_refl]
  · simp only [Function.iterate_succ_apply']
    generalize hw : (fun z ↦ z ^ d / (1 + c * z ^ d))^[n] z⁻¹ = w at h
    generalize hx : (fb d ‖c‖)^[n] ‖z‖⁻¹ = x at h
    simp only [norm_pow, norm_div, fb] at h ⊢
    apply div_le_div₀ (by bound) (by bound) (by bound)
    calc ‖1 + c * w ^ d‖
      _ ≥ ‖(1 : ℂ)‖ - ‖c * w ^ d‖ := by bound
      _ = 1 - ‖c‖ * ‖w‖ ^ d := by simp only [norm_one, Complex.norm_mul, norm_pow]
      _ ≥ 1 - ‖c‖ * x ^ d := by bound

/-- `fb` is monotone in `z` for fixed `c` -/
@[bound] lemma fb_mono_z (d : ℕ) [Fact (2 ≤ d)] (c z : ℝ) (c3 : 3 ≤ c) (cz : c ≤ z) (n : ℕ) :
    (fb d c)^[n] z⁻¹ ≤ (fb d c)^[n] c⁻¹ := by
  induction' n with n h
  · simp
    bound
  · simp only [Function.iterate_succ_apply', fb]
    bound

/-- Diagonal `fb` is monotone in `c`, in two different ways -/
lemma fb_mono_c (d : ℕ) [Fact (2 ≤ d)] (c b : ℝ) (b3 : 3 ≤ b) (bc : b ≤ c) (n : ℕ) :
    (fb d c)^[n] c⁻¹ ≤ (fb d b)^[n] b⁻¹ ∧ c * (fb d c)^[n] c⁻¹ ^ d ≤ b * (fb d b)^[n] b⁻¹ ^ d := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq, mul_inv_pow_d]
    bound
  · have dd : d * d = d + d * (d - 1) := by rw [← mul_one_add, Nat.add_sub_cancel' (d_ge_one d)]
    simp only [Function.iterate_succ_apply', fb, div_pow, ← mul_div_assoc, ← pow_mul, dd, pow_add,
      ← mul_assoc]
    bound

@[bound] lemma fb_mono_c_weak (d : ℕ) [Fact (2 ≤ d)] (c b : ℝ) (b3 : 3 ≤ b) (bc : b ≤ c) (n : ℕ) :
    (fb d c)^[n] c⁻¹ ≤ (fb d b)^[n] b⁻¹ := (fb_mono_c d c b b3 bc n).1
@[bound] lemma fb_mono_c_strong (d : ℕ) [Fact (2 ≤ d)] (c b : ℝ) (b3 : 3 ≤ b) (bc : b ≤ c) (n : ℕ) :
    c * (fb d c)^[n] c⁻¹ ^ d ≤ b * (fb d b)^[n] b⁻¹ ^ d := (fb_mono_c d c b b3 bc n).2

@[bound] lemma fb_mono_cz_weak (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bc : b ≤ c)
    (cz : c ≤ z) (n : ℕ) : (fb d c)^[n] z⁻¹ ≤ (fb d b)^[n] b⁻¹ :=
  le_trans (by bound) (fb_mono_c_weak d c b b3 bc n)
@[bound] lemma fb_mono_cz_strong (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bc : b ≤ c)
    (cz : c ≤ z) (n : ℕ) : c * (fb d c)^[n] z⁻¹ ^ d ≤ b * (fb d b)^[n] b⁻¹ ^ d :=
  le_trans (by bound) (fb_mono_c_strong d c b b3 bc n)

@[bound] lemma term_mono_d (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bc : b ≤ c) (cz : c ≤ z)
    (n : ℕ) :
    (1 - c * (fb d c)^[n] z⁻¹ ^ d) ^ (-1 / d ^ (n + 1) : ℝ) - 1 ≤
      (1 - c * (fb 2 c)^[n] z⁻¹ ^ 2) ^ (-1 / 2 ^ (n + 1) : ℝ) - 1 := by
  have c3 : 3 ≤ c := by bound
  apply sub_le_sub_right
  trans (1 - c * (fb 2 c)^[n] z⁻¹ ^ 2) ^ (-1 / d ^ (n + 1) : ℝ)
  · apply Real.rpow_le_rpow_of_nonpos <;> bound
  · apply Real.rpow_le_rpow_of_exponent_ge
    · bound
    · bound
    · simp only [neg_div, one_div, neg_le_neg_iff]
      bound

/-!
### Factorised bounds
-/

/-- Iteration after we pull out the `b⁻¹ ^ 2 ^ d` factor -/
def factor (d : ℕ) (b : 𝕜) (p : 𝕜 × 𝕜) : 𝕜 × 𝕜 :=
  let a := (1 - b * p.1 ^ d)⁻¹
  (p.1 ^ d * a, p.2 ^ d * a)

@[simp] lemma fst_factor (d : ℕ) (b x : ℝ) (n : ℕ) :
    ((factor d b)^[n] (x,1)).1 = (fb d b)^[n] x := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq]
  · simp only [Function.iterate_succ_apply', factor, h, fb, div_eq_mul_inv]

/-- Factored version of `fb` iteration -/
lemma fb_eq_factor (d : ℕ) (b x : ℝ) (n : ℕ) :
    (fb d b)^[n] x = ((factor d b)^[n] (x,1)).2 * x ^ d ^ n := by
  induction' n with n h
  · simp only [Function.iterate_zero, id_eq, pow_zero, pow_one, one_mul]
  · simp only [Function.iterate_succ_apply', fb, factor, h, div_eq_mul_inv, mul_pow, ← pow_mul,
      ← pow_succ, mul_assoc, mul_comm (x ^ _), fst_factor]

/-- `factor.2` as a division -/
lemma factor_eq_div {d : ℕ} {b x : ℝ} (x0 : x ≠ 0) {n : ℕ} :
    ((factor d b)^[n] (x,1)).2 = (fb d b)^[n] x / x ^ d ^ n := by
  simp only [fb_eq_factor, mul_div_assoc, ← div_pow, div_self x0, one_pow, mul_one]

@[bound] lemma factor_pos (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (b3 : 3 ≤ b) (bx : b ≤ x) (n : ℕ) :
    0 < ((factor d b)^[n] (x⁻¹,1)).2 := by
  induction' n with n h
  · simp
  · simp only [Function.iterate_succ_apply', factor, fst_factor]
    bound

@[bound] lemma factor_nonneg (d : ℕ) [Fact (2 ≤ d)] (b x : ℝ) (b3 : 3 ≤ b) (bx : b ≤ x) (n : ℕ) :
    0 ≤ ((factor d b)^[n] (x⁻¹,1)).2 := (factor_pos d b x b3 bx n).le

@[bound] lemma factor_mono (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bc : b ≤ c) (cz : c ≤ z)
    (n : ℕ) : ((factor d c)^[n] (z⁻¹, 1)).2 ≤ ((factor d b)^[n] (b⁻¹, 1)).2 := by
  induction' n with n h
  · simp
  · simp only [Function.iterate_succ_apply', factor, fst_factor]
    bound [fb_mono_cz_strong d b3 bc cz n]

@[bound] lemma fb_le_factor (d : ℕ) [Fact (2 ≤ d)] {b c z : ℝ} (b3 : 3 ≤ b) (bc : b ≤ c)
    (cz : c ≤ z) (n : ℕ) :
    c * (fb d c)^[n] z⁻¹ ^ d ≤ ((factor d b)^[n] (b⁻¹, 1)).2 ^ d * z⁻¹ ^ (d ^ (n + 1) - 1) := by
  have z0 : 0 < z := by linarith
  simp only [fb_eq_factor, mul_pow, ← pow_mul, ← pow_succ, mul_comm c]
  rw [pow_sub₀ _ (by positivity) (by bound), ← mul_assoc, pow_one, inv_inv]
  bound

/-!
### Doubly exponential bounds, and related

These are used to bound the tail products of `term` bounds.
-/

lemma fb_le_pow_pow (d : ℕ) [Fact (2 ≤ d)] {b : ℝ} (b3 : 3 ≤ b) (n : ℕ) :
    (fb 2 b)^[n] b⁻¹ ≤ 2 / 3 * 2⁻¹ ^ 2 ^ n := by
  induction' n with n h
  · norm_num
    simp only [one_div]
    bound
  · simp only [Function.iterate_succ_apply', fb]
    generalize hx : (fb 2 b)^[n] b⁻¹ = x at h
    calc x ^ 2 / (1 - b * x ^ 2)
      _ ≤ (2 / 3 * 2⁻¹ ^ 2 ^ n) ^ 2 / (1 - 3⁻¹) := by bound
    simp only [mul_pow, ← pow_mul, ← pow_succ, div_eq_inv_mul]
    linarith
