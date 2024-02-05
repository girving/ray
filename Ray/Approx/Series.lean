import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Ray.Approx.Array
import Ray.Approx.Division

open Pointwise

/-!
## Function approximation via `Interval` power series
-/

open BigOperators
open Classical
open Set
open scoped Real

variable {s t : Int64}

/-!
### Sums of Taylor series
-/

/-- Sum an `Interval` Taylor series, spitting out `x^n` and the result.
    For now, we use a slow linear loop. -/
@[irreducible] def taylor_sum' (c : Array (Interval)) (x p t : Interval) (offset steps : ℕ)
    (_ : offset + steps ≤ c.size) :
    Interval :=
  match steps with
  | 0 => t
  | steps+1 => taylor_sum' c x (p * x) (t + c[offset]'(by omega) * p) (offset+1) steps (by omega)

/-- Sum an `Interval` Taylor series -/
@[irreducible] def taylor_sum (c : Array (Interval)) (x : Interval) : Interval :=
  taylor_sum' c x 1 0 0 c.size (by omega)

/-- `taylor_sum'` is conservative -/
lemma approx_taylor_sum' (c : Array (Interval)) (c' : ℕ → ℝ) (x p t : Interval) (x' p' t' : ℝ)
    (offset steps : ℕ) (os : offset + steps ≤ c.size)
    (ac : ∀ k : Fin c.size, c' k ∈ approx (c[k]))
    (xx : x' ∈ approx x) (pp : p' ∈ approx p) (tt : t' ∈ approx t) :
    t' + ∑ k in Finset.range steps, c' (offset + k) * p' * x' ^ k ∈
      approx (taylor_sum' c x p t offset steps os) := by
  induction' steps with steps h generalizing p p' t t' offset
  · rw [taylor_sum']; simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, add_zero, tt]
  · rw [taylor_sum']
    simp only [Finset.sum_range_succ', pow_zero, mul_one, add_zero, add_comm (Finset.sum _ _),
      ←add_assoc, pow_succ, ←mul_assoc _ x', mul_assoc _ _ x', add_right_comm _ _ (1:ℕ)]
    apply h
    · exact mem_approx_mul pp xx
    · exact mem_approx_add tt (mem_approx_mul (ac ⟨_, by omega⟩) pp)

/-- `taylor_sum` is conservative -/
lemma approx_taylor_sum (c : Array (Interval)) (c' : ℕ → ℝ) (x : Interval) (x' : ℝ)
    (ac : ∀ k : Fin c.size, c' k ∈ approx (c[k])) (xx : x' ∈ approx x) :
    ∑ k in Finset.range c.size, c' k * x' ^ k ∈ approx (taylor_sum c x) := by
  have h := approx_taylor_sum' c c' x 1 0 x' 1 0 0 c.size (by omega) ac xx
  simp only [Interval.approx_one, Interval.approx_zero, mem_singleton_iff, zero_add, mul_one,
    forall_true_left] at h
  rw [taylor_sum]; exact h

-- DO NOT SUBMIT: Switch order of summation so that small things get summed first

/-!
### Generic `Series` machinery
-/

/-- A power series approximation within an interval `[-r,r]` around `0` -/
structure Series (s : Int64) where
  /-- Lower bound on the radius of accuracy -/
  radius : Floating
  /-- Power series coefficients -/
  coeffs : Array (Interval)
  /-- Upper bound on the error within `[-r,r]` -/
  error : Floating

/-- Evaluation of a `Series` at a point.  For now, we use a slow linear loop. -/
@[irreducible] def Series.eval (p : Series s) (x : Interval) : Interval :=
  let a := x.abs
  bif a.hi == nan || p.radius < a.hi then nan else
  taylor_sum p.coeffs x + Interval.error p.error

/-- `Series` objects approximate functions -/
instance : Approx (Series s) (ℝ → ℝ) where
  approx p := {f | ∀ (x : ℝ) (y : Interval), x ∈ approx y → f x ∈ approx (p.eval y)}

/-- `Series.eval` propagates `nan` -/
@[simp] lemma Series.eval_nan {p : Series s} : p.eval (nan : Interval) = nan := by
  rw [Series.eval]
  simp only [Interval.abs_nan, Interval.hi_nan, beq_self_eq_true, Floating.n_nan, Bool.true_or,
    cond_true]

/-- `Approx` proof given an effective Taylor series bound -/
lemma Series.approx_of_taylor (p : Series s) (f : ℝ → ℝ) (a : ℕ → ℝ) (b : ℝ)
    (pf : p.radius ≠ nan → ∀ x : ℝ,
      |x| ≤ p.radius.val → |f x - ∑ n in Finset.range p.coeffs.size, a n * x ^ n| ≤ b)
    (ac : ∀ n : Fin p.coeffs.size, a n ∈ approx p.coeffs[n])
    (be : p.error ≠ nan → b ≤ p.error.val) :
    f ∈ approx p := by
  intro x y xy
  by_cases n : y.abs = nan ∨ p.radius < y.abs.hi
  · rw [Series.eval]
    rcases n with yn | ry
    · simp only [yn, Interval.hi_nan, beq_self_eq_true, Floating.n_nan, Bool.true_or, cond_true,
        Interval.approx_nan, mem_univ]
    · simp only [ry, decide_True, Bool.or_true, cond_true, Interval.approx_nan, mem_univ]
  simp only [not_or, not_lt, ←Ne.def, Floating.val_le_val] at n
  rcases n with ⟨yn, ry⟩
  have yn' : y ≠ nan := by simpa only [ne_eq, Interval.abs_eq_nan] using yn
  have rn : p.radius ≠ nan := Floating.ne_nan_of_le (y.abs.hi_ne_nan yn) ry
  have xa : |x| ≤ p.radius.val := by
    have a := Interval.mem_approx_abs xy
    simp only [approx, Interval.lo_eq_nan, yn, ite_false, mem_Icc] at a
    exact le_trans a.2 ry
  specialize pf rn x xa
  simp only [eval, bif_eq_if, Floating.val_lt_val, not_lt.mpr ry, decide_False, Bool.or_false,
    beq_iff_eq, Interval.hi_eq_nan, Interval.abs_eq_nan, yn', ite_false]
  exact Interval.approx_add_error pf be (approx_taylor_sum _ _ _ _ ac xy)

/-!
### `Series` approximations for `exp` and `log`

Our series for `log (1 + x)` is not very good: see
https://en.wikipedia.org/wiki/Natural_logarithm#Series for a better one with exponent
`(x / (x + 2)) ^ 2`.  We can switch to that later if desired.
-/

/-- `exp_series` will be accurate on `[-r,r]` for `r` slightly larger than `log 2 / 2`. -/
def exp_series_radius : ℚ := 0.346574

/-- A power series approximation for `exp` -/
@[irreducible] def exp_series (s : Int64) (n : ℕ) : Series s where
  radius := .ofRat exp_series_radius false
  coeffs := (Array.range n).map (fun n ↦ .ofRat (Nat.factorial n)⁻¹)
  error := bif n == 0 then nan
           else .ofRat (exp_series_radius ^ n * ((n + 1) / (Nat.factorial n * n))) true

/-- Our power series for `exp` is correct -/
lemma approx_exp_series (n : ℕ) : Real.exp ∈ approx (exp_series s n) := by
  have nn : (exp_series s n).coeffs.size = n := by rw [exp_series, Array.size_map, Array.size_range]
  by_cases n0 : n = 0
  · intro a x _
    have e : (exp_series s 0).error = nan := by
      rw [exp_series]
      simp only [beq_self_eq_true, pow_zero, CharP.cast_eq_zero, zero_add, Nat.factorial_zero,
        Nat.cast_one, mul_zero, div_zero, cond_true]
    simp only [n0, Series.eval._eq_1, bif_eq_if, Floating.val_lt_val, Bool.or_eq_true, beq_iff_eq,
      Interval.hi_eq_nan, Interval.abs_eq_nan, decide_eq_true_eq, e, Interval.error_nan,
      Interval.add_nan, ite_self, Interval.approx_nan, mem_univ]
  · apply (exp_series s n).approx_of_taylor
    · intro rn x xr
      rw [exp_series] at xr rn; simp only at xr
      have xr' : |x| ≤ exp_series_radius := le_trans xr (Floating.ofRat_le rn)
      have x1 : |x| ≤ 1 := by simp only [exp_series_radius] at xr'; exact le_trans xr' (by norm_num)
      simp only [nn]
      have h := Real.exp_bound x1 (Nat.pos_iff_ne_zero.mpr n0)
      simp only [div_eq_inv_mul] at h
      exact le_trans h (mul_le_mul_of_nonneg_right (pow_le_pow_left (by positivity) xr' _)
        (by positivity))
    · intro k
      have e : (Nat.factorial k : ℝ)⁻¹ = (Nat.factorial k : ℚ)⁻¹ := by
        simp only [Rat.cast_inv, Rat.cast_coe_nat]
      simp only [exp_series, getElem_fin, Array.getElem_map, Array.range_getElem,
        ←Rat.cast_inv, e]
      apply Interval.approx_ofRat
    · intro en
      simp only [mul_inv_rev, Nat.cast_succ]
      rw [exp_series, bif_eq_if] at en ⊢
      simp only [beq_iff_eq, ne_eq, ite_eq_left_iff, not_forall, exists_prop, n0, not_false_iff,
        true_or, if_false] at en ⊢
      refine le_trans (le_of_eq ?_) (Floating.le_ofRat en)
      simp only [div_eq_inv_mul, mul_inv, mul_comm _ ((n:ℚ)⁻¹), Rat.cast_mul, Rat.cast_pow,
        Rat.cast_inv, Rat.cast_coe_nat, Rat.cast_add, Rat.cast_one]

/-- `mono` friendly version of `approx_exp_series` -/
@[mono] lemma mem_approx_exp_series {a : ℝ} {x : Interval} (ax : a ∈ approx x) {n : ℕ} :
    Real.exp a ∈ approx ((exp_series s n).eval x) :=
  approx_exp_series n a x ax

/-- 16 terms are about enough for 64 bits of precision -/
@[irreducible] def exp_series_16 := exp_series (-62) 16

/-- `log1p_div_series` will be accurate on `[-1/3 - ε, 1/3 + ε]` -/
def log_series_radius : ℚ := 1/3 + 1/10000

/-- `log (1 + x) / x`, with the singularity removed -/
noncomputable def log1p_div (x : ℝ) : ℝ := if x = 0 then 1 else Real.log (1 + x) / x

/-- The defining property of `log1p_div` -/
@[simp] lemma mul_log1p_div {x : ℝ} : x * log1p_div x = Real.log (1 + x) := by
  simp only [log1p_div]
  by_cases x0 : x = 0
  · simp only [x0, add_zero, Real.log_one, div_zero, ite_true, mul_one]
  · simp only [x0, ite_false, mul_div_cancel' _ x0]

/-- Exact precision series for `log1p_div` -/
lemma log1p_div_bound {x : ℝ} (x1 : |x| < 1) (n : ℕ) :
    |log1p_div x - ∑ k in Finset.range n, (-1)^k / (k + 1) * x^k| ≤ |x| ^ n / (1 - |x|) := by
  by_cases x0 : x = 0
  · simp only [log1p_div, x0, add_zero, Real.log_one, div_zero, ite_true, abs_zero, sub_zero,
      div_one]
    induction' n with n _
    · simp only [Nat.zero_eq, Finset.range_zero, Finset.sum_empty, sub_zero, abs_one, pow_zero,
        le_refl]
    · simp only [Finset.sum_range_succ', Nat.cast_add, Nat.cast_one, ne_eq, add_eq_zero,
        one_ne_zero, and_false, not_false_eq_true, zero_pow', mul_zero, Finset.sum_const_zero,
        pow_zero, CharP.cast_eq_zero, zero_add, div_self, mul_one, sub_self, abs_zero,
        Nat.succ_ne_zero, le_refl]
  · have n1 : |-x| < 1 := by simpa only [abs_neg] using x1
    have h := Real.abs_log_sub_add_sum_range_le n1 n
    have e : Real.log (1 + x) = x * log1p_div x := by
      simp only [log1p_div, x0, ite_false, mul_comm x, div_mul_cancel _ x0]
    simp only [pow_succ, neg_mul, neg_div, Finset.sum_neg_distrib, sub_neg_eq_add,
      add_comm _ (Real.log _), ← sub_eq_add_neg, abs_neg, mul_div_assoc, ←Finset.mul_sum] at h
    simp only [e, ←mul_sub, abs_mul, mul_le_mul_iff_of_pos_left (abs_pos.mpr x0), neg_pow x] at h
    simpa only [mul_comm_div, ←mul_div_assoc]

/-- A power series approximation for `log1p_div` -/
@[irreducible] def log1p_div_series (s : Int64) (n : ℕ) : Series s where
  radius := .ofRat log_series_radius false
  coeffs := (Array.range n).map (fun n : ℕ ↦ .ofRat ((-1)^n / (n + 1)))
  error := .ofRat (log_series_radius ^ n / (1 - log_series_radius)) true

/-- Our power series for `log1p_div` is correct -/
lemma approx_log1p_div_series (n : ℕ) : log1p_div ∈ approx (log1p_div_series s n) := by
  have nn : (log1p_div_series s n).coeffs.size = n := by
    rw [log1p_div_series, Array.size_map, Array.size_range]
  have r0 : 0 ≤ log_series_radius := by rw [log_series_radius]; norm_num
  have r1 : 0 < 1 - (log_series_radius : ℝ) := by rw [log_series_radius]; norm_num
  apply (log1p_div_series s n).approx_of_taylor (a := fun n ↦ (-1)^n / (n + 1))
      (b := log_series_radius ^ n / (1 - log_series_radius))
  · intro rn x xr
    rw [log1p_div_series] at xr rn; simp only at xr
    have xr' : |x| ≤ log_series_radius := le_trans xr (Floating.ofRat_le rn)
    have x1 : |x| < 1 := by
      simp only [log_series_radius] at xr'
      exact lt_of_le_of_lt xr' (by norm_num)
    simp only [nn]
    exact le_trans (log1p_div_bound x1 n) (by gcongr)
  · intro ⟨k,kn⟩
    have e : (-1 : ℝ) ^ k / (k + 1) = ↑((-1) ^ k / (↑k + 1) : ℚ) := by
      simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_add,
        Rat.cast_coe_nat]
    simp only [log1p_div_series, getElem_fin, Array.getElem_map, Array.range_getElem, e]
    apply Interval.approx_ofRat
  · intro en
    simp only [log1p_div_series] at en ⊢
    refine le_trans (le_of_eq ?_) (Floating.le_ofRat en)
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one]

/-- `mono` friendly version of `approx_log1p_div_series` -/
@[mono] lemma mem_approx_log1p_div_series {a : ℝ} {x : Interval} (ax : a ∈ approx x) {n : ℕ} :
    log1p_div a ∈ approx ((log1p_div_series s n).eval x) :=
  approx_log1p_div_series n a x ax

/-- The series for `log1p_div` converges very slowly, so we need ~38 terms -/
@[irreducible] def log1p_div_series_38 := log1p_div_series (-62) 38

/-!
### `log 2` and `(log 2)⁻¹` estimates

We need these for argument reduction in `exp` and `log` below, and in particular need to derive
them before we've done the general argument reduction.
-/

/-- `log 2` -/
@[irreducible] def Interval.log_2 : Interval :=
  -- log 2 = 2 * log (4/3) + log (9/8) = 2/3 * log1p_div (1/3) + 1/8 * log1p_div (1/8)
  .ofRat (2/3) * log1p_div_series_38.eval (ofRat (1/3)) +
    .ofRat (1/8) * log1p_div_series_38.eval (ofRat (1/8))

/-- Untrusted rational approximation to `(log 2)⁻¹` -/
@[irreducible] def untrusted_inv_log_2 : Floating :=
  .ofRat (1 / 0.693147180559945309417232121458) false

/-- `Interval.log_2` is conservative -/
@[mono] lemma Interval.approx_log_2 : Real.log 2 ∈ approx Interval.log_2 := by
  have e : Real.log 2 = 2/3 * log1p_div (1/3) + 1/8 * log1p_div (1/8) := by
    simp only [log1p_div, one_div, inv_eq_zero, OfNat.ofNat_ne_zero, div_inv_eq_mul,
      mul_comm (Real.log _), ite_false, ← mul_assoc, ne_eq, not_false_eq_true, div_mul_cancel,
      inv_mul_cancel, one_mul]
    rw [←Real.log_rpow (by norm_num), ←Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  rw [Interval.log_2, e, log1p_div_series_38]
  mono

/-!
### `exp x` for arbitrary `x`, via argument reduction

To compute `exp x`, we choose `n` s.t. `y = x - n log 2 ∈ [-log 2 / 2, log 2 / 2]`, compute `exp y`
via Taylor series, and form `exp x = exp (y + n log 2) = exp y * 2^n` via shifting.
-/

/-- `exp x` for potentially large `x`, via argument reduction -/
@[irreducible] def Floating.exp (x : Floating) : Interval :=
  bif x == nan then nan else
  -- We want
  --   `x - n log 2 ∈ [-log 2 / 2, log 2 / 2]`
  --   `x / log 2 - n ∈ [-1/2, 1/2]`
  --   `n ∈ x/log2 + [-1/2, 1/2]`
  --   `n ∈ x/log2 - 1/2 + [0,1]`
  -- We're not going to trust that `n` is correct, so we needn't trust our `(log 2)⁻¹` estimate.
  let z : Floating := x.mul untrusted_inv_log_2 false
  let n : Floating := ⟨(z.n + 1).shiftRightRound 1 false⟩
  let y : Interval := x - Interval.log_2.mul_float n
  (exp_series_16.eval y).scaleB n

#exit

/-- `exp x` for potentially large `x`, via argument reduction -/
@[irreducible] def Interval.exp (x : Interval) : Interval :=
  x.lo.exp ∪ x.hi.exp

/-- `Floating.exp` is conservative -/
@[mono] lemma Floating.mem_approx_exp {x : Floating} {x' : ℝ} (xm : x' ∈ approx x) :
    Real.exp x' ∈ approx x.exp := by
  rw [Floating.exp]
  generalize x.mul untrusted_inv_log_2 _ false = z
  simp only [bif_eq_if, beq_iff_eq]
  generalize (⟨(z.n + 1).shiftRightRound 1 false⟩ : Floating 0) = n
  by_cases xn : x = nan
  · simp only [xn, ite_true, FloatingInterval.nan_x, Interval.lo_nan,
      FloatingInterval.approx_of_lo_eq_nan, mem_univ]
  simp only [ne_eq, neg_neg, xn, not_false_eq_true, ne_nan_of_neg, ite_false]
  have e : Real.exp x' = Real.exp (x' - Real.log 2 * n.val) * 2 ^ n.val := by
    rw [Real.exp_sub, Real.exp_mul, Real.exp_log (by norm_num),
      div_mul_cancel _ (Real.rpow_pos_of_pos (by norm_num) _).ne']
  rw [e, exp_series_16]
  mono

/-- `Floating.exp` propagates `nan` -/
@[simp] lemma Floating.exp_nan : (nan : Floating).exp = nan := by
  rw [Floating.exp, exp_series_16]
  simp only [beq_self_eq_true, ← Interval.nan_def, nan_mul, nan_n, Interval.nan_sub,
    Interval.repoint_nan, Series.eval_nan, cond_true]

/-- `Interval.exp` is conservative (`⊆` version) -/
@[mono] lemma Interval.approx_exp {x : Interval} : Real.exp '' approx x ⊆ approx x.exp := by
  rw [Interval.exp]
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n
    · simp only [n, approx_of_lo_nan, image_univ, Real.range_exp, Floating.exp_nan,
        FloatingInterval.nan_union, FloatingInterval.nan_x, lo_nan,
        FloatingInterval.approx_of_lo_eq_nan, subset_univ]
    · simp only [n, approx_of_hi_nan, image_univ, Real.range_exp, Floating.exp_nan,
        FloatingInterval.union_nan, FloatingInterval.nan_x, lo_nan,
        FloatingInterval.approx_of_lo_eq_nan, subset_univ]
  rcases not_or.mp n with ⟨ln,hn⟩
  have e : approx x = Icc x.lo.val x.hi.val := by simp only [approx, ln, hn, false_or, if_false]
  rw [e]
  refine subset_trans Real.exp_monotone.image_Icc_subset (Icc_subset_approx ?_ ?_)
  · apply FloatingInterval.approx_union_left; mono
  · apply FloatingInterval.approx_union_right; mono

/-- `Interval.exp` is conservative (`∈` version) -/
@[mono] lemma Interval.mem_approx_exp {x : Interval} {a : ℝ} (ax : a ∈ approx x) :
    Real.exp a ∈ approx x.exp :=
  Interval.approx_exp (mem_image_of_mem _ ax)

/-- `Interval.exp` propagates `nan` -/
@[simp] lemma Interval.exp_nan : (nan : Interval).exp = nan := by
  rw [Interval.exp]
  simp only [lo_nan, Floating.exp_nan, hi_nan, FloatingInterval.union_nan]

/-!
### `log x` for arbitrary `x`, via argument reduction

We choose `n` s.t. `x = (1 + y) * 2^n` has `y ∈ [-1/3, 1/3]`.  Then `log x = log y + n log 2`,
and we can compute `log (1 + y)` via our series.  The surprisingly awkward part is the final
addition, since `n` might be big.  For now, we choose extreme laziness and require the user to
set the final precision.
-/

/-- Untrusted 4/3 approximation -/
@[irreducible] def untrusted_four_thirds : Floating (-62) := .ofRat (4/3) false

/-- Choose `n` s.t. `x * 2^-n ∈ [2/3, 4/3]`.  We don't trust the output of this routine for
    our conservativeness results. -/
@[irreducible] def Floating.untrusted_log_shift (x : Floating) : Floating 0 :=
  -- we make an initial guess that puts us in [1,2], then add 1 if we're not small enough
  let g := x.log2
  let y := ((x : Floating).scaleB (-g)).x.repoint (-62) false
  bif y.n ≤ untrusted_four_thirds.n then g else g+1

/-- `log x` for arbitrary `x`, via argument reduction -/
@[irreducible] def Floating.log (x : Floating) : FloatingInterval :=
  bif x.n ≤ 0 then nan else
  let n := x.untrusted_log_shift
  let y := ((x : Floating).scaleB (-n) : FloatingInterval).x.repoint (-62) - 1
  -- To choose our precision `t`, note that
  --   `x * 2^-n ∈ [2/3, 4/3]`
  --   `x ∈ [2/3, 4/3] * 2^n`
  --   `log x ∈ [log (2/3), log (4/3)] + n log 2`
  --   `|log x| ≤ 1/2 + |n| log 2 ≤ |n+1|`
  let t : Int64 := ⟨(n.n.abs + 1).log2⟩ - 62
  y.mul (log1p_div_series_38.eval y) t + Interval.log_2.mul_fixed n t

/-- `log x` for arbitrary `x`, via argument reduction -/
@[irreducible] def Interval.log (x : Interval) : FloatingInterval :=
  x.lo.log ∪ x.hi.log

/-- `Floating.log` is conservative -/
@[mono] lemma Floating.mem_approx_log {x : Floating} {x' : ℝ} (xm : x' ∈ approx x) :
    Real.log x' ∈ approx x.log := by
  rw [Floating.log, log1p_div_series_38]
  generalize x.untrusted_log_shift = n
  simp only [bif_eq_if]
  by_cases x0 : x.n ≤ 0
  · simp only [x0, decide_True, ite_true, FloatingInterval.nan_x, Interval.lo_nan,
      FloatingInterval.approx_of_lo_eq_nan, mem_univ]
  simp only [x0, decide_False, ite_false]
  simp only [not_le, ←Floating.val_pos] at x0
  simp only [approx_eq_singleton (Floating.ne_nan_of_pos x0), mem_singleton_iff] at xm
  simp only [xm]; clear xm x'
  generalize hy : (((x : Floating).scaleB (-n)) : FloatingInterval).x.repoint (-62) - 1 = y
  generalize hy' : x.val * 2^(-n.val) - 1 = y'
  have e : Real.log x.val = y' * log1p_div y' +  Real.log 2 * n.val := by
    simp only [← hy', mul_log1p_div, add_sub_cancel'_right]
    rw [Real.log_mul x0.ne' (Real.rpow_pos_of_pos (by norm_num) _).ne', Real.log_rpow (by norm_num)]
    ring
  have ym : y' ∈ approx y := by
    rw [←hy, ←hy']
    mono
  rw [e]
  mono

/-- `Floating.log` propagates `nan` -/
@[simp] lemma Floating.log_nan : (nan : Floating).log = nan := by
  rw [Floating.log]; simp only [nan_n, Int64.min_le, decide_True, cond_true]

/-- `Floating.log` turns nonpositives to `nan` -/
@[simp] lemma Floating.log_nonpos {x : Floating} (x0 : x.val ≤ 0) : x.log = nan := by
  rw [Floating.log]
  simp only [val_nonpos] at x0
  simp only [x0, decide_True, cond_true]

/-- `Interval.log` is conservative (`⊆` version) -/
@[mono] lemma Interval.approx_log {x : Interval} : Real.log '' approx x ⊆ approx x.log := by
  rw [Interval.log]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ x.lo.val ≤ 0
  · rcases n with n | n | n; repeat simp [n]
  simp only [not_or, not_le, ←Ne.def] at n
  rcases n with ⟨ln,hn,l0⟩
  have e : approx x = Icc x.lo.val x.hi.val := by simp only [approx, ln, hn, false_or, if_false]
  have le : Real.log '' Icc x.lo.val x.hi.val ⊆ Icc (Real.log x.lo.val) (Real.log x.hi.val) := by
    simp only [image_subset_iff]
    intro a ⟨m0,m1⟩
    simp only [mem_preimage, mem_Icc]
    exact ⟨Real.log_le_log l0 m0, Real.log_le_log (by linarith) m1⟩
  rw [e]
  refine subset_trans le (Icc_subset_approx ?_ ?_)
  · apply FloatingInterval.approx_union_left; mono
  · apply FloatingInterval.approx_union_right; mono

/-- `Interval.log` is conservative (`∈` version) -/
@[mono] lemma Interval.mem_approx_log {x : Interval} {a : ℝ} (ax : a ∈ approx x) :
    Real.log a ∈ approx x.log :=
  Interval.approx_log (mem_image_of_mem _ ax)

/-- `Interval.log` turns nonpositives to `nan` -/
@[simp] lemma Interval.log_nonpos {x : Interval} {a : ℝ} (a0 : a ≤ 0) (ax : a ∈ approx x) :
    x.log = nan := by
  rw [Interval.log]
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n; repeat simp [n]
  · rcases not_or.mp n with ⟨n0,n1⟩
    simp only [approx, ne_eq, neg_neg, n0, not_false_eq_true, Floating.ne_nan_of_neg, n1, or_self,
      ite_false, mem_Icc] at ax
    have l0 : x.lo.val ≤ 0 := by linarith
    simp only [Floating.log_nonpos l0, FloatingInterval.nan_union]

/-!
### Powers

These are easy now that we have `exp` and `log`.
-/

/-- `x^y = exp (x.log * y)` -/
@[irreducible] def Interval.pow (x : Interval) (y : Interval t) : FloatingInterval :=
  (x.log * y).x.exp

/-- `Interval.pow` is conservative -/
@[mono] lemma Interval.mem_approx_pow {x : Interval} {y : Interval t} {x' y' : ℝ}
    (xm : x' ∈ approx x) (ym : y' ∈ approx y) : x' ^ y' ∈ approx (x.pow y) := by
  rw [Interval.pow]
  by_cases x0 : 0 < x'
  · rw [Real.rpow_def_of_pos x0]; mono
  · simp only [not_lt] at x0
    rw [Interval.log_nonpos x0 xm, FloatingInterval.nan_mul, FloatingInterval.nan_x,
      Interval.exp_nan]
    simp only [FloatingInterval.nan_x, lo_nan, FloatingInterval.approx_of_lo_eq_nan, mem_univ]

/-!
### Unit tests

We test only the width of the resulting intervals, since their correctness is proved above.

I'm not happy with the precision we reach, but I will set debugging that aside for now.
-/

/-- `exp` series tests (for small `x`) -/
def exp_series_test (x : ℚ) (e : Float := 1e-17) : Bool :=
  (exp_series_16.eval (.ofRat x)).size.toFloat < e
lemma exp_series_test1 : exp_series_test 0 := by native_decide
lemma exp_series_test2 : exp_series_test (1/7) := by native_decide
lemma exp_series_test3 : exp_series_test (-1/7) := by native_decide
lemma exp_series_test4 : exp_series_test 0.34656 := by native_decide
lemma exp_series_test5 : exp_series_test (-0.34656) := by native_decide

/-- `log1p_div` series tests (for small `x`) -/
def log1p_div_series_test (x : ℚ) (e : Float := 2e-17) : Bool :=
  (log1p_div_series_38.eval (.ofRat x)).size.toFloat < e
lemma log1p_div_series_test1 : log1p_div_series_test 0 := by native_decide
lemma log1p_div_series_test2 : log1p_div_series_test (1/7) := by native_decide
lemma log1p_div_series_test3 : log1p_div_series_test (-1/7) := by native_decide
lemma log1p_div_series_test4 : log1p_div_series_test (1/3) := by native_decide
lemma log1p_div_series_test5 : log1p_div_series_test (-1/3) := by native_decide

/-- Our constants are accurately estimated -/
lemma log_2_size_test : Interval.log_2.size.toFloat < 2e-17 := by native_decide
lemma untrusted_inv_log_2_test : untrusted_inv_log_2.toFloat * 0.693147180559945309417 == 1 := by
  native_decide

/-- `exp` tests -/
def exp_test (x : ℚ) (e : Float) : Bool :=
  ((FloatingInterval.ofRat x).x.exp).x.size.toFloat < e
lemma exp_test1 : exp_test 0 1e-17 := by native_decide
lemma exp_test2 : exp_test 10 1e-11 := by native_decide
lemma exp_test3 : exp_test (-10) 1e-19 := by native_decide

/-- `log` tests -/
def log_test (x : ℚ) (s : Int64) (e : Float) : Bool :=
  (.ofRat x : Interval).log.x.size.toFloat ≤ e
lemma log_test1 : log_test 1 (-62) 0 := by native_decide
lemma log_test2 : log_test 2 (-61) 1e-16 := by native_decide
lemma log_test3 : log_test 1237821 (-42) 1e-15 := by native_decide
lemma log_test4 : log_test 1e-8 (-60) 1e-10 := by native_decide

/-- `pow` tests -/
def pow_test (x y : ℚ) (e : Float) : Bool :=
  ((.ofRat x : FloatingInterval).x.pow (.ofRat y : FloatingInterval).x).x.size.toFloat ≤ e
lemma pow_test1 : pow_test 3.7 4.2 1e-13 := by native_decide
lemma pow_test2 : pow_test 0.1 (-1/2) 1e-15 := by native_decide
lemma pow_test3 : pow_test 2 (1/2) 1e-16 := by native_decide
lemma pow_test4 : pow_test 2 (1/100) 1e-15 := by native_decide
