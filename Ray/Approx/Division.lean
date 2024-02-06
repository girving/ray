import Ray.Approx.Box
import Ray.Approx.Floating.TwoPow
import Ray.Approx.Interval.Conversion
import Ray.Approx.Interval.Around
import Ray.Approx.Interval.Mul
import Std.Data.Rat.Basic

open Pointwise

/-!
## `Interval` and `Box` inv and division

Given `x : Interval`, we want `1 / x` (division will follow immediately).  If `0 ∈ x`, then
`1 / x = nan`.  Otherwise, `x` is reliably positive or negative.

Given a smooth function `f : ℝ → ℝ` and its extension `f : Interval → Interval`.  At each step,
we can choose any `c ∈ approx x`.  Newton's method applied to intervals is

  `step f x c = c - f c / deriv f x`
  `newton f x c = x ∩ step f x c`

Does this work for `inv`, using `f x = 1/x - a`?  We have

  `deriv f x = -1 / x^2`
  `step f x c = c - f c / (-1 / x^2) = c + (1/c - a) / (1 / x^2)`
  `           = c + x^2/c - a x^2 = c + x^2 (1/c - a)`
  `           = c + x^2/c (1 - a c)`

Happily, we can cancel `x/c` to get `step f x c = c + x (1 - a c)`.  Let `c = 1/a + d`.  Then

  `step f x c = 1/a + d + x (1 - a (1/a + d)) = 1/a + d (1 - a x)`

If `1/a ∈ x`, the two endpoints of `x` will produce opposite sign for `1 - a x`, which regardless of
the sign of `d` will produce opposite signs for `d (1 - a x)`, and will bracket `1/a`.
-/

open Set
open scoped Real
namespace Interval

/-!
## Exact precision preliminaries
-/

/-- The exact precision reason why `inv_step` is conservative -/
lemma approx_inv_step_reason (c : ℝ) {x rl rh ml mh : ℝ} (x0 : 0 < x) (xr : rl ≤ x⁻¹ ∧ x⁻¹ ≤ rh)
    (mm : (fun z ↦ z * (1 - x * c)) '' Icc rl rh ⊆ Icc ml mh)
    : c + ml ≤ x⁻¹ ∧ x⁻¹ ≤ c + mh := by
  generalize he : 1/x - c = e
  replace he : c = 1/x - e := by linarith
  simp only [he, one_div, mul_sub, mul_inv_cancel x0.ne', sub_sub_cancel, add_comm_sub,
    add_le_iff_nonpos_right, tsub_le_iff_right, zero_add, le_add_iff_nonneg_right,
    sub_nonneg] at mm ⊢
  by_cases e0 : 0 ≤ e
  · have xe : 0 ≤ x * e := mul_nonneg x0.le e0
    simp only [image_mul_right_Icc (le_trans xr.1 xr.2) xe] at mm
    rw [Set.Icc_subset_Icc_iff (by nlinarith)] at mm
    constructor
    · refine le_trans mm.1 (le_trans (mul_le_mul_of_nonneg_right xr.1 xe) ?_)
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]
    · refine le_trans (le_trans ?_ (mul_le_mul_of_nonneg_right xr.2 xe)) mm.2
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]
  · simp only [not_le] at e0
    have xe : x * e < 0 := mul_neg_of_pos_of_neg x0 e0
    simp only [image_mul_right_Icc_of_neg xe] at mm
    rw [Set.Icc_subset_Icc_iff (by nlinarith)] at mm
    constructor
    · refine le_trans mm.1 (le_trans (mul_le_mul_of_nonpos_right xr.2 xe.le) ?_)
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]
    · refine le_trans (le_trans ?_ (mul_le_mul_of_nonpos_right xr.1 xe.le)) mm.2
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]

/-- The exact precision reason why `inv_step` is conservative, with `c` in a different place -/
lemma approx_inv_step_reason' (c : ℝ) {x rl rh ml mh : ℝ} (x0 : 0 < x) (xr : rl ≤ x⁻¹ ∧ x⁻¹ ≤ rh)
    (mm : (fun z ↦ c + z * (1 - x * c)) '' Icc rl rh ⊆ Icc ml mh)
    : ml ≤ x⁻¹ ∧ x⁻¹ ≤ mh := by
  generalize hsl : ml - c = sl
  generalize hsh : mh - c = sh
  have sml : ml = c + sl := by rw [←hsl]; linarith
  have smh : mh = c + sh := by rw [←hsh]; linarith
  rw [sml, smh]
  refine approx_inv_step_reason c x0 xr ?_
  rw [←image_image (g := fun z ↦ c + z) (f := fun z ↦ z * (1 - x * c)), image_subset_iff] at mm
  refine subset_trans mm ?_
  simp only [preimage_const_add_Icc, ← hsl, ← hsh, subset_refl]

/-!
## `Interval` reciprocal
-/

/-- Approximate the reciprocal of a positive number using 64-bit integer division -/
def inv_guess (x : Floating) : Floating :=
  bif x.s == 0 then nan else  -- Bail if we're denormalized or zero
  -- Our guess will be
  --   `x = x.n.n * 2^(x.s - 2^63)`
  --   `x⁻¹ = (1 / x.n.n) * 2^(2^63 - x.s)`
  --   `x⁻¹ = (2^63 / (x.n.n / 2^a)) * 2^(2^63 - x.s - 63 - a)`
  --   `x⁻¹ = (2^63 / (x.n.n / 2^a)) * 2^(2^64 - 63 - a - x.s - 2^63)`
  -- We get maximum precision if `x.n.n / 2^a = 2^32`, so we set `a = 30`:
  --   `x⁻¹ = (2^63 / (x.n.n / 2^30)) * 2^(2^64 - 93 - x.s - 2^63)`
  let t := (2^64 - 93 : UInt64) - x.s
  let y := ((1 : UInt64) <<< 63) / (x.n.n >>> 30)
  .of_ns ⟨y⟩ t

/-- Conservative region that includes `x⁻¹` -/
@[irreducible] def inv_region (x : Floating) (x0 : 0 < x.val) : Interval :=
  bif x.s == 0 then nan else  -- Bail if we're denormalized
  --
  -- We have
  --   `x.val = x.n.n * 2^(x.s - 2^63)`
  --   `x.n.n ∈ [2^62, 2^63) ⊆ 2^[62, 63]`
  --   `1 / x.val ∈ 2^(2^63 - [62, 63] - x.s)`
  --   `1 / x.val ∈ 2^(2^64 - [62, 63] - x.s - 2^63)`
  --   `1 / x.val ∈ 2^62 * 2^(2^64 - 62 - [62, 63] - x.s - 2^63)`
  let t : UInt64 := 2^64 - 62 - 63
  if ts : t < x.s then nan else  -- Bail if our result would be denormalized
  { lo := Floating.two_pow_special (t - x.s)
    hi := Floating.two_pow_special (t - x.s + 1)
    norm := by simp only [Floating.two_pow_special_ne_nan]
    le' := by
      intro _ _
      simp only [UInt64.pow_eq_zero, zero_sub, not_lt] at ts
      have o : (-62 - 63 - x.s).toNat ≠ 2 ^ 64 - 1 := by
        simp only [UInt64.toNat_sub ts]
        exact ne_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (by decide))
      simp only [UInt64.pow_eq_zero, zero_sub, Floating.val_two_pow_special]
      apply zpow_le_of_le (by norm_num)
      simp only [UInt64.toNat_add_one o, UInt64.toNat_sub ts]
      omega }

/-- `inv_region` is conservative -/
@[mono] lemma approx_inv_region {x : Floating} (x0 : 0 < x.val) :
    x.val⁻¹ ∈ approx (inv_region x x0) := by
  rw [inv_region]
  simp only [UInt64.pow_eq_zero, zero_sub, bif_eq_if, beq_iff_eq]
  split_ifs with s0 ts
  · simp only [s0, sub_zero, ite_true, approx_nan, mem_univ]
  · simp only [approx_nan, mem_univ]
  · simp only [not_lt] at ts
    have o : (-62 - 63 - x.s).toNat ≠ 2 ^ 64 - 1 := by
      simp only [UInt64.toNat_sub ts]
      exact ne_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (by decide))
    have e : (-62 - 63 : UInt64).toNat = 2^64 - 125 := by decide
    have t0 : (2 : ℝ) ≠ 0 := by norm_num
    have le_n : 2^62 ≤ ((x.n : ℤ) : ℝ) := by
      apply Floating.le_coe_coe_n s0
      simp only [Floating.isNeg_iff, decide_eq_false_iff_not, not_lt, x0.le]
    have n_lt : ((x.n : ℤ) : ℝ) < 2^63 := Floating.coe_coe_n_lt
    simp only [approx, Floating.two_pow_special_ne_nan, Floating.val_two_pow_special, ite_false,
      mem_Icc, UInt64.toNat_add_one o, UInt64.toNat_sub ts, e]
    simp only [UInt64.le_iff_toNat_le, e] at ts
    simp only [Nat.cast_sub ts]
    rw [Floating.val, mul_inv, ←zpow_neg, UInt64.toInt, Nat.cast_add_one, Nat.cast_sub ts]
    constructor
    · refine le_trans ?_ (mul_le_mul_of_nonneg_right
        (inv_le_inv_of_le (by positivity) n_lt.le) two_zpow_pos.le)
      simp only [←zpow_neg, ←zpow_ofNat, ←zpow_add₀ t0]
      apply zpow_le_of_le (by norm_num)
      norm_num; linarith
    · refine le_trans (mul_le_mul_of_nonneg_right
        (inv_le_inv_of_le (by norm_num) le_n) two_zpow_pos.le) ?_
      simp only [←zpow_neg, ←zpow_ofNat, ←zpow_add₀ t0]
      apply zpow_le_of_le (by norm_num)
      norm_num; linarith

/-- One step of Newton's method for the reciprocal.
    We trust that `1/x ∈ r`, but do not trust the guess `c`. -/
@[irreducible] def inv_step' (x : Floating) (r : Interval) (c : Floating) : Interval :=
  -- `r ∩ (c + r (1 - x c))`, where `x ∈ [1/2,1]`, `r,c ∈ [1,2]`
  c + r * (1 - Interval.float_mul_float x c)

/-- `inv_step'` is conservative -/
@[mono] lemma approx_inv_step' {x : Floating} {r : Interval} (c : Floating) (x0 : 0 < x.val)
    (xr : x.val⁻¹ ∈ approx r) : x.val⁻¹ ∈ approx (inv_step' x r c) := by
  rw [inv_step']
  simp only [approx, mem_ite_univ_left, mem_Icc]
  intro n
  simp only [lo_eq_nan] at n
  rcases ne_nan_of_add n with ⟨cn,ran⟩
  rcases ne_nan_of_mul ran with ⟨rn,sn⟩
  have xn := x.ne_nan_of_nonneg x0.le
  simp only [mem_inv, Floating.approx_eq_singleton xn, approx, inv_eq_iff_eq_inv,
    xn, if_false, r.lo_ne_nan rn, inv_singleton, mem_Icc] at xr
  simp only [ne_eq, coe_eq_nan] at cn
  apply approx_inv_step_reason' c.val x0 xr
  simp only [←approx_eq_Icc n, ←approx_eq_Icc rn, image_subset_iff]
  intro z m
  simp only [mem_preimage]
  mono

/-- One step of Newton's method for the reciprocal.
    We trust that `1/x ∈ r`, but do not trust the guess `c`. -/
@[irreducible] def inv_step (x : Floating) (r : Around x.val⁻¹) (c : Floating) (x0 : 0 < x.val) :
    Around x.val⁻¹ :=
  r ∩ ⟨inv_step' x r.i c, approx_inv_step' c x0 r.mem⟩

/-- Floating point interval reciprocal using Newton's method.
    We assume `x⁻¹ ∈ approx r`. -/
@[irreducible, pp_dot] def _root_.Floating.inv_pos (x : Floating) (x0 : 0 < x.val) :
    Around x.val⁻¹ :=
  -- Three steps of Newton's method to produce a tight, conservative interval.
  -- Probably two is enough, but I'm lazy.
  let r0 : Around x.val⁻¹ := ⟨inv_region x x0, approx_inv_region x0⟩
  let r1 := inv_step x r0 (inv_guess x) x0
  let r2 := inv_step x r1 r1.i.lo x0
  inv_step x r2 r2.i.lo x0

/-- `Interval` reciprocal of a positive interval -/
@[irreducible, pp_dot] def inv_pos (x : Interval) (x0 : 0 < x.lo.val) : Interval :=
  (x.hi.inv_pos (lt_of_lt_of_le x0 x.le)).i ∪ (x.lo.inv_pos x0).i

/-- `Interval` reciprocal using Newton's method. -/
@[irreducible, pp_dot] def inv (x : Interval) : Interval :=
  if z : x.zero_mem then nan else
  let r := x.abs.inv_pos (by
    simp only [zero_mem_eq, decide_eq_true_eq] at z
    apply abs_pos_of_not_zero_mem z)
  bif x.lo.n.isNeg then -r else r

/-- `Interval.inv_pos` is conservative -/
@[mono] lemma approx_inv_pos {x : Interval} (l0 : 0 < x.lo.val) :
    (approx x)⁻¹ ⊆ approx (x.inv_pos l0) := by
  rw [inv_pos]
  have xn : x ≠ nan := by
    contrapose l0; simp only [ne_eq, not_not] at l0
    simp only [l0, lo_nan, not_lt, Floating.val_nan_lt_zero.le]
  have h0 := lt_of_lt_of_le l0 x.le
  have ie : (approx x)⁻¹ = Icc x.hi.val⁻¹ x.lo.val⁻¹ := by
    simp only [approx, lo_eq_nan, xn, ite_false, inv_Icc l0 h0]
  simp only [ie]
  apply Icc_subset_approx
  · exact Interval.approx_union_left (Around.mem _)
  · exact Interval.approx_union_right (Around.mem _)

/-- `Interval.inv` is conservative -/
@[mono] lemma approx_inv {x : Interval} : (approx x)⁻¹ ⊆ approx x.inv := by
  rw [inv]
  split_ifs with z
  · simp only [approx_nan, subset_univ]
  simp only [zero_mem_eq, decide_eq_true_eq] at z
  simp only [Floating.isNeg_iff, Bool.cond_decide]
  split_ifs with l0
  · have e : x = -x.abs := by
      rw [abs_of_nonpos, neg_neg]
      rw [lo_lt_zero_iff_hi_lt_zero z] at l0
      exact l0.le
    nth_rw 1 [e]
    simp only [approx_neg, Set.inv_neg, neg_subset_neg]
    apply approx_inv_pos
  · nth_rw 1 [←abs_of_nonneg (not_lt.mp l0)]
    apply approx_inv_pos

/-- `Interval.inv` is conservative, `mono ⊆` version -/
@[mono] lemma subset_approx_inv {p : Set ℝ} {x : Interval}
    (px : p ⊆ approx x) : p⁻¹ ⊆ approx x.inv :=
  subset_trans (inv_subset_inv.mpr px) Interval.approx_inv

/-- `Interval.inv` is conservative, `mono ∈` version -/
@[mono] lemma mem_approx_inv {p : ℝ} {x : Interval}
    (px : p ∈ approx x) : p⁻¹ ∈ approx x.inv :=
  Interval.approx_inv (inv_mem_inv.mpr px)

/-!
## `Interval` and `Box` division
-/

/-- `Interval` division via reciproval multiplication -/
instance : Div Interval where
  div x y := x * y.inv

/-- `Box / Interval` via reciproval multiplication -/
@[irreducible] def _root_.Box.div_scalar (z : Box) (x : Interval) : Box :=
  x.inv.mul_box z

lemma div_def (x y : Interval) : x / y = x * y.inv := rfl

/-- `Interval.div` is conservative -/
noncomputable instance : ApproxDiv Interval ℝ where
  approx_div x y := by
    rw [div_def, div_eq_mul_inv]; mono

/-- `Box / Interval` is conservative -/
@[mono] lemma _root_.Box.approx_div_scalar {z : Box} {x : Interval} :
    approx z / Complex.ofReal '' approx x ⊆ approx (z.div_scalar x) := by
  rw [Box.div_scalar, div_eq_inv_mul]
  refine subset_trans (mul_subset_mul ?_ subset_rfl) (Interval.approx_mul_box _ _)
  intro a
  simp only [Complex.ofReal_eq_coe, mem_inv, mem_image, forall_exists_index, and_imp]
  intro b m e
  use b⁻¹
  constructor
  · exact Interval.mem_approx_inv m
  · rw [Complex.ofReal_inv, e, inv_inv]

/-!
### Unit tests
-/

/-- We're don't verify anything about `inv_guess`, but we do need some tests -/
def guess_test (x : Float) (e : Float := 1e-10) : Bool :=
  ((inv_guess (.ofFloat x false : Floating) : Floating).toFloat - 1 / x).abs < e
example : guess_test 0.5 := by native_decide
example : guess_test 0.67862 := by native_decide
example : guess_test 0.999 (1e-9) := by native_decide
example : guess_test 0.67862 := by native_decide
example : guess_test 1e-4 := by native_decide
example : guess_test 7 := by native_decide

/-- `Interval.inv` is provably conservative, but we need to test that it's accurate -/
def inv_test (l h : Float) (e : Float := 1e-100) : Bool :=
  let x : Interval := ofFloat l ∪ ofFloat h
  let r := x.inv
  (r.lo.toFloat * h - 1).abs < e && (r.hi.toFloat * l - 1).abs ≤ e
example : inv_test 0.4 0.6 := by native_decide
example : inv_test 0.4871231 17.87341 := by native_decide
example : inv_test 0.001871 17.87341 1e-15 := by native_decide
example : inv_test (-0.6) (-0.4) 1e-100 := by native_decide
example : inv_test (-17.87341) (-0.4871231) := by native_decide
example : inv_test (-17.87341) (-0.001871) 1e-15 := by native_decide
example : inv_test 7 7 := by native_decide
