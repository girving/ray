import Mathlib.Data.Real.Basic
import Ray.Approx.Approx
import Ray.Approx.Float
import Ray.Approx.Int
import Ray.Approx.Int64
import Ray.Approx.UInt128

/-!
## 64-bit fixed point numbers
-/

open Pointwise
open Set
open scoped Real

variable {s t : Int64}

/-!
### `Fixed` definitions and basics
-/

/-- A 64-bit fixed point number, corresponding to either
    1. `n * 2^s`, if `n ≠ nan`
    2. Arbitrary, if `n = nan` -/
structure Fixed (s : Int64) where
  n : Int64
  deriving DecidableEq, BEq

/-- Sentinel value, indicating we don't know what the number is -/
def nan : Fixed s := ⟨.min⟩

/-- Reduce `Fixed s` equality to `Int64` equality -/
lemma Fixed.ext_iff (x y : Fixed s) : x = y ↔ x.n = y.n := by
  induction' x with x; induction' y with y; simp only [mk.injEq]

/-- `Fixed s` has nice equality -/
instance : LawfulBEq (Fixed s) where
  eq_of_beq {x y} e := by
    simp only [BEq.beq] at e
    rw [Fixed.ext_iff, Int64.ext_iff]
    rw [eq_of_beq e]
  rfl {x} := beq_self_eq_true' x.n.n

/-- The `ℝ` that a `Fixed` represents, if it's not `nan` -/
@[pp_dot] noncomputable def Fixed.val (x : Fixed s) :=
  ((x.n : ℤ) : ℝ) * (2 : ℝ)^(s : ℤ)

/-- Approximate `Fixed s` by a `Float` -/
@[pp_dot] def Fixed.toFloat (x : Fixed s) :=
  bif x == nan then Float.nan else x.n.toFloat.scaleB s

/-- We print `Fixed s` as an approximate floating point number -/
instance : Repr (Fixed s) where
  reprPrec x p := reprPrec x.toFloat p

/-- `0` is easy regardless of `s` -/
instance : Zero (Fixed s) where
  zero := ⟨0⟩

lemma Fixed.zero_def : (0 : Fixed s) = ⟨0⟩ := rfl
@[simp] lemma Fixed.zero_n : (0 : Fixed s).n = 0 := rfl

@[simp] lemma Fixed.val_zero : (0 : Fixed s).val = 0 := by
  simp only [val, zero_def, Int64.coe_zero, Int.cast_zero, zero_mul]

@[simp] lemma Fixed.isNeg_nan : (nan : Fixed s).n.isNeg = true := rfl

@[simp] lemma Fixed.zero_ne_nan : 0 ≠ (nan : Fixed s) := by
  simp only [nan, ne_eq, Fixed.ext_iff, Fixed.zero_n, Int64.ext_iff, Int64.n_zero, Int64.n_min,
    Nat.cast_pow, Nat.cast_ofNat]
  decide
@[simp] lemma Fixed.nan_ne_zero : (nan : Fixed s) ≠ 0 := by rw [ne_comm]; exact zero_ne_nan

/-!
### Additive group operations: `add, sub, neg`
-/

/-- `Fixed` negation -/
def Fixed.neg (x : Fixed s) : Fixed s := ⟨-x.n⟩
instance : Neg (Fixed s) where neg x := x.neg
lemma Fixed.neg_def (x : Fixed s) : -x = x.neg := rfl

/-- `-nan = nan` -/
@[simp] lemma Fixed.neg_nan : -(nan : Fixed s) = nan := by
  simp only [nan, neg_def, neg, Int64.neg_def, Int64.n_min, Nat.cast_pow, Nat.cast_ofNat, ext_iff]
  decide

/-- `Fixed` addition saturates to `nan` -/
def Fixed.add (x y : Fixed s) :=
  let z : Fixed s := ⟨x.n + y.n⟩
  bif x == nan || y == nan || (x.n.isNeg == y.n.isNeg && x.n.isNeg != z.n.isNeg) then nan else z
instance : Add (Fixed s) where add x y := x.add y
lemma Fixed.add_def (x y : Fixed s) : x + y = x.add y := rfl

/-- `Fixed` subtraction saturates to `nan` -/
def Fixed.sub (x y : Fixed s) :=
  let z : Fixed s := ⟨x.n - y.n⟩
  bif x == nan || y == nan || (x.n.isNeg != y.n.isNeg && x.n.isNeg != z.n.isNeg) then nan else z
instance : Sub (Fixed s) where sub x y := x.sub y
lemma Fixed.sub_def (x y : Fixed s) : x - y = x.sub y := rfl

/-- `Fixed` addition with fewer bools -/
lemma Fixed.add_as_eq (x y : Fixed s) : x + y = (
    let z : Fixed s := ⟨x.n + y.n⟩
    if x = nan ∨ y = nan ∨ (x.n.isNeg = y.n.isNeg ∧ x.n.isNeg ≠ z.n.isNeg) then nan else z) := by
  simp only [Fixed.add_def, add, bif_eq_if]
  simp only [bne, Bool.or_assoc, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq]

/-- `-(-x) = x` -/
instance : InvolutiveNeg (Fixed s) where
  neg_neg x := by induction' x with x; simp only [Fixed.neg_def, Fixed.neg, _root_.neg_neg]

/-- Negation preserves `nan` -/
@[simp] lemma Fixed.neg_eq_nan {x : Fixed s} : (-x) = nan ↔ x = nan := by
  have i : ∀ {x : Fixed s}, x = nan → (-x) = nan := by
    intro x h
    simp only [h, nan, neg_def, neg, Int64.neg_def, Int64.n_min, Nat.cast_pow, Nat.cast_ofNat,
      mk.injEq]
    decide
  by_cases a : x = nan
  · simp only [a, neg_nan]
  · by_cases b : (-x) = nan
    · rw [b, ←neg_neg x, i b]
    · simp only [a, b]

/-- Negation preserves `nan` -/
@[simp] lemma Fixed.neg_beq_nan {x : Fixed s} : ((-x) == nan) = (x == nan) := by
  simp only [Bool.beq_eq_decide_eq', neg_eq_nan]

/-- Negation flips `isNeg` unless we're `0` or `nan` -/
lemma Fixed.isNeg_neg {x : Fixed s} (x0 : x.n ≠ 0) (xn : x ≠ nan) : (-x.n).isNeg = !x.n.isNeg := by
  apply Int64.isNeg_neg x0
  simp only [Ne.def, Fixed.ext_iff] at xn
  exact xn

/-- `x - y = x + (-y)` -/
lemma Fixed.sub_eq_add_neg (x y : Fixed s) : x - y = x + (-y) := by
  simp only [sub_def, sub, Bool.cond_eq_ite, Bool.beq_eq_decide_eq', Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, add_def, add, neg_eq_nan]
  by_cases nx : x = nan
  · simp only [nx, true_or, ite_true]
  by_cases ny : y = nan
  · simp only [ny, or_true, true_or, ite_true, neg_nan]
  simp only [nx, ny, Bool.or_self, Bool.false_or, neg_def, neg]
  by_cases y0 : y.n = 0
  · simp only [y0, Int64.isNeg_zero, Bool.not_eq_false, sub_zero, not_true, and_false, or_self,
      ite_false, neg_zero, add_zero]
  · simp only [_root_.sub_eq_add_neg, false_or, Fixed.isNeg_neg y0 ny, Bool.beq_not_iff_ne, ne_eq]

lemma Fixed.add_comm (x y : Fixed s) : x + y = y + x := by
  simp only [Fixed.add_as_eq, add, _root_.add_comm]
  refine if_congr ?_ rfl rfl
  by_cases xn : x = nan
  · by_cases yn : y = nan
    · simp only [xn, yn, ne_eq, true_and, true_or, or_self]
    · simp only [xn, ne_eq, true_or, or_true]
  · by_cases yn : y = nan
    · simp only [yn, ne_eq, true_or, or_true]
    · simp only [xn, yn, ne_eq, false_or]
      by_cases x0 : x.n.isNeg; repeat {
        by_cases y0 : y.n.isNeg
        repeat simp only [x0, y0, true_and, false_and] }

-- Addition and subtraction propagate nans
@[simp] lemma Fixed.nan_add {x : Fixed s} : nan + x = nan := by
  simp only [add_def, add, beq_self_eq_true, Bool.true_or, cond_true]
@[simp] lemma Fixed.add_nan {x : Fixed s} : x + nan = nan := by rw [Fixed.add_comm]; rfl
@[simp] lemma Fixed.nan_sub {x : Fixed s} : nan - x = nan := by simp only [sub_eq_add_neg, nan_add]
@[simp] lemma Fixed.sub_nan {x : Fixed s} : x - nan = nan := by
  simp only [sub_eq_add_neg, neg_nan, add_nan]

/-- If `x + y ≠ nan`, neither `x` or `y` are `nan` -/
lemma Fixed.ne_nan_of_add {x y : Fixed s} (h : x + y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose h; simp only [not_and_or, not_not] at h
  cases' h with h h
  · simp only [h, nan_add, ne_eq, not_true, not_false_eq_true]
  · simp only [h, add_nan, ne_eq, not_true, not_false_eq_true]

/-- `Fixed.val` commutes with negation, except at `nan` -/
lemma Fixed.val_neg {x : Fixed s} (xn : x ≠ nan) : (-x).val = -x.val := by
  simp only [Ne.def, Fixed.ext_iff, nan] at xn
  simp only [val, neg_def, neg, Int64.coe_neg xn, Int.cast_neg, neg_mul]

/-- `Fixed.val` commutes with add if `isNeg` matches the left argument -/
lemma Fixed.val_add_eq {x y : Fixed s} (h : (x.n + y.n).isNeg = x.n.isNeg) :
    (⟨x.n + y.n⟩ : Fixed s).val = x.val + y.val := by
  simp only [val, Int64.coe_add_eq h, Int.cast_add, add_mul]

/-- `Fixed.val` commutes with add if the two arguments have different `isNeg`s -/
lemma Fixed.val_add_ne {x y : Fixed s} (h : x.n.isNeg ≠ y.n.isNeg) :
    (⟨x.n + y.n⟩ : Fixed s).val = x.val + y.val := by
  simp only [val, Int64.coe_add_ne h, Int.cast_add, add_mul]

/-- `Fixed` approximates `ℝ` -/
instance : Approx (Fixed s) ℝ where
  approx x := if x = nan then univ else {x.val}

lemma Fixed.val_mem_approx {x : Fixed s} : x.val ∈ approx x := by
  simp only [approx]; split_ifs; repeat simp

@[simp] lemma Fixed.approx_zero : approx (0 : Fixed s) = {0} := by
  simp only [approx, nan, ext_iff, zero_n, Int64.zero_def, Int64.ext_iff, Int64.n_min, Nat.cast_pow,
    Nat.cast_ofNat, val_zero, ite_eq_right_iff]
  intro h; contrapose h; decide

/-- `Fixed` negation respects `approx` -/
instance : ApproxNeg (Fixed s) ℝ where
  approx_neg x := by
    simp only [approx, ge_iff_le, not_le, gt_iff_lt, Bool.cond_eq_ite, Bool.or_eq_true, beq_iff_eq,
      image_neg, Fixed.neg_eq_nan, or_comm, Fixed.neg_eq_nan]
    by_cases h : x = nan
    · simp only [h, ite_true, neg_univ, Fixed.neg_nan, subset_univ]
    · simp only [h, ite_false, neg_singleton, Fixed.val_neg h, subset_refl]

/-- `Fixed` addition respects `approx` -/
instance : ApproxAdd (Fixed s) ℝ where
  approx_add x y := by
    simp only [Fixed.add_as_eq, approx]
    by_cases xn : x = nan
    · simp only [xn, ite_true, image2_add, ne_eq, true_or, subset_univ]
    · by_cases yn : y = nan
      · simp only [yn, ite_true, image2_add, ne_eq, true_or, or_true, subset_univ]
      · simp only [xn, ite_false, yn, image2_singleton_right, image_singleton, ne_eq, false_or,
          ite_eq_left_iff, not_and, not_not, singleton_subset_iff, mem_ite_univ_left, not_forall,
          exists_prop, mem_singleton_iff, and_imp]
        by_cases x0 : x.n.isNeg
        · by_cases z0 : (x.n + y.n).isNeg
          · simp only [add_singleton, image_singleton, x0, z0, forall_true_left, not_true,
              and_false, ite_false, Fixed.val_add_eq (z0.trans x0.symm), singleton_subset_iff,
              mem_ite_univ_left, mem_singleton_iff, implies_true]
          · by_cases y0 : y.n.isNeg
            · simp only [add_singleton, image_singleton, x0, y0, z0, forall_true_left,
                IsEmpty.forall_iff, not_false_eq_true, and_self, ite_true, subset_univ]
            · simp only [add_singleton, image_singleton, x0, y0, IsEmpty.forall_iff,
                forall_true_left, false_and, ite_false, Fixed.val_add_ne (x0.trans_ne (Ne.symm y0)),
                singleton_subset_iff, mem_ite_univ_left, mem_singleton_iff, implies_true]
        · by_cases y0 : y.n.isNeg
          · simp only [add_singleton, image_singleton, x0, y0, IsEmpty.forall_iff,
              forall_true_left, false_and, ite_false, Fixed.val_add_ne (Ne.trans_eq x0 y0.symm),
              singleton_subset_iff, mem_ite_univ_left, mem_singleton_iff, implies_true]
          · by_cases z0 : (x.n + y.n).isNeg
            · simp only [add_singleton, image_singleton, x0, y0, z0, forall_true_left,
                IsEmpty.forall_iff, not_false_eq_true, and_self, ite_true, subset_univ]
            · simp only [Bool.not_eq_true] at x0 z0
              simp only [add_singleton, image_singleton, x0, y0, z0, forall_true_left, not_true,
                and_false, ite_false, Fixed.val_add_eq (z0.trans x0.symm), singleton_subset_iff,
                mem_ite_univ_left, mem_singleton_iff, implies_true]

/-- `Fixed.val` commutes with add if the result isn't `nan` -/
lemma Fixed.val_add_of_ne_nan {x y : Fixed s} (n : x + y ≠ nan) : (x + y).val = x.val + y.val := by
  have h := image2_subset_iff.mp (approx_add x y) x.val val_mem_approx y.val val_mem_approx
  simp only [approx, n, ite_false, mem_singleton_iff] at h
  rw [h]

/-- `Fixed` subtraction respects `approx` -/
instance : ApproxSub (Fixed s) ℝ where
  approx_sub x y := by
    simp only [Fixed.sub_eq_add_neg, sub_eq_add_neg]
    exact subset_trans (add_subset_add_left (approx_neg _)) (approx_add x (-y))

/-- `Fixed.val` commutes with sub if the result isn't `nan` -/
lemma Fixed.val_sub_of_ne_nan {x y : Fixed s} (n : x - y ≠ nan) : (x - y).val = x.val - y.val := by
  have h := image2_subset_iff.mp (approx_sub x y) x.val val_mem_approx y.val val_mem_approx
  simp only [approx, n, ite_false, mem_singleton_iff] at h
  rw [h]

/-- `Fixed` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup (Fixed s) ℝ where

/-!
### Order operations on `Fixed`: min, max, abs
-/

lemma Fixed.val_lt_zero {x : Fixed s} : x.val < 0 ↔ x.n.isNeg := by
  have b : 0 < (2:ℝ)^(s:ℤ) := zpow_pos_of_pos (by norm_num) _
  simp only [val, mul_neg_iff, Int.cast_pos, not_lt.mpr b.le, and_false, Int.cast_lt_zero,
    Int64.coe_lt_zero_iff, b, and_true, false_or]

lemma Fixed.val_nonneg {x : Fixed s} : 0 ≤ x.val ↔ x.n.isNeg = false := by
  rw [←not_iff_not]; simp only [not_le, val_lt_zero, Bool.not_eq_false]

instance : Min (Fixed s) where
  min x y := ⟨min x.n y.n⟩

instance : Max (Fixed s) where
  max x y := -min (-x) (-y)  -- Use `min` so that `nan` propagates

@[pp_dot] def Fixed.abs (x : Fixed s) : Fixed s :=
  ⟨⟨x.n.abs⟩⟩

@[simp] lemma Fixed.abs_nan : (nan : Fixed s).abs = nan := by
  simp only [abs, Int64.abs, ext_iff, Int64.ext_iff, nan]
  decide

@[simp] lemma Fixed.abs_eq_nan {x : Fixed s} : x.abs = nan ↔ x = nan := by
  simp only [abs, Int64.abs, nan, ext_iff, Int64.ext_iff, Int64.n_min, Nat.cast_pow, Nat.cast_ofNat,
    UInt64.eq_iff_toNat_eq, UInt64.toNat_2_pow_63]
  by_cases n : x.n.isNeg
  · simp only [n, cond_true, UInt64.toNat_neg, ge_iff_le]
    generalize x.n.n = n
    by_cases n0 : n = 0
    · simp only [n0, UInt64.toNat_zero, ge_iff_le, tsub_zero, ite_true]
    · simp only [n0, ge_iff_le, ite_false]
      zify
      simp only [Nat.cast_sub (UInt64.le_size _)]
      simp only [UInt64.size_eq_pow, Nat.cast_pow, Nat.cast_ofNat]
      constructor; repeat { intro h; linarith }
  · simp only [n, cond_false]

@[simp] lemma Fixed.isNeg_abs {x : Fixed s} : x.abs.n.isNeg = (x == nan) := by
  have b : 0 < (2:ℝ)^(s:ℤ) := zpow_pos_of_pos (by norm_num) _
  rw [Bool.eq_iff_iff, ← val_lt_zero, beq_iff_eq]
  simp only [val, abs, mul_neg_iff, Int.cast_pos, not_lt.mpr b.le, and_false, Int.cast_lt_zero,
    Int64.abs_lt_zero, b, and_true, false_or, nan, ext_iff]

lemma Fixed.val_abs {x : Fixed s} (n : x ≠ nan) : x.abs.val = |x.val| := by
  simp only [val, abs_mul, abs_zpow, abs_two, mul_eq_mul_right_iff]
  left
  simp only [nan, ne_eq, ext_iff] at n
  simp only [abs, ←Int.cast_abs, Int.cast_inj, Int64.coe_abs' n]

lemma Fixed.approx_abs_eq {x : Fixed s} (n : x ≠ nan) : approx x.abs = {|x.val|} := by
  simp only [approx, abs_eq_nan, n, Fixed.val_abs n, ite_false]

lemma Fixed.approx_abs (x : Fixed s) : image (fun x ↦ |x|) (approx x) ⊆ approx x.abs := by
  by_cases n : x = nan
  · simp only [approx, n, ite_true, image_univ, abs_nan, subset_univ]
  · simp only [approx, n, ite_false, image_singleton, abs_eq_nan, subset_singleton_iff,
      mem_singleton_iff, forall_eq, val_abs n]

@[simp] lemma Fixed.min_eq_nan {x y : Fixed s} : min x y = nan ↔ x = nan ∨ y = nan := by
  simp only [min, Int64.blt_eq_decide_lt, bif_eq_if, decide_eq_true_eq, nan, ext_iff,
    Int64.eq_min_iff_min_lt]
  split_ifs with xy
  · constructor
    · intro h; exact Or.inl h
    · intro h; cases' h with h h
      · exact h
      · exact le_trans xy.le h
  · simp only [not_lt] at xy
    constructor
    · intro h; exact Or.inr h
    · intro h; cases' h with h h
      · exact le_trans xy h
      · exact h

@[simp] lemma Fixed.max_eq_nan {x y : Fixed s} : max x y = nan ↔ x = nan ∨ y = nan := by
  simp only [max, neg_eq_nan, min_eq_nan]

lemma Fixed.val_lt_val {x y : Fixed s} : x.val < y.val ↔ x.n < y.n := by
  rw [val, val, mul_lt_mul_right]
  · simp only [Int.cast_lt, Int64.coe_lt_coe]
  · exact zpow_pos_of_pos (by norm_num) _

lemma Fixed.val_le_val {x y : Fixed s} : x.val ≤ y.val ↔ x.n ≤ y.n := by
  rw [val, val, mul_le_mul_right]
  · simp only [Int.cast_le, Int64.coe_le_coe]
  · exact zpow_pos_of_pos (by norm_num) _

@[simp] lemma Fixed.val_min {x y : Fixed s} : (min x y).val = min x.val y.val := by
  simp only [min, Int64.blt_eq_decide_lt, Bool.cond_decide]
  split_ifs with h
  · simp only [left_eq_inf, Fixed.val_le_val]; exact h.le
  · simp only [not_lt] at h; simp only [right_eq_inf, val_le_val]; exact h

lemma Fixed.val_max {x y : Fixed s} (nx : x ≠ nan) (ny : y ≠ nan) :
    (max x y).val = max x.val y.val := by
  have n : min (-x) (-y) ≠ nan := by
    simp only [ne_eq, min_eq_nan, neg_eq_nan, nx, ny, or_self, not_false_eq_true]
  simp only [max, val_neg n, val_min, val_neg nx, val_neg ny, min_neg_neg, neg_neg]

/-!
### `Fixed` multiplication, rounding up or down
-/

/-- Cast a `UInt128` to `Fixed s`, ignoring `s`.  Too large values become `nan`. -/
def Fixed.of_raw_uint128 (n : UInt128) : Fixed s :=
  bif n.hi != 0 || (⟨n.lo⟩ : Int64).isNeg then nan else ⟨⟨n.lo⟩⟩

/-- If `of_raw_uint128 ≠ nan`, the input is small -/
lemma Fixed.lt_of_of_raw_uint128_ne_nan {n : UInt128} {s : Int64}
    (h : (of_raw_uint128 n : Fixed s) ≠ nan) : n.toNat < 2^63 := by
  simp only [of_raw_uint128, Int64.isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
    UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63, bif_eq_if, Bool.or_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, ite_eq_left_iff, not_or, not_not, not_le, and_imp, not_forall, exists_prop,
    exists_and_left] at h
  rw [UInt128.toNat, h.1]
  simp only [UInt64.toNat_zero, zero_mul, zero_add, h.2.1]

/-- Multiply two positive, non-nan `Fixed`s -/
def Fixed.mul_of_pos (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) : Fixed u :=
  let d : Fixed 0 := ⟨s⟩ + ⟨t⟩ - ⟨u⟩
  bif d == nan then nan else
  let z := mul128 x.n.n y.n.n
  of_raw_uint128 (bif d.n.isNeg then z.shiftRightRound (-d.n).n up else z.shiftLeftSaturate d.n.n)

/-- Multiply, changing `s` and rounding up or down.  We have
  `z = x * y`
  `z.n * 2^u = x.n * y.n * 2^(s + t)`
  `z.n = x.n * y.n * 2^(s + t - u)` -/
def Fixed.mul (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) : Fixed u :=
  bif x == nan || y == nan then nan else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_pos x.abs y.abs u (up.xor p)
  bif p then -z else z

lemma Fixed.of_raw_uint128_val {n : UInt128} (h : (of_raw_uint128 n : Fixed s) ≠ nan) :
    (of_raw_uint128 n : Fixed s).val = (n : ℝ) * (2:ℝ)^(s : ℤ) := by
  simp only [of_raw_uint128, bif_eq_if, Bool.or_eq_true, bne_iff_ne, ne_eq, ite_eq_left_iff, not_or,
    not_not, Bool.not_eq_true, and_imp, not_forall, exists_prop, exists_and_left] at h
  simp only [val, Int64.toInt, of_raw_uint128, h.1, bne_self_eq_false, h.2.1, Bool.or_self,
    bif_eq_if, ite_false, CharP.cast_eq_zero, sub_zero, Int.cast_ofNat, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat, UInt128.toReal, UInt128.toNat, UInt64.toNat_zero, zero_mul, zero_add]

/-- If we're not `nan`, `shiftLeftSaturate` is nice -/
lemma Fixed.toNat_shiftLeftSaturate_of_ne_nan {x : UInt128} {s : UInt64} {t : Int64}
    (h : (of_raw_uint128 (x.shiftLeftSaturate s) : Fixed t) ≠ nan) :
    (x.shiftLeftSaturate s).toNat = x.toNat * 2 ^ s.toNat := by
  replace h := Fixed.lt_of_of_raw_uint128_ne_nan h
  simp only [UInt128.shiftLeftSaturate_eq, UInt128.toNat_ofNat, UInt128.toNat_max] at h ⊢
  generalize hn : x.toNat * 2 ^ s.toNat = n
  rw [hn] at h
  clear hn t s x
  have lt : min n (2 ^ 128 - 1) < 2^128 := min_lt_of_right_lt (by norm_num)
  simp only [ge_iff_le, tsub_le_iff_right, Nat.mod_eq_of_lt lt, min_lt_iff, or_false,
    min_eq_left_iff] at h ⊢
  norm_num at h
  exact le_trans h.le (by norm_num)

/-- `Fixed.mul_of_pos` respects `approx` -/
lemma Fixed.approx_mul_of_pos (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool)
    (xn : x ≠ nan) (yn : y ≠ nan) (xp : x.n.isNeg = false) (yp : y.n.isNeg = false) :
    approx x * approx y ⊆ rounds (approx (mul_of_pos x y u up)) !up := by
  have two0 : (2 : ℝ) ≠ 0 := by norm_num
  have twop : ∀ {x : ℤ}, (2:ℝ)^x ≠ 0 := fun {_} ↦ zpow_ne_zero _ (by norm_num)
  simp only [image2_mul, mul_of_pos, bif_eq_if, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]
  generalize hd : (⟨s⟩ + ⟨t⟩ - ⟨u⟩ : Fixed 0) = d
  generalize hw : (x.n.n.toNat : ℝ) * y.n.n.toNat = w
  have wa : (mul128 x.n.n y.n.n : ℝ) = w := by
    simp only [UInt128.toReal, toNat_mul128, Nat.cast_mul, hw]
  by_cases dn : d = nan
  · simp only [approx, dn, ite_true, rounds_univ, subset_univ]
  · simp only [dn, ite_false]
    have de : (d.n : ℤ) = ↑s + ↑t - ↑u := by
      have e : d.val = s + t - u := by
        simp only [←hd] at dn
        by_cases stn : (⟨s⟩ + ⟨t⟩ : Fixed 0) = nan
        · simp only [stn, nan_sub, not_true] at dn
        · simp only [← hd, Fixed.val_sub_of_ne_nan dn, Fixed.val_add_of_ne_nan stn]
          simp only [val, Int64.coe_zero, zpow_zero, mul_one]
      simpa only [val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_add, ←Int.cast_sub,
        Int.cast_inj] using e
    by_cases ds : d.n.isNeg
    · have dn : (2:ℝ) ^ (-d.n).n.toNat = (2:ℝ) ^ ((u:ℤ) - ↑s - ↑t) := by
        suffices h : ↑(-d.n).n.toNat = -(d.n : ℤ) by
          rw [←zpow_ofNat, h, de, neg_sub, sub_add_eq_sub_sub]
        by_cases z : d.n = 0
        · simp only [z, Int64.isNeg_zero] at ds
        · simp only [Int64.zero_def, Int64.ext_iff] at z
          simp only [Int64.neg_def, UInt64.toNat_neg, z, ge_iff_le, ite_false, UInt64.le_size,
            Nat.cast_sub, Int64.toInt, ds, cond_true, Nat.cast_pow, Nat.cast_ofNat, neg_sub,
            sub_left_inj]
          norm_num
      generalize hz : (mul128 x.n.n y.n.n).shiftRightRound (-d.n).n up = z
      have za := UInt128.approx_shiftRightRound (mul128 x.n.n y.n.n) (-d.n).n up
      simp only [hz, wa, dn] at za
      clear hz
      simp only [approx, xn, ite_false, yn, mul_singleton, image_singleton, ds, ite_true,
        apply_ite (f := fun x ↦ rounds x !up), rounds_univ, singleton_subset_iff, mem_ite_univ_left,
        mem_rounds_singleton]
      intro zn
      simp only [Fixed.of_raw_uint128_val zn]
      simp only [Fixed.val, ←mul_assoc, mul_comm _ ((2:ℝ)^(t : ℤ))]
      simp only [←mul_assoc, mul_comm _ ((2:ℝ)^(s : ℤ)), Int64.toReal_toInt xp,
        Int64.toReal_toInt yp]
      simp only [mul_assoc, hw]
      induction up
      · simp only [rounds, mem_singleton_iff, ite_false, exists_eq_left, mem_setOf_eq,
          ite_true] at za ⊢
        refine le_trans (mul_le_mul_of_nonneg_right za (zpow_nonneg (by norm_num) _)) (le_of_eq ?_)
        simp only [zpow_sub₀ two0, div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv, ne_eq,
          inv_mul_cancel twop, mul_one]
        ring
      · simp only [rounds, mem_singleton_iff, ite_true, exists_eq_left, mem_setOf_eq,
          ite_false] at za ⊢
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right za (zpow_nonneg (by norm_num) _))
        simp only [zpow_sub₀ two0, div_eq_mul_inv, mul_assoc, mul_inv_rev, inv_inv, ne_eq,
          inv_mul_cancel twop, mul_one]
        ring
    · have dn : (2:ℝ) ^ d.n.n.toNat = (2:ℝ) ^ ((s:ℤ) + ↑t - ↑u) := by
        suffices h : ↑d.n.n.toNat = (d.n : ℤ) by rw [←zpow_ofNat, h, de]
        simp only [Int64.toInt, ds, cond_false, CharP.cast_eq_zero, sub_zero]
      simp only [approx, xn, ite_false, yn, mul_singleton, image_singleton, ds,
        apply_ite (f := fun x ↦ rounds x !up), rounds_univ, singleton_subset_iff, mem_ite_univ_left,
        mem_rounds_singleton, Bool.not_eq_true']
      intro zn
      simp only [UInt128.toReal] at wa
      simp only [Fixed.of_raw_uint128_val zn, UInt128.toReal, Nat.cast_mul,
        Fixed.toNat_shiftLeftSaturate_of_ne_nan zn, wa, Nat.cast_pow, Nat.cast_two]
      simp only [Fixed.val, ←mul_assoc, mul_comm _ ((2:ℝ)^(t : ℤ))]
      simp only [←mul_assoc, mul_comm _ ((2:ℝ)^(s : ℤ)), Int64.toReal_toInt xp,
        Int64.toReal_toInt yp]
      simp only [mul_assoc, hw, dn, zpow_add₀ two0, zpow_sub₀ two0, div_mul_cancel _ twop]
      simp only [←mul_assoc, mul_comm _ w, le_refl, ite_self]

/-- `Fixed.mul_of_pos` respects `approx` -/
lemma Fixed.approx_mul_abs {x : Fixed s} {y : Fixed t} {u : Int64} {up : Bool}
    (xn : x ≠ nan) (yn : y ≠ nan) :
    approx x.abs * approx y.abs ⊆ rounds (approx (mul_of_pos x.abs y.abs u up)) !up := by
  apply approx_mul_of_pos
  · rw [Ne.def, abs_eq_nan]; exact xn
  · rw [Ne.def, abs_eq_nan]; exact yn
  · simp only [isNeg_abs, beq_eq_false_iff_ne, ne_eq, xn, not_false_eq_true]
  . simp only [isNeg_abs, beq_eq_false_iff_ne, ne_eq, yn, not_false_eq_true]

 /-- If signs are equal, `*` is `abs * abs`-/
lemma mul_of_isNeg_eq {x : Fixed s} {y : Fixed t} (xn : x ≠ nan) (yn : y ≠ nan)
    (p : x.n.isNeg = y.n.isNeg) : approx x * approx y = approx x.abs * approx y.abs := by
  simp only [approx, xn, ite_false, yn, mul_singleton, image_singleton, Fixed.abs_eq_nan,
    Fixed.val_abs xn, Fixed.val_abs yn, singleton_eq_singleton_iff]
  have y0 := p.symm
  by_cases x0 : x.n.isNeg
  · simp only [x0] at y0
    simp only [abs_of_neg (Fixed.val_lt_zero.mpr x0), abs_of_neg (Fixed.val_lt_zero.mpr y0),
      mul_neg, neg_mul, neg_neg]
  · simp only [Bool.not_eq_true] at x0
    simp only [x0] at y0
    simp only [abs_of_nonneg (Fixed.val_nonneg.mpr x0), abs_of_nonneg (Fixed.val_nonneg.mpr y0)]

 /-- If signs are different, `*` is `-(abs * abs)`-/
lemma mul_of_isNeg_ne {x : Fixed s} {y : Fixed t} (xn : x ≠ nan) (yn : y ≠ nan)
    (p : x.n.isNeg ≠ y.n.isNeg) : approx x * approx y = -(approx x.abs * approx y.abs) := by
  simp only [approx, xn, ite_false, yn, mul_singleton, image_singleton, Fixed.abs_eq_nan,
    Fixed.val_abs xn, Fixed.val_abs yn, neg_singleton, singleton_eq_singleton_iff]
  have y0 := p.symm
  by_cases x0 : x.n.isNeg
  · simp only [x0, ne_eq, Bool.not_eq_true] at y0
    simp only [abs_of_neg (Fixed.val_lt_zero.mpr x0), abs_of_nonneg (Fixed.val_nonneg.mpr y0),
      neg_mul, neg_neg]
  · simp only [Bool.not_eq_true] at x0
    simp only [x0, ne_eq, Bool.not_eq_false] at y0
    simp only [abs_of_nonneg (Fixed.val_nonneg.mpr x0), abs_of_neg (Fixed.val_lt_zero.mpr y0),
      mul_neg, neg_neg]

/-- `Fixed.mul` respects `approx` -/
lemma Fixed.approx_mul (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) :
    approx x * approx y ⊆ rounds (approx (x.mul y u up)) !up := by
  simp only [mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ite_not, or_assoc]
  by_cases n : x = nan ∨ y = nan
  · simp only [approx, mul_ite, ite_mul, univ_mul_univ, singleton_mul, image_univ, mul_singleton,
      image_singleton, n, ite_true, rounds_univ, subset_univ]
  · simp only [n, ite_false]
    simp only [not_or, ←Ne.def] at n
    by_cases p : x.n.isNeg = y.n.isNeg
    · simp only [mul_of_isNeg_eq n.1 n.2 p, p, bne_self_eq_false, Bool.xor_false, ite_true]
      exact approx_mul_abs n.1 n.2
    · have p' : x.n.isNeg != y.n.isNeg := by simpa only [bne_iff_ne, ne_eq]
      simp only [ne_eq, p, not_false_eq_true, mul_of_isNeg_ne n.1 n.2, p', Bool.xor_true, ite_false]
      refine subset_trans ?_ (rounds_mono (approx_neg _))
      simp only [rounds_neg, neg_subset_neg]
      exact approx_mul_abs n.1 n.2

/-- `Fixed.mul nan _ _ _ = nan` -/
@[simp] lemma Fixed.nan_mul {y : Fixed t} {u : Int64} {up : Bool} :
    Fixed.mul (nan : Fixed s) y u up = nan := by
  simp only [mul, beq_self_eq_true, Bool.true_or, isNeg_nan, Bool.true_xor, abs_nan, Bool.cond_not,
    cond_true]

/-- `Fixed.mul nan _ _ _ = nan` -/
@[simp] lemma Fixed.mul_nan {x : Fixed s} {u : Int64} {up : Bool} :
    Fixed.mul x (nan : Fixed t) u up = nan := by
  simp only [mul, beq_self_eq_true, Bool.or_true, isNeg_nan, Bool.xor_true, abs_nan, Bool.cond_not,
    cond_true]

/-- `Fixed.approx_mul` in plainer form (down version) -/
lemma Fixed.mul_le {x : Fixed s} {y : Fixed t} {u : Int64} (n : Fixed.mul x y u false ≠ nan) :
    (Fixed.mul x y u false).val ≤ x.val * y.val := by
  have h := approx_mul x y u false
  by_cases m : x = nan ∨ y = nan
  · rcases m with m | m; repeat simp only [m, nan_mul, mul_nan, ne_eq, not_true_eq_false] at n
  simp only [not_or] at m
  simpa only [approx, m.1, ite_false, m.2, mul_singleton, image_singleton, rounds, n,
    mem_singleton_iff, Bool.not_false, ite_true, exists_eq_left, singleton_subset_iff,
    mem_setOf_eq] using h

/-- `Fixed.approx_mul` in plainer form (up version) -/
lemma Fixed.le_mul {x : Fixed s} {y : Fixed t} {u : Int64} (n : Fixed.mul x y u true ≠ nan) :
    x.val * y.val ≤ (Fixed.mul x y u true).val := by
  have h := approx_mul x y u true
  by_cases m : x = nan ∨ y = nan
  · rcases m with m | m; repeat simp only [m, nan_mul, mul_nan, ne_eq, not_true_eq_false] at n
  simp only [not_or] at m
  simpa only [approx, m.1, ite_false, m.2, mul_singleton, image_singleton, rounds, n,
    mem_singleton_iff, Bool.not_true, exists_eq_left, singleton_subset_iff, mem_setOf_eq] using h
