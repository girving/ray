import Mathlib.Data.Real.Basic
import Ray.Approx.Approx
import Ray.Approx.Float
import Ray.Approx.Int64
import Ray.Approx.UInt128
import Ray.Misc.Int
import Ray.Misc.Real

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
instance : Nan (Fixed s) where
  nan := ⟨.min⟩

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
  reprPrec x _ := x.toFloat.toStringFull

/-- `0` is easy regardless of `s` -/
instance : Zero (Fixed s) where
  zero := ⟨0⟩

lemma Fixed.zero_def : (0 : Fixed s) = ⟨0⟩ := rfl
lemma Fixed.nan_def : (nan : Fixed s) = ⟨Int64.min⟩ := rfl
@[simp] lemma Fixed.zero_n : (0 : Fixed s).n = 0 := rfl
@[simp] lemma Fixed.nan_n : (nan : Fixed s).n = Int64.min := rfl

@[simp] lemma Fixed.val_zero : (0 : Fixed s).val = 0 := by
  simp only [val, zero_def, Int64.coe_zero, Int.cast_zero, zero_mul]

lemma Fixed.val_of_s0 {x : Fixed 0} : x.val = ↑x.n := by
  simp only [val, Int64.coe_zero, zpow_zero, mul_one]

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

/-- The contrapose of `-nan = nan` -/
@[simp] lemma Fixed.ne_nan_of_neg {x : Fixed s} (h : -x ≠ nan) : x ≠ nan := by
  contrapose h
  simp only [ne_eq, not_not] at h
  simp only [h, neg_nan, ne_eq, not_true_eq_false, not_false_eq_true]

/-- `Fixed` addition saturates to `nan` -/
@[irreducible] def Fixed.add (x y : Fixed s) :=
  let z : Fixed s := ⟨x.n + y.n⟩
  bif x == nan || y == nan || (x.n.isNeg == y.n.isNeg && x.n.isNeg != z.n.isNeg) then nan else z
instance : Add (Fixed s) where add x y := x.add y
lemma Fixed.add_def (x y : Fixed s) : x + y = x.add y := rfl

/-- `Fixed` subtraction saturates to `nan` -/
@[irreducible] def Fixed.sub (x y : Fixed s) :=
  let z : Fixed s := ⟨x.n - y.n⟩
  bif x == nan || y == nan || (x.n.isNeg != y.n.isNeg && x.n.isNeg != z.n.isNeg) then nan else z
instance : Sub (Fixed s) where sub x y := x.sub y
lemma Fixed.sub_def (x y : Fixed s) : x - y = x.sub y := rfl

/-- `Fixed` addition with fewer bools -/
lemma Fixed.add_as_eq (x y : Fixed s) : x + y = (
    let z : Fixed s := ⟨x.n + y.n⟩
    if x = nan ∨ y = nan ∨ (x.n.isNeg = y.n.isNeg ∧ x.n.isNeg ≠ z.n.isNeg) then nan else z) := by
  rw [Fixed.add_def, add, bif_eq_if]
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
@[simp] lemma Fixed.neg_ne_nan {x : Fixed s} : (-x) ≠ nan ↔ x ≠ nan := by
  simp only [ne_eq, neg_eq_nan]

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
  rw [sub_def, sub, add_def, add]
  simp only [Bool.cond_eq_ite, Bool.beq_eq_decide_eq', Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, neg_eq_nan]
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
@[simp] lemma Fixed.add_nan {x : Fixed s} : x + nan = nan := by
  rw [Fixed.add_comm, Fixed.add_def, Fixed.add]; rfl
@[simp] lemma Fixed.nan_sub {x : Fixed s} : nan - x = nan := by simp only [sub_eq_add_neg, nan_add]
@[simp] lemma Fixed.sub_nan {x : Fixed s} : x - nan = nan := by
  simp only [sub_eq_add_neg, neg_nan, add_nan]

/-- If `x + y ≠ nan`, neither `x` or `y` are `nan` -/
lemma Fixed.ne_nan_of_add {x y : Fixed s} (h : x + y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose h; simp only [not_and_or, not_not] at h
  cases' h with h h
  · simp only [h, nan_add, ne_eq, not_true, not_false_eq_true]
  · simp only [h, add_nan, ne_eq, not_true, not_false_eq_true]

/-- If `x - y ≠ nan`, neither `x` or `y` are `nan` -/
lemma Fixed.ne_nan_of_sub {x y : Fixed s} (h : x - y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose h; simp only [not_and_or, not_not] at h
  cases' h with h h
  · simp only [h, nan_sub, ne_eq, not_true, not_false_eq_true]
  · simp only [h, sub_nan, ne_eq, not_true, not_false_eq_true]

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

@[simp] lemma Fixed.approx_nan : approx (nan : Fixed s) = univ := by
  simp only [approx, nan, ite_true]

@[mono] lemma Fixed.val_mem_approx (x : Fixed s) : x.val ∈ approx x := by
  simp only [approx]; split_ifs; repeat simp

@[simp] lemma Fixed.approx_zero : approx (0 : Fixed s) = {0} := by
  simp only [approx, nan, ext_iff, zero_n, Int64.zero_def, Int64.ext_iff, Int64.n_min, Nat.cast_pow,
    Nat.cast_ofNat, val_zero, ite_eq_right_iff]
  intro h; contrapose h; decide

/-- If we're not `nan`, `approx` is a singleton -/
@[simp] lemma Fixed.approx_eq_singleton {x : Fixed s} (n : x ≠ nan) : approx x = {x.val} := by
  simp only [approx, n, ite_false]

/-- `Fixed` negation respects `approx` -/
instance : ApproxNeg (Fixed s) ℝ where
  approx_neg x := by
    simp only [approx, ge_iff_le, not_le, gt_iff_lt, Bool.cond_eq_ite, Bool.or_eq_true, beq_iff_eq,
      image_neg, Fixed.neg_eq_nan, or_comm, Fixed.neg_eq_nan]
    by_cases h : x = nan
    · simp only [h, ite_true, neg_univ, Fixed.neg_nan, subset_univ]
    · simp only [h, ite_false, neg_singleton, Fixed.val_neg h, subset_refl]

/-- For `Fixed`, `-` and `approx` commute -/
@[simp] lemma Fixed.approx_neg (x : Fixed s) : approx (-x) = -approx x := by
  by_cases n : x = nan
  · simp only [n, neg_nan, approx_nan, neg_univ]
  · simp only [approx_eq_singleton (neg_ne_nan.mpr n), val_neg n, approx_eq_singleton n,
    neg_singleton]

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
lemma Fixed.val_add {x y : Fixed s} (n : x + y ≠ nan) : (x + y).val = x.val + y.val := by
  have h := image2_subset_iff.mp (approx_add x y) x.val (val_mem_approx _) y.val (val_mem_approx _)
  simp only [approx, n, ite_false, mem_singleton_iff] at h
  rw [h]

/-- `Fixed` subtraction respects `approx` -/
instance : ApproxSub (Fixed s) ℝ where
  approx_sub x y := by
    simp only [Fixed.sub_eq_add_neg, sub_eq_add_neg]
    exact subset_trans (add_subset_add_left (approx_neg _)) (approx_add x (-y))

/-- `Fixed.val` commutes with sub if the result isn't `nan` -/
lemma Fixed.val_sub {x y : Fixed s} (n : x - y ≠ nan) : (x - y).val = x.val - y.val := by
  have h := image2_subset_iff.mp (approx_sub x y) x.val (val_mem_approx _) y.val (val_mem_approx _)
  simp only [approx, n, ite_false, mem_singleton_iff] at h
  rw [h]

/-- `neg_add` for `Fixed s` -/
lemma Fixed.neg_add {x y : Fixed s} : -(x + y) = -y + -x := by
  simp only [Fixed.add_as_eq]
  by_cases xn : x = nan
  · simp only [xn, nan_n, Int64.isNeg_min, ne_eq, true_or, ite_true, neg_nan, neg_eq_nan, or_true]
  by_cases yn : y = nan
  · simp only [yn, nan_n, Int64.isNeg_min, ne_eq, true_or, or_true, ite_true, neg_nan, neg_eq_nan]
  simp only [ne_eq, neg_neg, xn, not_false_eq_true, ne_nan_of_neg, yn, false_or]
  by_cases x0 : x.n = 0
  · simp only [x0, Int64.isNeg_zero, zero_add, and_not_self, ite_false, neg_def, neg, neg_zero,
      add_zero, not_true_eq_false, and_false]
  by_cases y0 : y.n = 0
  · simp only [y0, Int64.isNeg_zero, zero_add, and_not_self, ite_false, neg_def, neg, neg_zero,
      add_zero, not_true_eq_false, and_false]
  simp only [ext_iff, nan_n] at xn yn
  have e : -y.n + -x.n = -(x.n + y.n) := by ring
  simp only [neg_def, neg, Int64.isNeg_neg y0 yn, Int64.isNeg_neg x0 xn, Bool.beq_not_iff_ne, ne_eq,
    Bool.not_not_eq, ext_iff, apply_ite (f := fun x : Int64 ↦ -x), e]
  by_cases xyn : x.n.isNeg = y.n.isNeg
  · simp only [xyn, true_and, ite_not, apply_ite (f := fun x : Fixed s ↦ -x.n), e]
    by_cases xym : x.n + y.n = .min
    · split_ifs
      · simp only [xym, Int64.neg_min, nan]
      · simp only [xym, Int64.neg_min]
      · rw [nan_n, Int64.neg_min]
      · rw [xym, Int64.neg_min, nan_n, Int64.neg_min]
    · have xy0 : x.n + y.n ≠ 0 := by
        contrapose xyn
        simp only [not_not] at xyn
        simp only [eq_neg_iff_add_eq_zero.mpr xyn, Int64.isNeg_neg y0 yn, Bool.not_not_eq]
      simp only [Int64.isNeg_neg xy0 xym, Bool.eq_not_iff, ite_not]
      split_ifs
      · simp only [neg_add_rev]
      · rw [nan_n, Int64.neg_min]
  · simp only [xyn, Ne.symm xyn, false_and, ite_false, neg_add_rev]

/-- `neg_sub` for `Fixed s` -/
lemma Fixed.neg_sub {x y : Fixed s} : -(x - y) = y - x := by
  simp only [sub_eq_add_neg, Fixed.neg_add, neg_neg]

/-- `Fixed` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup (Fixed s) ℝ where

/-!
### Order operations on `Fixed`: min, max, abs
-/

lemma Fixed.val_lt_zero {x : Fixed s} : x.val < 0 ↔ x.n.isNeg := by
  simp only [val, mul_neg_iff, Int.cast_pos, two_zpow_not_neg, and_false,
    Int.cast_lt_zero, Int64.coe_lt_zero_iff, two_zpow_pos, and_true, false_or]

lemma Fixed.val_nonneg {x : Fixed s} : 0 ≤ x.val ↔ x.n.isNeg = false := by
  rw [←not_iff_not]; simp only [not_le, val_lt_zero, Bool.not_eq_false]

lemma Fixed.val_nonpos {x : Fixed s} : x.val ≤ 0 ↔ x.n ≤ 0 := by
  simp only [val, mul_nonpos_iff, two_zpow_pos.le, and_true, two_zpow_not_nonpos,
    and_false, false_or, Int.cast_nonpos, Int64.coe_nonpos_iff]

lemma Fixed.val_pos {x : Fixed s} : 0 < x.val ↔ 0 < x.n := by
  simp only [val, two_zpow_pos, mul_pos_iff_of_pos_right, Int.cast_pos, Int64.coe_pos_iff]

lemma Fixed.isNeg_eq {x : Fixed s} : x.n.isNeg = decide (x.val < 0) := by
  by_cases n : x.n.isNeg
  · simp only [n, true_eq_decide_iff]; rwa [val_lt_zero]
  · simp only [Bool.not_eq_true] at n; simp only [n, false_eq_decide_iff, not_lt]; rwa [val_nonneg]

/-- `x.val = 0` iff `x = 0` is -/
lemma Fixed.val_eq_zero_iff {x : Fixed s} : x.val ≠ 0 ↔ x ≠ 0 := by
  have z : (2:ℝ) ≠ 0 := by norm_num
  simp only [val, ne_eq, mul_eq_zero, Int.cast_eq_zero, Int64.coe_eq_zero, zpow_ne_zero _ z,
    or_false, ext_iff, zero_n]

/-- `x.val` is nonzero iff `x` is -/
lemma Fixed.val_ne_zero_iff {x : Fixed s} : x.val ≠ 0 ↔ x ≠ 0 := by
  simp only [not_iff_not, val_eq_zero_iff]

instance : Min (Fixed s) where
  min x y := ⟨min x.n y.n⟩

instance : Max (Fixed s) where
  max x y := -min (-x) (-y)  -- Use `min` so that `nan` propagates

/-- Unfortunately we can't use `|x|`, since that notation can't use our own implementation.-/
def Fixed.abs (x : Fixed s) : Fixed s :=
  ⟨⟨x.n.abs⟩⟩

lemma Fixed.min_def {x y : Fixed s} : min x y = ⟨min x.n y.n⟩ := rfl
lemma Fixed.max_def {x y : Fixed s} : max x y = -min (-x) (-y) := rfl
lemma Fixed.abs_def {x : Fixed s} : x.abs = ⟨⟨x.n.abs⟩⟩ := rfl

@[simp] lemma Fixed.min_nan {x : Fixed s} : min x nan = nan := by
  simp only [nan, min_def, ge_iff_le, Int64.min_le, min_eq_right]

@[simp] lemma Fixed.nan_min {x : Fixed s} : min nan x = nan := by
  simp only [nan, min_def, ge_iff_le, Int64.min_le, min_eq_left]

@[simp] lemma Fixed.max_nan {x : Fixed s} : max x nan = nan := by
  simp only [max_def, neg_nan, min_nan]

@[simp] lemma Fixed.nan_max {x : Fixed s} : max nan x = nan := by
  simp only [max_def, neg_nan, nan_min]

@[simp] lemma Fixed.abs_nan : abs (nan : Fixed s) = nan := by
  simp only [abs, Int64.abs, ext_iff, Int64.ext_iff, nan]
  decide

@[simp] lemma Fixed.abs_zero : abs (0 : Fixed s) = 0 := by
  simp only [abs, zero_n, Int64.abs_zero]; rfl

@[simp] lemma Fixed.abs_eq_nan {x : Fixed s} : abs x = nan ↔ x = nan := by
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

@[simp] lemma Fixed.abs_ne_nan {x : Fixed s} : abs x ≠ nan ↔ x ≠ nan := by
  simp only [ne_eq, abs_eq_nan]

@[simp] lemma Fixed.isNeg_abs {x : Fixed s} : (abs x).n.isNeg = (x == nan) := by
  rw [Bool.eq_iff_iff, ← val_lt_zero, beq_iff_eq]
  simp only [val, abs, mul_neg_iff, Int.cast_pos, two_zpow_not_neg, and_false,
    Int.cast_lt_zero, Int64.abs_lt_zero, two_zpow_pos, and_true, false_or, nan, ext_iff]

lemma Fixed.val_abs {x : Fixed s} (n : x ≠ nan) : (abs x).val = |x.val| := by
  simp only [val, abs_mul, abs_zpow, abs_two, mul_eq_mul_right_iff]
  left
  simp only [nan, ne_eq, ext_iff] at n
  simp only [abs_def, ←Int.cast_abs, Int.cast_inj, Int64.coe_abs' n]

lemma Fixed.approx_abs_eq {x : Fixed s} (n : x ≠ nan) : approx (abs x) = {|x.val|} := by
  simp only [approx, abs_eq_nan, n, Fixed.val_abs n, ite_false]

lemma Fixed.approx_abs (x : Fixed s) : image (fun x ↦ |x|) (approx x) ⊆ approx (abs x) := by
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
  rw [val, val, mul_lt_mul_right two_zpow_pos]
  simp only [Int.cast_lt, Int64.coe_lt_coe]

lemma Fixed.val_le_val {x y : Fixed s} : x.val ≤ y.val ↔ x.n ≤ y.n := by
  rw [val, val, mul_le_mul_right two_zpow_pos]
  simp only [Int.cast_le, Int64.coe_le_coe]

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

lemma Fixed.min_comm {x y : Fixed s} : min x y = min y x := by
  simp only [min, Int64.blt_eq_decide_lt, Bool.cond_decide]
  split_ifs with l r r
  · simp only [not_lt.mpr r.le] at l
  · rfl
  · rfl
  · simp only [not_lt, Fixed.ext_iff] at l r ⊢
    exact le_antisymm l r

lemma Fixed.max_comm {x y : Fixed s} : max x y = max y x := by
  simp only [max, min_comm]

/-!
### Order lemmas about `nan`
-/

/-- `nan.val` is very negative -/
lemma Fixed.val_nan : (nan : Fixed s).val = -(2:ℝ) ^ (s + 63 : ℤ) := by
  simp only [nan, val]
  rw [Int64.coe_min']
  have e : (2:ℝ) ^ (63 : ℕ) = (2:ℝ) ^ (63 : ℤ) := rfl
  simp only [Int.cast_neg, Int.cast_pow, Int.int_cast_ofNat, neg_mul, neg_inj, e]
  rw [←zpow_add₀ (by norm_num), Int.add_comm]

/-- `nan.val < 0` -/
@[simp] lemma Fixed.val_nan_neg : (nan : Fixed s).val < 0 := by
  simp only [val_nan, Left.neg_neg_iff, two_zpow_pos]

/-- ¬`0 ≤ nan.val` -/
@[simp] lemma Fixed.not_val_nan_nonneg : ¬0 ≤ (nan : Fixed s).val := not_le.mpr val_nan_neg

/-- ¬`0 < nan.val` -/
@[simp] lemma Fixed.not_val_nan_pos : ¬0 < (nan : Fixed s).val := not_lt.mpr val_nan_neg.le

/-- Positive `Fixed`s are `≠ nan` -/
lemma Fixed.ne_nan_of_pos {x : Fixed s} (h : 0 < x.val) : x ≠ nan := by
  contrapose h; rw [not_not] at h; simp only [not_lt, h, val_nan_neg.le]

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
  rw [UInt128.toNat_def, h.1]
  simp only [UInt64.toNat_zero, zero_mul, zero_add, h.2.1]

/-- Multiply two positive, non-nan `Fixed`s -/
@[irreducible] def Fixed.mul_of_pos (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) : Fixed u :=
  let d : Fixed 0 := ⟨s⟩ + ⟨t⟩ - ⟨u⟩
  bif d == nan then nan else
  let z := mul128 x.n.n y.n.n
  of_raw_uint128 (bif d.n.isNeg then z.shiftRightRound (-d.n).n up else z.shiftLeftSaturate d.n.n)

/-- Multiply, changing `s` and rounding up or down.  We have
  `z = x * y`
  `z.n * 2^u = x.n * y.n * 2^(s + t)`
  `z.n = x.n * y.n * 2^(s + t - u)` -/
@[irreducible] def Fixed.mul (x : Fixed s) (y : Fixed t) (u : Int64) (up : Bool) : Fixed u :=
  bif x == nan || y == nan then nan else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_pos (abs x) (abs y) u (up.xor p)
  bif p then -z else z

lemma Fixed.of_raw_uint128_val {n : UInt128} (h : (of_raw_uint128 n : Fixed s) ≠ nan) :
    (of_raw_uint128 n : Fixed s).val = (n : ℝ) * (2:ℝ)^(s : ℤ) := by
  simp only [of_raw_uint128, bif_eq_if, Bool.or_eq_true, bne_iff_ne, ne_eq, ite_eq_left_iff, not_or,
    not_not, Bool.not_eq_true, and_imp, not_forall, exists_prop, exists_and_left] at h
  simp only [val, Int64.toInt, of_raw_uint128, h.1, bne_self_eq_false, h.2.1, Bool.or_self,
    bif_eq_if, ite_false, CharP.cast_eq_zero, sub_zero, Int.cast_ofNat, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat, UInt128.toReal, UInt128.toNat_def, UInt64.toNat_zero, zero_mul, zero_add]

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
  rw [mul_of_pos]
  simp only [image2_mul, bif_eq_if, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq]
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
        · simp only [← hd, Fixed.val_sub dn, Fixed.val_add stn]
          simp only [val, Int64.coe_zero, zpow_zero, mul_one]
      simpa only [val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_add, ←Int.cast_sub,
        Int.cast_inj] using e
    by_cases ds : d.n.isNeg
    · have dn : (2:ℝ) ^ (-d.n).n.toNat = (2:ℝ) ^ ((u:ℤ) - ↑s - ↑t) := by
        suffices h : ↑(-d.n).n.toNat = -(d.n : ℤ) by
          rw [←zpow_ofNat, h, de, _root_.neg_sub, sub_add_eq_sub_sub]
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
    approx (abs x) * approx (abs y) ⊆ rounds (approx (mul_of_pos (abs x) (abs y) u up)) !up := by
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
  rw [mul]
  simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ite_not, or_assoc]
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
      refine subset_trans ?_ (rounds_mono (ApproxNeg.approx_neg _))
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

/-!
## Conversion from `ℕ`, `ℤ`, `ℚ`, `Float`
-/

/-- Conversion from `ℕ` literals to `Fixed s`, rounding up or down -/
@[irreducible] def Fixed.ofNat (n : ℕ) (up : Bool) : Fixed s :=
  let t : ℤ := s
  bif t < 0 then
    let u := (-t).toNat
    bif n != 0 && (63 ≤ u || 63-u ≤ n.log2) then nan
    else ⟨n <<< u⟩
  else
    let u := t.toNat
    let k := (bif up then n + (1 <<< u) - 1 else n) >>> u
    bif k.log2 < 63 then ⟨k⟩ else nan

/-- Conversion from `ℕ` literals to `Fixed 0`, not rounding -/
@[irreducible] def Fixed.ofNat0 (n : ℕ) : Fixed 0 :=
  bif n.log2 < 63 then ⟨n⟩ else nan

 /-- We use the general `.ofNat` routine even for `1`, to handle overflow,
    rounding down arbitrarily -/
instance : One (Fixed s) := ⟨.ofNat 1 false⟩

/-- Conversion from `ℕ` literals to `Fixed s` -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat (Fixed s) n := ⟨.ofNat n false⟩

/-- Conversion from `ℤ` -/
@[irreducible] def Fixed.ofInt (n : ℤ) (up : Bool) : Fixed s :=
  bif n < 0 then -.ofNat (-n).toNat !up else .ofNat n.toNat up

/-- Conversion from `ℚ`, rounding up or down -/
@[irreducible] def Fixed.ofRat (x : ℚ) (up : Bool) : Fixed s :=
  -- Our rational is `x = a / b`.  The `Int64` result `y` should satisfy
  --   `y * 2^s ≈ a / b`
  -- We can do this via an exact integer division if we merge `2^s` into either `a` or `b`.
  -- This might be expensive if `s` is large, but we can worry about that later.
  let (a,b) := bif s.isNeg then (x.num >>> ↑s, x.den) else (x.num, x.den <<< s.n.toNat)
  let d := a.rdiv b up
  bif |d| < 2^63 then ⟨d⟩ else nan

/-- Convert a `Float` to `Fixed s` -/
@[irreducible] def Fixed.ofFloat (x : Float) : Fixed s :=
  let xs := x.abs.scaleB (-s)
  bif xs ≤ 0.5 then 0 else
  let y : Int64 := ⟨xs.toUInt64⟩
  bif y == 0 || y.isNeg then nan else
  ⟨bif x < 0 then -y else y⟩

/-- `Fixed.ofNat` rounds the desired way -/
lemma Fixed.approx_ofNat (n : ℕ) (up : Bool) :
    ↑n ∈ rounds (approx (.ofNat n up : Fixed s)) !up := by
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  by_cases nn : (.ofNat n up : Fixed s) = nan
  · simp only [nn, approx_nan, rounds_univ, mem_univ]
  rw [ofNat] at nn ⊢
  simp only [bif_eq_if, decide_eq_true_eq, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true] at nn ⊢
  generalize ht : (s : ℤ) = t at nn
  by_cases tn : t < 0
  · simp only [tn, ite_true, ite_eq_left_iff, not_and, not_forall, exists_prop] at nn
    by_cases n0 : n = 0
    · simp [n0, ofNat, Fixed.val, tn, rounds, approx]
      use 0
      simp only [implies_true, le_refl, ite_self, and_self]
    simp only [rounds, approx, tn, n0, not_false_eq_true, nn, and_false, ite_false, ite_true,
      mem_singleton_iff, Bool.not_eq_true', exists_eq_left, mem_setOf_eq, Fixed.val, ht]
    replace nn := nn.1
    simp only [n0, not_false_eq_true, not_or, not_le, forall_true_left] at nn
    simp only [Nat.shiftLeft_eq]
    have lt : n * 2 ^ Int.toNat (-t) < 2^63 := by
      have lt := (Nat.log2_lt n0).mp nn.2
      refine lt_of_lt_of_le ((mul_lt_mul_right (pow_pos (by norm_num) _)).mpr lt) ?_
      simp only [←pow_add, Nat.sub_add_cancel nn.1.le, le_refl]
    have e : (Int.toNat (-t) : ℤ) = -t := Int.toNat_of_nonneg (by omega)
    simp only [Int64.toInt_ofNat lt, Nat.cast_mul (α := ℤ), Int.cast_pow, Nat.cast_two,
      Int.cast_mul, Int.cast_ofNat, Nat.cast_pow, Int.cast_two, mul_assoc]
    simp only [←zpow_ofNat, ←zpow_add₀ t0, e, add_left_neg, zpow_zero, mul_one, le_refl, ite_self]
  · have tp := not_lt.mp tn
    have tz : (2:ℝ) ^ t = ↑(2 ^ t.toNat : ℕ) := by
      generalize hu : t.toNat = u
      have tu : (t : ℤ) = u := by rw [←hu]; exact (Int.toNat_of_nonneg tp).symm
      simp only [tu, zpow_coe_nat, Int.toNat_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    simp only [tn, tsub_le_iff_right, ite_false, ite_eq_right_iff, not_forall, exists_prop] at nn
    induction up
    · simp only [ite_false] at nn
      simp only [rounds, approx, tn, tsub_le_iff_right, ite_false, nn, ite_true, val._eq_1,
        mem_singleton_iff, Bool.not_false, exists_eq_left, mem_setOf_eq, ge_iff_le]
      replace nn := nn.1
      simp only [Nat.shiftRight_eq_div_pow, ht] at nn ⊢
      by_cases n0 : n / 2^t.toNat = 0
      · simp only [n0, Nat.cast_zero, Int64.coe_zero, Int.cast_zero, zero_mul, Nat.cast_nonneg]
      simp only [Nat.log2_lt n0] at nn
      simp only [Int64.toInt_ofNat nn, tz, ←Nat.cast_mul, Int.cast_ofNat, Nat.cast_le]
      apply Nat.div_mul_le_self
    · simp only [ite_true] at nn
      simp only [rounds, approx, tn, tsub_le_iff_right, ite_true, nn, ite_false, mem_singleton_iff,
        Bool.not_true, exists_eq_left, mem_setOf_eq, ge_iff_le, Fixed.val, ht, tz]
      simp only [Nat.shiftLeft_eq, one_mul, Nat.shiftRight_eq_div_pow] at nn ⊢
      by_cases np : n = 0
      · simp only [np, zero_add, Nat.two_pow_sub_one_div_two_pow, ge_iff_le,
          le_refl, tsub_eq_zero_of_le, pow_zero, Nat.cast_zero, Int64.coe_zero, Int.cast_zero,
          Nat.cast_ofNat, zero_mul]
      rw [←Ne.def, ←Nat.pos_iff_ne_zero] at np
      have n0'' : 0 < n + 2 ^ Int.toNat t - 1 := by
        have le : 1 ≤ 2 ^ Int.toNat t := Nat.one_le_two_pow _
        simp only [Nat.add_sub_assoc le]
        exact lt_of_lt_of_le np (by omega)
      by_cases zero : (n + 2 ^ Int.toNat t - 1) / 2 ^ Int.toNat t = 0
      · simp only [zero, Nat.cast_zero, Int64.coe_zero, Int.cast_zero, zero_mul]
        rw [←Nat.cast_zero, Nat.cast_le]
        rw [Nat.div_eq_zero_iff (pow_pos (by norm_num) _)] at zero
        omega
      · simp only [Int64.toInt_ofNat ((Nat.log2_lt zero).mp nn.1), Int.cast_ofNat, ←Nat.cast_mul,
          Nat.cast_le]
        exact Nat.le_add_div_mul (Nat.pos_pow_of_pos _ (by norm_num))

/-- `Fixed.ofNat0` is conservative -/
@[mono] lemma Fixed.approx_ofNat0 (n : ℕ) : ↑n ∈ approx (ofNat0 n) := by
  by_cases nn : (ofNat0 n) = nan
  · simp only [nn, approx_nan, mem_univ]
  rw [ofNat0] at nn ⊢
  simp only [bif_eq_if, decide_eq_true_eq, ite_eq_right_iff, not_forall, exists_prop] at nn ⊢
  simp only [approx, nn, ite_true, ne_eq, neg_neg, not_false_eq_true, ne_nan_of_neg, val._eq_1,
    Int64.coe_zero, zpow_zero, mul_one, ite_false, mem_singleton_iff]
  replace nn := nn.1
  by_cases n0 : n = 0
  · simp only [n0, CharP.cast_eq_zero, Nat.cast_zero, Int64.coe_zero, Int.cast_zero]
  simp only [Nat.log2_lt n0] at nn
  simp only [Int64.toInt_ofNat nn, Int.cast_ofNat]

/-- `Fixed.approx_ofNat`, down version -/
lemma Fixed.ofNat_le {n : ℕ} (h : (.ofNat n false : Fixed s) ≠ nan) :
    (.ofNat n false : Fixed s).val ≤ n := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    Fixed.approx_ofNat n false (s := s)

/-- `Fixed.approx_ofNat`, up version -/
lemma Fixed.le_ofNat {n : ℕ} (h : (.ofNat n true : Fixed s) ≠ nan) :
    n ≤ (.ofNat n true : Fixed s).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using
    Fixed.approx_ofNat n true (s := s)

/-- `Fixed.ofInt` rounds the desired way -/
lemma Fixed.approx_ofInt (n : ℤ) (up : Bool) :
    ↑n ∈ rounds (approx (.ofInt n up : Fixed s)) !up := by
  rw [Fixed.ofInt]
  by_cases n0 : n < 0
  · have e : (n : ℝ) = -↑(-n).toNat := by
      have e : (n : ℝ) = -↑(-n) := by simp only [Int.cast_neg, neg_neg]
      have le : 0 ≤ -n := by omega
      rw [e, ←Int.toNat_of_nonneg le, neg_inj, Int.cast_ofNat]
      rw [Int.toNat_of_nonneg le]
    simpa only [e, n0, decide_True, cond_true, approx_neg, rounds_neg, Bool.not_not, mem_neg,
      neg_neg] using approx_ofNat (-n).toNat (!up) (s := s)
  · have e : (n : ℝ) = ↑n.toNat := by
      rw [←Int.toNat_of_nonneg (not_lt.mp n0), Int.cast_ofNat]
      simp only [Int.toNat_of_nonneg (not_lt.mp n0)]
    simp only [e, n0, decide_False, cond_false, approx_ofNat]

/-- `Fixed.approx_ofInt`, down version -/
lemma Fixed.ofInt_le {n : ℤ} (h : (.ofInt n false : Fixed s) ≠ nan) :
    (.ofInt n false : Fixed s).val ≤ n := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    Fixed.approx_ofInt n false (s := s)

/-- `Fixed.approx_ofInt`, up version -/
lemma Fixed.le_ofInt {n : ℤ} (h : (.ofInt n true : Fixed s) ≠ nan) :
    n ≤ (.ofInt n true : Fixed s).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using
    Fixed.approx_ofInt n true (s := s)

/-- `Fixed.ofRat` rounds the desired way -/
lemma Fixed.approx_ofRat (x : ℚ) (up : Bool) :
    ↑x ∈ rounds (approx (.ofRat x up : Fixed s)) !up := by
  by_cases n : (ofRat x up : Fixed s) = nan
  · simp only [n, approx_nan, rounds_univ, mem_univ]
  rw [Fixed.approx_eq_singleton n, ofRat]
  by_cases sn : s.isNeg
  · simp only [Bool.cond_decide, sn, cond_true, neg_neg, Bool.cond_self]
    by_cases dn : |Int.rdiv (x.num >>> ↑s) ↑x.den up| < 2 ^ 63
    · simp only [dn, ite_true, Int64.toInt_ofInt dn, val]
      rw [←Int64.coe_lt_zero_iff] at sn
      generalize (s : ℤ) = s at sn dn
      have e : s = -(-s).toNat := by rw [Int.toNat_of_nonneg (by omega), neg_neg]
      rw [e] at dn ⊢; clear e sn
      generalize (-s).toNat = s at dn
      simp only [Int.shiftRight_neg, Int.shiftLeft_eq_mul_pow, zpow_neg,
        mul_inv_le_iff two_pow_pos, Nat.cast_pow, Nat.cast_ofNat, zpow_coe_nat, ge_iff_le] at dn ⊢
      nth_rw 1 [←Rat.num_div_den x]
      simp only [Rat.cast_div, Rat.cast_coe_int, Rat.cast_coe_nat, ←mul_div_assoc,
        Int64.toInt_ofInt dn]
      induction up
      · simp only [Bool.not_false, mem_rounds_singleton, mul_inv_le_iff two_pow_pos, ←
          mul_div_assoc, mul_comm _ (x.num : ℝ), ite_true, ge_iff_le]
        refine le_trans Int.rdiv_le ?_
        simp only [Int.cast_mul, Int.cast_pow, Int.int_cast_ofNat, le_refl]
      · simp only [rounds, ← div_eq_mul_inv, mem_singleton_iff, Bool.not_true, ite_false,
          exists_eq_left, le_div_iff two_pow_pos, mem_setOf_eq, ge_iff_le]
        refine le_trans (le_of_eq ?_) Int.le_rdiv
        simp only [div_eq_mul_inv, Int.cast_mul, Int.cast_pow, Int.int_cast_ofNat]; ring_nf
    · rw [ofRat, sn, cond_true] at n
      simp only [bif_eq_if, dn, decide_False, ite_false, not_true_eq_false] at n
  · simp only [Bool.cond_decide, sn, cond_false, val._eq_1, mem_rounds_singleton,
      Bool.not_eq_true']
    simp only [Bool.not_eq_true] at sn
    by_cases dn : |Int.rdiv x.num (x.den <<< s.n.toNat) up| < 2 ^ 63
    · simp only [dn, ite_true, Int64.toInt_of_isNeg_eq_false sn, zpow_ofNat]
      rw [Int64.toInt_ofInt dn, Nat.shiftLeft_eq]
      generalize s.n.toNat = s; clear dn
      induction up
      · simp only [ite_true]
        refine le_trans (mul_le_mul_of_nonneg_right Int.rdiv_le two_pow_pos.le) (le_of_eq ?_)
        simp only [div_eq_mul_inv, Nat.cast_mul, mul_inv, Nat.cast_pow, Nat.cast_two,  mul_assoc,
          inv_mul_cancel (two_pow_pos (R := ℝ)).ne', mul_one]
        nth_rw 3 [←Rat.num_div_den x]
        simp only [← div_eq_mul_inv, Rat.cast_div, Rat.cast_coe_int, Rat.cast_coe_nat]
      · simp only [ite_false]
        refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right Int.le_rdiv two_pow_pos.le)
        simp only [div_eq_mul_inv, Nat.cast_mul, mul_inv, Nat.cast_pow, Nat.cast_two,  mul_assoc,
          inv_mul_cancel (two_pow_pos (R := ℝ)).ne', mul_one]
        nth_rw 1 [←Rat.num_div_den x]
        simp only [← div_eq_mul_inv, Rat.cast_div, Rat.cast_coe_int, Rat.cast_coe_nat]
    · rw [ofRat, sn, cond_false] at n
      simp only [Bool.cond_decide, dn, ite_false, not_true_eq_false] at n

/-- `Fixed.approx_ofRat`, down version -/
lemma Fixed.ofRat_le {x : ℚ} (h : (.ofRat x false : Fixed s) ≠ nan) :
    (.ofRat x false : Fixed s).val ≤ x := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    Fixed.approx_ofRat x false (s := s)

/-- `Fixed.approx_ofRat`, up version -/
lemma Fixed.le_ofRat {x : ℚ} (h : (.ofRat x true : Fixed s) ≠ nan) :
    x ≤ (.ofRat x true : Fixed s).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using
    Fixed.approx_ofRat x true (s := s)

/-!
### `2^n` and `log2`
-/

/-- Find `n` s.t. `2^n ≤ x.val < 2^(n+1)`, or `nan` -/
@[irreducible, pp_dot] def Fixed.log2 (x : Fixed s) : Fixed 0 :=
  bif x.n ≤ 0 then nan else ⟨⟨x.n.n.log2⟩⟩ + ⟨s⟩

/-- `2^n : Fixed s`, rounded up or down -/
@[irreducible] def Fixed.two_pow (n : Fixed 0) (up : Bool) : Fixed s :=
  -- In the end, we'll have `⟨⟨x⟩⟩ : Fixed s` with `.val = x * 2^s`.
  -- We want `x * 2^s = s^n`, so `x = 2^(n - s)`.
  let k := n - ⟨s⟩
  bif k == nan || 63 ≤ k.n then nan else
  bif k.n.isNeg then bif up then ⟨1⟩ else 0 else
  ⟨⟨1 <<< k.n.n⟩⟩

/-- `x.log2` gives us a bracketing interval of two powers around `x.val` -/
lemma Fixed.val_mem_log2 {x : Fixed s} (h : x.log2 ≠ nan) :
    x.val ∈ Ico (2^(x.log2.n : ℤ)) (2^(x.log2.n + 1 : ℤ)) := by
  rw [Fixed.log2] at h ⊢
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  have tp : ∀ n : ℕ, (2:ℝ) ^ n = (2^n : ℕ) := fun n ↦ by rw [Nat.cast_pow, Nat.cast_two]
  by_cases x0 : x.n ≤ 0
  · simp only [x0, decide_True, bif_eq_if, ite_true, ne_eq, not_true_eq_false] at h
  · simp only [val, x0, decide_False, cond_false, mem_Ico, ←div_le_iff two_zpow_pos,
      ←lt_div_iff two_zpow_pos, ←zpow_sub₀ t0] at h ⊢
    have v := Fixed.val_add h
    simp only [val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_add, Int.cast_inj] at v
    simp only [v]; ring_nf
    simp only [not_le] at x0
    have xn : x.n.isNeg = false := by simp only [Int64.isNeg_eq, not_lt.mpr x0.le, decide_False]
    rw [Int64.coe_log2, UInt64.toNat_log2, ←Nat.cast_one, ←Nat.cast_add, zpow_coe_nat, zpow_coe_nat,
      Nat.add_comm, Int64.toReal_toInt xn, tp, tp, Nat.cast_le, Nat.cast_lt]
    refine ⟨Nat.log2_self_le ?_, Nat.lt_log2_self⟩
    simp only [←UInt64.ne_zero_iff_toNat_ne_zero, ←Int64.ne_zero_iff_n_ne_zero]
    exact x0.ne'

/-- `Fixed.two_pow` is correctly rounded -/
lemma Fixed.approx_two_pow (n : Fixed 0) (up : Bool) :
    2 ^ (n.n : ℤ) ∈ rounds (approx (.two_pow n up : Fixed s)) !up := by
  generalize hk : n - ⟨s⟩ = k
  rw [two_pow]
  simp only [rounds, approx, bif_eq_if, hk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
    ite_eq_left_iff, mem_ite_univ_left, not_forall, exists_prop, mem_singleton_iff, and_imp,
    Bool.not_eq_true', mem_setOf_eq]
  by_cases h : k = nan ∨ 63 ≤ k.n
  · use 2 ^ (n.n : ℤ)
    simp only [h, not_true_eq_false, ite_true, IsEmpty.forall_iff, le_refl, ite_self, and_self]
  · simp only [h, not_false_eq_true, ite_false, forall_true_left]
    simp only [not_or] at h
    by_cases kn : k.n.isNeg = true
    · simp only [kn, ite_true]
      use (if up = true then ⟨1⟩ else 0 : Fixed s).val
      refine ⟨fun _ ↦ rfl, ?_⟩
      induction up
      · simp only [ite_false, val_zero, two_zpow_pos.le, ite_true]
      · simp only [ite_true, val, Int64.coe_one, Int.cast_one, one_mul, ite_false]
        apply zpow_le_of_le (by norm_num)
        simp only [← hk, not_le, isNeg_eq, decide_eq_true_eq] at h kn
        simp only [Fixed.val_sub h.1, sub_neg] at kn
        simp only [val, Int64.coe_zero, zpow_zero, mul_one, Int.cast_lt, Int64.coe_lt_coe] at kn
        simp only [Int64.coe_le_coe, kn.le]
    · use (⟨⟨1 <<< k.n.n⟩⟩ : Fixed s).val
      simp only [Bool.not_eq_true] at kn
      simp only [kn, ite_false, val, implies_true, true_and]
      have k63 : k.n.n.toNat < 63 := by
        have e : ((63 : Int64) : ℤ) = ((63 : ℕ) : ℤ) := rfl
        simp only [not_le, ←Int64.coe_lt_coe, Int64.toInt_of_isNeg_eq_false kn, e,
          Nat.cast_lt] at h
        exact h.2
      have k64 : k.n.n.toNat < 64 := by omega
      have e1 : 1 % 2 ^ (64 - k.n.n.toNat) = 1 :=
        Nat.mod_eq_of_lt (one_lt_pow (by norm_num) (by omega))
      have lt : (⟨1 <<< k.n.n⟩ : Int64).n.toNat < 2 ^ 63 := by
        simp only [UInt64.toNat_shiftLeft k64, UInt64.toNat_one, e1, one_mul]
        exact pow_lt_pow_right (by norm_num) k63
      have e : (2:ℝ) ^ k.n.n.toNat * 2 ^ (s : ℤ) = 2 ^ (n.n : ℤ) := by
        rw [pow_mul_zpow (by norm_num)]; apply congr_arg₂ _ rfl
        rw [←hk] at h
        have v := Fixed.val_sub h.1
        simp only [hk, val, Int64.toInt_of_isNeg_eq_false kn, Int64.coe_zero, zpow_zero,
          mul_one, ←Int.cast_sub, Int.cast_inj] at v
        linarith
      simp only [Int64.toInt_eq_toNat_of_lt lt, UInt64.toNat_shiftLeft k64, UInt64.toNat_one, e1,
        one_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.int_cast_ofNat, e, le_refl,
        ite_self]

/-- `Fixed.log2 = nan` if we're nonpos -/
@[simp] lemma Fixed.log2_eq_nan_of_nonpos {x : Fixed s} (x0 : x.val ≤ 0) : x.log2 = nan := by
  simp only [val_nonpos] at x0
  rw [log2]
  simp only [x0, decide_True, cond_true]

/-- `Fixed.log2` propagates `nan` -/
@[simp] lemma Fixed.log2_nan : (nan : Fixed s).log2 = nan := by
  rw [log2]
  simp only [Bool.cond_decide, ite_eq_left_iff, not_le, ← val_pos, not_val_nan_pos,
    IsEmpty.forall_iff]

/-- `Fixed.two_pow` propagates `nan` -/
@[simp] lemma Fixed.two_pow_nan {up : Bool} : (two_pow nan up : Fixed s) = nan := by
  rw [two_pow]
  simp only [nan_sub, beq_self_eq_true, Bool.true_or, isNeg_nan, cond_true]

/-- `Fixed.two_pow ≠ nan` implies the argument `≠ nan` -/
@[simp] lemma Fixed.ne_nan_of_two_pow {n : Fixed 0} {up : Bool}
    (h : (two_pow n up : Fixed s) ≠ nan) : n ≠ nan := by
  contrapose h
  simp only [ne_eq, not_not] at h
  simp only [h, two_pow_nan, ne_eq, not_true_eq_false, not_false_eq_true]

/-- `Fixed.approx_two_pow`, down version -/
lemma Fixed.two_pow_le {n : Fixed 0} (h : (.two_pow n false : Fixed s) ≠ nan) :
    (.two_pow n false : Fixed s).val ≤ 2 ^ (n.n : ℤ) := by
  simpa only [approx, h, ite_false, Bool.not_false, mem_rounds_singleton, ite_true] using
    Fixed.approx_two_pow n false (s := s)

/-- `Fixed.approx_ofNat`, up version -/
lemma Fixed.le_two_pow {n : Fixed 0} (h : (.two_pow n true : Fixed s) ≠ nan) :
    2 ^ (n.n : ℤ) ≤ (.two_pow n true : Fixed s).val := by
  simpa only [approx, h, ite_false, Bool.not_true, mem_rounds_singleton] using
    Fixed.approx_two_pow n true (s := s)

/-!
### Exponent changes: `Fixed s → Fixed t`
-/

/-- Change `Fixed s` to `Fixed t`, rounding up or down as desired -/
@[irreducible, pp_dot] def Fixed.repoint (x : Fixed s) (t : Int64) (up : Bool) : Fixed t :=
  -- We want `y : Int64` s.t. `y = x * 2^(s-t)`
  let k : Fixed 0 := ⟨s⟩ - ⟨t⟩
  bif k == nan || x == nan then nan else
  bif t ≤ s then
    bif 63 ≤ k.n.n && x.n != 0 then nan
    else bif x.n.abs >>> (63 - k.n.n) != 0 then nan
    else ⟨x.n <<< k.n.n⟩
  else
    ⟨x.n.shiftRightRound (-k).n.n up⟩

/-- `Fixed.repoint` propagates `nan` -/
@[simp] lemma Fixed.repoint_nan (t : Int64) (up : Bool) : (nan : Fixed s).repoint t up = nan := by
  rw [Fixed.repoint]
  simp only [beq_self_eq_true, Bool.or_true, nan_n, Int64.abs_min, Int64.coe_min', Int.cast_neg,
    Int.cast_pow, Int.int_cast_ofNat, Int64.n_min, Bool.cond_decide, cond_true]

/-- Special case of `pow_sub` involving `UInt64`s -/
lemma two_pow_coe_sub {s t : Int64} {k : Fixed 0} (st : s ≤ t) (e : ⟨t⟩ - ⟨s⟩ = k) (kn : k ≠ nan) :
    (2:ℝ) ^ (t:ℤ) / 2 ^ (s:ℤ) = (2^k.n.n.toNat : ℤ) := by
  rw [←zpow_sub₀ (by norm_num)]
  rw [←e] at kn
  have h := Fixed.val_sub kn
  simp only [Fixed.val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_sub, Int.cast_inj, e] at h
  simp only [← h, Int.cast_pow, Int.int_cast_ofNat]
  rw [Int64.coe_of_nonneg, zpow_ofNat]
  have k0 : 0 ≤ k.n := by rwa [←Int64.coe_le_coe, Int64.coe_zero, h, sub_nonneg, Int64.coe_le_coe]
  simp only [Int64.isNeg_eq, not_lt.mpr k0, decide_False]

/-- `Fixed.repoint` is conservative -/
lemma Fixed.approx_repoint (x : Fixed s) (t : Int64) (up : Bool) :
    approx x ⊆ rounds (approx (x.repoint t up)) !up := by
  by_cases xn : x = nan
  · simp only [xn, approx_nan, repoint_nan, rounds_univ, subset_univ]
  rw [Fixed.repoint]
  by_cases kn : (⟨s⟩ - ⟨t⟩ : Fixed 0) = nan
  · simp only [kn, beq_self_eq_true, Bool.true_or, nan_n, Int64.n_min, Int64.neg_min,
      Bool.cond_decide, cond_true, approx_nan, rounds_univ, subset_univ]
  simp only [ne_eq, neg_eq_nan, xn, not_false_eq_true, ne_nan_of_neg, approx_eq_singleton,
    bif_eq_if, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ite_not, beq_iff_eq, neg_neg,
    ite_false, singleton_subset_iff, Bool.or_eq_true, kn, false_or]
  generalize hk : (⟨s⟩ - ⟨t⟩ : Fixed 0) = k at kn
  by_cases ts : t ≤ s
  · simp only [ts, ite_true]
    by_cases k63 : 63 ≤ k.n.n
    · by_cases x0 : x.n = 0
      · simp only [approx, k63, x0, not_true_eq_false, and_false, Int64.abs_zero,
          UInt64.zero_shiftRight, Int64.n_zero, UInt64.zero_shiftLeft, ite_true, ite_false]
        split_ifs
        · simp only [rounds_univ, mem_univ]
        · simp only [val._eq_1, x0, Int64.coe_zero, Int.cast_zero, zero_mul, Int64.zero_shiftLeft,
            mem_rounds_singleton, Bool.not_eq_true', le_refl, ite_self]
      · simp only [k63, x0, not_false_eq_true, and_self, ite_true, approx_nan, rounds_univ,
          mem_univ]
    · simp only [k63, false_and, ite_false]
      simp only [not_le] at k63
      have e62 : (62 : UInt64).toNat = 62 := rfl
      have e63 : (63 : UInt64).toNat = 63 := rfl
      have st62 : k.n.n ≤ 62 := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, e62, e63] at k63 ⊢; omega
      have st63 : k.n.n ≤ 63 := by
        simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, e62, e63] at k63 ⊢; omega
      have st62' : k.n.n.toNat ≤ 62 := by rwa [UInt64.le_iff_toNat_le, e62] at st62
      have lt : 63 - k.n.n.toNat < 64 := by omega
      simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_shiftRight', UInt64.toNat_sub st63, e63,
        Nat.mod_eq_of_lt lt, UInt64.toNat_zero, gt_iff_lt, zero_lt_two, pow_pos,
        Nat.div_eq_zero_iff]
      by_cases lt : x.n.abs.toNat < 2 ^ (63 - k.n.n.toNat)
      · by_cases xn : (⟨x.n <<< k.n.n⟩ : Fixed t) = nan
        · simp only [approx, lt, xn, ite_self, ite_true, rounds_univ, mem_univ]
        · have pst : (2:ℝ) ^ (s:ℤ) / 2 ^ (t:ℤ) = (2^k.n.n.toNat : ℤ) := two_pow_coe_sub ts hk kn
          have r : ((x.n <<< k.n.n : Int64) : ℤ) = ↑x.n * 2^k.n.n.toNat :=
            Int64.coe_shiftLeft (by omega) lt
          simp only [val, approx, lt, ite_true, ne_eq, neg_neg, xn, not_false_eq_true,
            ne_nan_of_neg, ite_false, mem_rounds_singleton, Bool.not_eq_true',
            ←le_div_iff (two_zpow_pos (n := t)), mul_div_assoc, ite_self,
            ←div_le_iff (two_zpow_pos (n := t)), pst, ←Int.cast_mul, Int.cast_le, r, le_refl]
      · simp only [lt, ite_false, approx_nan, rounds_univ, mem_univ]
  · simp only [ts, ite_false]
    simp only [not_le] at ts
    by_cases sn : (⟨Int64.shiftRightRound x.n (-k).n.n up⟩ : Fixed t) = nan
    · simp only [sn, approx_nan, rounds_univ, mem_univ]
    · have pts : (2:ℝ) ^ (t:ℤ) / 2 ^ (s:ℤ) = (2^(-k.n).n.toNat : ℤ) := by
        apply two_pow_coe_sub ts.le
        · rw [←Fixed.neg, ←Fixed.neg_def, ←hk, Fixed.neg_sub]
        · rw [←Fixed.neg_eq_nan, Fixed.neg_def, Fixed.neg] at kn
          exact kn
      simp only [val._eq_1, approx_eq_singleton sn, mem_rounds_singleton, Bool.not_eq_true',
        ←div_le_iff (two_zpow_pos (n := s)), mul_div_assoc, pts, Int.int_cast_ofNat,
        ←le_div_iff (two_zpow_pos (n := s))]
      simp only [←Int.cast_mul, Int.cast_le, Int64.coe_shiftRightRound]
      induction up
      · simp only [Int.rdiv, Nat.cast_pow, Nat.cast_ofNat, cond_false, ite_true, ge_iff_le]
        exact Int.ediv_mul_le _ (by positivity)
      · simp only [Int.rdiv, Nat.cast_pow, Nat.cast_ofNat, cond_true, neg_mul, le_neg, ite_false]
        exact Int.ediv_mul_le _ (by positivity)

/-- `Fixed.repoint _ _ false` rounds down -/
lemma Fixed.repoint_le {x : Fixed s} {t : Int64} (n : x.repoint t false ≠ nan) :
    (x.repoint t false).val ≤ x.val := by
  by_cases xn : x = nan
  · simp only [xn, repoint_nan, ne_eq, not_true_eq_false] at n
  have h := Fixed.approx_repoint (x := x) (s := s) (t := t) (up := false)
  simpa only [ge_iff_le, ne_eq, neg_eq_nan, xn, not_false_eq_true, ne_nan_of_neg,
    approx_eq_singleton, n, Bool.not_false, singleton_subset_iff, mem_rounds_singleton,
    ite_true] using h

/-- `Fixed.repoint _ _ true` rounds up -/
lemma Fixed.le_repoint {x : Fixed s} {t : Int64} (n : x.repoint t true ≠ nan) :
    x.val ≤ (x.repoint t true).val := by
  by_cases xn : x = nan
  · simp only [xn, repoint_nan, ne_eq, not_true_eq_false] at n
  have h := Fixed.approx_repoint (x := x) (s := s) (t := t) (up := true)
  simpa only [ge_iff_le, ne_eq, neg_eq_nan, xn, not_false_eq_true, ne_nan_of_neg,
    approx_eq_singleton, n, Bool.not_false, singleton_subset_iff, mem_rounds_singleton,
    ite_true] using h

/-!
### Unit tests
-/

/-- Test `Fixed.repoint` -/
lemma repoint_test0 : (.ofNat 7 false : Fixed 0).repoint (-60) true != nan := by native_decide
lemma repoint_test1 : (.ofNat 7 false : Fixed 0).repoint (-60) false != nan := by native_decide
lemma repoint_test2 : (.ofNat 14 false : Fixed 0).repoint 2 false == (.ofNat 14 false) := by
  native_decide
lemma repoint_test3 : (.ofNat 14 false : Fixed 0).repoint 2 true == (.ofNat 14 true) := by
  native_decide
lemma repoint_test4 : (.ofNat 14 false : Fixed 0).repoint 2 true != (.ofNat 14 false) := by
  native_decide
