import Mathlib.Data.Real.Basic
import Ray.Approx.Approx
import Ray.Approx.Fixed
import Ray.Approx.Float
import Ray.Approx.Int
import Ray.Approx.Int64
import Ray.Approx.UInt128
import Ray.Misc.Real

open Pointwise

/-!
## Floating point arithmetic

The floating point number `⟨n,s⟩` represents `n * 2^(s - 2^63)`, where `n : Int64`, `s : UInt64`.
-/

open Set
open scoped Real

/-!
## `Floating` basics
-/

/-- Floating point number -/
structure Floating where
  /-- Unscaled value -/
  n : Int64
  /-- Binary exponent + `2^63` -/
  s : UInt64
  /-- `0` has a single, standardized representation -/
  zero_same : n = 0 → s = 0
  /-- `nan` has a single, standardized representation -/
  nan_same : n = .min → s = .max
  /-- If we're not `0`, `nan`, or denormalized, the high bit of `n` is set -/
  norm : n ≠ 0 → n ≠ .min → s ≠ 0 → 2^62 ≤ n.abs
  deriving DecidableEq

instance : BEq Floating where
  beq x y := x.n == y.n && x.s == y.s

lemma Floating.beq_def {x y : Floating} : (x == y) = (x.n == y.n && x.s == y.s) := rfl

instance : LawfulBEq Floating where
  eq_of_beq {x y} e := by
    induction x
    induction y
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq] at e
    simp only [e.1, e.2]
  rfl {x} := by
    induction x
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq, true_and]

lemma Floating.ext_iff {x y : Floating} : x = y ↔ x.n = y.n ∧ x.s = y.s := by
  induction x; induction y; simp only [mk.injEq]

/-- Standard floating point nan -/
instance : Nan Floating where
  nan := ⟨.min, .max, by decide, by decide, by decide⟩

/-- The `ℝ` that a `Fixed` represents, if it's not `nan` -/
@[pp_dot] noncomputable def Floating.val (x : Floating) : ℝ :=
  ((x.n : ℤ) : ℝ) * (2 : ℝ)^(x.s.toInt - 2^63)

/-- `Fixed` approximates `ℝ` -/
instance : Approx Floating ℝ where
  approx x := if x = nan then univ else {x.val}

/-- `0` has a standard representation -/
instance : Zero Floating where
  zero := ⟨0, 0, by decide, by decide, by decide⟩

-- Definition lemmas
@[simp] lemma Floating.n_zero : (0 : Floating).n = 0 := rfl
@[simp] lemma Floating.s_zero : (0 : Floating).s = 0 := rfl
@[simp] lemma Floating.n_nan : (nan : Floating).n = .min := rfl
@[simp] lemma Floating.s_nan : (nan : Floating).s = .max := rfl

/-- `nan` could be anything -/
@[simp] lemma Floating.approx_nan : approx (nan : Floating) = univ := rfl

@[simp] lemma Floating.val_zero : (0 : Floating).val = 0 := by
  simp only [val, n_zero, Int64.coe_zero, Int.cast_zero, s_zero, zero_mul]

/-- `0 ≠ nan` -/
@[simp] lemma Floating.zero_ne_nan : (0 : Floating) ≠ nan := by decide

/-- `0` is just zero -/
@[simp] lemma Floating.approx_zero : approx (0 : Floating) = {0} := by
  simp only [approx, zero_ne_nan, val_zero, ite_false]

/-- If we're not `nan`, `approx` is a singleton -/
@[simp] lemma Floating.approx_eq_singleton {x : Floating} (n : x ≠ nan) : approx x = {x.val} := by
  simp only [approx, n, ite_false]

@[simp] lemma Floating.val_mem_approx {x : Floating} : x.val ∈ approx x := by
  by_cases n : x = nan
  · simp only [n, approx_nan, mem_univ]
  · simp only [ne_eq, n, not_false_eq_true, approx_eq_singleton, mem_singleton_iff]

/-- If we're not nan, `x.n ≠ .min` -/
lemma Floating.n_ne_min {x : Floating} (n : x ≠ nan) : x.n ≠ .min := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.nan_same n⟩

/-- If we're not zero, `x.n ≠ 0` -/
lemma Floating.n_ne_zero {x : Floating} (n : x ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.zero_same n⟩

/-- If `x.s ≠ 0`, `x.n ≠ 0` -/
lemma Floating.n_ne_zero' {x : Floating} (n : x.s ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  simp only [x.zero_same n]

/-!
### Simplification lemmas used below
-/

@[simp] private lemma u62 : (62 : UInt64).toNat = 62 := rfl
@[simp] private lemma u64 : (64 : UInt64).toNat = 64 := rfl
@[simp] private lemma u65 : (65 : UInt64).toNat = 65 := rfl
@[simp] private lemma u126 : (126 : UInt64).toNat = 126 := rfl
@[simp] private lemma u127 : (127 : UInt64).toNat = 127 := rfl
@[simp] private lemma up62 : (2^62 : UInt64).toNat = 2^62 := rfl
@[simp] private lemma up63 : (2^63 : UInt64).toNat = 2^63 := rfl
@[simp] private lemma ua2 : (2 : ℤ).natAbs = 2 := rfl

/-!
### Conversion to `Float`
-/

/-- Approximate `Floating` by a `Float` -/
@[irreducible, pp_dot] def Floating.toFloat (x : Floating) : Float :=
  bif x == nan then Float.nan else x.n.toFloat.scaleB (x.s.toInt - 2^63)

/-- We print `Fixed s` as an approximate floating point number -/
instance : Repr Floating where
  reprPrec x _ := x.toFloat.toStringFull

/-!
### Negation
-/

instance : Neg Floating where
  neg x := {
    n := -x.n
    s := x.s
    zero_same := by intro h; simp only [neg_eq_zero] at h; exact x.zero_same h
    nan_same := by intro h; simp only [Int64.neg_eq_min] at h; exact x.nan_same h
    norm := by
      intro z n d
      simp only [ne_eq, neg_eq_zero, Int64.neg_eq_min] at z n
      simp only [ne_eq, not_false_eq_true, Int64.abs_neg, z, n, x.norm, d] }

@[simp] lemma Floating.n_neg {x : Floating} : (-x).n = -x.n := rfl
@[simp] lemma Floating.s_neg {x : Floating} : (-x).s = x.s := rfl

/-- Negation propagates `nan` -/
@[simp] lemma Floating.neg_nan : (-nan : Floating) = nan := by
  simp only [Floating.ext_iff, Floating.n_neg, Floating.n_nan, Int64.neg_min, Floating.s_neg,
    Floating.s_nan, and_self]

/-- Negation preserves `nan` -/
@[simp] lemma Floating.neg_eq_nan_iff {x : Floating} : -x = nan ↔ x = nan := by
  simp only [ext_iff, n_neg, n_nan, Int64.neg_eq_min, s_neg, s_nan]

/-- `-0 = 0` -/
@[simp] lemma Floating.neg_zero : (-0 : Floating) = 0 := by
  simp only [ext_iff, n_neg, n_zero, s_neg, s_zero, and_self, _root_.neg_zero]

/-- Negation preserves `0` -/
@[simp] lemma Floating.neg_eq_zero_iff {x : Floating} : -x = 0 ↔ x = 0 := by
  simp only [ext_iff, n_neg, n_zero, neg_eq_zero, s_neg, s_zero]

/-- Negation flips `.val`, except at `nan` -/
@[simp] lemma Floating.val_neg {x : Floating} (n : x ≠ nan) : (-x).val = -x.val := by
  rw [Floating.val, Floating.val]
  simp only [n_neg, s_neg, ←neg_mul, Int64.coe_neg (x.n_ne_min n), Int.cast_neg]

/-- Negation negates `approx` -/
@[simp] lemma Floating.approx_neg {x : Floating} : approx (-x) = -approx x := by
  by_cases n : x = nan
  · simp only [n, neg_nan, approx_nan, neg_univ]
  · simp only [ne_eq, neg_eq_nan_iff, n, not_false_eq_true, approx_eq_singleton, val_neg,
      neg_singleton]

/-- `-` is conservative -/
instance : ApproxNeg Floating ℝ where
  approx_neg x := by simp only [Floating.approx_neg, subset_refl]

/-!
### Ordering
-/

/-- Unlike `Float`, we don't worry about `nan` for our comparisons -/
@[irreducible, pp_dot] def Floating.blt (x y : Floating) : Bool :=
  let xn := x.n.isNeg
  let yn := y.n.isNeg
  xn > yn || (xn == yn &&
    ((bif xn then x.s > y.s else x.s < y.s) || (x.s == y.s && x.n.n < y.n.n)))

/-- Unlike `Float`, we don't worry about `nan` for our comparisons -/
@[irreducible, pp_dot] def Floating.ble (x y : Floating) : Bool := !(y.blt x)

-- Ordering instances
instance : LT Floating where lt x y := x.blt y
instance : LE Floating where le x y := x.ble y
instance : DecidableRel (α := Floating) (· < ·) | a, b => by dsimp [LT.lt]; infer_instance
instance : DecidableRel (α := Floating) (· ≤ ·) | a, b => by dsimp [LE.le]; infer_instance
instance : Min Int64 where min x y := bif x.blt y then x else y
instance : Max Int64 where max x y := bif x.blt y then y else x

/-- `<` in more mathematical terms -/
lemma Floating.lt_def {x y : Floating} : x < y ↔ (x.n.isNeg > y.n.isNeg ∨
    (x.n.isNeg = y.n.isNeg ∧ (
      (if x.n.isNeg then x.s > y.s else x.s < y.s) ∨ (x.s = y.s ∧ x.n.n < y.n.n)))) := by
  have e : x < y ↔ x.blt y := by simp only [LT.lt]
  rw [e, blt]
  simp only [gt_iff_lt, bif_eq_if, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    Bool.ite_eq_true_distrib]

/-- `≤` in terms of `<` -/
lemma Floating.le_def {x y : Floating} : x ≤ y ↔ ¬(y < x) := by
  have e0 : y < x ↔ y.blt x := by simp only [LT.lt]
  have e1 : x ≤ y ↔ x.ble y := by simp only [LE.le]
  rw [e0, e1, ble, Bool.not_eq_true', Bool.not_eq_true]

/-- `<` respects `-` -/
@[simp] lemma Floating.neg_lt_neg {x y : Floating} (xm : x ≠ nan) (ym : y ≠ nan) :
    (-x) < (-y) ↔ y < x := by
  simp only [lt_def, n_neg, gt_iff_lt, s_neg, Bool.lt_iff]
  have flip : x ≠ 0 → y ≠ 0 → ((-x.n).n < (-y.n).n ↔ y.n.n < x.n.n) := by
    intro x0 y0
    simp only [Int64.neg_def, UInt64.lt_iff_toNat_lt, UInt64.toNat_neg,
      ←Int64.eq_zero_iff_n_eq_zero, x.n_ne_zero x0, y.n_ne_zero y0, if_false]
    have xs := x.n.n.lt_size
    have ys := y.n.n.lt_size
    omega
  by_cases x0 : x = 0
  · simp only [x0, n_zero, _root_.neg_zero, Int64.isNeg_zero, and_false, s_zero, ite_false,
      Int64.n_zero, false_or, true_and]
    by_cases y0 : y = 0
    · simp only [y0, n_zero, _root_.neg_zero, Int64.isNeg_zero, s_zero, lt_self_iff_false,
        Int64.n_zero, and_false, or_self, ite_self]
    · simp only [Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min ym), Bool.beq_not_iff_ne, ne_eq]
      by_cases yn : y.n.isNeg
      · simp only [yn, not_false_eq_true, true_and, ite_true, false_and, or_false, iff_true,
          UInt64.pos_iff_ne_zero, ←Int64.ne_zero_iff_n_ne_zero, Ne.def, neg_eq_zero, y.n_ne_zero y0,
          and_true, eq_comm (a := (0 : UInt64)), ne_or_eq]
      · simp only [yn, not_true_eq_false, false_and, ite_false, true_and, false_or, false_iff,
          not_or, not_lt, UInt64.nonneg, not_and, implies_true, and_self]
  · by_cases y0 : y = 0
    · simp only [y0, n_zero, _root_.neg_zero, Int64.isNeg_zero, true_and, s_zero, Int64.n_zero,
        and_false, ite_false, false_or]
      by_cases xn : x.n.isNeg
      · simp only [Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm), xn, Bool.not_true, ite_false,
          true_and, false_or, false_and, iff_false, not_or, not_lt, UInt64.nonneg, not_and,
          implies_true, and_self]
      · simp only [Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm), xn, Bool.not_false, ite_true,
          false_and, or_false, true_and, true_iff, UInt64.pos_iff_ne_zero,
          ←Int64.ne_zero_iff_n_ne_zero, Ne.def, x.n_ne_zero x0, not_false_eq_true, and_true,
          eq_comm (a := (0 : UInt64)), ne_or_eq]
    · simp only [Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min ym), Bool.not_eq_false',
      Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm), Bool.not_eq_true', Bool.beq_not_iff_ne,
        ne_eq, Bool.not_not_eq]
      by_cases xn : x.n.isNeg
      · by_cases yn : y.n.isNeg
        · simp only [yn, xn, and_false, ite_false, true_and, false_or, and_true, ite_true,
            flip x0 y0, eq_comm (a := x.s)]
        · simp only [yn, xn, and_self, ite_false, false_and, or_self]
      · by_cases yn : y.n.isNeg
        · simp only [yn, xn, and_self, ite_true, false_and, or_false]
        · simp only [yn, xn, and_true, ite_true, eq_comm (a := x.s), flip x0 y0, true_and,
            false_or, and_false, ite_false]

/-- `nan` appears negative -/
@[simp] lemma Floating.nan_lt_zero : (nan : Floating) < 0 := by native_decide

/-- Our ordering is antireflexive -/
lemma Floating.not_lt_self (x : Floating) : ¬x < x := by
  simp only [lt_def, lt_self_iff_false, ite_self, and_false, or_self, not_false_eq_true]

/-- `<` is antisymmetric -/
lemma Floating.not_lt_of_lt {x y : Floating} (xy : x < y) : ¬(y < x) := by
  simp only [lt_def] at xy ⊢
  by_cases xn : x.n.isNeg
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, gt_iff_lt, lt_self_iff_false, ite_true, true_and, false_or, not_or,
        not_lt, not_and] at xy ⊢
      rcases xy with h | h
      · simp only [h.le, h.ne, IsEmpty.forall_iff, and_self]
      · simp only [h.1, le_refl, h.2.le, forall_true_left, and_self]
    · simp only [yn, xn, gt_iff_lt, ite_false, false_and, or_false, not_lt, Bool.le_true]
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, gt_iff_lt, not_lt.mpr (Bool.false_le _), ite_false, false_and,
        or_self] at xy
    · simp only [xn, yn, gt_iff_lt, lt_self_iff_false, ite_false, true_and, false_or, not_or,
        not_lt, not_and] at xy ⊢
      rcases xy with h | h
      · simp only [h.le, h.ne', IsEmpty.forall_iff, and_self]
      · simp only [h.1, le_refl, h.2.le, forall_true_left, and_self]

/-- `≤` is antisymmetric -/
lemma Floating.le_antisymm' {x y : Floating} (xy : x ≤ y) (yx : y ≤ x) : x = y := by
  simp only [le_def, lt_def] at xy yx
  simp only [ext_iff]
  by_cases xn : x.n.isNeg
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, lt_self_iff_false, ite_true, true_and, false_or, not_or, not_lt,
        not_and] at xy yx
      simp only [le_antisymm xy.1 yx.1, le_refl, forall_true_left, true_and, and_true] at xy yx ⊢
      simp only [Int64.ext_iff, le_antisymm xy yx]
    · simp only [xn, yn, ite_false, false_and, or_false, not_lt, Bool.le_true, Bool.false_lt_true,
        ite_true, not_true_eq_false] at xy yx
  · by_cases yn : y.n.isNeg
    · simp only [xn, yn, Bool.false_lt_true, ite_true, false_and, or_false,
        not_true_eq_false] at xy yx
    · simp only [xn, yn, lt_self_iff_false, ite_false, true_and, false_or, not_or, not_lt,
        not_and] at xy yx
      simp only [le_antisymm xy.1 yx.1, le_refl, forall_true_left, true_and, and_true] at xy yx ⊢
      simp only [Int64.ext_iff, le_antisymm xy yx]

 /-- `x.n.isNeg` determines negativity -/
lemma Floating.isNeg_iff {x : Floating} : x.n.isNeg = decide (x < 0) := by
  by_cases xn : x.n.isNeg
  · simp only [xn, lt_def, n_zero, Int64.isNeg_zero, gt_iff_lt, Bool.false_lt_true, s_zero,
      ite_true, Int64.n_zero, false_and, or_false, decide_True]
  · simp only [xn, lt_def, n_zero, Int64.isNeg_zero, gt_iff_lt, lt_self_iff_false, s_zero,
      ite_false, Int64.n_zero, not_lt.mpr x.n.n.nonneg, and_false, or_false, true_and, false_or,
      false_eq_decide_iff, not_lt, UInt64.nonneg]

/-- Strict upper bound for `↑↑x.n`, if we're normalized and positive -/
@[simp] lemma Floating.le_coe_coe_n {x : Floating} (s0 : x.s ≠ 0) (xn : x.n.isNeg = false) :
    2^62 ≤ ((x.n : ℤ) : ℝ) := by
  by_cases x0 : x = 0
  · simp only [x0, s_zero, ne_eq, not_true_eq_false] at s0
  have xm : x.n ≠ .min := by
    contrapose xn
    simp only [ne_eq, not_not] at xn
    simp only [xn, Int64.isNeg_min, not_false_eq_true]
  have e : (2^62 : ℝ) = (2^62 : ℤ) := by norm_num
  simp only [e, Int.cast_le, x.n.coe_lt_pow, ←Int64.abs_eq_self xn, UInt64.toInt]
  simpa only [UInt64.le_iff_toNat_le, up62, ← Nat.cast_le (α := ℤ), Nat.cast_pow,
    Nat.cast_ofNat] using x.norm (x.n_ne_zero x0) xm s0

/-- Strict upper bound for `↑↑x.n` -/
@[simp] lemma Floating.coe_coe_n_lt {x : Floating} : ((x.n : ℤ) : ℝ) < 2^63 := by
  have e : (2^63 : ℝ) = (2^63 : ℤ) := by norm_num
  simp only [e, Int.cast_lt, x.n.coe_lt_pow]

/-- Strict upper bound for `-↑↑x.n` -/
@[simp] lemma Floating.neg_coe_coe_n_lt {x : Floating} (n : x ≠ nan) : -((x.n : ℤ) : ℝ) < 2^63 := by
  rw [neg_lt]
  have me : (-2 ^ 63 : ℝ) = (Int64.min : ℤ) := by
    simp only [Int64.coe_min', Int.cast_neg, Int.cast_pow, Int.int_cast_ofNat]
  rw [me, Int.cast_lt, Int64.coe_lt_coe]
  exact Ne.lt_of_le (x.n_ne_min n).symm x.n.min_le

/-- Upper bound for `-↑↑x.n` -/
@[simp] lemma Floating.neg_coe_coe_n_le (x : Floating) : -((x.n : ℤ) : ℝ) ≤ 2^63 := by
  by_cases n : x = nan
  · simp only [n, n_nan, Int64.coe_min', Int.cast_neg, Int.cast_pow, Int.int_cast_ofNat, neg_neg,
      le_refl]
  · exact (neg_coe_coe_n_lt n).le

 /-- `nan` is the unique minimum -/
@[simp] lemma Floating.nan_lt {x : Floating} (n : x ≠ nan) : nan < x := by
  simp only [lt_def, n_nan, Int64.isNeg_min, gt_iff_lt, s_nan, Int64.n_min]
  by_cases xn : x.n.isNeg
  · simp only [xn, lt_self_iff_false, ite_true, true_and, false_or, UInt64.lt_iff_toNat_lt, up63]
    simp only [Int64.isNeg_eq_le, decide_eq_true_eq] at xn
    simp only [UInt64.toNat_max, not_lt.mpr xn, and_false, or_false, not_lt,
      UInt64.toNat_le_pow_sub_one]
    contrapose n
    simp only [not_or, not_lt, tsub_le_iff_right, not_and, not_not] at n ⊢
    have se : x.s = .max := by
      simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_max]
      have h := x.s.toNat_le_pow_sub_one
      omega
    simp only [se, UInt64.toNat_max, forall_true_left] at n
    simp only [ext_iff, n_nan, Int64.ext_iff, Int64.n_min, UInt64.eq_iff_toNat_eq,
      UInt64.toNat_2_pow_63, se, s_nan, and_true]
    omega
  · simp only [xn, Bool.false_lt_true, ite_true, false_and, or_false]

/-- `nan` is the minimum -/
@[simp] lemma Floating.nan_le (x : Floating) : nan ≤ x := by
  simp only [le_def, lt_def, n_nan, Int64.isNeg_min, gt_iff_lt, s_nan, Int64.n_min]
  by_cases xn : x.n.isNeg
  · simp only [xn, lt_self_iff_false, ite_true, true_and, false_or, UInt64.lt_iff_toNat_lt, up63]
    simp only [Int64.isNeg_eq_le, decide_eq_true_eq] at xn
    simp only [UInt64.toNat_max, not_lt.mpr xn, and_false, or_false, not_lt,
      UInt64.toNat_le_pow_sub_one]
  · simp only [xn, ite_false, false_and, or_false, not_lt, Bool.le_true]

/-- `nan` is the unique minimum, `val` version -/
@[simp] lemma Floating.nan_val_lt {x : Floating} (n : x ≠ nan) : (nan : Floating).val < x.val := by
  rw [val, val]
  simp only [n_nan, Int64.coe_min', Int.cast_neg, Int.cast_pow, Int.int_cast_ofNat, s_nan, neg_mul,
    UInt64.toInt, UInt64.toNat_max]
  rw [neg_lt, ←neg_mul]
  refine lt_of_lt_of_le (b := 2^63 * 2 ^ ((x.s.toNat : ℤ) - 2 ^ 63)) ?_ ?_
  · rw [mul_lt_mul_iff_of_pos_right two_zpow_pos]
    exact neg_coe_coe_n_lt n
  · refine mul_le_mul_of_nonneg_left ?_ two_pow_pos.le
    apply zpow_le_of_le (by norm_num)
    have h := x.s.toNat_le_pow_sub_one
    omega

/-- `nan` is the minimum, `val` version -/
@[simp] lemma Floating.nan_val_le (x : Floating) : (nan : Floating).val ≤ x.val := by
  by_cases n : x = nan
  · simp only [n, le_refl]
  · exact (nan_val_lt n).le

/-- `nan` is the minimum -/
@[simp] lemma Floating.not_lt_nan (x : Floating) : ¬x < nan := by
  simpa only [le_def] using nan_le x

/-- `x.n.isNeg` determines negativity, `val` version -/
lemma Floating.isNeg_iff_val {x : Floating} : x.n.isNeg = decide (x.val < 0) := by
  rw [val]; symm
  by_cases xn : x.n.isNeg
  · simp only [xn, decide_eq_true_eq, ←not_le, mul_nonneg_iff_of_pos_right two_zpow_pos]
    simpa only [Int.cast_nonneg, not_le, Int64.coe_lt_zero_iff]
  · simp only [xn, decide_eq_false_iff_not, not_lt, gt_iff_lt, two_zpow_pos,
      mul_nonneg_iff_of_pos_right, Int.cast_nonneg, Int64.coe_nonneg_iff]

/-- The order is consistent with `.val`, nonnegative case -/
lemma Floating.val_lt_val_of_nonneg {x y : Floating}
    (xn : x.n.isNeg = false) (yn : y.n.isNeg = false) : x.val < y.val ↔ x < y := by
  rw [val, val, UInt64.toInt, UInt64.toInt, lt_def]
  simp only [xn, yn, gt_iff_lt, lt_self_iff_false, ite_true, true_and, false_or]
  by_cases se : x.s = y.s
  · simp only [se, gt_iff_lt, two_zpow_pos, mul_lt_mul_right, Int.cast_lt, Int64.coe_lt_coe,
      Int64.lt_def, xn, yn, lt_self_iff_false, true_and, false_or, ite_self]
  simp only [ite_false, se, false_and, or_false]
  by_cases xys : x.s < y.s
  · simp only [xys, iff_true]
    have ys0 : y.s ≠ 0 := (trans x.s.nonneg xys).ne'
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_right coe_coe_n_lt two_zpow_pos) ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_coe_coe_n ys0 yn) two_zpow_pos.le)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow, Nat.cast_ofNat]
    apply zpow_le_of_le (by norm_num)
    simp only [UInt64.lt_iff_toNat_lt] at xys
    omega
  · simp only [xys, iff_false, not_lt]
    replace xys := (Ne.symm se).lt_of_le (not_lt.mp xys)
    have xs0 : x.s ≠ 0 := (trans y.s.nonneg xys).ne'
    refine le_trans (mul_le_mul_of_nonneg_right coe_coe_n_lt.le two_zpow_pos.le) ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_coe_coe_n xs0 xn) two_zpow_pos.le)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow, Nat.cast_ofNat]
    apply zpow_le_of_le (by norm_num)
    simp only [UInt64.lt_iff_toNat_lt] at xys
    omega

/-- The order is consistent with `.val` -/
@[simp] lemma Floating.val_lt_val {x y : Floating} : x.val < y.val ↔ x < y := by
  by_cases xn : x.n.isNeg
  · by_cases yn : y.n.isNeg
    · by_cases xm : x = nan
      · by_cases ym : y = nan
        · simp only [xm, ym, lt_self_iff_false, not_lt_nan]
        · simp only [xm, ne_eq, ym, not_false_eq_true, nan_val_lt, nan_lt]
      · by_cases ym : y = nan
        · simp only [ym, not_lt_nan, iff_false, not_lt, nan_val_le]
        · by_cases x0 : x = 0
          · simp only [x0, val_zero]
            have h0 : y < 0 := by simpa only [isNeg_iff, decide_eq_true_eq] using yn
            have h1 : y.val < 0 := by simpa only [isNeg_iff_val, decide_eq_true_eq] using yn
            simp only [not_lt.mpr h1.le, not_lt_of_lt h0]
          · by_cases y0 : y = 0
            · simp only [y0, val_zero]
              have h0 : x < 0 := by simpa only [isNeg_iff, decide_eq_true_eq] using xn
              have h1 : x.val < 0 := by simpa only [isNeg_iff_val, decide_eq_true_eq] using xn
              simp only [h1, h0]
            · rw [←neg_lt_neg ym xm, ←neg_lt_neg_iff, ←val_neg xm, ←val_neg ym]
              apply val_lt_val_of_nonneg
              · simpa only [n_neg, Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min ym),
                  Bool.not_eq_false']
              · simpa only [n_neg, Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xm),
                  Bool.not_eq_false']
    · simp only [Bool.not_eq_true] at yn
      trans True
      · simp only [isNeg_iff_val, decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at xn yn
        simp only [iff_true]
        linarith
      · simp only [lt_def, xn, yn, gt_iff_lt, Bool.false_lt_true, ite_true, false_and, or_false]
  · by_cases yn : y.n.isNeg
    · simp only [Bool.not_eq_true] at xn
      trans False
      · simp only [isNeg_iff_val, decide_eq_true_eq, decide_eq_false_iff_not, not_lt] at xn yn
        simp only [iff_false, not_lt]
        linarith
      · simp only [lt_def, xn, yn, gt_iff_lt, ite_false, false_and, or_false, false_iff, not_lt,
        Bool.le_true]
    · simp only [Bool.not_eq_true] at xn yn
      exact val_lt_val_of_nonneg xn yn

/-- The order is consistent with `.val` -/
@[simp] lemma Floating.val_le_val {x y : Floating} : x.val ≤ y.val ↔ x ≤ y := by
  rw [←not_lt, le_def, not_iff_not, val_lt_val]

 /-- `Floating` is a linear order (though not an ordered algebraic structure) -/
instance : LinearOrder Floating where
  le_refl x := by simp only [←Floating.val_le_val, le_refl]
  le_trans x y z := by simp only [←Floating.val_le_val]; apply le_trans
  le_antisymm x y := Floating.le_antisymm'
  le_total x y := by simp only [←Floating.val_le_val]; apply le_total
  lt_iff_le_not_le x y := by
    simp only [←Floating.val_lt_val, ←Floating.val_le_val]; apply lt_iff_le_not_le
  decidableLE x y := by infer_instance
  min_def x y := by
    simp only [min, Int64.blt_eq_decide_lt, bif_eq_if, decide_eq_true_eq]
  max_def x y := by
    simp only [max, Int64.blt_eq_decide_lt, bif_eq_if, decide_eq_true_eq]

/-!
### Standardization: build a `Floating` out of `n : Int64`, s : UInt64`
-/

/-
-- DO NOT SUBMIT: Do I need preorder?
/-- Typeclass for `UInt64` and `UInt128` to express what we need for standardization.
    This is a mess, but for now I'm going to just push ahead. -/
class Low (I : Type) (U : outParam Type) [Zero I] [Zero U] [Preorder U] where
  nonneg (n : U) : 0 ≤ n
  toNat : U → ℕ
  toInt : I → ℤ
  abs (n : I) : U
  log2 (n : U) : UInt64
  bits' : UInt64
  min : I
  abs_zero : abs 0 = 0
  log2_zero : log2 0 = 0
  toNat_log2 (n : U) : (log2 n).toNat = Nat.log2 (toNat n)
  ne_zero_iff (n : U) : n ≠ 0 ↔ toNat n ≠ 0
  abs_ne_zero_iff (n : I) : abs n ≠ 0 ↔ n ≠ 0

instance : Low Int64 UInt64 where
  abs := Int64.abs
  log2 := UInt64.log2
  bits' := 64
  min := Int64.min
  abs_zero := Int64.abs_zero
  log2_zero := UInt64.log2_zero
  nonneg _ := UInt64.nonneg
  toNat_log2 _ := UInt64.toNat_log2 _

variable {I U : Type} [Zero I] [Zero U] [Preorder U] [low : Low I U]
-/

/-- Decrease `s` by `g` if possible, saturating at `s = 0`.
    We return `(t, s - t)` where `t` is the normalized exponent. -/
@[irreducible, specialize] def Floating.lower (g s : UInt64) : UInt64 × UInt64 :=
  let t := bif s < g then 0 else s - g
  ⟨t, s - t⟩

/-- `lower` returns small shifts -/
@[simp] lemma Floating.low_d_le (g s : UInt64) : (lower g s).2.toNat ≤ g.toNat := by
  rw [lower]
  simp only [bif_eq_if, decide_eq_true_eq]
  split_ifs with h
  · simp only [sub_zero, UInt64.toNat_le_toNat, h.le]
  · apply le_of_eq; ring_nf

/-- `lower` reduces the exponent -/
lemma Floating.low_le_s (g s : UInt64) : (lower g s).1 ≤ s := by
  rw [lower]
  simp only [bif_eq_if, decide_eq_true_eq]
  split_ifs with h
  · exact UInt64.nonneg
  · simp only [not_lt] at h
    exact UInt64.sub_le h

/-- `lower` reduces the exponent -/
lemma Floating.low_le_s' {g s : UInt64} : (lower g s).1.toNat ≤ s.toNat :=
  (UInt64.le_iff_toNat_le _ _).mp (low_le_s g s)

/-- `lower.2` in terms of `lower.1`, expressed in terms of `ℕ` -/
lemma Floating.low_s_2_eq {g s : UInt64} : (lower g s).2.toNat = s.toNat - (lower g s).1.toNat := by
  have e : (lower g s).2 = s - (lower g s).1 := by rw [lower]
  rw [e, UInt64.toNat_sub (low_le_s _ s)]

@[simp] lemma Floating.log2_g_le_62 {n : Int64} (nm : n ≠ .min) : n.abs.log2 ≤ 62 := by
  by_cases n0 : n = 0
  · simp only [n0, Int64.abs_zero, UInt64.log2_zero, UInt64.nonneg]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_log2, u62]
  suffices h : n.abs.toNat.log2 < 63 by omega
  refine (Nat.log2_lt ?_).mpr ?_
  · simpa only [←UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_ne_zero_iff]
  · rwa [Int64.toNat_abs, Int64.natAbs_lt_pow_iff]

@[simp] lemma Floating.log2_g_le_62' {n : Int64} (nm : n ≠ .min) : n.abs.toNat.log2 ≤ 62 := by
  rw [←u62, ←UInt64.toNat_log2, ←UInt64.le_iff_toNat_le]; exact log2_g_le_62 nm

/-- `lower` returns shifts under `62` -/
@[simp] lemma Floating.low_d_le_62 {n : Int64} (nm : n ≠ .min) (s : UInt64) :
    (lower (62 - n.abs.log2) s).2.toNat ≤ 62 := by
  refine le_trans (low_d_le _ s) ?_
  rw [UInt64.toNat_sub (log2_g_le_62 nm), u62]
  apply Nat.sub_le

/-- `low` doesn't overflow -/
@[simp] lemma Floating.low_lt {n : Int64} (nm : n ≠ .min) (s : UInt64) :
    n.abs.toNat * 2 ^ (lower (62 - n.abs.log2) s).2.toNat < 2 ^ 63 := by
  refine lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_log2_self (n := n.abs.toNat))
    (Nat.pow_le_pow_of_le_right (by positivity) (low_d_le _ s)) (by positivity)) ?_
  simp only [← Nat.pow_add, ←Nat.add_sub_assoc (log2_g_le_62' nm), UInt64.toNat_log2,
    UInt64.toNat_sub (log2_g_le_62 nm), u62]
  exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)

/-- `low` doesn't overflow -/
@[simp] lemma Floating.low_lt' {n : Int64} (nm : n ≠ .min) (s : UInt64) :
    |(n : ℤ) * 2 ^ (lower (62 - n.abs.log2) s).2.toNat| < 2 ^ 63 := by
  have h := low_lt nm s
  generalize (lower n s).2.toNat = k at h
  refine lt_of_le_of_lt (abs_mul _ _).le ?_
  simp only [←Int.coe_natAbs, ←Int64.toNat_abs, abs_pow, abs_two]
  rw [←Nat.cast_lt (α := ℤ)] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- `lower` respects `ℤ` conversion -/
lemma Floating.coe_low_s {n : Int64} {s : UInt64} (nm : n ≠ .min) :
    ((n <<< (lower (62 - n.abs.log2) s).2 : Int64) : ℤ) =
      (n : ℤ) * 2^(lower (62 - n.abs.log2) s).2.toNat := by
  rw [Int64.coe_shiftLeft (lt_of_le_of_lt (low_d_le_62 nm s) (by norm_num))]
  have d := low_d_le_62 nm s
  rw [←Nat.pow_div (by omega) (by norm_num), Nat.lt_div_iff_mul_lt, mul_comm]
  · exact low_lt nm s
  · rw [Nat.pow_dvd_pow_iff_le_right (by omega)]; omega

/-- `of_ns` doesn't create `nan` -/
lemma Floating.of_ns_ne_nan {n : Int64} {s : UInt64} (nm : n ≠ .min) :
    n <<< (lower (62 - n.abs.log2) s).2 ≠ .min := by
  intro m; contrapose m
  have h := low_lt' nm s
  simp only [abs_lt] at h
  rw [←Int64.coe_eq_coe, coe_low_s nm, Int64.coe_min']
  exact ne_of_gt h.1

/-- `of_ns` satisfies `norm` -/
lemma Floating.of_ns_norm {n : Int64} {s : UInt64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    n <<< (lower (62 - n.abs.log2) s).2 ≠ 0 → n <<< (lower (62 - n.abs.log2) s).2 ≠ Int64.min →
      (lower (62 - n.abs.log2) s).1 ≠ 0 → 2 ^ 62 ≤ (n <<< (lower (62 - n.abs.log2) s).2).abs := by
  intro _ _ sm
  rw [UInt64.le_iff_toNat_le, up62, Int64.toNat_abs, coe_low_s nm, Int.natAbs_mul,
    Int.natAbs_pow, ua2, ←Int64.toNat_abs]
  rw [lower] at sm ⊢
  simp only [Bool.cond_decide, ne_eq, ite_eq_left_iff, not_lt, not_forall, exists_prop] at sm ⊢
  generalize hd : s - (s - (62 - n.abs.log2)) = d
  simp only [not_lt.mpr sm.1, if_false, hd]
  have a0 : n.abs.toNat ≠ 0 := by
    simpa only [ne_eq, ← UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_eq_zero_iff]
  refine le_trans ?_ (Nat.mul_le_mul_right _ (Nat.log2_self_le a0))
  rw [←pow_add]
  refine Nat.pow_le_pow_of_le_right (by norm_num) ?_
  rw [←hd]
  simp only [Int64.sub_def, sub_sub_cancel]
  rw [UInt64.toNat_sub (log2_g_le_62 nm), u62]
  omega

/-- Construct a `Floating` given possibly non-standardized `n, n` -/
@[irreducible] def Floating.of_ns (n : Int64) (s : UInt64) : Floating :=
  if nm : n = .min then nan else
  if n0 : n = 0 then 0 else
  -- If `n` is small, we decrease `s` until either `n` has the high bit set or `s = .min`
  let t := lower (62 - n.abs.log2) s
  { n := n <<< t.2
    s := t.1
    zero_same := by
      intro z; contrapose z
      simp only [←Int64.coe_eq_coe, Int64.coe_zero, coe_low_s nm, mul_eq_zero, not_or,
        pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, not_false_eq_true, and_true]
      simp only [Int64.coe_eq_zero, n0, not_false_eq_true]
    nan_same := by simp only [of_ns_ne_nan nm, IsEmpty.forall_iff]
    norm := of_ns_norm n0 nm }

/-- `of_ns` propagates `nan` -/
@[simp] lemma Floating.of_ns_nan (s : UInt64) : of_ns .min s = nan := by
  rw [of_ns]; simp only [Int64.min_ne_zero, dite_false, dite_true]

/-- `of_ns` propagates `0` -/
@[simp] lemma Floating.of_ns_zero (s : UInt64) : of_ns 0 s = 0 := by
  rw [of_ns]; simp only [Int64.zero_ne_min, dite_true, dite_eq_ite, ite_false]

/-- `of_ns` preserves `val` -/
lemma Floating.val_of_ns {n : Int64} {s : UInt64} (nm : n ≠ .min) :
    (of_ns n s).val = (n : ℤ) * 2^(s.toInt - 2^63) := by
  rw [of_ns, val]
  simp only [nm, dite_false]
  by_cases n0 : n = 0
  · simp only [n0, Int64.zero_shiftLeft, dite_true, n_zero, Int64.coe_zero, Int.cast_zero, s_zero,
      zero_mul]
  simp only [n0, dite_false, coe_low_s nm, Int.cast_mul, Int.cast_pow, Int.int_cast_ofNat]
  simp only [low_s_2_eq, mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow,
    mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj, Int.cast_eq_zero,
    Int64.coe_eq_zero, n0, or_false, Nat.cast_sub low_le_s', UInt64.toInt]
  ring_nf

/-- `of_ns` doesn't create `nan` -/
@[simp] lemma Floating.of_ns_eq_nan_iff {n : Int64} {s : UInt64} : of_ns n s = nan ↔ n = .min := by
  constructor
  · intro nm; contrapose nm
    rw [of_ns, ext_iff]
    by_cases n0 : n = 0
    · simp only [n0, Int64.zero_ne_min, Int64.zero_shiftLeft, dite_true, dite_eq_ite, ite_false,
        n_zero, n_nan, s_zero, s_nan, false_and, not_false_eq_true]
    · simp only [nm, n0, dite_false, n_nan, of_ns_ne_nan nm, s_nan, false_and, not_false_eq_true]
  · intro h; rw [h, of_ns_nan]

/-- `of_ns` doesn't create `nan` -/
@[simp] lemma Floating.of_ns_ne_nan_iff {n : Int64} {s : UInt64} : of_ns n s ≠ nan ↔ n ≠ .min := by
  simp only [ne_eq, of_ns_eq_nan_iff]

/-!
### Coersion from fixed point to floating point
-/

/-- `Fixed s` to `Floating` by hiding `s` -/
@[irreducible, coe] def Fixed.toFloating {s : Int64} (x : Fixed s) : Floating :=
  .of_ns x.n (s.n + 2^63)

/-- Coersion from `Fixed s` to `Floating` -/
instance {s : Int64} : CoeHead (Fixed s) Floating where
  coe x := x.toFloating

/-- To prove `a ∈ approx (x : Floating)`, we prove `a ∈ approx x` -/
@[mono] lemma Floating.mem_approx_coe {s : Int64} {x : Fixed s} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : Floating) := by
  rw [Fixed.toFloating]
  by_cases n : x = nan
  · simp only [n, Fixed.nan_n, of_ns_nan, approx_nan, mem_univ]
  · have nm : x.n ≠ .min := by simpa only [ne_eq, Fixed.ext_iff, Fixed.nan_n] using n
    simp only [Fixed.approx_eq_singleton n, mem_singleton_iff,
      approx_eq_singleton (of_ns_ne_nan_iff.mpr nm)] at ax ⊢
    rw [ax, Fixed.val, val_of_ns nm]
    simp only [Int64.toInt, Int64.isNeg_eq_le, bif_eq_if, decide_eq_true_eq, Nat.cast_ite,
      Nat.cast_pow, Int.cast_sub, Int.cast_ofNat, Int.cast_ite,
      Int.cast_pow, Int.int_cast_ofNat, Int.cast_zero, UInt64.toInt, UInt64.toNat_add,
      UInt64.toNat_2_pow_63, Int.ofNat_emod, Nat.cast_add, mul_eq_mul_left_iff,
      zero_lt_two, ne_eq, not_false_eq_true, zpow_inj, UInt64.size_eq_pow, Nat.cast_pow,
      Nat.cast_two]
    left
    have sp : s.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
    by_cases le : 2^63 ≤ s.n.toNat
    · have d0 : (s.n.toNat : ℤ) + 2^63 = (s.n.toNat - 2^63) + 2^64 := by ring
      have d1 : 0 ≤ (s.n.toNat : ℤ) - 2^63 := by linarith
      have d2 : (s.n.toNat : ℤ) - 2^63 < 2^64 := by linarith
      simp only [le, CharP.cast_eq_zero, ite_true, gt_iff_lt, zero_lt_two, ne_eq,
        OfNat.ofNat_ne_one, not_false_eq_true, zpow_inj, d0, Int.add_emod_self,
        Int.emod_eq_of_lt d1 d2]
      ring
    · simp only [le, CharP.cast_eq_zero, ite_false, sub_zero, zpow_coe_nat]
      have d0 : 0 ≤ (s.n.toNat : ℤ) + 2^63 := by omega
      have d1 : (s.n.toNat : ℤ) + 2^63 < 2^64 := by linarith
      simp only [Int.emod_eq_of_lt d0 d1, add_sub_cancel, zpow_coe_nat]

/-!
### Scale by changing the exponent
-/

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def Floating.scaleB (x : Floating) (t : Int64) (up : Bool) : Floating :=
  bif t.isNeg then
    let t := (-t).n
    bif x.s < t then
      bif x = nan then nan else of_ns (x.n.shiftRightRound (t-x.s) up) 0
    else of_ns x.n (x.s - t)
  else
    bif .max - t.n < x.s then nan else of_ns x.n (x.s + t.n)

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def Floating.scaleB' (x : Floating) (t : Fixed 0) (up : Bool) : Floating :=
  bif t == nan then nan else scaleB x t.n up

/-- `Floating.scaleB` is conservative -/
@[mono] lemma Floating.mem_approx_scaleB {x : Floating} {t : Int64} {up : Bool} {x' : ℝ}
    (xm : x' ∈ approx x) : x' * 2^(t : ℤ) ∈ rounds (approx (x.scaleB t up)) !up := by
  rw [Floating.scaleB]
  have t0 : 0 < (2 : ℝ) := by norm_num
  by_cases xn : x = nan
  · simp only [Bool.cond_decide, xn, s_nan, decide_True, n_nan, cond_true, of_ns_nan, ite_self,
      Bool.cond_self, approx_nan, rounds_univ, mem_univ]
  simp only [approx_eq_singleton xn, mem_singleton_iff] at xm
  simp only [bif_eq_if, decide_eq_true_eq, xm]
  clear x' xm
  by_cases tn : t.isNeg
  · simp only [tn, ite_true]
    by_cases xt : x.s < (-t).n
    · have yn : x.n.shiftRightRound ((-t).n-x.s) up ≠ .min :=
        Int64.shiftRightRound_ne_min (x.n_ne_min xn) _ _
      simp only [xt, xn, ite_false, ite_true, approx_eq_singleton (of_ns_ne_nan_iff.mpr yn),
        val_of_ns yn, Int64.coe_shiftRightRound, UInt64.toInt_zero, zero_sub, zpow_neg,
        mem_rounds_singleton, Bool.not_eq_true']
      rw [val]
      simp only [mul_comm _ _⁻¹, zpow_sub₀ t0.ne', div_eq_mul_inv, ← mul_assoc]
      simp only [mul_assoc, ← zpow_add₀ t0.ne', gt_iff_lt, inv_pos, two_zpow_pos, mul_le_mul_left]
      induction up
      · simp only [ite_true, ge_iff_le]
        refine le_trans Int.rdiv_le ?_
        simp only [Nat.cast_pow, Nat.cast_ofNat, UInt64.toInt, gt_iff_lt, zero_lt_two, pow_pos,
          div_le_iff, mul_assoc, zpow_mul_pow t0.ne', UInt64.coe_toNat_sub xt.le,
          Int64.toNat_neg tn]
        ring_nf
        simp only [zpow_zero, mul_one, le_refl]
      · simp only [ite_false, ge_iff_le]
        refine le_trans ?_ Int.le_rdiv
        simp only [Nat.cast_pow, Nat.cast_ofNat, UInt64.toInt, gt_iff_lt, zero_lt_two, pow_pos,
          le_div_iff, mul_assoc, zpow_mul_pow t0.ne', UInt64.coe_toNat_sub xt.le,
          Int64.toNat_neg tn]
        ring_nf
        simp only [zpow_zero, mul_one, le_refl]
    · apply subset_rounds
      simp only [xt, ite_false, approx_eq_singleton (of_ns_ne_nan_iff.mpr (x.n_ne_min xn)),
        val_of_ns (x.n_ne_min xn), mem_singleton_iff]
      simp only [not_lt] at xt
      rw [val]
      simp only [mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ← zpow_add₀,
        mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj, Int.cast_eq_zero,
        Int64.coe_eq_zero, UInt64.toInt, UInt64.coe_toNat_sub xt, Int64.toNat_neg tn]
      left
      ring
  · apply subset_rounds
    simp only [tn, ite_false]
    by_cases xt : .max - t.n < x.s
    · simp only [xt, ite_true, approx_nan, mem_univ]
    · simp only [xt, ite_false, approx_eq_singleton (of_ns_ne_nan_iff.mpr (x.n_ne_min xn)),
        val_of_ns (x.n_ne_min xn), mem_singleton_iff]
      simp only [not_lt] at xt
      simp only [Bool.not_eq_true] at tn
      rw [val, mul_assoc, ←zpow_add₀ t0.ne']
      simp only [mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, ne_eq, OfNat.ofNat_ne_one,
        not_false_eq_true, zpow_inj, Int.cast_eq_zero, Int64.coe_eq_zero, UInt64.toInt,
        UInt64.toNat_add_of_le xt, Nat.cast_add, Int64.coe_of_nonneg tn]
      left
      ring

/-!
### Addition and subtraction

To add, we shift the smaller number to near the bigger number, perform a 128-bit addition, and
normalize the result.
-/

/-- Adjust an exponent for addition.  The result is `(t, d+1)`, where `d - 65` is the amount
    to shift left by, and `t` is the final exponent. -/
@[irreducible] def Floating.add_adjust (l s : UInt64) : UInt64 × UInt64 :=
  bif l == 127 then ⟨s+1, 0⟩ else
  let (s, d) := lower (126 - l) s
  (s, d + 1)

/-- Abbreviation for our expanded `n` value -/
def Floating.add_n (r : UInt128) (s : UInt64) (up : Bool) : Int64 :=
  ⟨(if 65 ≤ (add_adjust r.log2 s).2
    then r.lo <<< ((add_adjust r.log2 s).2 - 65)
    else (r.shiftRightRound (65 - (add_adjust r.log2 s).2) up).lo)⟩

/-- `add_adjust` produces small `d + 1` -/
lemma Floating.adjust_d_le (r : UInt128) (s : UInt64) :
    (add_adjust r.log2 s).2.toNat ≤ 127 - r.toNat.log2 := by
  rw [add_adjust]; simp only [bif_eq_if, beq_iff_eq, UInt64.cast_toNat]
  split_ifs with h
  · simp only [UInt64.toNat_zero, zero_le]
  · simp only
    have d0 : r.toNat.log2 ≤ 126 := by
      simp only [UInt64.eq_iff_toNat_eq, UInt128.toNat_log2, u127] at h
      have le := UInt128.log2_le_127' r
      omega
    have d1 : r.log2 ≤ 126 := by simpa only [UInt64.le_iff_toNat_le, UInt128.toNat_log2, u126]
    have d2 : (lower (126 - r.log2) s).2.toNat + 1 ≤ 127 - r.toNat.log2 := by
      refine le_trans (add_le_add_right (low_d_le _ _) _) ?_
      rw [UInt64.toNat_sub d1, u126, UInt128.toNat_log2]
      omega
    rwa [UInt64.toNat_add, UInt64.toNat_one, UInt64.size_eq_pow, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (le_trans d2 (Nat.sub_le _ _)) (by norm_num)

/-- `add_adjust` doesn't overflow `r` -/
lemma Floating.adjust_r_lt_128 (r : UInt128) (s : UInt64) :
    r.toNat < 2 ^ (128 - (add_adjust r.log2 s).2.toNat) := by
  have h0 := adjust_d_le r s
  have h1 := UInt128.log2_le_127' r
  refine lt_of_lt_of_le Nat.lt_log2_self ?_
  exact pow_le_pow_right (by norm_num) (by omega)

/-- `add_adjust` normalizes `r` -/
lemma Floating.adjust_le_r {r : UInt128} {s : UInt64} (r0 : r.toNat ≠ 0)
    (s0 : (add_adjust r.log2 s).1.toNat ≠ 0) :
    2 ^ (127 - (add_adjust r.log2 s).2.toNat) ≤ r.toNat := by
  refine le_trans ?_ (Nat.log2_self_le r0)
  apply pow_le_pow_right (by norm_num)
  rw [add_adjust] at s0 ⊢
  simp only [bif_eq_if, beq_iff_eq, UInt64.eq_iff_toNat_eq, UInt128.toNat_log2, u127, ne_eq,
    tsub_le_iff_right] at s0 ⊢
  by_cases e : r.toNat.log2 = 127
  · simp only [e, ite_true, UInt64.toNat_zero, add_zero, le_refl] at s0 ⊢
  · simp only [e, ite_false] at s0 ⊢
    rw [lower] at s0 ⊢
    simp only [bif_eq_if, decide_eq_true_eq] at s0 ⊢
    by_cases s126 : s < 126 - UInt128.log2 r
    · simp only [s126, ite_true, UInt64.toNat_zero, not_true_eq_false] at s0
    · have d0 : 126 - r.log2 + 1 = 127 - r.log2 := by ring
      simp only [s126, ite_false, sub_sub_cancel, d0, UInt64.toNat_sub (UInt128.log2_le_127 r),
        u127, UInt128.toNat_log2, Nat.add_sub_cancel' (UInt128.log2_le_127' _), le_refl]

/-- `add_adjust` doesn't overflow `r` -/
lemma Floating.adjust_mul_lt_128 (r : UInt128) (s : UInt64) :
    r.toNat * 2 ^ (add_adjust r.log2 s).2.toNat < 2 ^ 128 := by
  have h0 := adjust_d_le r s
  refine lt_of_lt_of_le (mul_lt_mul_of_pos_right (adjust_r_lt_128 r s) (by positivity)) ?_
  rw [←pow_add]
  exact pow_le_pow_right (by norm_num) (by omega)

/-- `add_adjust` normalizes `r` -/
lemma Floating.adjust_le_mul {r : UInt128} {s : UInt64} (r0 : r.toNat ≠ 0)
    (s0 : (add_adjust r.log2 s).1.toNat ≠ 0) :
    2^127 ≤ r.toNat * 2 ^ (add_adjust r.log2 s).2.toNat := by
  refine le_trans ?_ (Nat.mul_le_mul_right _ (adjust_le_r r0 s0))
  simp only [← pow_add]
  exact pow_le_pow_right (by norm_num) (by omega)

lemma Floating.adjust_lo_eq {r : UInt128} {s : UInt64} (a65 : 65 ≤ (add_adjust r.log2 s).2.toNat) :
    r.lo.toNat = r.toNat := by
  apply UInt128.toNat_lo
  exact lt_of_lt_of_le (adjust_r_lt_128 r s) (pow_le_pow_right (by norm_num) (by omega))

/-- `add_adjust` doesn't make `r` too big -/
lemma Floating.adjust_shift_le_63 (r : UInt128) (s : UInt64) (up : Bool)
    (a65 : (add_adjust r.log2 s).2.toNat < 65) :
    (r.shiftRightRound (65 - (add_adjust r.log2 s).2) up).toNat ≤ 2^63 := by
  apply Nat.le_of_lt_succ
  rw [←Nat.cast_lt (α := ℤ), UInt128.toInt_shiftRightRound]
  rw [←Int.cast_lt (α := ℝ)]
  refine lt_of_lt_of_le Int.rdiv_lt ?_
  simp only [Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_succ, Int.cast_add,
    Int.cast_pow, Int.int_cast_ofNat, Int.cast_one, ← le_sub_iff_add_le, add_sub_cancel]
  have a65' : (add_adjust r.log2 s).2 < 65 := by simpa only [UInt64.lt_iff_toNat_lt, u65]
  rw [div_le_iff (by positivity), ←pow_add, UInt64.toNat_sub a65'.le, u65,
    ←Nat.add_sub_assoc a65.le]
  have lt := adjust_r_lt_128 r s
  simp only [← Nat.cast_lt (α := ℝ), Nat.cast_pow, Nat.cast_ofNat] at lt
  exact lt.le

/-- `add_adjust` doesn't make `r` too big -/
lemma Floating.adjust_lo_shift_le_63 (r : UInt128) (s : UInt64) (up : Bool)
    (a65 : (add_adjust r.log2 s).2.toNat < 65) :
    (r.shiftRightRound (65 - (add_adjust r.log2 s).2) up).lo.toNat ≤ 2^63 := by
  have h := adjust_shift_le_63 r s up a65
  rwa [UInt128.toNat_lo (lt_of_le_of_lt h (by norm_num))]

/-- `add_n` produces small `n` values -/
lemma Floating.add_n_le (r : UInt128) (s : UInt64) (up : Bool) (n63 : (add_n r s up).n ≠ 2^63) :
    (add_n r s up).n.toNat < 2^63 := by
  rw [add_n] at n63 ⊢
  simp only [Ne.def, UInt64.eq_iff_toNat_eq, up63] at n63 ⊢
  apply Ne.lt_of_le n63; clear n63
  have r_lt := adjust_r_lt_128 r s
  have mul_lt := adjust_mul_lt_128 r s
  generalize ha : add_adjust r.log2 s = a at r_lt mul_lt
  by_cases a65 : 65 ≤ a.2
  · have d0 : a.2.toNat - 65 < 64 := by have le := adjust_d_le r s; rw [ha] at le; omega
    have d1 : 65 ≤ a.2.toNat := by simpa only [UInt64.le_iff_toNat_le, u65] using a65
    have d2 : 0 < 2^65 := by norm_num
    have d3 : r.lo.toNat = r.toNat := by rw [←ha] at d1; exact adjust_lo_eq d1
    simp only [a65, ite_true, UInt64.toNat_shiftLeft', UInt64.toNat_sub a65, u65,
      Nat.mod_eq_of_lt d0, ← Nat.sub_sub_assoc d1, gt_iff_lt, d3]
    rw [Nat.mod_eq_of_lt]
    · rw [←mul_le_mul_iff_of_pos_right d2, mul_assoc, ←pow_add, ←pow_add, Nat.sub_add_cancel d1]
      exact mul_lt.le
    · exact lt_of_lt_of_le r_lt (pow_le_pow_right (by norm_num) (by omega))
  · simp only [a65, ite_false, gt_iff_lt]
    simp only [← ha, not_le, UInt64.lt_iff_toNat_lt, u65] at a65
    simp only [←ha, adjust_lo_shift_le_63 _ _ _ a65]

/-- `add_adjust` never produces `n = .min` -/
lemma Floating.add_n_ne_min (r : UInt128) (s : UInt64) (up : Bool) (n63 : (add_n r s up).n ≠ 2^63) :
    add_n r s up ≠ .min := by
  rw [←Int64.natAbs_lt_pow_iff]
  have h := add_n_le r s up n63
  have n : (add_n r s up).isNeg = false := by
    simp only [Int64.isNeg_eq_le, not_le.mpr h, decide_false_eq_false]
  rwa [Int64.toInt, n, cond_false, Nat.cast_zero, sub_zero, Int.natAbs_ofNat]

/-- `add_n` respects `ℤ` conversion -/
lemma Floating.coe_add_n {r : UInt128} {s : UInt64} {up : Bool}
    (n63 : (add_n r s up).n ≠ 2^63) :
    (add_n r s up : ℤ) = ((r.toNat : ℤ) * 2^(add_adjust r.log2 s).2.toNat).rdiv (2 ^ 65) up := by
  rw [add_n]
  have d0 := adjust_d_le r s
  have d1 := adjust_r_lt_128 r s
  generalize ha : (add_adjust r.log2 s).2 = a at d0 d1
  by_cases a65 : 65 ≤ a
  · simp only [a65, ite_true]
    have d2 : ∀ n, (2 : ℤ)^n = (2^n : ℕ) := by intro _; simp only [Nat.cast_pow, Nat.cast_ofNat]
    have d3 : ∀ {n}, 2^n ≠ 0 := by intro _; positivity
    have d4 : 65 ≤ a.toNat := by simpa only [UInt64.le_iff_toNat_le, u65] using a65
    have d5 : r.lo.toNat = r.toNat := UInt128.toNat_lo_of_log2_lt (by omega)
    have d6 : r.lo.toNat < 2^63 := by
      by_cases r0 : r.toNat = 0
      · simp only [r0, zero_lt_two, pow_pos, UInt128.toNat_lo]
      · rw [UInt128.toNat_lo_of_log2_lt (by omega)]; rw [←Nat.log2_lt r0]; omega
    have d7 : (a - 65).toNat < 64 := by rw [UInt64.toNat_sub a65, u65]; omega
    have d8 : r.toNat < 2^(63 - (a - 65).toNat) := by
      rw [UInt64.toNat_sub a65, u65, ←Nat.sub_sub_assoc d4]; exact d1
    have d9 : ((⟨r.lo⟩ : Int64) : ℤ) = r.toNat := by
      simpa only [Int64.toInt._eq_1, Int64.isNeg_eq_le, not_le.mpr d6, decide_False, cond_false,
        CharP.cast_eq_zero, sub_zero, Nat.cast_inj]
    have d10 : (⟨r.lo⟩ : Int64).abs.toNat < 2^(63 - (a - 65).toNat) := by
      simp only [Int64.toNat_abs, d9, Int.natAbs_ofNat, d8]
    apply (Int64.coe_shiftLeft d7 d10).trans
    generalize hd : a.toNat - 65 = d
    have d50 : a.toNat = d + 65 := by rw [←hd, Nat.sub_add_cancel d4]
    simp only [d9, d50, UInt64.toNat_sub a65, u65, Nat.add_sub_cancel, pow_add, ←mul_assoc,
      Int.mul_rdiv_cancel d3, d2]
  · simp only [a65, ite_false]
    have a65' : a.toNat < 65 := by simpa only [not_le, UInt64.lt_iff_toNat_lt, u65] using a65
    have d2 : (r.shiftRightRound (65 - a) up).toNat ≤ 2 ^ 63 := by
      rw [←ha] at a65' ⊢; exact adjust_shift_le_63 r s up a65'
    have d3 : (r.shiftRightRound (65 - a) up).toNat < 2^64 := lt_of_le_of_lt d2 (by norm_num)
    have d4 : (r.shiftRightRound (65 - a) up).toNat < 2^63 := by
      rw [add_n] at n63
      simp only [ha, a65, ite_false, Ne.def, UInt64.eq_iff_toNat_eq, up63,
        UInt128.toNat_lo d3] at n63
      exact Ne.lt_of_le n63 d2
    have d5 : (⟨(r.shiftRightRound (65 - a) up).lo⟩ : Int64).isNeg = false := by
      simpa only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, UInt128.toNat_lo d3]
    simp only [Int64.toInt_of_isNeg_eq_false d5, UInt128.toNat_lo d3, UInt128.toInt_shiftRightRound,
      UInt64.toNat_sub (not_le.mp a65).le, u65]
    rw [←Nat.pow_div a65'.le (by norm_num), Int.rdiv_div (pow_dvd_pow _ a65'.le),
      Nat.cast_pow, Nat.cast_ofNat]

/-- `add_adjust` results in normalized `n` -/
lemma Floating.add_n_norm (r : UInt128) (s : UInt64) (up : Bool)
    (n63 : (add_n r s up).n ≠ 2^63) :
    add_n r s up ≠ 0 → add_n r s up ≠ .min → (add_adjust r.log2 s).1 ≠ 0 →
      2^62 ≤ (add_n r s up).abs := by
  intro r0 _ s0
  have e62 : (2^62 : ℤ).toNat = 2^62 := by decide
  simp only [UInt64.le_iff_toNat_le, up62, Int64.toNat_abs, coe_add_n n63]
  rw [Int.natAbs_eq_toNat (Int.rdiv_nonneg (by positivity)), ←e62]
  apply Int.toNat_le_toNat
  refine le_trans ?_ (Int.rdiv_le_rdiv (Bool.false_le _))
  have tp : ∀ n, (2 : ℤ)^n = (2^n : ℕ) := by simp only [Nat.cast_pow, Nat.cast_ofNat, forall_const]
  simp only [Int.rdiv, cond_false, tp, ←Nat.cast_mul, ←Nat.cast_div, ←Int.coe_nat_div, Nat.cast_le]
  rw [Nat.le_div_iff_mul_le (by positivity), ←pow_add]
  refine adjust_le_mul ?_ (UInt64.ne_zero_iff_toNat_ne_zero.mp s0)
  contrapose r0
  simp only [ne_eq, not_not, ←UInt128.eq_zero_iff] at r0 ⊢
  rw [add_n]
  simp only [r0, UInt128.log2_zero, UInt128.zero_lo, UInt64.zero_shiftLeft,
    UInt128.zero_shiftRightRound, ite_self]
  rfl

-- DO NOT SUBMIT: Dead code eliminate the above

/-- Turn an `r * 2^(s - 64 - 2^63)` value into a `Floating` -/
@[irreducible] def Floating.add_shift_r (r : UInt128) (s : UInt64) (up : Bool) :
    Floating :=
  let l := r.log2
  bif l == 127 && s == .max then nan else
  let t := add_adjust l s
  let n := bif 65 ≤ t.2 then r.lo <<< (t.2 - 65) else (r.shiftRightRound (65 - t.2) up).lo
  if n0 : n = 0 then 0 else
  if n63 : n = 2^63 then
    bif t.1 = .max then nan else {
      n := 2^62
      s := t.1 + 1
      zero_same := by intro z; contrapose z; decide
      nan_same := by intro n; contrapose n; decide
      norm := by intro _ _ _; decide }
  else {
    n := ⟨n⟩
    s := t.1
    zero_same := by intro z; clear n63; contrapose n0; rw [Int64.ext_iff] at z; exact not_not.mpr z
    nan_same := by intro m; rw [Int64.ext_iff] at m; exfalso; exact n63 m
    norm := by simp only [Bool.cond_decide] at n63 ⊢ ; exact add_n_norm r s up n63 }

/-- Exactly rounded floating point addition, with `0 < x` and special cases removed -/
@[irreducible, pp_dot, inline] def Floating.pos_add (x y : Floating) (up : Bool) : Floating :=
  -- Shift `y` to be near `x`
  let y := (⟨0, y.n.n⟩ : UInt128).shiftRightRound (x.s - y.s) up
  -- Add, then shift into final position
  add_shift_r ⟨y.lo, x.n.n + y.hi⟩ x.s up

/-- Exactly rounded floating point addition, with most special cases removed -/
@[irreducible, pp_dot, inline] def Floating.add_core (x y : Floating) (up : Bool) : Floating :=
  -- Arrange for x to be positive
  let (z, x, y) := bif x.n.isNeg then (true, -x, -y) else (false, x, y)
  -- Add
  let r := pos_add x y (up != z)
  -- Restore the sign of x
  bif z then -r else r

/-- Exactly rounded floating point addition -/
@[irreducible, pp_dot] def Floating.add (x y : Floating) (up : Bool) : Floating :=
  -- Handle special cases
  bif x == 0 || y == nan then y else
  bif y == 0 || x == nan then x else
  -- Arrange for x to have the larger exponent
  let (x, y) := if y ≤ x then (x, y) else (y, x)
  -- Add
  add_core x y up

/-- `Floating.pos_add` rounds in the correct direction -/
lemma Floating.val_pos_add {x y : Floating} {up : Bool} (xn : x ≠ nan) (yn : y ≠ nan) (x0 : x ≠ 0)
    (y0 : y ≠ 0) (xy : y ≤ x) (x0' : x.n.isNeg = false) :
    x.val + y.val ∈ rounds (approx (x.pos_add y up)) !up := by
  rw [pos_add]
  generalize hz : (⟨0, y.n.n⟩ : UInt128).shiftRightRound (x.s - y.s) up = z
  generalize hzv : ((z.toNat : ℝ) - if y.n.isNeg then 2^127 else 0) *
      2^((x.s.toNat : ℤ) - 2^63) = zv
  generalize hw : (⟨z.lo, x.n.n + z.hi⟩ : UInt128) = w
  simp only [hw]
  have za : if up then y.val ≤ zv else zv ≤ y.val := sorry
  sorry

/-- `Floating.add_core` rounds in the correct direction -/
lemma Floating.val_add_core {x y : Floating} {up : Bool} (xn : x ≠ nan) (yn : y ≠ nan) (x0 : x ≠ 0)
    (y0 : y ≠ 0) (xy : y ≤ x) :
    x.val + y.val ∈ rounds (approx (x.add_core y up)) !up := by
  rw [add_core]
  simp only [bif_eq_if]
  by_cases z : x.n.isNeg
  · simp only [z, ite_true, Bool.xor_true, approx_neg, rounds_neg, Bool.not_not, mem_neg,
      neg_add_rev, add_comm _ (-x).val, ←val_neg xn, ←val_neg yn]
    nth_rw 2 [←Bool.not_not up]
    apply val_pos_add
    repeat simpa only [ne_eq, neg_eq_nan_iff, neg_eq_zero_iff, s_neg, n_neg,
      Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xn), Bool.not_eq_false']
  · simp only [z, ite_false, Bool.xor_false]
    simp only [Bool.not_eq_true] at z
    exact val_pos_add xn yn x0 y0 xy z

/-- `Floating.add` rounds in the correct direction -/
lemma Floating.val_add {x y : Floating} {up : Bool} :
    approx x + approx y ⊆ rounds (approx (x.add y up)) !up := by
  rw [add]
  generalize hs : (if y.s ≤ x.s then (x, y) else (y, x)) = s
  simp only [bif_eq_if, beq_iff_eq, Bool.or_eq_true]
  by_cases x0 : x = 0
  · simp only [x0, ne_eq, zero_ne_nan, not_false_eq_true, approx_eq_singleton, val_zero,
      singleton_add, zero_add, image_id', true_or, or_false, ite_true]
    apply subset_rounds
  simp only [x0, false_or]
  by_cases yn : y = nan
  · simp only [yn, approx_nan, ite_true, rounds_univ, subset_univ]
  simp only [yn, if_false]
  by_cases y0 : y = 0
  · simp only [y0, ne_eq, zero_ne_nan, not_false_eq_true, approx_eq_singleton, val_zero,
      add_singleton, add_zero, image_id', true_or, ite_true]
    apply subset_rounds
  by_cases xn : x = nan
  · simp only [xn, approx_nan, or_true, true_or, ite_true, rounds_univ, subset_univ]
  simp only [ne_eq, xn, not_false_eq_true, approx_eq_singleton, yn, add_singleton, image_singleton,
    or_self, ite_false, singleton_subset_iff]
  simp only [x0, y0, ite_false]
  by_cases xy : y.s ≤ x.s
  · simp only [xy, ite_true] at hs
    simp only [←hs]
    exact val_add_core xn yn x0 y0 xy
  · simp only [xy, ite_false] at hs
    simp only [←hs, add_comm _ y.val]
    exact val_add_core yn xn y0 x0 (not_le.mp xy).le
