import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Pointwise.Interval
import Ray.Approx.Fixed
import Ray.Approx.Real

open Classical
open Pointwise

/-!
## 64-bit fixed point interval arithmetic
-/

open Set
open scoped Real

variable {s t : Int64}

/-- 64-bit fixed point intervals -/
structure Interval (s : Int64) where
  lo : Fixed s
  hi : Fixed s
  deriving DecidableEq, BEq

/-- The most common `Interval` nan.  Not the only one! -/
instance : Nan (Interval s) where
  nan := ⟨nan,nan⟩

/-- `Interval` has nice equality -/
instance : LawfulBEq (Interval s) where
  eq_of_beq {x y} e := by
    induction' x with xlo xhi; induction' y with ylo yhi
    have g : ((xlo == ylo && xhi == yhi) = true) := e
    simp only [Bool.and_eq_true, beq_iff_eq] at g
    simp only [g.1, g.2]
  rfl {x} := by
    have e : (x == x) = (x.lo == x.lo && x.hi == x.hi) := rfl
    simp only [e, beq_self_eq_true, Bool.and_self]

/-- Intervals are equal iff their components are equal -/
lemma Interval.ext_iff {x y : Interval s} : x = y ↔ x.lo = y.lo ∧ x.hi = y.hi := by
  induction x; induction y; simp only [mk.injEq]

/-- `Interval` approximates `ℝ` -/
instance : Approx (Interval s) ℝ where
  approx x := if x.lo = nan ∨ x.hi = nan then univ else Icc x.lo.val x.hi.val

/-- Zero -/
instance : Zero (Interval s) where
  zero := ⟨0,0⟩

/-- Negation -/
instance : Neg (Interval s) where
  neg x := ⟨-x.hi, -x.lo⟩

/-- Addition -/
instance : Add (Interval s) where
  add x y := ⟨x.lo + y.lo, x.hi + y.hi⟩

/-- Subtraction -/
instance : Sub (Interval s) where
  sub x y := ⟨x.lo - y.hi, x.hi - y.lo⟩

/-- Intersection -/
instance : Inter (Interval s) where
  inter x y := ⟨max x.lo y.lo, min x.hi y.hi⟩

/-- Union -/
instance : Union (Interval s) where
  union x y := ⟨min x.lo y.lo, max x.hi y.hi⟩

/-- `Fixed s` converts to `Interval s` -/
@[coe] def Fixed.toInterval (x : Fixed s) : Interval s := ⟨x,x⟩

/-- `Fixed s` converts to `Interval s` -/
instance : Coe (Fixed s) (Interval s) where
  coe x := x.toInterval

/-- Clamp a `Fixed` to be within an `Interval` -/
@[pp_dot] def Interval.clamp (x : Interval s) (y : Fixed s) : Fixed s :=
  ⟨max x.lo.n (min x.hi.n y.n)⟩

-- Bounds properties of interval arithmetic
lemma Interval.nan_def : (nan : Interval s) = ⟨nan,nan⟩ := rfl
lemma Interval.neg_def {x : Interval s} : -x = ⟨-x.hi, -x.lo⟩ := rfl
lemma Interval.add_def {x y : Interval s} : x + y = ⟨x.lo + y.lo, x.hi + y.hi⟩ := rfl
lemma Interval.sub_def {x y : Interval s} : x - y = ⟨x.lo - y.hi, x.hi - y.lo⟩ := rfl
lemma Interval.inter_def {x y : Interval s} : x ∩ y = ⟨max x.lo y.lo, min x.hi y.hi⟩ := rfl
lemma Interval.union_def {x y : Interval s} : x ∪ y = ⟨min x.lo y.lo, max x.hi y.hi⟩ := rfl
@[simp] lemma Interval.lo_nan : (nan : Interval s).lo = nan := rfl
@[simp] lemma Interval.hi_nan : (nan : Interval s).hi = nan := rfl
@[simp] lemma Interval.lo_neg {x : Interval s} : (-x).lo = -x.hi := rfl
@[simp] lemma Interval.hi_neg {x : Interval s} : (-x).hi = -x.lo := rfl
@[simp] lemma Interval.lo_zero : (0 : Interval s).lo = 0 := rfl
@[simp] lemma Interval.hi_zero : (0 : Interval s).hi = 0 := rfl
@[simp] lemma Interval.approx_zero : approx (0 : Interval s) = {0} := by
  simp only [approx, lo_zero, Fixed.val_zero, ite_false, hi_zero, Ici_inter_Iic, Icc_self,
    Fixed.zero_ne_nan, false_or]
@[simp] lemma Interval.approx_nan : approx (nan : Interval s) = univ := by
  simp only [approx, nan, ite_true, inter_self, true_or]
@[simp] lemma Interval.approx_of_lo_nan {x : Interval s} (h : x.lo = nan) : approx x = univ := by
  simp only [approx, h, true_or, ite_true]
@[simp] lemma Interval.approx_of_hi_nan {x : Interval s} (h : x.hi = nan) : approx x = univ := by
  simp only [approx, h, or_true, ite_true]
@[simp] lemma Interval.lo_fixed {x : Fixed s} : (x : Interval s).lo = x := rfl
@[simp] lemma Interval.hi_fixed {x : Fixed s} : (x : Interval s).hi = x := rfl
@[simp] lemma Interval.union_nan {x : Interval s} : x ∪ nan = nan := by
  simp only [nan_def, union_def, Fixed.min_nan, Fixed.max_nan]
@[simp] lemma Interval.nan_union {x : Interval s} : nan ∪ x = nan := by
  simp only [nan_def, union_def, Fixed.nan_min, Fixed.nan_max]

/-- We print `Interval s` as an approximate floating point interval -/
instance : Repr (Interval s) where
  reprPrec x _ := "[" ++ repr x.lo ++ "," ++ repr x.hi ++ "]"

/-- `x - y = x + (-y)` -/
lemma Interval.sub_eq_add_neg (x y : Interval s) : x - y = x + (-y) := by
  simp only [sub_def, Fixed.sub_eq_add_neg, add_def, lo_neg, hi_neg]

/-- `Interval.neg` respects `approx` -/
instance : ApproxNeg (Interval s) ℝ where
  approx_neg x := by
    by_cases n : x.lo = nan ∨ x.hi = nan
    · rcases n with n | n; repeat simp [n, approx]
    simp only [not_or] at n
    simp only [approx, Interval.lo_neg, Interval.hi_neg, Set.inter_neg, n.1, n.2, false_or,
      if_false, Fixed.neg_eq_nan, preimage_neg_Icc, Fixed.val_neg n.1, Fixed.val_neg n.2,
      subset_refl]

/-- `Interval.add` respects `approx` -/
instance : ApproxAdd (Interval s) ℝ where
  approx_add x y := by
    simp only [approx]
    by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan
    · rcases n with n | n | n | n; repeat simp [n, Set.univ_add, Interval.add_def]
    simp only [not_or] at n
    rcases n with ⟨n0,n1,n2,n3⟩
    simp only [n0, n1, or_self, ite_false, n2, n3, Interval.add_def]
    split_ifs with h
    · rcases h with h | h; repeat simp only [h, subset_univ]
    simp only [not_or] at h
    simp only [Fixed.val_add h.1, Fixed.val_add h.2]
    apply Set.Icc_add_Icc_subset

/-- `Interval.sub` respects `approx` -/
instance : ApproxSub (Interval s) ℝ where
  approx_sub x y := by
    simp only [Interval.sub_eq_add_neg, sub_eq_add_neg]
    refine subset_trans ?_ (approx_add x (-y))
    refine subset_trans ?_ (image2_subset_left (approx_neg _))
    simp only [←Set.image2_sub, ←Set.image_neg, image2_image_right, ←image2_add, image2_image_right,
      ←sub_eq_add_neg, subset_refl]

/-- `Interval` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup (Interval s) ℝ where

/-- `Interval` `approx` is `OrdConncted` -/
instance : ApproxConnected (Interval s) ℝ where
  connected x := by
    simp only [approx]
    split_ifs
    · exact ordConnected_univ
    · exact ordConnected_Icc

/-- `Interval.inter` respects `approx` -/
lemma Interval.approx_inter {x y : Interval s} : approx x ∩ approx y ⊆ approx (x ∩ y) := by
  intro a ⟨ax,ay⟩
  simp only [approx, mem_ite_univ_left, mem_Icc, Inter.inter, Fixed.max_eq_nan, Fixed.min_eq_nan,
    Fixed.val_min, le_min_iff] at ax ay ⊢
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, n1, or_self, not_false_eq_true, forall_true_left, n2, n3, Fixed.val_max n0 n2,
    max_le_iff] at ax ay ⊢
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  repeat linarith

/-- `Interval.union` is commutative -/
lemma Interval.union_comm {x y : Interval s} : x ∪ y = y ∪ x := by
  simp only [Union.union, Interval.ext_iff, Fixed.min_comm, Fixed.max_comm]

/-- `Interval.union` respects `approx` -/
lemma Interval.approx_union_left {x y : Interval s} : approx x ⊆ approx (x ∪ y) := by
  intro a ax
  simp only [approx, mem_if_univ_iff, Union.union, Fixed.min_eq_nan, Fixed.max_eq_nan] at ax ⊢
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, n1, or_self, not_false_eq_true, mem_Icc, forall_true_left, n2, n3, Fixed.val_min,
    min_le_iff, Fixed.val_max n1 n3, le_max_iff] at ax ⊢
  simp only [ax.1, true_or, ax.2, and_self]

/-- `Interval.union` respects `approx` -/
lemma Interval.approx_union_right {x y : Interval s} : approx y ⊆ approx (x ∪ y) := by
  rw [Interval.union_comm]; exact approx_union_left

/-- `Interval.union` respects `approx` -/
lemma Interval.approx_union {x y : Interval s} : approx x ∪ approx y ⊆ approx (x ∪ y) :=
  union_subset approx_union_left approx_union_right

/-- `mono` version of `Interval.approx_inter` -/
@[mono] lemma Interval.subset_approx_inter {s : Set ℝ} {x y : Interval t}
    (sx : s ⊆ approx x) (sy : s ⊆ approx y) : s ⊆ approx (x ∩ y) :=
  subset_trans (subset_inter sx sy) Interval.approx_inter

/-- If an `Interval` is nonempty, the expected inequality usually holds -/
lemma Interval.le_of_nonempty {x : Interval s} (a : (approx x).Nonempty) (hn : x.hi ≠ nan) :
    x.lo.val ≤ x.hi.val := by
  rcases a with ⟨a,h⟩
  simp only [approx, hn, or_false] at h
  by_cases ln : x.lo = nan
  · simp only [Fixed.val, ln, nan, mul_le_mul_right two_zpow_pos, Int.cast_le, Int64.coe_le_coe,
    Int64.min_le]
  simp only [ln, ite_false, mem_Icc] at h
  linarith

/-- `Interval.clamp` respects `approx` -/
lemma Interval.approx_clamp {x : Interval s} {y : Fixed s} (xn : (approx x).Nonempty) :
    (x.clamp y).val ∈ approx x := by
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n; repeat simp [approx, n]
  rcases not_or.mp n with ⟨ln,hn⟩
  have le := Interval.le_of_nonempty xn hn
  simp only [Fixed.val, gt_iff_lt, two_zpow_pos, mul_le_mul_right, Int.cast_le,
    Int64.coe_le_coe] at le
  simp only [Fixed.val, clamp, approx, ln, hn, or_self, ite_false, mem_Icc, gt_iff_lt, two_zpow_pos,
    mul_le_mul_right, Int.cast_le, Int64.coe_le_coe, le_max_iff, le_refl, le_min_iff, le, true_and,
    true_or, max_le_iff, min_le_iff, and_self]

/-!
### Utility lemmas
-/

/-- Either `approx = ∅` or `x.lo ≤ x.hi` (if we're not nan) -/
lemma Interval.sign_cases {x : Interval s} (a : (approx x).Nonempty) (hn : x.hi ≠ nan) :
    (x.lo.n.isNeg ∧ x.hi.n.isNeg) ∨ (x.lo.n.isNeg = false ∧ x.hi.n.isNeg = false) ∨
    (x.lo.n.isNeg ∧ x.hi.n.isNeg = false) := by
  by_cases ln : x.lo = nan
  · simp only [ln, Fixed.isNeg_nan, true_and, false_and, false_or, Bool.eq_false_or_eq_true]
  · rcases a with ⟨a,h⟩
    simp only [approx, ln, ite_false, hn, mem_inter_iff, mem_Ici, mem_Iic] at h
    replace h := le_trans h.1 h.2
    simp only [Fixed.val, mul_le_mul_right two_zpow_pos, Int.cast_le, Int64.coe_le_coe] at h
    simp only [Int64.isNeg_eq, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
    by_cases ls : x.lo.n < 0
    all_goals by_cases hs : x.hi.n < 0
    all_goals simp_all
    have h := lt_of_le_of_lt (le_trans ls h) hs
    simp only [lt_self_iff_false] at h

/-!
### Interval absolute value
-/

/-- Absolute value -/
instance Interval.instAbs : Abs (Interval s) where
  abs x :=
    let a := abs x.lo
    let b := abs x.hi
    ⟨bif x.lo.n.isNeg != x.hi.n.isNeg then 0 else min a b, max a b⟩

/-- `abs` respects `approx` -/
lemma Interval.approx_abs {x : Interval s} : abs '' approx x ⊆ approx |x| := by
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ approx x = ∅
  · rcases n with n | n | n
    · simp only [approx, n, true_or, ite_true, image_univ, instAbs, Fixed.isNeg_nan, Bool.true_xor,
        Fixed.abs_nan, Bool.cond_not, Fixed.max_eq_nan, Fixed.abs_eq_nan, or_true, subset_univ]
    · simp only [approx, n, or_true, ite_true, image_univ, instAbs, Fixed.isNeg_nan, Bool.xor_true,
        Fixed.abs_nan, Bool.cond_not, Fixed.max_eq_nan, Fixed.abs_eq_nan, subset_univ]
    · simp only [n, image_empty, empty_subset]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨nl,nh,nx⟩
  simp only [approx, nl, nh, or_self, ite_false, instAbs, bif_eq_if, bne_iff_ne, ne_eq, ite_not,
    Fixed.max_eq_nan, Fixed.abs_eq_nan, or_false, subset_if_univ_iff]
  simp only [subset_def, mem_Icc, Fixed.val_max (Fixed.abs_ne_nan.mpr nl) (Fixed.abs_ne_nan.mpr nh),
    le_max_iff, apply_ite (f := fun x ↦ Fixed.val x), Fixed.val_zero, Fixed.val_min,
    Fixed.val_abs nl, Fixed.val_abs nh, mem_image]
  rcases sign_cases nx nh with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals simp only [ls, hs, if_true, if_false, Fixed.zero_ne_nan, not_false_iff, true_implies]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg] at ls hs
  · intro _ a ⟨b,⟨lb,bh⟩,ba⟩; simp only [min_le_iff, abs_of_neg ls, abs_of_neg hs, ←ba]
    rcases nonpos_or_nonneg b with bs | bs
    · simp only [abs_of_nonpos bs]; exact ⟨Or.inr (by linarith), Or.inl (by linarith)⟩
    · simp only [abs_of_nonneg bs]; exact ⟨Or.inr (by linarith), Or.inl (by linarith)⟩
  · intro _ a ⟨b,⟨lb,bh⟩,ba⟩; simp only [min_le_iff, abs_of_nonneg ls, abs_of_nonneg hs, ←ba]
    rcases nonpos_or_nonneg b with bs | bs
    · simp only [abs_of_nonpos bs]; exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
    · simp only [abs_of_nonneg bs]; exact ⟨Or.inl (by linarith), Or.inr (by linarith)⟩
  · intro a ⟨b,⟨lb,bh⟩,ba⟩; simp only [min_le_iff, abs_of_neg ls, abs_of_nonneg hs, ←ba]
    rcases nonpos_or_nonneg b with bs | bs
    · simp only [abs_of_nonpos bs]; exact ⟨by linarith, Or.inl (by linarith)⟩
    · simp only [abs_of_nonneg bs]; exact ⟨by linarith, Or.inr (by linarith)⟩

/-- `abs` preserves nonnegative intervals -/
lemma Interval.abs_of_nonneg {x : Interval s} (h : 0 ≤ x.lo.val)
    (ax : (approx x).Nonempty) : approx |x| = approx x := by
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n; repeat simp [instAbs, n]
  rcases not_or.mp n with ⟨n0,n1⟩
  have lh := le_of_nonempty ax n1
  have h' := le_trans h lh
  simp only [approx, instAbs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide,
    ite_not, not_lt.mpr h, not_lt.mpr h', ite_true, Fixed.min_eq_nan, Fixed.abs_eq_nan, n0, n1,
    or_self, Fixed.max_eq_nan, Fixed.val_min, Fixed.val_abs n0, _root_.abs_of_nonneg h,
    Fixed.val_abs n1, _root_.abs_of_nonneg h', min_eq_left lh,
    Fixed.val_max (Fixed.abs_ne_nan.mpr n0) (Fixed.abs_ne_nan.mpr n1), max_eq_right lh, ite_false]

/-- `abs` negates nonpositive intervals -/
lemma Interval.abs_of_nonpos {x : Interval s} (h : x.hi.val ≤ 0)
    (ax : (approx x).Nonempty) : approx |x| = -approx x := by
  by_cases n0 : x.lo = nan
  · simp only [instAbs, n0, Fixed.isNeg_nan, Bool.true_xor, Fixed.abs_nan, Bool.cond_not,
      Fixed.max_eq_nan, Fixed.abs_eq_nan, true_or, approx_of_hi_nan, approx_of_lo_nan, neg_univ]
  by_cases n1 : x.hi = nan
  · simp only [instAbs, n1, Fixed.isNeg_nan, Bool.xor_true, Fixed.abs_nan, Bool.cond_not,
      Fixed.max_eq_nan, Fixed.abs_eq_nan, or_true, approx_of_hi_nan, neg_univ]
  have lh := le_of_nonempty ax n1
  have h' := le_trans lh h
  simp only [approx, instAbs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide,
    ite_not, Fixed.max_eq_nan, Fixed.abs_eq_nan, n0, n1, or_self, or_false,
    Fixed.val_max (Fixed.abs_ne_nan.mpr n0) (Fixed.abs_ne_nan.mpr n1), Fixed.val_abs n0,
    _root_.abs_of_nonpos h', Fixed.val_abs n1, _root_.abs_of_nonpos h, ite_false, preimage_neg_Icc,
    apply_ite (f := fun x ↦ x = nan), apply_ite (f := fun x : Fixed s ↦ x.val), Fixed.zero_ne_nan,
    Fixed.min_eq_nan, Fixed.val_min, min_eq_right (neg_le_neg lh), Fixed.val_zero,
    max_eq_left (neg_le_neg lh)]
  by_cases h0 : x.hi.val = 0
  · by_cases l0 : x.lo.val = 0
    · simp only [l0, lt_self_iff_false, h0, ite_self, neg_zero, Icc_self, ite_false]
    · simp only [h0, lt_self_iff_false, iff_false, not_lt, not_le.mpr (Ne.lt_of_le l0 h'), ite_self,
        neg_zero, ite_false]
  · replace h0 := Ne.lt_of_le h0 h
    simp only [lt_of_le_of_lt lh h0, h0, ite_self, ite_true, ite_false]

/-- `|x|.lo` is nonneg if inputs are not `nan` -/
lemma Interval.abs_nonneg {x : Interval s} (n0 : x.lo ≠ nan) (n1 : x.hi ≠ nan) :
    0 ≤ |x|.lo.val := by
  simp only [instAbs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not,
    apply_ite (f := fun x : Fixed s ↦ 0 ≤ x.val), Fixed.val_min, le_min_iff, Fixed.val_zero,
    le_refl, Fixed.val_abs n0, Fixed.val_abs n1, _root_.abs_nonneg, true_and, ite_self]

/-- `|x|.lo` is pos if inputs are not `nan` or `0` and have the same sign -/
lemma Interval.abs_pos {x : Interval s} (n0 : x.lo ≠ nan) (n1 : x.hi ≠ nan)
    (l0 : x.lo ≠ 0) (h0 : x.hi ≠ 0) (lh : x.lo.val < 0 ↔ x.hi.val < 0) : 0 < |x|.lo.val := by
  refine Ne.lt_of_le (Ne.symm ?_) (Interval.abs_nonneg n0 n1)
  contrapose l0
  simp only [instAbs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not, lh,
    ite_true, Fixed.val_min, Fixed.val_abs n0, Fixed.val_abs n1, not_not,
    ←Fixed.val_eq_zero_iff] at l0 ⊢
  have nonpos : |x.lo.val| ≤ 0 := by
    cases' min_le_iff.mp (le_of_eq l0) with h h
    · exact h
    · exfalso
      rw [←Fixed.val_ne_zero_iff, Ne.def, ←abs_eq_zero] at h0
      exact not_le.mpr (Ne.lt_of_le h0 h) (_root_.abs_nonneg _)
  exact abs_eq_zero.mp (le_antisymm nonpos (_root_.abs_nonneg _))

/-- `|x|` propagates `nan` from `lo` to `hi` -/
lemma Interval.abs_eq_nan_of_lo {x : Interval s} (n : x.lo = nan) : |x|.hi = nan := by
  simp only [instAbs, n, Fixed.isNeg_nan, Bool.true_xor, Fixed.abs_nan, Bool.cond_not,
    Fixed.max_eq_nan, Fixed.abs_eq_nan, true_or]

/-- `|x|` propagates `nan` from `hi` to `hi` -/
lemma Interval.abs_eq_nan_of_hi {x : Interval s} (n : x.hi = nan) : |x|.hi = nan := by
  simp only [instAbs, n, Fixed.isNeg_nan, Bool.true_xor, Fixed.abs_nan, Bool.cond_not,
    Fixed.max_eq_nan, Fixed.abs_eq_nan, or_true]

/-!
### Interval multiplication
-/

/-- Multiply, changing `s` -/
@[pp_dot] def Interval.mul (x : Interval s) (y : Interval t) (u : Int64) : Interval u :=
  bif x.lo == nan || x.hi == nan || y.lo == nan || y.hi == nan then nan
  else bif x.lo.n.isNeg != x.hi.n.isNeg && y.lo.n.isNeg != x.hi.n.isNeg then  -- x,y have mixed sign
    ⟨min (x.lo.mul y.hi u false) (x.hi.mul y.lo u false),
     max (x.lo.mul y.lo u true) (x.hi.mul y.hi u true)⟩
  else -- At least one of x,y has constant sign, so we can save multiplications
    let (a,b,c,d) := match (x.lo.n.isNeg, x.hi.n.isNeg, y.lo.n.isNeg, y.hi.n.isNeg) with
      | (false, _, false, _)    => (x.lo, x.hi, y.lo, y.hi)  -- 0 ≤ x, 0 ≤ y
      | (false, _, true, false) => (x.hi, x.hi, y.lo, y.hi)  -- 0 ≤ x, 0 ∈ y
      | (false, _, _, true)     => (x.hi, x.lo, y.lo, y.hi)  -- 0 ≤ x, y ≤ 0
      | (true, false, false, _) => (x.lo, x.hi, y.hi, y.hi)  -- 0 ∈ x, 0 ≤ y
      | (true, false, _, _)     => (x.hi, x.lo, y.lo, y.lo)  -- 0 ∈ x, y ≤ 0 (0 ∈ y is impossible)
      | (_, true, false, _)     => (x.lo, x.hi, y.hi, y.lo)  -- x ≤ 0, 0 ≤ y
      | (_, true, true, false)  => (x.lo, x.lo, y.hi, y.lo)  -- x ≤ 0, 0 ∈ y
      | (_, true, _, true)      => (x.hi, x.lo, y.hi, y.lo)  -- x ≤ 0, y ≤ 0
    ⟨a.mul c u false, b.mul d u true⟩

/-- By default, multiplying intervals preserves `s` -/
instance : Mul (Interval s) where
  mul (x y : Interval s) := x.mul y s

set_option maxHeartbeats 10000000 in
/-- Rewrite `Icc * Icc ⊆ Icc` in terms of inequalities -/
lemma Icc_mul_Icc_subset_Icc {a b c d x y : ℝ} (ab : a ≤ b) (cd : c ≤ d) :
    Icc a b * Icc c d ⊆ Icc x y ↔
      x ≤ a * c ∧ x ≤ a * d ∧ x ≤ b * c ∧ x ≤ b * d ∧
      a * c ≤ y ∧ a * d ≤ y ∧ b * c ≤ y ∧ b * d ≤ y := by
  have am : a ∈ Icc a b := left_mem_Icc.mpr ab
  have bm : b ∈ Icc a b := right_mem_Icc.mpr ab
  have cm : c ∈ Icc c d := left_mem_Icc.mpr cd
  have dm : d ∈ Icc c d := right_mem_Icc.mpr cd
  simp only [←image2_mul, image2_subset_iff]
  constructor
  · intro h
    simp only [mem_Icc (a := x)] at h
    exact ⟨(h _ am _ cm).1, (h _ am _ dm).1, (h _ bm _ cm).1, (h _ bm _ dm).1,
           (h _ am _ cm).2, (h _ am _ dm).2, (h _ bm _ cm).2, (h _ bm _ dm).2⟩
  · simp only [mem_Icc]
    rintro ⟨xac,xad,xbc,xbd,acy,ady,bcy,bdy⟩ u ⟨au,ub⟩ v ⟨cv,vd⟩
    all_goals cases nonpos_or_nonneg c
    all_goals cases nonpos_or_nonneg d
    all_goals cases nonpos_or_nonneg u
    all_goals cases nonpos_or_nonneg v
    all_goals exact ⟨by nlinarith, by nlinarith⟩

set_option maxHeartbeats 10000000 in
/-- `Interval.mul` respects `approx` -/
lemma Interval.approx_mul (x : Interval s) (y : Interval t) (u : Int64) :
    approx x * approx y ⊆ approx (x.mul y u) := by
  -- Handle special cases
  simp only [image2_mul, mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan ∨ approx x = ∅ ∨ approx y = ∅
  · rcases n with n | n | n | n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,n2,n3,nx,ny⟩
  have xi : x.lo.val ≤ x.hi.val := by
    simpa only [approx, n0, n1, or_self, ite_false, nonempty_Icc] using nx
  have yi : y.lo.val ≤ y.hi.val := by
    simpa only [approx, n2, n3, or_self, ite_false, nonempty_Icc] using ny
  simp only [n0, n1, n2, n3, or_self, ite_false]
  -- Record Fixed.mul bounds
  generalize mll0 : Fixed.mul x.lo y.lo u false = ll0
  generalize mlh0 : Fixed.mul x.lo y.hi u false = lh0
  generalize mhl0 : Fixed.mul x.hi y.lo u false = hl0
  generalize mhh0 : Fixed.mul x.hi y.hi u false = hh0
  generalize mll1 : Fixed.mul x.lo y.lo u true = ll1
  generalize mlh1 : Fixed.mul x.lo y.hi u true = lh1
  generalize mhl1 : Fixed.mul x.hi y.lo u true = hl1
  generalize mhh1 : Fixed.mul x.hi y.hi u true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * y.lo.val := by rw [←mll0]; exact Fixed.mul_le
  have ilh0 : lh0 ≠ nan → lh0.val ≤ x.lo.val * y.hi.val := by rw [←mlh0]; exact Fixed.mul_le
  have ihl0 : hl0 ≠ nan → hl0.val ≤ x.hi.val * y.lo.val := by rw [←mhl0]; exact Fixed.mul_le
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * y.hi.val := by rw [←mhh0]; exact Fixed.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * y.lo.val ≤ ll1.val := by rw [←mll1]; exact Fixed.le_mul
  have ilh1 : lh1 ≠ nan → x.lo.val * y.hi.val ≤ lh1.val := by rw [←mlh1]; exact Fixed.le_mul
  have ihl1 : hl1 ≠ nan → x.hi.val * y.lo.val ≤ hl1.val := by rw [←mhl1]; exact Fixed.le_mul
  have ihh1 : hh1 ≠ nan → x.hi.val * y.hi.val ≤ hh1.val := by rw [←mhh1]; exact Fixed.le_mul
  -- Split on signs
  rcases Interval.sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals rcases Interval.sign_cases ny n3 with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
  all_goals simp only [xls, xhs, yls, yhs, n0, n1, n2, n3, bne_self_eq_false, Bool.false_and,
    if_false, Bool.xor_false, Bool.and_self, ite_true, Bool.and_false, ite_false, approx,
    Ici_inter_Iic, Fixed.min_eq_nan, false_or, Fixed.max_eq_nan, subset_if_univ_iff, not_or,
    and_imp, mll0, mlh0, mhl0, mhh0, mll1, mlh1, mhl1, mhh1, Icc_mul_Icc_subset_Icc xi yi,
    Fixed.val_min, min_le_iff]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg] at xls xhs yls yhs
  all_goals clear mll0 mlh0 mhl0 mhh0 mll1 mlh1 mhl1 mhh1 nx ny
  -- Dispatch everything with nlinarith
  · intro m0 m1; specialize ihh0 m0; specialize ill1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ilh0 m0; specialize ihl1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ilh0 m0; specialize ill1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ihl0 m0; specialize ilh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ill0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ihl0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1 m2 m3
    specialize ilh0 m0; specialize ihl0 m1; specialize ill1 m2; specialize ihh1 m3
    simp only [Fixed.val_max m2 m3, le_max_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
  · intro m0 m1; specialize ilh0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1 m2 m3
    specialize ilh0 m0; specialize ihl0 m1; specialize ill1 m2; specialize ihh1 m3
    simp only [Fixed.val_max m2 m3, le_max_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith

/-- `Interval` multiplication approximates `ℝ` -/
instance : ApproxMul (Interval s) ℝ where
  approx_mul _ _ := Interval.approx_mul _ _ _

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing (Interval s) ℝ where

/-- `Interval.approx_mul` in `mono` form, `⊆` version -/
@[mono] lemma Interval.subset_approx_mul {a b : Set ℝ} {x : Interval s} {y : Interval t} {u : Int64}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) : a * b ⊆ approx (x.mul y u) :=
  subset_trans (mul_subset_mul as bs) (Interval.approx_mul x y _)

/-- `Interval.approx_mul` in `mono` form, `∈` version -/
@[mono] lemma Interval.mem_approx_mul {a b : ℝ} {x : Interval s} {y : Interval t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (x.mul y u) :=
  Interval.subset_approx_mul (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `Interval.mul` propagates `lo = nan` -/
@[simp] lemma Interval.mul_nan_lo {x : Interval s} {y : Interval t} {u : Int64} (yn : y.lo = nan) :
    x.mul y u = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `Interval.mul` propagates `hi = nan` -/
@[simp] lemma Interval.mul_nan_hi {x : Interval s} {y : Interval t} {u : Int64} (yn : y.hi = nan) :
    x.mul y u = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `Interval.mul` propagates `lo = nan` -/
@[simp] lemma Interval.nan_mul_lo {x : Interval s} {y : Interval t} {u : Int64} (xn : x.lo = nan) :
    x.mul y u = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `Interval.mul` propagates `hi = nan` -/
@[simp] lemma Interval.nan_mul_hi {x : Interval s} {y : Interval t} {u : Int64} (xn : x.hi = nan) :
    x.mul y u = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `Interval.mul` arguments are `≠ nan` if the result is -/
lemma Interval.ne_nan_of_mul {x : Interval s} {y : Interval t} {u : Int64}
    (n : (x.mul y u).lo ≠ nan) : x.lo ≠ nan ∧ x.hi ≠ nan ∧ y.lo ≠ nan ∧ y.hi ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n | n | n
  · rwa [Interval.nan_mul_lo, nan_def]
  · rwa [Interval.nan_mul_hi, nan_def]
  · rwa [Interval.mul_nan_lo, nan_def]
  · rwa [Interval.mul_nan_hi, nan_def]

/-!
### `Fixed * Fixed`, but conservative
-/

/-- Multiply two `Fixed`s, producing an `Interval -/
def Interval.fixed_mul_fixed (x : Fixed s) (y : Fixed t) (u : Int64) : Interval u :=
  ⟨x.mul y u false, x.mul y u true⟩

/-- `Interval.fixed_mul_fixed` respects `approx` -/
lemma Interval.approx_fixed_mul_fixed (x : Fixed s) (y : Fixed t) (u : Int64) :
    approx x * approx y ⊆ approx (Interval.fixed_mul_fixed x y u) := by
  intro a m
  simp only [mem_mul, exists_and_left] at m
  rcases m with ⟨b,bm,c,cm,bc⟩
  simp only [approx, mem_ite_univ_left, mem_singleton_iff, mem_Icc,
    Interval.fixed_mul_fixed] at bm cm ⊢
  by_cases n : x = nan ∨ y = nan ∨ Fixed.mul x y u false = nan ∨ Fixed.mul x y u true = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←Ne.def] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, not_false_eq_true, forall_true_left, n1] at bm cm
  simp only [n2, n3, or_self, not_false_eq_true, ← bc, bm, cm, forall_true_left]
  exact ⟨Fixed.mul_le n2, Fixed.le_mul n3⟩

/-- `Interval.approx_fixed_mul_fixed` in `mono` form, `⊆` version -/
@[mono] lemma Interval.subset_approx_fixed_mul_fixed {a b : Set ℝ} {x : Fixed s} {y : Fixed t}
    {u : Int64} (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (Interval.fixed_mul_fixed x y u) :=
  subset_trans (mul_subset_mul as bs) (Interval.approx_fixed_mul_fixed x y _)

/-- `Interval.approx_fixed_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma Interval.mem_approx_fixed_mul_fixed {a b : ℝ} {x : Fixed s} {y : Fixed t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (Interval.fixed_mul_fixed x y u) :=
  Interval.subset_approx_fixed_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `Interval.fixed_mul_fixed _ nan _ = nan` -/
@[simp] lemma Interval.fixed_mul_fixed_nan_right {x : Fixed s} {u : Int64} :
    Interval.fixed_mul_fixed x (nan : Fixed t) u = nan := by
  simp only [fixed_mul_fixed, Fixed.mul_nan, nan_def]

/-- `Interval.fixed_mul_fixed nan _ _ = nan` -/
@[simp] lemma Interval.fixed_mul_fixed_nan_left {x : Fixed t} {u : Int64} :
    Interval.fixed_mul_fixed (nan : Fixed s) x u = nan := by
  simp only [fixed_mul_fixed, Fixed.nan_mul, nan_def]

/-- `Interval.fixed_mul_fixed` arguments are `≠ nan` if the result is -/
lemma Interval.ne_nan_of_fixed_mul_fixed {x : Fixed s} {y : Fixed t} {u : Int64}
    (n : (Interval.fixed_mul_fixed x y u).lo ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp [n]

/-!
### `Interval * Fixed`
-/

/-- Multiply times a `Fixed`, changing `s` -/
@[pp_dot] def Interval.mul_fixed (x : Interval s) (y : Fixed t) (u : Int64) : Interval u :=
  bif x.lo == nan || x.hi == nan || y == nan then nan else
  let (a,b) := bif y.n.isNeg then (x.hi, x.lo) else (x.lo, x.hi)
  ⟨a.mul y u false, b.mul y u true⟩

/-- Diagonal comparison to 0 -/
@[simp] lemma Interval.diagonal_eq_zero (x : Fixed s) : ((⟨x,x⟩ : Interval s) = 0) ↔ x == 0 := by
  simp only [ext_iff, lo_zero, hi_zero, and_self, beq_iff_eq]

/-- `Interval.mul_fixed` respects `approx` -/
lemma Interval.approx_mul_fixed (x : Interval s) (y : Fixed t) (u : Int64) :
    approx x * approx y ⊆ approx (x.mul_fixed y u) := by
  -- Handle special cases
  simp only [image2_mul, mul_fixed, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y = nan ∨ approx x = ∅
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,n2,nx⟩
  have xi : x.lo.val ≤ x.hi.val := by
    simpa only [approx, n0, n1, or_self, ite_false, nonempty_Icc] using nx
  simp only [n0, n1, n2, or_self, ite_false]
  -- Record Fixed.mul bounds
  generalize ml0 : Fixed.mul x.lo y u false = l0
  generalize mh0 : Fixed.mul x.hi y u false = h0
  generalize ml1 : Fixed.mul x.lo y u true = l1
  generalize mh1 : Fixed.mul x.hi y u true = h1
  have il0 : l0 ≠ nan → l0.val ≤ x.lo.val * y.val := by rw [←ml0]; exact Fixed.mul_le
  have ih0 : h0 ≠ nan → h0.val ≤ x.hi.val * y.val := by rw [←mh0]; exact Fixed.mul_le
  have il1 : l1 ≠ nan → x.lo.val * y.val ≤ l1.val := by rw [←ml1]; exact Fixed.le_mul
  have ih1 : h1 ≠ nan → x.hi.val * y.val ≤ h1.val := by rw [←mh1]; exact Fixed.le_mul
  -- Split on signs
  by_cases ys : y.n.isNeg
  all_goals simp only [ys, n0, n1, n2, ite_true, ite_false, approx, false_or, subset_if_univ_iff,
    not_or, and_imp, ml0, mh0, ml1, mh1, mul_singleton]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg, not_lt] at ys
  -- Handle each case
  · intro mh0 ml1
    have le : x.hi.val * y.val ≤ x.lo.val * y.val := by nlinarith
    simp only [image_mul_right_Icc_of_neg ys, Icc_subset_Icc_iff le]
    exact ⟨ih0 mh0, il1 ml1⟩
  · intro ml0 mh1
    have le : x.lo.val * y.val ≤ x.hi.val * y.val := by nlinarith
    simp only [image_mul_right_Icc xi ys, Icc_subset_Icc_iff le]
    exact ⟨il0 ml0, ih1 mh1⟩

/-!
### Interval squaring
-/

/-- Tighter than `Interval.mul x x u` -/
@[pp_dot] def Interval.sqr (x : Interval s) (u : Int64 := s) : Interval u :=
  bif x == 0 then 0
  else bif x.lo == nan || x.hi == nan then nan
  else bif x.lo.n.isNeg != x.hi.n.isNeg then  -- x has mixed sign
    ⟨0, max (x.lo.mul x.lo u true) (x.hi.mul x.hi u true)⟩
  else bif x.lo.n.isNeg then ⟨x.hi.mul x.hi u false, x.lo.mul x.lo u true⟩
  else ⟨x.lo.mul x.lo u false, x.hi.mul x.hi u true⟩

/-- Rewrite `Icc^2 ⊆ Icc` in terms of inequalities -/
lemma sqr_Icc_subset_Icc {a b x y : ℝ} :
    (fun x ↦ x^2) '' Icc a b ⊆ Icc x y ↔ ∀ u, a ≤ u → u ≤ b → x ≤ u^2 ∧ u^2 ≤ y := by
  simp only [subset_def, mem_image, mem_Icc, forall_exists_index, and_imp]
  constructor
  · intro h u au ub; exact h _ u au ub rfl
  · intro h u v av vb vu; rw [←vu]; exact h v av vb

/-- `Interval.sqr` respects `approx` -/
lemma Interval.approx_sqr (x : Interval s) (u : Int64) :
    (fun x ↦ x^2) '' approx x ⊆ approx (x.sqr u) := by
  -- Record Fixed.mul bounds
  generalize mll0 : x.lo.mul x.lo u false = ll0
  generalize mll1 : x.lo.mul x.lo u true = ll1
  generalize mhh0 : x.hi.mul x.hi u false = hh0
  generalize mhh1 : x.hi.mul x.hi u true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * x.lo.val := by rw [←mll0]; exact Fixed.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * x.lo.val ≤ ll1.val := by rw [←mll1]; exact Fixed.le_mul
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * x.hi.val := by rw [←mhh0]; exact Fixed.mul_le
  have ihh1 : hh1 ≠ nan → x.hi.val * x.hi.val ≤ hh1.val := by rw [←mhh1]; exact Fixed.le_mul
  -- Handle special cases
  simp only [sqr, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases x0 : x = 0; · simp [x0]
  simp only [x0, or_self, ite_false]
  clear x0
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ approx x = ∅
  · rcases n with n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,nx⟩
  simp only [n0, n1, or_self, ite_false]
  -- Split on signs
  rcases Interval.sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals simp only [xls, xhs, n0, n1, bne_self_eq_false, Bool.false_and, if_false, not_or,
    Bool.xor_false, Bool.and_self, ite_true, Bool.and_false, ite_false, approx, false_or,
    Fixed.max_eq_nan, subset_if_univ_iff, and_imp, mll0, mhh0, mll1, mhh1, sqr_Icc_subset_Icc]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg] at xls xhs
  all_goals clear mll0 mhh0 mll1 mhh1 nx
  -- Dispatch everything with nlinarith
  · intro nhh0 nll1 u lu uh
    specialize ihh0 nhh0; specialize ill1 nll1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro nll0 nhh1 u lu uh
    specialize ill0 nll0; specialize ihh1 nhh1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro _ nll1 nhh1 u lu uh
    specialize ill1 nll1; specialize ihh1 nhh1
    simp only [Fixed.val_zero, Fixed.val_max nll1 nhh1, le_max_iff]
    constructor
    · nlinarith
    · by_cases us : u < 0
      · left; nlinarith
      · right; nlinarith

/-!
## Conversion from `ℕ`
-/

/-- `ℕ` converts to `Interval s` -/
@[irreducible] def Interval.ofNat (n : ℕ) : Interval s := ⟨.ofNat n false, .ofNat n true⟩

/-- `ℤ` converts to `Interval s` -/
@[irreducible] def Interval.ofInt (n : ℤ) : Interval s := ⟨.ofInt n false, .ofInt n true⟩

/-- We use the general `.ofNat` routine for `1`, to handle overflow -/
instance : One (Interval s) := ⟨.ofNat 1⟩

lemma Interval.one_def : (1 : Interval s) = .ofNat 1 := rfl

/-- Conversion from `ℕ` literals to `Interval s` -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat (Interval s) n := ⟨.ofNat n⟩

/-- `.ofNat` is conservative -/
@[mono] lemma Interval.approx_ofNat (n : ℕ) : ↑n ∈ approx (.ofNat n : Interval s) := by
  rw [ofNat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofNat n false : Fixed s) = nan ∨ (.ofNat n true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofNat_le g.1, Fixed.le_ofNat g.2⟩

/-- `.ofInt` is conservative -/
@[mono] lemma Interval.approx_ofInt (n : ℤ) : ↑n ∈ approx (.ofInt n : Interval s) := by
  rw [ofInt]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofInt n false : Fixed s) = nan ∨ (.ofInt n true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofInt_le g.1, Fixed.le_ofInt g.2⟩

/-- `1 : Interval` is conservative -/
@[mono] lemma Interval.approx_one : 1 ∈ approx (1 : Interval s) := by
  rw [←Nat.cast_one]
  apply Interval.approx_ofNat

/-- `1 : Interval` is conservative, `⊆` version since this appears frequently -/
@[mono] lemma Interval.subset_approx_one : {1} ⊆ approx (1 : Interval s) := by
  simp only [singleton_subset_iff]; exact approx_one

/-- `n.lo ≤ n` -/
lemma Interval.ofNat_le (n : ℕ) : (.ofNat n : Interval s).lo.val ≤ n := by
  simp only [ofNat]
  by_cases n : (.ofNat n false : Fixed s) = nan
  · simp only [n, Fixed.val_nan]
    exact le_trans (neg_nonpos.mpr (zpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
  · exact le_trans (Fixed.ofNat_le n) (by norm_num)

/-- `n ≤ n.hi` unless we're `nan` -/
lemma Interval.le_ofNat (n : ℕ) (h : (.ofNat n : Interval s).hi ≠ nan) :
    n ≤ (.ofNat n : Interval s).hi.val := by
  rw [Interval.ofNat] at h ⊢; exact Fixed.le_ofNat h

/-- `1.lo ≤ 1` -/
lemma Interval.one_le : (1 : Interval s).lo.val ≤ 1 := by
  simpa only [Nat.cast_one] using Interval.ofNat_le 1 (s := s)

/-- `1 ≤ 1.hi` unless we're `nan` -/
lemma Interval.le_one (n : (1 : Interval s).hi ≠ nan) : 1 ≤ (1 : Interval s).hi.val := by
  rw [Interval.one_def, Interval.ofNat] at n ⊢
  refine le_trans (by norm_num) (Fixed.le_ofNat n)
