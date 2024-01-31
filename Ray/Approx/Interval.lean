import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Pointwise.Interval
import Ray.Approx.Floating.Add
import Ray.Approx.Floating.Order
import Ray.Misc.Real

open Classical
open Pointwise

/-!
## 64-bit precision floating point interval arithmetic
-/

open Set
open scoped Real

/-!
#### Type definition and basic lemmas
-/

/-- 64-bit fixed point intervals -/
structure Interval where
  /-- Lower bound -/
  lo : Floating
  /-- Upper bound -/
  hi : Floating
  /-- None or both of our bounds are `nan` -/
  norm : lo = nan ↔ hi = nan
  /-- The interval is nontrivial -/
  le' : lo ≠ nan → hi ≠ nan → lo.val ≤ hi.val
  deriving DecidableEq

namespace Interval

instance : BEq Interval where
  beq x y := x.lo == y.lo && x.hi == y.hi

lemma beq_def {x y : Interval} : (x == y) = (x.lo == y.lo && x.hi == y.hi) := rfl

/-- `Interval` has nice equality -/
instance : LawfulBEq Interval where
  eq_of_beq {x y} e := by
    induction x
    induction y
    simp only [beq_def, Bool.and_eq_true, beq_iff_eq] at e
    simp only [e.1, e.2]
  rfl {x} := by
    induction x
    simp only [beq_def, Bool.and_eq_true, beq_iff_eq, true_and]

/-- The unique `Interval` nan -/
instance : Nan Interval where
  nan := ⟨nan, nan, by simp only, fun _ _ ↦ le_refl _⟩

/-- Intervals are equal iff their components are equal -/
lemma ext_iff {x y : Interval} : x = y ↔ x.lo = y.lo ∧ x.hi = y.hi := by
  induction x; induction y; simp only [mk.injEq]

/-- `Interval` approximates `ℝ` -/
instance : Approx Interval ℝ where
  approx x := if x.lo = nan then univ else Icc x.lo.val x.hi.val

/-- Zero -/
instance : Zero Interval where
  zero := ⟨0, 0, by simp only [Floating.zero_ne_nan], fun _ _ ↦ le_refl _⟩

/-- The width of an interval -/
@[pp_dot] def size (x : Interval) : Floating := x.hi.sub x.lo true

/-!
#### Basic lemmas
-/

-- Bounds properties of interval arithmetic
@[simp] lemma lo_zero : (0 : Interval).lo = 0 := rfl
@[simp] lemma hi_zero : (0 : Interval).hi = 0 := rfl
@[simp] lemma lo_nan : (nan : Interval).lo = nan := rfl
@[simp] lemma hi_nan : (nan : Interval).hi = nan := rfl
@[simp] lemma approx_zero : approx (0 : Interval) = {0} := by
  simp only [approx, lo_zero, Floating.zero_ne_nan, Floating.val_zero, hi_zero, Icc_self, ite_false]
@[simp] lemma approx_nan : approx (nan : Interval) = univ := by
  simp only [approx, nan, ite_true, inter_self, true_or]

/-- `x.lo = nan` if `x = nan` -/
@[simp] lemma lo_eq_nan {x : Interval} : x.lo = nan ↔ x = nan := by
  simp only [ext_iff, lo_nan, hi_nan, iff_self_and]; intro n; rwa [←x.norm]

/-- `x.hi = nan` if `x = nan` -/
@[simp] lemma hi_eq_nan {x : Interval} : x.hi = nan ↔ x = nan := by
  simp only [← x.norm, lo_eq_nan]

/-- If we're not `nan`, our components are not `nan` -/
@[simp] lemma lo_ne_nan {x : Interval} (n : x ≠ nan) : x.lo ≠ nan := by
  contrapose n
  simp only [ne_eq, not_not] at n
  simp only [ne_eq, ext_iff, n, lo_nan, x.norm.mp n, hi_nan, and_self, not_true_eq_false,
    not_false_eq_true]

/-- If we're not `nan`, our components are not `nan` -/
@[simp] lemma hi_ne_nan {x : Interval} (n : x ≠ nan) : x.hi ≠ nan := by
  contrapose n
  simp only [ne_eq, not_not] at n
  simp only [ne_eq, ext_iff, n, lo_nan, x.norm.mpr n, hi_nan, and_self, not_true_eq_false,
    not_false_eq_true]

/-- The inequality always holds -/
@[simp] lemma le (x : Interval) : x.lo.val ≤ x.hi.val := by
  by_cases n : x = nan
  · simp only [n, lo_nan, hi_nan, le_refl]
  · exact x.le' (lo_ne_nan n) (hi_ne_nan n)

/-!
### Propagate nans into both bounds
-/

/-- Assemble the interval `[lo,hi]`, propagating nans into both components -/
@[irreducible] def mix (lo hi : Floating) (le : lo ≠ nan → hi ≠ nan → lo.val ≤ hi.val) : Interval :=
  if n : lo = nan ∨ hi = nan then nan else {
    lo := lo
    hi := hi
    norm := by simp only [not_or] at n; simp only [n]
    le' := le }

/-- `mix` propagates `nan` -/
@[simp] lemma mix_nan (x : Floating)
    (le : x ≠ nan → (nan : Floating) ≠ nan → x.val ≤ (nan : Floating).val) :
    mix x nan le = nan := by
  rw [mix]; simp only [or_true, dite_true]

/-- `mix` propagates `nan` -/
@[simp] lemma nan_mix (x : Floating)
    (le : (nan : Floating) ≠ nan → x ≠ nan → (nan : Floating).val ≤ x.val) :
    mix nan x le = nan := by
  rw [mix]; simp only [true_or, dite_true]

/-- `mix` propagates `nan` -/
@[simp] lemma ne_nan_of_mix {lo hi : Floating} {le : lo ≠ nan → hi ≠ nan → lo.val ≤ hi.val}
    (n : mix lo hi le ≠ nan) : lo ≠ nan ∧ hi ≠ nan := by
  by_cases h : lo = nan ∨ hi = nan
  · rcases h with h | h; repeat simp only [h, nan_mix, mix_nan, ne_eq, not_true_eq_false] at n
  simpa only [ne_eq, not_or] using h

/-- `(mix _ _ _).lo` -/
@[simp] lemma lo_mix {lo hi : Floating} {le : lo ≠ nan → hi ≠ nan → lo.val ≤ hi.val}
    (n : mix lo hi le ≠ nan) : (mix lo hi le).lo = lo := by
  rcases ne_nan_of_mix n with ⟨n0, n1⟩
  rw [mix]
  simp only [n0, n1, or_self, dite_false]

/-- `(mix _ _ _).hi` -/
@[simp] lemma hi_mix {lo hi : Floating} {le : lo ≠ nan → hi ≠ nan → lo.val ≤ hi.val}
    (n : mix lo hi le ≠ nan) : (mix lo hi le).hi = hi := by
  rcases ne_nan_of_mix n with ⟨n0, n1⟩
  rw [mix]
  simp only [n0, n1, or_self, dite_false]

/-!
### Negation
-/

/-- Negation -/
instance : Neg Interval where
  neg x := {
    lo := -x.hi
    hi := -x.lo
    norm := by simp only [Floating.neg_eq_nan_iff, x.norm]
    le' := by
      intro n0 n1
      simp only [ne_eq, Floating.neg_eq_nan_iff] at n0 n1
      simp only [ne_eq, n0, not_false_eq_true, Floating.val_neg, n1, neg_le_neg_iff, x.le' n1 n0] }

@[simp] lemma neg_nan : -(nan : Interval) = nan := rfl
@[simp] lemma lo_neg {x : Interval} : (-x).lo = -x.hi := rfl
@[simp] lemma hi_neg {x : Interval} : (-x).hi = -x.lo := rfl

@[simp] lemma approx_neg {x : Interval} : approx (-x) = -approx x := by
  by_cases n : x = nan
  · simp only [n, neg_nan, approx_nan, neg_univ]
  · simp only [approx, lo_neg, Floating.neg_eq_nan_iff, ne_eq, n, not_false_eq_true, hi_ne_nan,
      Floating.val_neg, hi_neg, lo_ne_nan, ite_false, preimage_neg_Icc]

/-- `neg` respects `approx` -/
instance : ApproxNeg Interval ℝ where
  approx_neg x := by simp only [approx_neg, neg_subset_neg, subset_refl]

/-!
### Union
-/

/-- Union -/
instance : Union Interval where
  union x y := {
    lo := min x.lo y.lo
    hi := x.hi.max y.hi  -- Use the version that propagates `nan`
    norm := by simp only [Floating.min_eq_nan, lo_eq_nan, Floating.max_eq_nan, hi_eq_nan]
    le' := by
      intro _ n; simp only [ne_eq, Floating.max_eq_nan, hi_eq_nan, not_or] at n
      simp only [Floating.val_min, Floating.val_max (x.hi_ne_nan n.1) (y.hi_ne_nan n.2),
        le_max_iff, min_le_iff, le, true_or, or_true, or_self] }

/-- Union propagates `nan` -/
@[simp] lemma union_nan {x : Interval} : x ∪ nan = nan := by
  simp only [Union.union, lo_nan, Floating.val_le_val, Floating.nan_val_le, min_eq_right,
    hi_nan, Floating.max_nan, ext_iff, and_self]

/-- Union propagates `nan` -/
@[simp] lemma nan_union {x : Interval} : nan ∪ x = nan := by
  simp only [Union.union, lo_nan, Floating.val_le_val, Floating.nan_val_le, min_eq_left,
    hi_nan, Floating.nan_max, ext_iff, and_self]

/-!
### Intersection

We require a proof that the intersection is nontrivial.  This is harder for the user, but
we expect intersection to mainly be used a tool inside routines such as Newton's method,
where intersections are guaranteed nonempty.
-/

/-- Intersection, requiring a proof that the intersection is nontrivial -/
@[irreducible] def inter (x y : Interval) (t : (approx x ∩ approx y).Nonempty) : Interval where
  lo := x.lo.max y.lo
  hi := min x.hi y.hi
  norm := by simp only [Floating.max_eq_nan, lo_eq_nan, Floating.min_eq_nan, hi_eq_nan]
  le' := by
    intro n _
    simp only [ne_eq, Floating.max_eq_nan, lo_eq_nan, not_or] at n
    simp only [Floating.val_max (x.lo_ne_nan n.1) (y.lo_ne_nan n.2), Floating.val_min, le_min_iff,
      max_le_iff, le, true_and, and_true]
    rcases t with ⟨a,ax,ay⟩
    simp only [approx, lo_eq_nan, n.1, ite_false, mem_Icc, n.2] at ax ay
    exact ⟨by linarith, by linarith⟩

/-- `inter` propagates `nan` -/
@[simp] lemma inter_nan {x : Interval} {t : (approx x ∩ approx nan).Nonempty} :
    x.inter nan t = nan := by
  rw [inter]
  simp only [lo_nan, Floating.max_nan, hi_nan, ge_iff_le, Floating.val_le_val, Floating.nan_val_le,
    min_eq_right, ext_iff, and_self]

/-- `inter` propagates `nan` -/
@[simp] lemma nan_inter {x : Interval} {t : (approx nan ∩ approx x).Nonempty} :
    (nan : Interval).inter x t = nan := by
  rw [inter]
  simp only [lo_nan, Floating.nan_max, hi_nan, ge_iff_le, Floating.val_le_val, Floating.nan_val_le,
    min_eq_left, ext_iff, and_self]

/-- `inter` respects `approx` -/
@[simp] lemma approx_inter {x y : Interval} {t : (approx x ∩ approx y).Nonempty} :
    approx x ∩ approx y ⊆ approx (x.inter y t) := by
  by_cases n : x = nan ∨ y = nan ∨ x.inter y t = nan
  · rcases n with n | n | n; repeat simp only [n, inter_nan, nan_inter, approx_nan, subset_univ]
  simp only [not_or] at n
  rcases n with ⟨xn,yn,n⟩
  simp only [approx, lo_eq_nan, xn, ite_false, yn, n, Icc_inter_Icc]
  apply Icc_subset_Icc
  · simp only [inter, Floating.val_max (x.lo_ne_nan xn) (y.lo_ne_nan yn), le_sup_iff,
      max_le_iff, le_refl, true_and, and_true, le_total]
  · simp only [inter, Floating.val_min, le_min_iff, inf_le_left, inf_le_right, and_self]

/-!
### Addition and subtraction
-/

/-- Addition -/
instance instAdd : Add Interval where
  add x y := mix (x.lo.add y.lo false) (x.hi.add y.hi true) (by
    intro ln hn
    exact le_trans (Floating.val_add_le ln) (le_trans (add_le_add x.le y.le)
      (Floating.le_val_add hn)))

/-- Subtraction -/
instance instSub : Sub Interval where
  sub x y := mix (x.lo.sub y.hi false) (x.hi.sub y.lo true) (by
    intro ln hn
    exact le_trans (Floating.val_sub_le ln) (le_trans (sub_le_sub x.le y.le)
      (Floating.le_val_sub hn)))

-- `+, -` propagate `nan`
@[simp] lemma add_nan {x : Interval} : x + nan = nan := by
  simp only [HAdd.hAdd, Add.add, lo_nan, Floating.add_nan, hi_nan, mix_nan]
@[simp] lemma nan_add {x : Interval} : nan + x = nan := by
  simp only [HAdd.hAdd, Add.add, lo_nan, Floating.nan_add, hi_nan, mix_nan]
@[simp] lemma sub_nan {x : Interval} : x - nan = nan := by
  simp only [HSub.hSub, Sub.sub, hi_nan, Floating.sub_nan, lo_nan, mix_nan]
@[simp] lemma nan_sub {x : Interval} : nan - x = nan := by
  simp only [HSub.hSub, Sub.sub, lo_nan, Floating.nan_sub, hi_nan, mix_nan]
lemma ne_nan_of_add {x y : Interval} (n : x + y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n; simp only [ne_eq, not_and_or, not_not] at n
  rcases n with n | n; repeat simp only [n, nan_add, add_nan, not_not]
lemma ne_nan_of_sub {x y : Interval} (n : x - y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n; simp only [ne_eq, not_and_or, not_not] at n
  rcases n with n | n; repeat simp only [n, nan_sub, sub_nan, not_not]

/-- `add` respects `approx` -/
instance : ApproxAdd Interval ℝ where
  approx_add x y := by
    by_cases n : x + y = nan
    · simp only [n, approx_nan, subset_univ]
    simp only [approx, lo_eq_nan, ne_nan_of_add n, ite_false, n]
    simp only [HAdd.hAdd, Add.add] at n ⊢
    refine subset_trans (Icc_add_Icc_subset _ _ _ _) (Icc_subset_Icc ?_ ?_)
    · simp only [lo_mix n, Floating.val_add_le (ne_nan_of_mix n).1]
    · simp only [hi_mix n, Floating.le_val_add (ne_nan_of_mix n).2]

/-- `sub` respects `approx` -/
instance : ApproxSub Interval ℝ where
  approx_sub x y := by
    by_cases n : x - y = nan
    · simp only [n, approx_nan, subset_univ]
    simp only [approx, lo_eq_nan, ne_nan_of_sub n, ite_false, n, sub_eq_add_neg, preimage_neg_Icc]
    simp only [HSub.hSub, Sub.sub] at n ⊢
    refine subset_trans (Icc_add_Icc_subset _ _ _ _) (Icc_subset_Icc ?_ ?_)
    · simp only [lo_mix n, ←sub_eq_add_neg, Floating.val_sub_le (ne_nan_of_mix n).1]
    · simp only [hi_mix n, ←sub_eq_add_neg, Floating.le_val_sub (ne_nan_of_mix n).2]

/-- `Interval` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup Interval ℝ where

/-!
### DO NOT SUBMIT
-/

#exit

/-- `Fixed s` converts to `Interval` -/
@[coe] def Fixed.toInterval (x : Fixed s) : Interval := ⟨x,x⟩

/-- `Fixed s` converts to `Interval` -/
instance : Coe (Fixed s) Interval where
  coe x := x.toInterval

/-- We print `Interval` as an approximate floating point interval -/
instance : Repr Interval where
  reprPrec x _ := "[" ++ repr x.lo ++ "," ++ repr x.hi ++ "]"

/-- `x - y = x + (-y)` -/
lemma sub_eq_add_neg (x y : Interval) : x - y = x + (-y) := by
  simp only [sub_def, Fixed.sub_eq_add_neg, add_def, lo_neg, hi_neg]

/-- If an interval is a single point, so is `approx` -/
@[simp] lemma approx_self {x : Fixed s} : approx (⟨x,x⟩ : Interval) = approx x := by
  simp only [approx, or_self, Icc_self]

/-- `Interval` `approx` is `OrdConncted` -/
instance : ApproxConnected Interval ℝ where
  connected x := by
    simp only [approx]
    split_ifs
    · exact ordConnected_univ
    · exact ordConnected_Icc

/-- `union` is commutative -/
lemma union_comm {x y : Interval} : x ∪ y = y ∪ x := by
  simp only [Union.union, ext_iff, Fixed.min_comm, Fixed.max_comm]

/-- `union` respects `approx` -/
lemma approx_union_left {x y : Interval} : approx x ⊆ approx (x ∪ y) := by
  intro a ax
  simp only [approx, mem_if_univ_iff, Union.union, Fixed.min_eq_nan, Fixed.max_eq_nan] at ax ⊢
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, n1, or_self, not_false_eq_true, mem_Icc, forall_true_left, n2, n3, Fixed.val_min,
    min_le_iff, Fixed.val_max n1 n3, le_max_iff] at ax ⊢
  simp only [ax.1, true_or, ax.2, and_self]

/-- `union` respects `approx` -/
lemma approx_union_right {x y : Interval} : approx y ⊆ approx (x ∪ y) := by
  rw [union_comm]; exact approx_union_left

/-- `union` respects `approx` -/
lemma approx_union {x y : Interval} : approx x ∪ approx y ⊆ approx (x ∪ y) :=
  union_subset approx_union_left approx_union_right

/-- `mono` version of `approx_inter` -/
@[mono] lemma subset_approx_inter {s : Set ℝ} {x y : Interval t}
    (sx : s ⊆ approx x) (sy : s ⊆ approx y) : s ⊆ approx (x ∩ y) :=
  subset_trans (subset_inter sx sy) approx_inter

/-- If an `Interval` is nonempty, the expected inequality usually holds -/
lemma le_of_nonempty {x : Interval} (a : (approx x).Nonempty) (hn : x.hi ≠ nan) :
    x.lo.val ≤ x.hi.val := by
  rcases a with ⟨a,h⟩
  simp only [approx, hn, or_false] at h
  by_cases ln : x.lo = nan
  · simp only [Fixed.val, ln, nan, mul_le_mul_right two_zpow_pos, Int.cast_le, Int64.coe_le_coe,
    Int64.min_le]
  simp only [ln, ite_false, mem_Icc] at h
  linarith

/-!
### Safe upper and lower bounds, even if the other field is `nan`
-/

-- DO NOT SUBMIT: .lo and .hi should work directly now

/-- `Interval` lower bound, even if `hi` is `nan` -/
@[pp_dot] def safe_lo (x : Interval) : Fixed s :=
  bif x.hi == nan then nan else x.lo

/-- `Interval` upper bound, even if `hi` is `nan` -/
@[pp_dot] def safe_hi (x : Interval) : Fixed s :=
  bif x.lo == nan then nan else x.hi

/-- Ignoring `nan`, `x.safe_lo.val` is a lower bound on `approx` -/
lemma safe_lo_le {a : ℝ} {x : Interval} (n : x.safe_lo ≠ nan) (m : a ∈ approx x) :
    x.safe_lo.val ≤ a := by
  simp only [safe_lo] at n ⊢
  by_cases hn : x.hi = nan
  · simp only [hn, beq_self_eq_true, cond_true, ne_eq, not_true_eq_false] at n
  · simp only [approx, ne_eq, neg_neg, hn, not_false_eq_true, Fixed.ne_nan_of_neg, or_false,
    mem_ite_univ_left, mem_Icc, bif_eq_if, beq_iff_eq, ite_false] at m n ⊢
    exact (m n).1

/-- Ignoring `nan`, `x.safe_hi.val` is an upper bound on `approx` -/
lemma le_safe_hi {a : ℝ} {x : Interval} (n : x.safe_hi ≠ nan) (m : a ∈ approx x) :
    a ≤ x.safe_hi.val := by
  simp only [safe_hi] at n ⊢
  by_cases ln : x.lo = nan
  · simp only [ln, beq_self_eq_true, cond_true, ne_eq, not_true_eq_false] at n
  · simp only [approx, ne_eq, neg_neg, ln, not_false_eq_true, Fixed.ne_nan_of_neg, false_or,
      mem_ite_univ_left, mem_Icc, bif_eq_if, beq_iff_eq, ite_false] at m n ⊢
    exact (m n).2

/-!
### Utility lemmas
-/

/-- Either `approx = ∅` or `x.lo ≤ x.hi` (if we're not nan) -/
lemma sign_cases {x : Interval} (a : (approx x).Nonempty) (hn : x.hi ≠ nan) :
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
def abs (x : Interval) : Interval :=
  let a := x.lo.abs
  let b := x.hi.abs
  ⟨bif x.lo.n.isNeg != x.hi.n.isNeg then 0 else min a b, max a b⟩

/-- `abs` respects `approx` -/
@[mono] lemma approx_abs {x : Interval} : _root_.abs '' approx x ⊆ approx x.abs := by
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ approx x = ∅
  · rcases n with n | n | n
    · simp only [approx, n, true_or, ite_true, image_univ, abs, Fixed.isNeg_nan, Bool.true_xor,
        Fixed.abs_nan, Bool.cond_not, Fixed.max_eq_nan, Fixed.abs_eq_nan, or_true, subset_univ]
    · simp only [approx, n, or_true, ite_true, image_univ, abs, Fixed.isNeg_nan, Bool.xor_true,
        Fixed.abs_nan, Bool.cond_not, Fixed.max_eq_nan, Fixed.abs_eq_nan, subset_univ]
    · simp only [n, image_empty, empty_subset]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨nl,nh,nx⟩
  simp only [approx, nl, nh, or_self, ite_false, abs, bif_eq_if, bne_iff_ne, ne_eq, ite_not,
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

/-- `abs` respects `approx`, `∈` version -/
@[mono] lemma mem_approx_abs {a : ℝ} {x : Interval} (ax : a ∈ approx x) :
    |a| ∈ approx x.abs :=
  approx_abs (mem_image_of_mem _ ax)

 /-- `abs` preserves nonnegative intervals -/
lemma abs_of_nonneg {x : Interval} (h : 0 ≤ x.lo.val)
    (ax : (approx x).Nonempty) : approx x.abs = approx x := by
  by_cases n : x.lo = nan ∨ x.hi = nan
  · rcases n with n | n; repeat simp [abs, n]
  rcases not_or.mp n with ⟨n0,n1⟩
  have lh := le_of_nonempty ax n1
  have h' := le_trans h lh
  simp only [approx, abs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide,
    ite_not, not_lt.mpr h, not_lt.mpr h', ite_true, Fixed.min_eq_nan, Fixed.abs_eq_nan, n0, n1,
    or_self, Fixed.max_eq_nan, Fixed.val_min, Fixed.val_abs n0, _root_.abs_of_nonneg h,
    Fixed.val_abs n1, _root_.abs_of_nonneg h', min_eq_left lh,
    Fixed.val_max (Fixed.abs_ne_nan.mpr n0) (Fixed.abs_ne_nan.mpr n1), max_eq_right lh, ite_false]

/-- `abs` negates nonpositive intervals -/
lemma abs_of_nonpos {x : Interval} (h : x.hi.val ≤ 0)
    (ax : (approx x).Nonempty) : approx x.abs = -approx x := by
  by_cases n0 : x.lo = nan
  · simp only [abs, n0, Fixed.isNeg_nan, Bool.true_xor, Fixed.abs_nan, Bool.cond_not,
      Fixed.max_eq_nan, Fixed.abs_eq_nan, true_or, approx_of_hi_nan, approx_of_lo_nan, neg_univ]
  by_cases n1 : x.hi = nan
  · simp only [abs, n1, Fixed.isNeg_nan, Bool.xor_true, Fixed.abs_nan, Bool.cond_not,
      Fixed.max_eq_nan, Fixed.abs_eq_nan, or_true, approx_of_hi_nan, neg_univ]
  have lh := le_of_nonempty ax n1
  have h' := le_trans lh h
  simp only [approx, abs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide,
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

/-- `x.abs.lo` is nonneg if inputs are not `nan` -/
lemma abs_nonneg {x : Interval} (n0 : x.lo ≠ nan) (n1 : x.hi ≠ nan) :
    0 ≤ x.abs.lo.val := by
  simp only [abs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not,
    apply_ite (f := fun x : Fixed s ↦ 0 ≤ x.val), Fixed.val_min, le_min_iff, Fixed.val_zero,
    le_refl, Fixed.val_abs n0, Fixed.val_abs n1, _root_.abs_nonneg, true_and, ite_self]

/-- `x.abs.lo` is pos if inputs are not `nan` or `0` and have the same sign -/
lemma abs_pos {x : Interval} (n0 : x.lo ≠ nan) (n1 : x.hi ≠ nan)
    (l0 : x.lo ≠ 0) (h0 : x.hi ≠ 0) (lh : x.lo.val < 0 ↔ x.hi.val < 0) : 0 < x.abs.lo.val := by
  refine Ne.lt_of_le (Ne.symm ?_) (abs_nonneg n0 n1)
  contrapose l0
  simp only [abs, Fixed.isNeg_eq, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not, lh,
    ite_true, Fixed.val_min, Fixed.val_abs n0, Fixed.val_abs n1, not_not,
    ←Fixed.val_eq_zero_iff] at l0 ⊢
  have nonpos : |x.lo.val| ≤ 0 := by
    cases' min_le_iff.mp (le_of_eq l0) with h h
    · exact h
    · exfalso
      rw [←Fixed.val_ne_zero_iff, Ne.def, ←abs_eq_zero] at h0
      exact not_le.mpr (Ne.lt_of_le h0 h) (_root_.abs_nonneg _)
  exact abs_eq_zero.mp (le_antisymm nonpos (_root_.abs_nonneg _))

/-- `x.abs` propagates `nan` from `lo` to `hi` -/
lemma abs_eq_nan_of_lo {x : Interval} (n : x.lo = nan) : x.abs.hi = nan := by
  simp only [abs, n, Fixed.isNeg_nan, Bool.true_xor, Fixed.abs_nan, Bool.cond_not,
    Fixed.max_eq_nan, Fixed.abs_eq_nan, true_or]

/-- `x.abs` propagates `nan` from `hi` to `hi` -/
lemma abs_eq_nan_of_hi {x : Interval} (n : x.hi = nan) : x.abs.hi = nan := by
  simp only [abs, n, Fixed.isNeg_nan, Bool.true_xor, Fixed.abs_nan, Bool.cond_not,
    Fixed.max_eq_nan, Fixed.abs_eq_nan, or_true]

/-- `x.abs` propagates `nan` to `hi` -/
@[simp] lemma abs_nan_hi : (nan : Interval).abs.hi = nan := by
  apply abs_eq_nan_of_hi; simp only [hi_nan]

/-- If `|x|.lo = nan`, then `.hi = nan` too -/
lemma abs_hi_eq_nan_of_lo {x : Interval} (n : x.abs.lo = nan) : x.abs.hi = nan := by
  simp only [abs, bif_eq_if] at n ⊢
  by_cases se : x.lo.n.isNeg != x.hi.n.isNeg
  · simp only [se, ite_true, ne_eq, neg_neg, Fixed.zero_ne_nan, not_false_eq_true,
      Fixed.ne_nan_of_neg] at n
  simp only [se, ite_false, Fixed.min_eq_nan, Fixed.abs_eq_nan] at n
  rcases n with n | n; repeat simp [n]

/-- If `|x|.hi ≠ nan`, then `.lo ≠ nan` too -/
lemma abs_lo_ne_nan_of_hi {x : Interval} (n : x.abs.hi ≠ nan) : x.abs.lo ≠ nan := by
  contrapose n; simp only [ne_eq, not_not] at n ⊢; exact abs_hi_eq_nan_of_lo n

 /-!
### Interval multiplication
-/

/-- Multiply, changing `s` -/
@[pp_dot] def mul (x : Interval) (y : Interval t) (u : Int64) : Interval u :=
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
instance : Mul Interval where
  mul (x y : Interval) := x.mul y s

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
/-- `mul` respects `approx` -/
lemma approx_mul (x : Interval) (y : Interval t) (u : Int64) :
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
  rcases sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals rcases sign_cases ny n3 with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
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
instance : ApproxMul Interval ℝ where
  approx_mul _ _ := approx_mul _ _ _

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing Interval ℝ where

/-- `approx_mul` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul {a b : Set ℝ} {x : Interval} {y : Interval t} {u : Int64}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) : a * b ⊆ approx (x.mul y u) :=
  subset_trans (mul_subset_mul as bs) (approx_mul x y _)

/-- `approx_mul` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul {a b : ℝ} {x : Interval} {y : Interval t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (x.mul y u) :=
  subset_approx_mul (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `mul` propagates `lo = nan` -/
@[simp] lemma mul_nan_lo {x : Interval} {y : Interval t} {u : Int64} (yn : y.lo = nan) :
    x.mul y u = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` propagates `hi = nan` -/
@[simp] lemma mul_nan_hi {x : Interval} {y : Interval t} {u : Int64} (yn : y.hi = nan) :
    x.mul y u = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` propagates `lo = nan` -/
@[simp] lemma nan_mul_lo {x : Interval} {y : Interval t} {u : Int64} (xn : x.lo = nan) :
    x.mul y u = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` propagates `hi = nan` -/
@[simp] lemma nan_mul_hi {x : Interval} {y : Interval t} {u : Int64} (xn : x.hi = nan) :
    x.mul y u = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_mul {x : Interval} {y : Interval t} {u : Int64}
    (n : (x.mul y u).lo ≠ nan) : x.lo ≠ nan ∧ x.hi ≠ nan ∧ y.lo ≠ nan ∧ y.hi ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n | n | n
  · rwa [nan_mul_lo, nan_def]
  · rwa [nan_mul_hi, nan_def]
  · rwa [mul_nan_lo, nan_def]
  · rwa [mul_nan_hi, nan_def]

/-!
### `Fixed * Fixed`, but conservative
-/

/-- Multiply two `Fixed`s, producing an `Interval -/
def fixed_mul_fixed (x : Fixed s) (y : Fixed t) (u : Int64) : Interval u :=
  ⟨x.mul y u false, x.mul y u true⟩

/-- `fixed_mul_fixed` respects `approx` -/
lemma approx_fixed_mul_fixed (x : Fixed s) (y : Fixed t) (u : Int64) :
    approx x * approx y ⊆ approx (fixed_mul_fixed x y u) := by
  intro a m
  simp only [mem_mul, exists_and_left] at m
  rcases m with ⟨b,bm,c,cm,bc⟩
  simp only [approx, mem_ite_univ_left, mem_singleton_iff, mem_Icc,
    fixed_mul_fixed] at bm cm ⊢
  by_cases n : x = nan ∨ y = nan ∨ Fixed.mul x y u false = nan ∨ Fixed.mul x y u true = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←Ne.def] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, not_false_eq_true, forall_true_left, n1] at bm cm
  simp only [n2, n3, or_self, not_false_eq_true, ← bc, bm, cm, forall_true_left]
  exact ⟨Fixed.mul_le n2, Fixed.le_mul n3⟩

/-- `approx_fixed_mul_fixed` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_fixed_mul_fixed {a b : Set ℝ} {x : Fixed s} {y : Fixed t}
    {u : Int64} (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (fixed_mul_fixed x y u) :=
  subset_trans (mul_subset_mul as bs) (approx_fixed_mul_fixed x y _)

/-- `approx_fixed_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_fixed_mul_fixed {a b : ℝ} {x : Fixed s} {y : Fixed t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (fixed_mul_fixed x y u) :=
  subset_approx_fixed_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `fixed_mul_fixed _ nan _ = nan` -/
@[simp] lemma fixed_mul_fixed_nan_right {x : Fixed s} {u : Int64} :
    fixed_mul_fixed x (nan : Fixed t) u = nan := by
  simp only [fixed_mul_fixed, Fixed.mul_nan, nan_def]

/-- `fixed_mul_fixed nan _ _ = nan` -/
@[simp] lemma fixed_mul_fixed_nan_left {x : Fixed t} {u : Int64} :
    fixed_mul_fixed (nan : Fixed s) x u = nan := by
  simp only [fixed_mul_fixed, Fixed.nan_mul, nan_def]

/-- `fixed_mul_fixed` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_fixed_mul_fixed {x : Fixed s} {y : Fixed t} {u : Int64}
    (n : (fixed_mul_fixed x y u).lo ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp [n]

/-!
### `Interval * Fixed`
-/

/-- Multiply times a `Fixed`, changing `s` -/
@[pp_dot] def mul_fixed (x : Interval) (y : Fixed t) (u : Int64) : Interval u :=
  bif x.lo == nan || x.hi == nan || y == nan then nan else
  let (a,b) := bif y.n.isNeg then (x.hi, x.lo) else (x.lo, x.hi)
  ⟨a.mul y u false, b.mul y u true⟩

/-- Diagonal comparison to 0 -/
@[simp] lemma diagonal_eq_zero (x : Fixed s) : ((⟨x,x⟩ : Interval) = 0) ↔ x == 0 := by
  simp only [ext_iff, lo_zero, hi_zero, and_self, beq_iff_eq]

/-- `mul_fixed` respects `approx` -/
lemma approx_mul_fixed (x : Interval) (y : Fixed t) (u : Int64) :
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

/-- `approx_mul_fixed` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul_fixed {a b : Set ℝ} {x : Interval} {y : Fixed t}
    {u : Int64} (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (mul_fixed x y u) :=
  subset_trans (mul_subset_mul as bs) (approx_mul_fixed x y _)

/-- `approx_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul_fixed {a b : ℝ} {x : Interval} {y : Fixed t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (mul_fixed x y u) :=
  subset_approx_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-!
### Intervalquaring
-/

/-- Tighter than `mul x x u` -/
@[pp_dot] def sqr (x : Interval) (u : Int64 := s) : Interval u :=
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

/-- `sqr` respects `approx` -/
lemma approx_sqr (x : Interval) (u : Int64) :
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
  rcases sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
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
## Conversion from `ℕ`, `ℤ`, `ℚ`, and `ofScientific`
-/

/-- `ℕ` converts to `Interval` -/
@[irreducible] def ofNat (n : ℕ) : Interval := ⟨.ofNat n false, .ofNat n true⟩

/-- `ℤ` converts to `Interval` -/
@[irreducible] def ofInt (n : ℤ) : Interval := ⟨.ofInt n false, .ofInt n true⟩

/-- `ℚ` converts to `Interval` -/
@[irreducible] def ofRat (x : ℚ) : Interval := ⟨.ofRat x false, .ofRat x true⟩

/-- Conversion from `ofScientific` -/
instance : OfScientific Interval where
  ofScientific x u t := .ofRat (OfScientific.ofScientific x u t)

/-- We use the general `.ofNat` routine for `1`, to handle overflow -/
instance : One Interval := ⟨.ofNat 1⟩

lemma one_def : (1 : Interval) = .ofNat 1 := rfl

/-- Conversion from `ℕ` literals to `Interval` -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat Interval n := ⟨.ofNat n⟩

/-- `.ofNat` is conservative -/
@[mono] lemma approx_ofNat (n : ℕ) : ↑n ∈ approx (.ofNat n : Interval) := by
  rw [ofNat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofNat n false : Fixed s) = nan ∨ (.ofNat n true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofNat_le g.1, Fixed.le_ofNat g.2⟩

/-- `.ofInt` is conservative -/
@[mono] lemma approx_ofInt (n : ℤ) : ↑n ∈ approx (.ofInt n : Interval) := by
  rw [ofInt]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofInt n false : Fixed s) = nan ∨ (.ofInt n true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofInt_le g.1, Fixed.le_ofInt g.2⟩

/-- `.ofRat` is conservative -/
@[mono] lemma approx_ofRat (x : ℚ) : ↑x ∈ approx (.ofRat x : Interval) := by
  rw [ofRat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofRat x false : Fixed s) = nan ∨ (.ofRat x true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofRat_le g.1, Fixed.le_ofRat g.2⟩

/-- `approx_ofRat` for rational literals `a / b` -/
@[mono] lemma ofNat_div_mem_approx_ofRat {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    OfNat.ofNat a / OfNat.ofNat b ∈
      approx (.ofRat (OfNat.ofNat a / OfNat.ofNat b) : Interval) := by
  convert approx_ofRat _; simp only [Rat.cast_div, Rat.cast_ofNat]

/-- `approx_ofRat` for rational literals `1 / b` -/
@[mono] lemma one_div_ofNat_mem_approx_ofRat {b : ℕ} [b.AtLeastTwo] :
    1 / OfNat.ofNat b ∈ approx (.ofRat (1 / OfNat.ofNat b) : Interval) := by
  convert approx_ofRat _; simp only [one_div, Rat.cast_inv, Rat.cast_ofNat]

/-- `ofRat` conversion is conservative -/
@[mono] lemma approx_ofScientific (x : ℕ) (u : Bool) (t : ℕ) :
    ↑(OfScientific.ofScientific x u t : ℚ) ∈
      approx (OfScientific.ofScientific x u t : Interval) := by
  simp only [OfScientific.ofScientific]
  apply approx_ofRat

/-- `1 : Interval` is conservative -/
@[mono] lemma approx_one : 1 ∈ approx (1 : Interval) := by
  rw [←Nat.cast_one]
  apply approx_ofNat

/-- `1 : Interval` is conservative, `⊆` version since this appears frequently -/
@[mono] lemma subset_approx_one : {1} ⊆ approx (1 : Interval) := by
  simp only [singleton_subset_iff]; exact approx_one

/-- `n.lo ≤ n` -/
lemma ofNat_le (n : ℕ) : (.ofNat n : Interval).lo.val ≤ n := by
  simp only [ofNat]
  by_cases n : (.ofNat n false : Fixed s) = nan
  · simp only [n, Fixed.val_nan]
    exact le_trans (neg_nonpos.mpr (zpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
  · exact le_trans (Fixed.ofNat_le n) (by norm_num)

/-- `n ≤ n.hi` unless we're `nan` -/
lemma le_ofNat (n : ℕ) (h : (.ofNat n : Interval).hi ≠ nan) :
    n ≤ (.ofNat n : Interval).hi.val := by
  rw [ofNat] at h ⊢; exact Fixed.le_ofNat h

/-- `1.lo ≤ 1` -/
lemma one_le : (1 : Interval).lo.val ≤ 1 := by
  simpa only [Nat.cast_one] using ofNat_le 1 (s := s)

/-- `1 ≤ 1.hi` unless we're `nan` -/
lemma le_one (n : (1 : Interval).hi ≠ nan) : 1 ≤ (1 : Interval).hi.val := by
  rw [one_def, ofNat] at n ⊢
  refine le_trans (by norm_num) (Fixed.le_ofNat n)

/-!
### Exponent changes: `Interval → Interval t`
-/

/-- Change `Interval` to `Interval t` -/
@[irreducible, pp_dot] def repoint (x : Interval) (t : Int64) : Interval t :=
  ⟨x.lo.repoint t false, x.hi.repoint t true⟩

/-- `repoint` preserves standard `nan` -/
@[simp] lemma repoint_nan {t : Int64} : (nan : Interval).repoint t = nan := by
  rw [repoint]; simp only [lo_nan, Fixed.repoint_nan, hi_nan, ← nan_def]

/-- `repoint` is conservative (`⊆` version) -/
@[mono] lemma approx_repoint {x : Interval} {t : Int64} :
    approx x ⊆ approx (x.repoint t) := by
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ (x.repoint t).lo = nan ∨ (x.repoint t).hi = nan
  · rcases n with n | n | n | n
    · rw [repoint]; simp only [approx, n, true_or, ite_true, Fixed.repoint_nan, subset_univ]
    · rw [repoint]; simp only [approx, n, or_true, ite_true, Fixed.repoint_nan, subset_univ]
    · simp only [n, approx_of_lo_nan, subset_univ]
    · simp only [n, approx_of_hi_nan, subset_univ]
  · simp only [not_or] at n
    rcases n with ⟨n0,n1,n2,n3⟩
    rw [repoint] at n2 n3 ⊢
    simp only at n2 n3
    simp only [approx, ne_eq, neg_neg, n0, not_false_eq_true, Fixed.ne_nan_of_neg, n1, or_self,
      ite_false, n2, n3]
    exact Icc_subset_Icc (Fixed.repoint_le n2) (Fixed.le_repoint n3)

/-- `repoint` is conservative (`∈` version) -/
@[mono] lemma mem_approx_repoint {x : Interval} {t : Int64} {x' : ℝ}
    (xm : x' ∈ approx x) : x' ∈ approx (x.repoint t) :=
  approx_repoint xm
