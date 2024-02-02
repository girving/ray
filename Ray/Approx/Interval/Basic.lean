import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Pointwise.Interval
import Ray.Approx.Floating.Add
import Ray.Approx.Floating.Abs
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

/-- We print `Interval` as an approximate floating point interval -/
instance : Repr Interval where
  reprPrec x _ := bif x = nan then "nan" else "[" ++ repr x.lo ++ "," ++ repr x.hi ++ "]"

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

/-- The raw_inequality always holds -/
@[simp] lemma lo_le_hi (x : Interval) : x.lo ≤ x.hi := by
  simp only [Floating.val_le_val, le]

/-- `Interval` `approx` is `OrdConncted` -/
instance : ApproxConnected Interval ℝ where
  connected x := by
    simp only [approx]
    split_ifs
    · exact ordConnected_univ
    · exact ordConnected_Icc

/-- Ignoring `nan`, `x.lo.val` is a lower bound on `approx` -/
lemma lo_le {a : ℝ} {x : Interval} (n : x ≠ nan) (m : a ∈ approx x) : x.lo.val ≤ a := by
  simp only [approx, lo_eq_nan, n, ite_false, mem_Icc] at m; exact m.1

/-- Ignoring `nan`, `x.lo.val` is a lower bound on `approx` -/
lemma le_hi {a : ℝ} {x : Interval} (n : x ≠ nan) (m : a ∈ approx x) : a ≤ x.hi.val := by
  simp only [approx, lo_eq_nan, n, ite_false, mem_Icc] at m; exact m.2

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

/-- `mix` is `nan` iff an argument is -/
@[simp] lemma mix_eq_nan {lo hi : Floating} {le : lo ≠ nan → hi ≠ nan → lo.val ≤ hi.val} :
    mix lo hi le = nan ↔ lo = nan ∨ hi = nan := by
  rw [mix]
  simp only [dite_eq_left_iff, not_or, ext_iff, lo_nan, hi_nan, and_imp]
  by_cases n : lo = nan ∨ hi = nan
  · simp only [n, iff_true]
    rcases n with n | n
    · simp only [n, not_true_eq_false, true_and, not_imp_self, IsEmpty.forall_iff]
    · simp only [n, not_true_eq_false, and_true, IsEmpty.forall_iff, implies_true]
  · simp only [not_or] at n
    simp only [n, not_false_eq_true, and_self, forall_true_left, or_self]

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

/-- `union` is commutative -/
lemma union_comm {x y : Interval} : x ∪ y = y ∪ x := by
  simp only [Union.union, ext_iff, min_comm, Floating.max_comm]

/-- `union` respects `approx` -/
lemma approx_union_left {x y : Interval} : approx x ⊆ approx (x ∪ y) := by
  intro a ax
  simp only [approx, mem_if_univ_iff, Union.union, Fixed.min_eq_nan, Fixed.max_eq_nan] at ax ⊢
  intro n
  simp only [Floating.min_eq_nan, lo_eq_nan, not_or] at n
  simp only [lo_eq_nan, n.1, not_false_eq_true, mem_Icc, forall_true_left, Floating.val_min, ne_eq,
    hi_eq_nan, n.2, Floating.val_max, min_le_iff, le_max_iff] at ax ⊢
  simp only [ax.1, true_or, ax.2, and_self]

/-- `union` respects `approx` -/
lemma approx_union_right {x y : Interval} : approx y ⊆ approx (x ∪ y) := by
  rw [union_comm]; exact approx_union_left

/-- `union` respects `approx` -/
lemma approx_union {x y : Interval} : approx x ∪ approx y ⊆ approx (x ∪ y) :=
  union_subset approx_union_left approx_union_right


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

/-- `mono` version of `approx_inter` -/
@[mono] lemma subset_approx_inter {s : Set ℝ} {x y : Interval} {t : (approx x ∩ approx y).Nonempty}
    (sx : s ⊆ approx x) (sy : s ⊆ approx y) : s ⊆ approx (x.inter y t) :=
  subset_trans (subset_inter sx sy) approx_inter

/-!
### Addition and subtraction
-/

/-- Addition -/
instance instAdd : Add Interval where
  add x y := mix (x.lo.add y.lo false) (x.hi.add y.hi true) (by
    intro ln hn
    exact le_trans (Floating.val_add_le ln) (le_trans (add_le_add x.le y.le)
      (Floating.le_add hn)))

/-- Subtraction -/
instance instSub : Sub Interval where
  sub x y := mix (x.lo.sub y.hi false) (x.hi.sub y.lo true) (by
    intro ln hn
    exact le_trans (Floating.sub_le ln) (le_trans (sub_le_sub x.le y.le)
      (Floating.le_sub hn)))

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
    · simp only [hi_mix n, Floating.le_add (ne_nan_of_mix n).2]

/-- `sub` respects `approx` -/
instance : ApproxSub Interval ℝ where
  approx_sub x y := by
    by_cases n : x - y = nan
    · simp only [n, approx_nan, subset_univ]
    simp only [approx, lo_eq_nan, ne_nan_of_sub n, ite_false, n, sub_eq_add_neg, preimage_neg_Icc]
    simp only [HSub.hSub, Sub.sub] at n ⊢
    refine subset_trans (Icc_add_Icc_subset _ _ _ _) (Icc_subset_Icc ?_ ?_)
    · simp only [lo_mix n, ←sub_eq_add_neg, Floating.sub_le (ne_nan_of_mix n).1]
    · simp only [hi_mix n, ←sub_eq_add_neg, Floating.le_sub (ne_nan_of_mix n).2]

/-- `Interval` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup Interval ℝ where

/-- `x - y = x + (-y)` -/
lemma sub_eq_add_neg (x y : Interval) : x - y = x + (-y) := by
  simp only [HSub.hSub, Sub.sub, HAdd.hAdd, Add.add, lo_neg, hi_neg, ext_iff]
  rw [mix, mix]
  simp only [←Floating.sub_eq_add_neg, and_self]

/-!
### Utility lemmas
-/

/-- Signs must correspond to `x.lo ≤ x.hi` -/
lemma sign_cases (x : Interval) :
    (x.lo.val < 0 ∧ x.hi.val < 0) ∨ (0 ≤ x.lo.val ∧ 0 ≤ x.hi.val) ∨
    (x.lo.val < 0 ∧ 0 ≤ x.hi.val) := by
  by_cases n : x = nan
  · simp only [n, lo_nan, Floating.val_nan_lt_zero, hi_nan, and_self, Floating.not_nan_nonneg,
    and_false, or_self, or_false]
  · by_cases h0 : x.hi.val < 0
    · simp only [trans x.le h0, h0, and_self, true_and, true_or]
    · simp only [h0, and_false, false_or, not_lt.mp h0, and_true]
      apply le_or_lt

/-!
### `Floating → Interval` coersion
-/

/-- `Floating` converts to `Interval` -/
@[coe] def _root_.Floating.toInterval (x : Floating) : Interval where
  lo := x
  hi := x
  norm := by simp only
  le' := by simp only [le_refl, implies_true]

/-- `Fixed s` converts to `Interval` -/
instance : Coe Floating Interval where
  coe x := x.toInterval

-- Definition lemmas
@[simp] lemma lo_coe {x : Floating} : (x : Interval).lo = x := rfl
@[simp] lemma hi_coe {x : Floating} : (x : Interval).hi = x := rfl

/-- Coercion preserves `nan` -/
@[simp] lemma coe_eq_nan {x : Floating} : (x : Interval) = nan ↔ x = nan := by
  simp only [ext_iff, lo_coe, lo_nan, hi_coe, hi_nan, and_self]

/-- Coercion propagates `nan` -/
@[simp] lemma coe_nan : ((nan : Floating) : Interval) = nan := by
  simp only [coe_eq_nan]

/-- Coercion preserves `approx` -/
@[simp] lemma approx_coe {x : Floating} : approx (x : Interval) = approx x := by
  simp only [approx, lo_coe, hi_coe, Icc_self]

/-- `mix x x _ = x -/
@[simp] lemma mix_self {x : Floating} {le : x ≠ nan → x ≠ nan → x.val ≤ x.val} :
    mix x x le = x := by
  by_cases n : x = nan
  · simp only [n, mix_nan, coe_nan]
  · rw [mix]
    simp only [n, or_self, dite_false, ext_iff, lo_coe, hi_coe, and_self]

/-!
### Absolute value
-/

/-- Absolute value -/
@[irreducible, pp_dot] def abs (x : Interval) : Interval :=
  let a := x.lo.abs
  let b := x.hi.abs
  mix (bif x.lo.n.isNeg != x.hi.n.isNeg then 0 else min a b) (a.max b) (by
    intro n0 n1
    simp only [Floating.isNeg_iff, Floating.val_lt_val, Floating.val_zero, bif_eq_if, bne_iff_ne,
      ne_eq, decide_eq_decide, ite_not, Floating.max_eq_nan, not_or, apply_ite (f := Floating.val),
      Floating.val_min] at n0 n1 ⊢
    simp only [Floating.val_max n1.1 n1.2, le_max_iff]
    split_ifs with h
    · simp only [min_le_iff, le_refl, true_or, or_true, or_self]
    · simp only [Floating.abs_eq_nan] at n1
      simp only [Floating.val_abs n1.1, abs_nonneg, Floating.val_abs n1.2, or_self])

/-- `x.abs` conserves `nan` -/
@[simp] lemma abs_eq_nan {x : Interval} : x.abs = nan ↔ x = nan := by
  rw [abs]
  simp only [bif_eq_if, bne_iff_ne, ne_eq, ite_not, mix_eq_nan, Floating.max_eq_nan,
    Floating.abs_eq_nan, lo_eq_nan, hi_eq_nan, or_self, or_iff_right_iff_imp]
  split_ifs with h
  · simp only [Floating.min_eq_nan, Floating.abs_eq_nan, lo_eq_nan, hi_eq_nan, or_self, imp_self]
  · simp only [Floating.zero_ne_nan, IsEmpty.forall_iff]

/-- `x.abs` propagates `nan` -/
@[simp] lemma abs_nan : (nan : Interval).abs = nan := by
  simp only [abs_eq_nan]

/-- `abs` is conservative -/
@[mono] lemma approx_abs {x : Interval} : _root_.abs '' approx x ⊆ approx x.abs := by
  by_cases n : x = nan
  · simp only [n, approx_nan, image_univ, abs_nan, subset_univ]
  have na : x.abs ≠ nan := by simp only [ne_eq, abs_eq_nan, n, not_false_eq_true]
  rw [abs] at na ⊢
  simp only [bif_eq_if, bne_iff_ne, ne_eq, ite_not, mix_eq_nan, Floating.max_eq_nan,
    Floating.abs_eq_nan, lo_eq_nan, n, hi_eq_nan, or_self, or_false, Floating.isNeg_iff,
    decide_eq_decide] at na
  simp only [approx, lo_eq_nan, n, ite_false, bif_eq_if, bne_iff_ne, ne_eq, ite_not, mix_eq_nan, na,
    Floating.max_eq_nan, Floating.abs_eq_nan, hi_eq_nan, or_self, not_false_eq_true, lo_mix, hi_mix,
    Floating.val_max, Floating.val_abs, image_subset_iff, Floating.isNeg_iff, decide_eq_decide]
  rcases x.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals try simp only [not_lt.mpr ls]
  all_goals try simp only [not_lt.mpr hs]
  all_goals try simp only [ls, hs, if_true, if_false, Fixed.zero_ne_nan, not_false_iff, true_implies,
    Floating.val_min, Floating.val_abs (x.lo_ne_nan n), Floating.val_abs (x.hi_ne_nan n),
    Floating.val_zero, true_iff]
  · intro a ⟨la,ah⟩
    simp only [abs_of_neg ls, abs_of_neg hs, ge_iff_le, neg_le_neg_iff, le, min_eq_right,
      max_eq_left, mem_preimage, mem_Icc]
    rcases nonpos_or_nonneg a with as | as
    · simp only [abs_of_nonpos as, neg_le_neg_iff]; exact ⟨ah, la⟩
    · simp only [abs_of_nonneg as]; exact ⟨by linarith, by linarith⟩
  · intro a ⟨la,ah⟩
    simp only [abs_of_nonneg ls, abs_of_nonneg hs, ge_iff_le, le, min_eq_left, max_eq_right,
      mem_preimage, mem_Icc]
    rcases nonpos_or_nonneg a with as | as
    · simp only [abs_of_nonpos as]; exact ⟨by linarith, by linarith⟩
    · simp only [abs_of_nonneg as]; exact ⟨by linarith, by linarith⟩
  · intro a ⟨la,ah⟩
    simp only [abs_of_neg ls, abs_of_nonneg hs, mem_preimage, mem_Icc, abs_nonneg, le_max_iff,
      true_and]
    rcases nonpos_or_nonneg a with as | as
    · simp only [abs_of_nonpos as, neg_le_neg_iff]; left; exact la
    · simp only [abs_of_nonneg as]; right; linarith

/-- `abs` respects `approx`, `∈` version -/
@[mono] lemma mem_approx_abs {a : ℝ} {x : Interval} (ax : a ∈ approx x) :
    |a| ∈ approx x.abs :=
  approx_abs (mem_image_of_mem _ ax)

 /-- `abs` preserves nonnegative intervals -/
lemma abs_of_nonneg {x : Interval} (x0 : 0 ≤ x.lo.val) : x.abs = x := by
  by_cases n : x = nan
  · simp only [n, lo_nan, Floating.not_nan_nonneg] at x0
  have na : x.abs ≠ nan := by simp only [ne_eq, abs_eq_nan, n, not_false_eq_true]
  rw [abs] at na ⊢
  rw [ext_iff, lo_mix na, hi_mix na]; clear na
  simp only [Floating.isNeg_iff, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not,
    ext_iff, not_lt.mpr x0, false_iff, not_lt, le_trans x0 x.le, ite_true,
    min_def, Floating.val_le_val, Floating.abs_of_nonneg x0,
    Floating.abs_of_nonneg (le_trans x0 x.le), x.le, true_and,
    Floating.max_eq_right x.le (Floating.ne_nan_of_nonneg x0), min_eq_left x.le]

/-- `abs` negates nonpositive intervals -/
lemma abs_of_nonpos {x : Interval} (x0 : x.hi.val ≤ 0) : x.abs = -x := by
  by_cases n : x = nan
  · simp only [n, abs_nan, neg_nan]
  have na : x.abs ≠ nan := by simp only [ne_eq, abs_eq_nan, n, not_false_eq_true]
  rw [abs] at na ⊢
  rw [ext_iff, lo_mix na, hi_mix na]; clear na
  simp only [Floating.isNeg_iff, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not, lo_neg,
    hi_neg]
  by_cases h0 : x.hi = 0
  · by_cases l0 : x.lo = 0
    · simp only [l0, Floating.val_zero, lt_self_iff_false, h0, le_refl, Floating.abs_of_nonneg,
        min_self, ite_self, Floating.neg_zero, ne_eq, Floating.zero_ne_nan, not_false_eq_true,
        Floating.max_eq_left, and_self]
    · replace l0 : x.lo.val < 0 := Ne.lt_of_le (Floating.val_ne_zero.mpr l0) (le_trans x.le x0)
      simp only [l0, h0, Floating.val_zero, lt_self_iff_false, iff_false, not_true_eq_false,
        Floating.abs_of_nonpos (le_trans x.le x0), le_refl, Floating.abs_of_nonneg, ite_false,
        Floating.neg_zero, true_and]
      apply Floating.max_eq_left
      · simp only [Floating.val_zero, Floating.val_neg (x.lo_ne_nan n), Left.nonneg_neg_iff, l0.le]
      · simp only [ne_eq, Floating.zero_ne_nan, not_false_eq_true]
  · replace h0 : x.hi.val < 0 := Ne.lt_of_le (Floating.val_ne_zero.mpr h0) x0
    have l0 : x.lo.val < 0 := lt_of_le_of_lt x.le h0
    simp only [Floating.isNeg_iff, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not, l0, h0,
      if_true]
    rw [min_eq_right, Floating.max_eq_left, Floating.abs_of_nonpos h0.le,
      Floating.abs_of_nonpos l0.le]
    · simp only [and_self]
    · simp only [Floating.abs_of_nonpos h0.le, Floating.abs_of_nonpos l0.le,
        Floating.val_neg (x.lo_ne_nan n), Floating.val_neg (x.hi_ne_nan n), neg_le_neg_iff, x.le]
    · simpa only [ne_eq, Floating.abs_eq_nan, hi_eq_nan]
    · simp only [Floating.abs_of_nonpos h0.le, Floating.abs_of_nonpos l0.le,
        Floating.val_neg (x.lo_ne_nan n), Floating.val_neg (x.hi_ne_nan n), neg_le_neg_iff, x.le,
        Floating.val_le_val]

/-- `x.abs` is nonneg if `x ≠ nan` -/
lemma abs_nonneg {x : Interval} (n : x ≠ nan) : 0 ≤ x.abs.lo.val := by
  have na : x.abs ≠ nan := by simp only [ne_eq, abs_eq_nan, n, not_false_eq_true]
  rw [abs] at na ⊢; rw [lo_mix na]; clear na
  simp only [Floating.isNeg_iff, bif_eq_if, bne_iff_ne, ne_eq, decide_eq_decide, ite_not, ge_iff_le]
  split_ifs
  · simp only [Floating.val_min, le_min_iff, Floating.abs_nonneg (x.lo_ne_nan n),
      Floating.abs_nonneg (x.hi_ne_nan n), and_self]
  · simp only [Floating.val_zero, le_refl]

/-- `x.abs.lo` is pos if inputs are not `nan` or `0` and have the same sign -/
lemma abs_pos {x : Interval} (n : x ≠ nan) (l0 : x.lo ≠ 0) (lh : x.lo.val < 0 ↔ x.hi.val < 0) :
    0 < x.abs.lo.val := by
  refine Ne.lt_of_le (Ne.symm ?_) (abs_nonneg n)
  have na : x.abs ≠ nan := by simp only [ne_eq, abs_eq_nan, n, not_false_eq_true]
  rw [abs] at na ⊢; rw [lo_mix na]; clear na
  simp only [Floating.isNeg_iff, min_def, Floating.val_le_val, bif_eq_if, bne_iff_ne, ne_eq,
    decide_eq_decide, ite_not]
  by_cases z : x.lo.val < 0
  · simp only [z, lh.mp z, Floating.abs_of_nonpos z.le, Floating.val_neg (x.lo_ne_nan n),
      Floating.abs_of_nonpos (lh.mp z).le, Floating.val_neg (x.hi_ne_nan n), neg_le_neg_iff,
      ite_true]
    split_ifs
    · simp only [Floating.val_neg (x.lo_ne_nan n), neg_eq_zero, z.ne, not_false_eq_true]
    · simp only [Floating.val_neg (x.hi_ne_nan n), neg_eq_zero, (lh.mp z).ne, not_false_eq_true]
  · simp only [not_lt] at z
    have z1 : 0 ≤ x.hi.val := le_trans z x.le
    simpa only [not_lt.mpr z, not_lt.mpr z1, Floating.abs_of_nonneg z, Floating.abs_of_nonneg z1,
      le, ite_true, Floating.val_eq_zero, ne_eq]
