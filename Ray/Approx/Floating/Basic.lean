import Mathlib.Data.Real.Basic
import Ray.Approx.Approx
import Ray.Approx.Fixed
import Ray.Approx.Float
import Ray.Approx.Int64
import Ray.Approx.UInt128
import Ray.Misc.Int
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

namespace Floating

instance : BEq Floating where
  beq x y := x.n == y.n && x.s == y.s

lemma beq_def {x y : Floating} : (x == y) = (x.n == y.n && x.s == y.s) := rfl

instance : LawfulBEq Floating where
  eq_of_beq {x y} e := by
    induction x
    induction y
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq] at e
    simp only [e.1, e.2]
  rfl {x} := by
    induction x
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq, true_and]

lemma ext_iff {x y : Floating} : x = y ↔ x.n = y.n ∧ x.s = y.s := by
  induction x; induction y; simp only [mk.injEq]

/-- Standard floating point nan -/
instance : Nan Floating where
  nan := ⟨.min, .max, by decide, by decide, by decide⟩

/-- The `ℝ` that a `Fixed` represents, if it's not `nan` -/
@[pp_dot] noncomputable def val (x : Floating) : ℝ :=
  ((x.n : ℤ) : ℝ) * (2 : ℝ)^(x.s.toInt - 2^63)

/-- `Fixed` approximates `ℝ` -/
instance : Approx Floating ℝ where
  approx x := if x = nan then univ else {x.val}

/-- `0 : Floating` -/
instance : Zero Floating where
  zero := ⟨0, 0, by decide, by decide, by decide⟩

/-- `1 : Floating` -/
instance : One Floating where
  one := ⟨2^62, 2^63 - 62, by decide, by decide, by decide⟩

-- Definition lemmas
@[simp] lemma n_zero : (0 : Floating).n = 0 := rfl
@[simp] lemma s_zero : (0 : Floating).s = 0 := rfl
@[simp] lemma n_one : (1 : Floating).n = 2^62 := rfl
@[simp] lemma s_one : (1 : Floating).s = 2^63 - 62 := rfl
@[simp] lemma n_nan : (nan : Floating).n = .min := rfl
@[simp] lemma s_nan : (nan : Floating).s = .max := rfl

/-- `nan` could be anything -/
@[simp] lemma approx_nan : approx (nan : Floating) = univ := rfl

/-- `0 = 0` -/
@[simp] lemma val_zero : (0 : Floating).val = 0 := by
  simp only [val, n_zero, Int64.coe_zero, Int.cast_zero, s_zero, zero_mul]

/-- `0 ≠ nan` -/
@[simp] lemma zero_ne_nan : (0 : Floating) ≠ nan := by decide

/-- `nan ≠ 0` -/
@[simp] lemma nan_ne_zero : (nan : Floating) ≠ 0 := by decide

/-- `1 ≠ nan` -/
@[simp] lemma one_ne_nan : (1 : Floating) ≠ nan := by decide

/-- `nan ≠ 1` -/
@[simp] lemma nan_ne_one : (nan : Floating) ≠ 1 := by decide

/-- `0` is just zero -/
@[simp] lemma approx_zero : approx (0 : Floating) = {0} := by
  simp only [approx, zero_ne_nan, val_zero, ite_false]

/-- `1 = 1` -/
@[simp] lemma val_one : (1 : Floating).val = 1 := by
  have e0 : ((2^62 : Int64) : ℤ) = 2^62 := by decide
  have e1 : (2^63 - 62 : UInt64).toInt - 2^63 = -62 := by decide
  simp only [val, n_one, e0, Int.cast_pow, Int.int_cast_ofNat, s_one, e1, zpow_neg]
  apply mul_inv_cancel; norm_num

/-- If we're not `nan`, `approx` is a singleton -/
@[simp] lemma approx_eq_singleton {x : Floating} (n : x ≠ nan) : approx x = {x.val} := by
  simp only [approx, n, ite_false]

@[simp, mono] lemma val_mem_approx {x : Floating} : x.val ∈ approx x := by
  by_cases n : x = nan
  · simp only [n, approx_nan, mem_univ]
  · simp only [ne_eq, n, not_false_eq_true, approx_eq_singleton, mem_singleton_iff]

/-- If we're not nan, `x.n ≠ .min` -/
lemma n_ne_min {x : Floating} (n : x ≠ nan) : x.n ≠ .min := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.nan_same n⟩

/-- If we're not zero, `x.n ≠ 0` -/
lemma n_ne_zero {x : Floating} (n : x ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.zero_same n⟩

/-- If `x.s ≠ 0`, `x.n ≠ 0` -/
lemma n_ne_zero' {x : Floating} (n : x.s ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  simp only [x.zero_same n]

/-- `x.n = 0` exactly at 0 -/
lemma n_eq_zero_iff {x : Floating} : x.n = 0 ↔ x = 0 := by
  constructor
  · intro e; simp only [ext_iff, e, n_zero, x.zero_same e, s_zero, and_self]
  · intro e; simp only [e, n_zero]

/-- More user friendly version of `x.norm` -/
lemma norm' {x : Floating} (x0 : x ≠ 0) (s0 : x.s.toNat ≠ 0) : 2^62 ≤ x.n.abs.toNat := by
  by_cases xn : x = nan
  · simp [xn]; decide
  · exact x.norm (x.n_ne_zero x0) (x.n_ne_min xn) (UInt64.ne_zero_iff_toNat_ne_zero.mpr s0)

/-- Only `0` has zero `val` -/
lemma val_eq_zero {x : Floating} : x.val = 0 ↔ x = 0 := by
  rw [val]
  simp only [mul_eq_zero, Int.cast_eq_zero, Int64.coe_eq_zero, two_zpow_pos.ne', or_false, ext_iff,
    n_zero, s_zero, iff_self_and]
  exact x.zero_same

/-- Only `0` has zero `val` -/
lemma val_ne_zero {x : Floating} : x.val ≠ 0 ↔ x ≠ 0 := by
  rw [←not_iff_not, not_not, not_not, val_eq_zero]

/-!
### Simplification lemmas used elsewhere

This should really be cleaned up
-/

@[simp] lemma u62 : (62 : UInt64).toNat = 62 := rfl
@[simp] lemma u64 : (64 : UInt64).toNat = 64 := rfl
@[simp] lemma u65 : (65 : UInt64).toNat = 65 := rfl
@[simp] lemma u126 : (126 : UInt64).toNat = 126 := rfl
@[simp] lemma u127 : (127 : UInt64).toNat = 127 := rfl
@[simp] lemma up62 : (2^62 : UInt64).toNat = 2^62 := rfl
@[simp] lemma up63 : (2^63 : UInt64).toNat = 2^63 := rfl
@[simp] lemma ua2 : (2 : ℤ).natAbs = 2 := rfl

/-- Remove a `nan` possibility from a rounding statement -/
lemma rounds_of_ne_nan {a : ℝ} {x : Floating} {up : Bool}
    (h : x ≠ nan → if up = true then x.val ≤ a else a ≤ x.val) : a ∈ rounds (approx x) up := by
  by_cases n : x = nan
  · simp only [n, approx_nan, rounds_univ, mem_univ]
  · simp only [ne_eq, n, not_false_eq_true, approx_eq_singleton, mem_rounds_singleton, h n]

/-- `val` if we're nonnegative -/
lemma val_of_nonneg {x : Floating} (x0 : 0 ≤ x.val) :
    x.val = (x.n.n.toNat : ℝ) * 2^((x.s.toNat : ℤ) - 2^63) := by
  rw [val, UInt64.toInt, Int64.coe_of_nonneg, Int.cast_ofNat]
  rw [val] at x0
  simpa only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, gt_iff_lt, two_zpow_pos,
    mul_nonneg_iff_of_pos_right, Int.cast_nonneg, Int64.coe_nonneg_iff] using x0

/-!
### The smallest normalized value
-/

/-- The smallest normalized floating point value -/
@[irreducible] def min_norm : Floating :=
  ⟨⟨2^62⟩, 0, by decide, by decide, by decide⟩

@[simp] lemma min_norm_ne_nan : min_norm ≠ nan := by native_decide

@[simp] lemma val_min_norm : min_norm.val = 2^(62 - 2^63 : ℤ) := by
  have t0 : (2 : ℝ) ≠ 0 := by norm_num
  rw [val, min_norm]
  simp only [UInt64.toInt_zero, zero_sub]
  rw [Int64.coe_of_nonneg (by decide)]
  simp only [up62, Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.int_cast_ofNat,
    pow_mul_zpow t0]
  ring_nf

/-!
### Conversion to `Float`
-/

/-- Approximate `Floating` by a `Float` -/
@[irreducible, pp_dot] def toFloat (x : Floating) : Float :=
  bif x == nan then Float.nan else x.n.toFloat.scaleB (x.s.toInt - 2^63)

/-- We print `Fixed s` as an approximate floating point number -/
instance : Repr Floating where
  reprPrec x _ := x.toFloat.toStringFull
