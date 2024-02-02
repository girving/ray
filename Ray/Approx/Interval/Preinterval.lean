import Ray.Approx.Interval.Basic

open Classical
open Pointwise

/-!
## `Preinterval` is `Interval` without the correctness properties

This lets us write a routine, prove it correct, then finalize it.
-/

open Set
open scoped Real

/-- `Interval` without the correctness properties. -/
structure Preinterval where
  /-- Lower bound -/
  lo : Floating
  /-- Upper bound -/
  hi : Floating

namespace Preinterval

/-- Standard `Preinterval` nan -/
instance : Nan Preinterval where
  nan := ⟨nan, nan⟩

/-- `Preinterval` approximates `ℝ` -/
instance : Approx Preinterval ℝ where
  approx x := if x.lo = nan ∨ x.hi = nan then univ else Icc x.lo.val x.hi.val

@[simp] lemma approx_nan : approx (nan : Preinterval) = univ := by
  simp only [approx, nan, or_self, Icc_self, ite_true]

@[simp] lemma approx_nan_lo {x : Floating} : approx (⟨nan,x⟩ : Preinterval) = univ := by
  simp only [approx, nan, true_or, ite_true]

@[simp] lemma approx_nan_hi {x : Floating} : approx (⟨x,nan⟩ : Preinterval) = univ := by
  simp only [approx, nan, or_true, ite_true]
