import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Set.NAry
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Tactic.Linarith.Frontend

/-!
## Approximate arithmetic typeclasses
-/

open Pointwise
open Set

variable {R A : Type}

/-- `A` approximates `R`, in that we can map `A → Set R` -/
class Approx (A : Type) (R : outParam Type) where
  approx : A → Set R

export Approx (approx)

/-- `-A` is conservative -/
class ApproxNeg (A R : Type) [Neg R] [Neg A] [Approx A R] where
  approx_neg : ∀ x : A, -approx x ⊆ approx (-x)

/-- `A + A` is conservative -/
class ApproxAdd (A R : Type) [Add R] [Add A] [Approx A R] where
  approx_add : ∀ x y : A, approx x + approx y ⊆ approx (x + y)

/-- `A - A` is conservative -/
class ApproxSub (A R : Type) [Sub R] [Sub A] [Approx A R] where
  approx_sub : ∀ x y : A, approx x - approx y ⊆ approx (x - y)

/-- `A * A` is conservative -/
class ApproxMul (A R : Type) [Mul R] [Mul A] [Approx A R] where
  approx_mul : ∀ x y : A, approx x * approx y ⊆ approx (x * y)

/-- `A / A` is conservative -/
class ApproxDiv (A R : Type) [Div R] [Div A] [Approx A R] where
  approx_div : ∀ x y : A, approx x / approx y ⊆ approx (x / y)

/-- `A` approximates the additive group `R` -/
class ApproxAddGroup (A : Type) (R : outParam Type) [AddGroup R] extends
  Neg A, Add A, Sub A, Approx A R, ApproxNeg A R, ApproxAdd A R, ApproxSub A R where

/-- `A` approximates the ring `R` -/
class ApproxRing (A : Type) (R : outParam Type) [Ring R] extends
  ApproxAddGroup A R, Mul A, ApproxMul A R where

/-- `A` approximates the field `R` -/
class ApproxField (A : Type) (R : outParam Type) [Field R] extends
  ApproxRing A R, Div A, ApproxDiv A R where

export ApproxNeg (approx_neg)
export ApproxAdd (approx_add)
export ApproxSub (approx_sub)
export ApproxMul (approx_mul)
export ApproxDiv (approx_div)

/-!
### Rounding utilities

For when we approximately round up or down.
-/

variable {I : Type} [LinearOrder I]
variable {up : Bool}
variable {s t : Set I}

def rounds [LE R] (s : Set R) (up : Bool) : Set R :=
  {x : R | ∃ y ∈ s, if up then y ≤ x else x ≤ y}

@[simp] lemma rounds_univ {up : Bool} : rounds (univ : Set I) up = univ := by
  ext x; simp only [rounds, mem_univ, true_and, mem_setOf_eq, iff_true]
  use x; simp only [ite_self]; rfl

lemma rounds_mono (st : s ⊆ t) : rounds s up ⊆ rounds t up := by
  intro x m; rcases m with ⟨y,m,h⟩; exact ⟨y, st m, h⟩

lemma rounds_neg [OrderedAddCommGroup I] : rounds (-s) up = -(rounds s !up) := by
  ext x
  simp only [rounds, mem_neg, mem_setOf_eq, Bool.not_eq_true']
  by_cases u : up
  repeat {
    constructor
    · intro ⟨y,m,h⟩; exact ⟨-y, m, by simpa only [u, neg_le_neg_iff, ite_false, ite_true] using h⟩
    · intro ⟨y,m,h⟩; refine ⟨-y, by simpa only [neg_neg], ?_⟩
      simp only [u, ite_false, ite_true] at h ⊢; simpa only [neg_le, le_neg] }

@[simp] lemma mem_rounds_singleton {x y : I} :
    x ∈ rounds {y} up ↔ (if up then y ≤ x else x ≤ y) := by
  simp only [rounds, mem_singleton_iff, exists_eq_left, mem_setOf_eq]
