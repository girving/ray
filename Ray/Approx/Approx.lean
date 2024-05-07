import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Set.NAry
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Monotonicity.Basic

/-!
## Approximate arithmetic typeclasses
-/

open Pointwise
open Set

variable {R A : Type}

/-- `A` approximates `R`, in that we can map `A → Set R` -/
class Approx (A : Type) (R : outParam Type) where
  approx (x : A) : Set R

export Approx (approx)

/-- `-A` is conservative -/
class ApproxNeg (A R : Type) [Neg R] [Neg A] [Approx A R] where
  approx_neg (x : A) : -approx x ⊆ approx (-x)

/-- `A + A` is conservative -/
class ApproxAdd (A R : Type) [Add R] [Add A] [Approx A R] where
  approx_add (x y : A) : approx x + approx y ⊆ approx (x + y)

/-- `A - A` is conservative -/
class ApproxSub (A R : Type) [Sub R] [Sub A] [Approx A R] where
  approx_sub (x y : A) : approx x - approx y ⊆ approx (x - y)

/-- `A * A` is conservative -/
class ApproxMul (A R : Type) [Mul R] [Mul A] [Approx A R] where
  approx_mul (x y : A) : approx x * approx y ⊆ approx (x * y)

/-- `A⁻¹` is conservative -/
class ApproxInv (A R : Type) [Inv R] [Inv A] [Approx A R] where
  approx_inv (x : A) : (approx x)⁻¹ ⊆ approx x⁻¹

/-- `star A` is conservative -/
class ApproxStar (A R : Type) [Star R] [Star A] [Approx A R] where
  approx_star (x : A) : star '' approx x ⊆ approx (star x)

/-- `A / A` is conservative -/
class ApproxDiv (A R : Type) [Div R] [Div A] [Approx A R] where
  approx_div (x y : A) : approx x / approx y ⊆ approx (x / y)

/-- `A • B` is conservative -/
class ApproxSMul (A B A' B' : Type) [SMul A B] [SMul A' B'] [Approx A A'] [Approx B B'] where
  mem_approx_smul {s' : A'} {x' : B'} {s : A} {x : B} (sm : s' ∈ approx s) (xm : x' ∈ approx x) :
      s' • x' ∈ approx (s • x)

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
export ApproxInv (approx_inv)
export ApproxStar (approx_star)
export ApproxDiv (approx_div)
export ApproxSMul (mem_approx_smul)

/-!
## Typeclass for `nan`
-/

class Nan (A : Type) where
  nan : A

export Nan (nan)

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

lemma subset_rounds [Preorder R] (s : Set R) (up : Bool) : s ⊆ rounds s up := by
  intro x m; use x
  simp only [ite_self, le_refl, m, true_and]

@[mono] lemma rounds_mono (st : s ⊆ t) : rounds s up ⊆ rounds t up := by
  intro x m; rcases m with ⟨y,m,h⟩; exact ⟨y, st m, h⟩

@[simp] lemma rounds_neg [OrderedAddCommGroup I] : rounds (-s) up = -(rounds s !up) := by
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

/-!
## `mono` machinery
-/

-- Make `mono` handle `s ⊆ s`
attribute [mono] subset_refl

attribute [mono] mem_approx_smul

@[mono] lemma subset_approx_neg [Neg R] [Neg A] [Approx A R] [ApproxNeg A R] {a : Set R} (x : A)
    (ax : a ⊆ approx x) : -a ⊆ approx (-x) := by
  refine subset_trans ?_ (approx_neg x)
  intro b m; exact ax m

@[mono] lemma subset_approx_add [Add R] [Add A] [Approx A R] [ApproxAdd A R] {a b : Set R} {x y : A}
    (ax : a ⊆ approx x) (yb : b ⊆ approx y) : a + b ⊆ approx (x + y) :=
  subset_trans (add_subset_add ax yb) (approx_add x y)

@[mono] lemma subset_approx_sub [Sub R] [Sub A] [Approx A R] [ApproxSub A R] {a b : Set R} {x y : A}
    (ax : a ⊆ approx x) (yb : b ⊆ approx y) : a - b ⊆ approx (x - y) :=
  subset_trans (sub_subset_sub ax yb) (approx_sub x y)

@[mono] lemma subset_approx_mul [Mul R] [Mul A] [Approx A R] [ApproxMul A R] {a b : Set R} {x y : A}
    (ax : a ⊆ approx x) (yb : b ⊆ approx y) : a * b ⊆ approx (x * y) :=
  subset_trans (mul_subset_mul ax yb) (approx_mul x y)

@[mono] lemma subset_approx_inv [InvolutiveInv R] [Inv A] [Approx A R] [ApproxInv A R] {s : Set R}
    {x : A} (sx : s ⊆ approx x) : s⁻¹ ⊆ approx x⁻¹ :=
  subset_trans (inv_subset_inv.mpr sx) (approx_inv x)

@[mono] lemma subset_approx_star [Star R] [Star A] [Approx A R] [ApproxStar A R] {s : Set R}
    {x : A} (sx : s ⊆ approx x) : star '' s ⊆ approx (star x) :=
  subset_trans (image_mono sx) (approx_star x)

@[mono] lemma subset_approx_div [Div R] [Div A] [Approx A R] [ApproxDiv A R] {a b : Set R} {x y : A}
    (ax : a ⊆ approx x) (yb : b ⊆ approx y) : a / b ⊆ approx (x / y) :=
  subset_trans (div_subset_div ax yb) (approx_div x y)

@[mono] lemma mem_approx_neg [InvolutiveNeg R] [Neg A] [Approx A R] [ApproxNeg A R] {a : R} {x : A}
    (ax : a ∈ approx x) : -a ∈ approx (-x) := by
  apply approx_neg x; simpa only [mem_neg, neg_neg]

@[mono] lemma mem_approx_add [Add R] [Add A] [Approx A R] [ApproxAdd A R] {a b : R} {x y : A}
    (ax : a ∈ approx x) (yb : b ∈ approx y) : a + b ∈ approx (x + y) := by
  apply subset_approx_add (singleton_subset_iff.mpr ax) (singleton_subset_iff.mpr yb)
  simp only [add_singleton, image_singleton, mem_singleton_iff]

@[mono] lemma mem_approx_sub [Sub R] [Sub A] [Approx A R] [ApproxSub A R] {a b : R} {x y : A}
    (ax : a ∈ approx x) (yb : b ∈ approx y) : a - b ∈ approx (x - y) := by
  apply subset_approx_sub (singleton_subset_iff.mpr ax) (singleton_subset_iff.mpr yb)
  simp only [sub_singleton, image_singleton, mem_singleton_iff]

@[mono] lemma mem_approx_mul [Mul R] [Mul A] [Approx A R] [ApproxMul A R] {a b : R} {x y : A}
    (ax : a ∈ approx x) (yb : b ∈ approx y) : a * b ∈ approx (x * y) := by
  apply subset_approx_mul (singleton_subset_iff.mpr ax) (singleton_subset_iff.mpr yb)
  simp only [mul_singleton, image_singleton, mem_singleton_iff]

@[mono] lemma mem_approx_inv [InvolutiveInv R] [Inv A] [Approx A R] [ApproxInv A R] {a : R} {x : A}
    (ax : a ∈ approx x) : a⁻¹ ∈ approx x⁻¹ := by
  apply subset_approx_inv (singleton_subset_iff.mpr ax)
  simp only [inv_singleton, mem_singleton_iff]

@[mono] lemma mem_approx_star [Star R] [Star A] [Approx A R] [ApproxStar A R] {a : R} {x : A}
    (ax : a ∈ approx x) : star a ∈ approx (star x) := by
  apply subset_approx_star (singleton_subset_iff.mpr ax)
  simp only [image_singleton, mem_singleton_iff]

@[mono] lemma mem_approx_div [Div R] [Div A] [Approx A R] [ApproxDiv A R] {a b : R} {x y : A}
    (ax : a ∈ approx x) (yb : b ∈ approx y) : a / b ∈ approx (x / y) := by
  apply subset_approx_div (singleton_subset_iff.mpr ax) (singleton_subset_iff.mpr yb)
  simp only [div_singleton, image_singleton, mem_singleton_iff]

/-- Test `mono` for `⊆ approx`-/
lemma approx_mono_subset_test [Field R] [ApproxField A R] (x y z : A) :
    approx x + approx y * -approx z ⊆ approx (x + y * -z) := by mono

/-- Test `mono` for `∈ approx`-/
lemma approx_mono_mem_test [Field R] [ApproxField A R] (a b c : R) (x y z : A)
    (am : a ∈ approx x) (bm : b ∈ approx y) (cm : c ∈ approx z) :
    a + b * -c ∈ approx (x + y * -z) := by mono

/-!
## Convexity of `approx`
-/

/-- `A` has a convex `approx` -/
class ApproxConnected (A R : Type) [Approx A R] [Preorder R] where
  connected (x : A) : OrdConnected (approx x)

/-- `Icc ⊆ approx` if the endpoints are included -/
@[mono] lemma Icc_subset_approx [Approx A R] [Preorder R] [ApproxConnected A R] {a b : R} {x : A}
    (ax : a ∈ approx x) (bx : b ∈ approx x) : Icc a b ⊆ approx x :=
  (ApproxConnected.connected _).out ax bx
