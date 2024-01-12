import Ray.Approx.Interval

open Classical
open Pointwise

/-!
## Simple floating point types and utilities

These are currently used for division.
-/

open Set
open scoped Real

/-!
## `Floating` and `FloatingInterval` basics
-/

/-- Very constrained floating point type.  We use this only for division currently. -/
structure Floating where
  s : Int64
  x : Fixed s

/-- Floating point interval -/
structure FloatingInterval where
  s : Int64
  x : Interval s

/-- Standard floating point nan -/
instance : Nan Floating where
  nan := ⟨0,nan⟩

/-- Standard floating point interval nan -/
instance : Nan FloatingInterval where
  nan := ⟨0,nan⟩

instance : Approx Floating ℝ where
  approx x := approx x.x

instance : Approx FloatingInterval ℝ where
  approx x := approx x.x

@[pp_dot] noncomputable def Floating.val (x : Floating) : ℝ :=
  x.x.val

instance : Neg Floating where
  neg x := ⟨x.s, -x.x⟩

instance : Neg FloatingInterval where
  neg x := ⟨x.s, -x.x⟩

def Floating.toFloat (x : Floating) : Float := x.x.toFloat

instance : Repr Floating where
  reprPrec x p := reprPrec x.x p

instance : Repr FloatingInterval where
  reprPrec x p := reprPrec x.x p

-- Basic lemmas
lemma Floating.approx_def (x : Floating) : approx x = approx x.x := rfl
lemma FloatingInterval.approx_def (x : FloatingInterval) : approx x = approx x.x := rfl
lemma Floating.neg_def (x : Floating) : -x = ⟨x.s, -x.x⟩ := rfl
lemma FloatingInterval.neg_def (x : FloatingInterval) : -x = ⟨x.s, -x.x⟩ := rfl
@[simp] lemma FloatingInterval.lo_neg (x : FloatingInterval) : (-x).x.lo = -x.x.hi := rfl
@[simp] lemma FloatingInterval.hi_neg (x : FloatingInterval) : (-x).x.hi = -x.x.lo := rfl

@[simp] lemma FloatingInterval.approx_nan : approx (nan : FloatingInterval) = univ := by
  simp only [approx, nan, or_self, Icc_self, ite_true]

@[simp] lemma FloatingInterval.approx_nan' {s : Int64} :
    approx (⟨s,nan⟩ : FloatingInterval) = univ := by
  simp only [approx, nan, or_self, Icc_self, ite_true]

instance : ApproxNeg (FloatingInterval) ℝ where
  approx_neg x := by apply approx_neg (A := Interval x.s)

/-- `FloatingInterval` has `OrdConncted` `approx` -/
instance : ApproxConnected FloatingInterval ℝ where
  connected x := by apply ApproxConnected.connected (A := Interval x.s)

/-- Turn `s ⊆ approx x.x` into `s ⊆ approx x` -/
@[mono] lemma Floating.approx_mono (x : Floating) (s : Set ℝ) (h : s ⊆ approx x) :
    s ⊆ approx x.x := h

/-- Turn `approx x` into `approx x` -/
@[simp] lemma Floating.approx_x (x : Floating) : approx x.x = approx x := rfl

/-- Turn `approx x` into `approx x` -/
@[simp] lemma FloatingInterval.approx_x (x : FloatingInterval) : approx x.x = approx x := rfl

/-- Turn `s ⊆ approx x.x` into `s ⊆ approx x` -/
@[mono] lemma FloatingInterval.approx_mono (x : FloatingInterval) (s : Set ℝ) (h : s ⊆ approx x) :
    s ⊆ approx x.x := h
