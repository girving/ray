import Ray.Approx.Interval

open Pointwise

/-!
## Simple floating point types and utilities

These are currently used for division.
-/

open Set
open scoped Real

/-!
## `Floating` basics
-/

/-- Floating point number -/
structure Floating where
  s : Int64
  x : Fixed s

/-- Standard floating point nan -/
instance : Nan Floating where
  nan := ⟨0,nan⟩

instance : Approx Floating ℝ where
  approx x := approx x.x

@[pp_dot] noncomputable def Floating.val (x : Floating) : ℝ :=
  x.x.val

instance : Zero Floating where
  zero := ⟨0,0⟩

instance : Neg Floating where
  neg x := ⟨x.s, -x.x⟩

def Floating.toFloat (x : Floating) : Float := x.x.toFloat

instance : Repr Floating where
  reprPrec x p := reprPrec x.x p

-- Basic lemmas
lemma Floating.approx_def (x : Floating) : approx x = approx x.x := rfl
lemma Floating.neg_def (x : Floating) : -x = ⟨x.s, -x.x⟩ := rfl
lemma Floating.nan_def : (nan : Floating) = ⟨0,nan⟩ := rfl
lemma Floating.zero_def : (0 : Floating) = ⟨0,0⟩ := rfl
@[simp] lemma Floating.approx_nan : approx (nan : Floating) = univ := rfl

/-- Turn `s ⊆ approx x.x` into `s ⊆ approx x` -/
@[mono] lemma Floating.approx_mono (x : Floating) (s : Set ℝ) (h : s ⊆ approx x) :
    s ⊆ approx x.x := h

/-- Turn `approx x` into `approx x` -/
@[simp] lemma Floating.approx_x (x : Floating) : approx x.x = approx x := rfl

/-!
### Coersion from fixed point to floating point
-/

/-- `Fixed s` to `Floating` by hiding `s` -/
@[irreducible, coe] def Fixed.toFloating {s : Int64} (x : Fixed s) : Floating := ⟨s,x⟩

/-- Coersion from `Fixed s` to `Floating` -/
instance {s : Int64} : CoeHead (Fixed s) Floating where
  coe x := x.toFloating

/-- To prove `a ∈ approx (x : Floating)`, we prove `a ∈ approx x` -/
@[mono] lemma Floating.mem_approx_coe {s : Int64} {x : Fixed s} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : Floating) := by
  rw [Fixed.toFloating, Floating.approx_def]
  simpa only

/-!
### Scale by changing the exponent
-/

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def Floating.scaleB (x : Floating) (t : Fixed 0) : Floating :=
  let k : Fixed 0 := ⟨x.s⟩ + t
  bif k == nan then nan else ⟨k.n, ⟨x.x.n⟩⟩

/-- `Floating.scaleB` is conservative -/
@[mono] lemma Floating.mem_approx_scaleB {x : Floating} {t : Fixed 0} {x' t' : ℝ}
    (xm : x' ∈ approx x) (tm : t' ∈ approx t) : x' * 2^t' ∈ approx (x.scaleB t) := by
  rw [Floating.scaleB]
  generalize hk : (⟨x.s⟩ + t : Fixed 0) = k
  simp only [bif_eq_if, beq_iff_eq]
  by_cases kn : k = nan
  · simp only [kn, ite_true, approx_nan, mem_univ]
  by_cases tn : t = nan
  · simp only [← hk, tn, Fixed.add_nan, not_true_eq_false] at kn
  simp only [apply_ite (f := fun f : Floating ↦ x' * 2^t' ∈ approx f), approx_nan, mem_univ]
  split_ifs
  simp only [ne_eq, neg_neg, kn, not_false_eq_true, Fixed.ne_nan_of_neg, approx, Fixed.val,
    ite_false]
  split_ifs with h
  · exact mem_univ _
  · by_cases xxn : x.x = nan
    · rw [xxn, Fixed.ext_iff] at h
      simp only [Fixed.nan_n, not_true_eq_false] at h
    · rw [Floating.approx_def, Fixed.approx_eq_singleton xxn, mem_singleton_iff] at xm
      rw [Fixed.approx_eq_singleton tn, mem_singleton_iff, Fixed.val_of_s0] at tm
      have st : (k.n : ℤ) = x.s + t.n := by
        rw [←hk] at kn ⊢
        simpa only [Fixed.val_of_s0, ←Int.cast_add, Int.cast_inj] using Fixed.val_add kn
      simp only [xm, Fixed.val, tm, Real.rpow_int_cast, mul_assoc, st,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mem_singleton_iff]

/-- A `Fixed s` is still `nan` if we change the point -/
lemma Fixed.ne_nan_of_s {s t : Int64} {x : Fixed s} (n : x ≠ nan) : (⟨x.n⟩ : Fixed t) ≠ nan := by
  contrapose n; simpa only [ne_eq, ext_iff, nan_n, not_not] using n
