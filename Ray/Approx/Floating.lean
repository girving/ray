import Ray.Approx.Interval

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

/-- Floating point number -/
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

instance : Zero Floating where
  zero := ⟨0,0⟩

instance : Zero FloatingInterval where
  zero := ⟨0,0⟩

instance : Neg Floating where
  neg x := ⟨x.s, -x.x⟩

instance : Neg FloatingInterval where
  neg x := ⟨x.s, -x.x⟩

def Floating.toFloat (x : Floating) : Float := x.x.toFloat

instance : Repr Floating where
  reprPrec x p := reprPrec x.x p

instance : Repr FloatingInterval where
  reprPrec x p := reprPrec x.x p

-- `.lo` and `.hi` for `FloatingInterval`
@[pp_dot] def FloatingInterval.lo (x : FloatingInterval) : Floating := ⟨x.s, x.x.lo⟩
@[pp_dot] def FloatingInterval.hi (x : FloatingInterval) : Floating := ⟨x.s, x.x.hi⟩

-- Basic lemmas
lemma Floating.approx_def (x : Floating) : approx x = approx x.x := rfl
lemma FloatingInterval.approx_def (x : FloatingInterval) : approx x = approx x.x := rfl
lemma Floating.neg_def (x : Floating) : -x = ⟨x.s, -x.x⟩ := rfl
lemma Floating.nan_def : (nan : Floating) = ⟨0,nan⟩ := rfl
lemma Floating.zero_def : (0 : Floating) = ⟨0,0⟩ := rfl
lemma FloatingInterval.neg_def (x : FloatingInterval) : -x = ⟨x.s, -x.x⟩ := rfl
lemma FloatingInterval.nan_def : (nan : FloatingInterval) = ⟨0,nan⟩ := rfl
lemma FloatingInterval.zero_def : (0 : FloatingInterval) = ⟨0,0⟩ := rfl
@[simp] lemma FloatingInterval.lo_neg (x : FloatingInterval) : (-x).x.lo = -x.x.hi := rfl
@[simp] lemma FloatingInterval.hi_neg (x : FloatingInterval) : (-x).x.hi = -x.x.lo := rfl
@[simp] lemma Floating.approx_nan : approx (nan : Floating) = univ := rfl
@[simp] lemma FloatingInterval.s_lo {x : FloatingInterval} : x.lo.s = x.s := rfl
@[simp] lemma FloatingInterval.s_hi {x : FloatingInterval} : x.hi.s = x.s := rfl
@[simp] lemma FloatingInterval.lo_nan : (nan : FloatingInterval).lo = nan := rfl
@[simp] lemma FloatingInterval.hi_nan : (nan : FloatingInterval).hi = nan := rfl
@[simp] lemma FloatingInterval.nan_x : (nan : FloatingInterval).x = nan := rfl

@[simp] lemma FloatingInterval.approx_nan : approx (nan : FloatingInterval) = univ := by
  simp only [approx, nan, or_self, Icc_self, ite_true]

@[simp] lemma FloatingInterval.approx_nan_lo {s : Int64} {hi : Fixed s} :
    approx (⟨s,nan,hi⟩ : FloatingInterval) = univ := by
  simp only [approx, true_or, ite_true]

@[simp] lemma FloatingInterval.approx_nan_hi {s : Int64} {lo : Fixed s} :
    approx (⟨s,lo,nan⟩ : FloatingInterval) = univ := by
  simp only [approx, or_true, ite_true]

@[simp] lemma FloatingInterval.approx_of_lo_eq_nan {x : FloatingInterval} (n : x.x.lo = nan) :
    approx x = univ := by
  simp only [approx, true_or, ite_true, n]

@[simp] lemma FloatingInterval.approx_of_hi_eq_nan {x : FloatingInterval} (n : x.x.hi = nan) :
    approx x = univ := by
  simp only [approx, or_true, ite_true, n]

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

/-- Turn `s ∈ approx x.x` into `s ∈ approx x` -/
@[mono] lemma FloatingInterval.mem_approx_mono (x : FloatingInterval) (a : ℝ) (h : a ∈ approx x) :
    a ∈ approx x.x := h

/-- `FloatingInterval`'s zero is conservative -/
@[mono] lemma FloatingInterval.approx_zero : 0 ∈ approx (0 : FloatingInterval) := by
  simp only [FloatingInterval.zero_def, FloatingInterval.approx_def, Interval.approx_zero,
    mem_singleton_iff]

/-!
### Coersion from fixed point to floating point, and from `Floating` to `FloatingInterval`
-/

/-- `Fixed s` to `Floating` by hiding `s` -/
@[irreducible, coe] def Fixed.toFloating {s : Int64} (x : Fixed s) : Floating := ⟨s,x⟩

/-- `Interval s` to `FloatingInterval` by hiding `s` -/
@[irreducible, coe] def Interval.toFloating {s : Int64} (x : Interval s) : FloatingInterval := ⟨s,x⟩

/-- `Floating` to `FloatingInterval` -/
@[irreducible, coe] def Floating.toFloatingInterval (x : Floating) : FloatingInterval :=
  ⟨x.s, x.x, x.x⟩

/-- Coersion from `Fixed s` to `Floating` -/
instance {s : Int64} : CoeHead (Fixed s) Floating where
  coe x := x.toFloating

/-- Coersion from `Interval s` to `FloatingInterval` -/
instance {s : Int64} : CoeHead (Interval s) FloatingInterval where
  coe x := x.toFloating

/-- Coersion from `Floating` to `FloatingInterval` -/
instance : Coe Floating FloatingInterval where
  coe x := x.toFloatingInterval

/-- `coe` doesn't change `approx` -/
@[simp] lemma Interval.approx_toFloating {s : Int64} {x : Interval s} :
    approx (x : FloatingInterval) = approx x := by
  rw [Interval.toFloating, FloatingInterval.approx_def]

/-- To prove `a ∈ approx (x : Floating)`, we prove `a ∈ approx x` -/
@[mono] lemma Floating.mem_approx_coe {s : Int64} {x : Fixed s} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : Floating) := by
  rw [Fixed.toFloating, Floating.approx_def]
  simpa only

/-- To prove `a ∈ approx (x : Floating)`, we prove `a ∈ approx x` -/
@[mono] lemma FloatingInterval.mem_approx_coe {s : Int64} {x : Interval s} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : FloatingInterval) := by
  rw [Interval.toFloating, FloatingInterval.approx_def]
  simpa only

/-- Coersion propagates  `nan` -/
@[simp] lemma FloatingInterval.coe_nan {s : Int64} :
    ((nan : Interval s) : FloatingInterval).x = nan := by
  simp only [Interval.toFloating, FloatingInterval.nan_def]

/-- To prove `a ∈ approx (x : FloatingInterval)`, we prove `a ∈ approx x` -/
@[mono] lemma Floating.mem_approx_toFloatingInterval {x : Floating} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : FloatingInterval) := by
  rw [Floating.toFloatingInterval, FloatingInterval.approx_def]
  simpa only [approx, mem_ite_univ_left, mem_singleton_iff, or_self, Icc_self] using ax

/-!
### Scale by changing the exponent
-/

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def Floating.scaleB (x : Floating) (t : Fixed 0) : Floating :=
  let k : Fixed 0 := ⟨x.s⟩ + t
  bif k == nan then nan else ⟨k.n, ⟨x.x.n⟩⟩

/-- Scale by changing the exponent -/
@[irreducible, pp_dot]
def FloatingInterval.scaleB (x : FloatingInterval) (t : Fixed 0) : FloatingInterval :=
  let k : Fixed 0 := ⟨x.s⟩ + t
  bif k == nan then nan else ⟨k.n, ⟨⟨x.x.lo.n⟩, ⟨x.x.hi.n⟩⟩⟩

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

/-- `FloatingInterval.scaleB` is `scaleB` of the endpoints -/
lemma FloatingInterval.scaleB_lo (x : FloatingInterval) (t : Fixed 0) :
    (x.scaleB t).lo = x.lo.scaleB t := by
  rw [FloatingInterval.scaleB, Floating.scaleB]
  simp only [bif_eq_if, beq_iff_eq, apply_ite (f := fun i : FloatingInterval ↦ i.lo), lo_nan, s_lo]
  simp only [FloatingInterval.lo, FloatingInterval.nan_def, Floating.nan_def]

/-- `FloatingInterval.scaleB` is `scaleB` of the endpoints -/
lemma FloatingInterval.scaleB_hi {x : FloatingInterval} {t : Fixed 0} :
    (x.scaleB t).hi = x.hi.scaleB t := by
  rw [FloatingInterval.scaleB, Floating.scaleB]
  simp only [bif_eq_if, beq_iff_eq, apply_ite (f := fun i : FloatingInterval ↦ i.hi), hi_nan, s_hi]
  simp only [FloatingInterval.hi, FloatingInterval.nan_def, Floating.nan_def]

/-- A `Fixed s` is still `nan` if we change the point -/
lemma Fixed.ne_nan_of_s {s t : Int64} {x : Fixed s} (n : x ≠ nan) : (⟨x.n⟩ : Fixed t) ≠ nan := by
  contrapose n; simpa only [ne_eq, ext_iff, nan_n, not_not] using n

/-- `FloatingInterval.scaleB` is conservative -/
@[mono] lemma FloatingInterval.mem_approx_scaleB {x : FloatingInterval} {t : Fixed 0} {x' t' : ℝ}
    (xm : x' ∈ approx x) (tm : t' ∈ approx t) : x' * 2^t' ∈ approx (x.scaleB t) := by
  by_cases n : x.x.lo = nan ∨ x.x.hi = nan ∨ (⟨x.s⟩ + t : Fixed 0) = nan
  · rcases n with n | n | n
    · rw [FloatingInterval.scaleB]
      simp only [bif_eq_if, beq_iff_eq, n, Fixed.nan_n, ← Fixed.nan_def, approx_nan_lo, ite_self,
        apply_ite (f := fun f : FloatingInterval ↦ x' * 2 ^ t' ∈ approx f), approx_nan, mem_univ]
    · rw [FloatingInterval.scaleB]
      simp only [bif_eq_if, beq_iff_eq, n, Fixed.nan_n, ← Fixed.nan_def, approx_nan_hi, ite_self,
        apply_ite (f := fun f : FloatingInterval ↦ x' * 2 ^ t' ∈ approx f), approx_nan, mem_univ]
    · rw [FloatingInterval.scaleB]
      simp only [bif_eq_if, n, beq_self_eq_true, ite_true, approx_nan, mem_univ]
  simp only [not_or, ←Ne.def] at n
  rcases n with ⟨ln, hn, kn⟩
  have kn' : ((⟨x.s⟩ + t : Fixed 0) == nan) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, neg_neg, kn, not_false_eq_true, Fixed.ne_nan_of_neg]
  rw [FloatingInterval.scaleB]
  simp only [bif_eq_if, beq_iff_eq, ne_eq, neg_neg, kn, not_false_eq_true, Fixed.ne_nan_of_neg,
    ite_false]
  simp only [approx, ne_eq, neg_neg, ln, not_false_eq_true, Fixed.ne_nan_of_neg, hn, or_self,
    ite_false, mem_Icc] at xm
  simp only [approx, mem_ite_univ_left, mem_Icc]
  intro _
  have lo := Floating.mem_approx_scaleB x.lo.x.val_mem_approx tm
  have hi := Floating.mem_approx_scaleB x.hi.x.val_mem_approx tm
  rw [Floating.scaleB] at lo hi
  -- Unfortunately making the following a `simp only` breaks things for some reason
  simp [kn', Floating.approx_def, FloatingInterval.lo, FloatingInterval.hi] at lo hi
  simp only [approx, ne_eq, neg_neg, Fixed.ne_nan_of_s ln, not_false_eq_true, Fixed.ne_nan_of_neg,
    ite_false, mem_singleton_iff, Fixed.ne_nan_of_s hn] at lo hi
  have p : ∀ {t : ℝ}, 0 < (2 : ℝ) ^ t := fun {_} ↦ Real.rpow_pos_of_pos (by norm_num) _
  simpa only [← lo, mul_le_mul_iff_of_pos_right p, ← hi]

/-- `scaleB` propagates coerced `nan`, roughly -/
@[simp] lemma FloatingInterval.approx_scaleB_coe_nan {s : Int64} {t : Fixed 0} :
    approx (FloatingInterval.scaleB (nan : Interval s) t) = univ := by
  rw [FloatingInterval.scaleB]
  simp only [bif_eq_if, beq_iff_eq, coe_nan, Interval.lo_nan, Fixed.nan_n, Interval.hi_nan]
  split_ifs
  · simp only [approx_nan]
  · simp only [approx, ← Fixed.nan_def, or_self, Icc_self, ite_true]

/-!
### Coersion from `ℚ` with maximum precision
-/

/-- The smallest `n` s.t. `|x| < 2^n` -/
@[irreducible] def Rat.log2 (x : ℚ) : ℤ :=
  -- Initial guess, which might be too low by one
  let n := x.num.natAbs
  let ln := n.log2
  let ld := x.den.log2
  let g : ℤ := ln - ld
  -- If `a / x.den < 2^g`, then `g` is good, otherwise we need `g + 1`
  let good := bif 0 ≤ g then decide (n < x.den <<< g.toNat) else n <<< (-g).toNat < x.den
  bif good then g else g+1

/-- Convert from `ℚ` to `FloatingInterval` with maximum precision -/
@[irreducible] def FloatingInterval.ofRat (x : ℚ) : FloatingInterval :=
  bif x == 0 then 0 else
  -- Don't worry about exponent overflow if we're nonzero (for now)
  let n : Int64 := (x.log2 - 63 : ℤ)
  (.ofRat x : Interval n)

/-- `FloatingInterval.ofRat` is conservative -/
@[mono] lemma FloatingInterval.approx_ofRat (x : ℚ) : ↑x ∈ approx (FloatingInterval.ofRat x) := by
  rw [ofRat]
  simp only [bif_eq_if, beq_iff_eq]
  split_ifs with h
  · simp only [h, Rat.cast_zero, approx_zero]
  · mono

/-- `FloatingInterval.approx_ofRat` for rational literals `a / b` -/
@[mono] lemma FloatingInterval.ofNat_div_mem_approx_ofRat {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    OfNat.ofNat a / OfNat.ofNat b ∈
      approx (FloatingInterval.ofRat (OfNat.ofNat a / OfNat.ofNat b)) := by
  convert FloatingInterval.approx_ofRat _; simp only [Rat.cast_div, Rat.cast_ofNat]

/-- `FloatingInterval.approx_ofRat` for rational literals `1 / b` -/
@[mono] lemma FloatingInterval.one_div_ofNat_mem_approx_ofRat {b : ℕ} [b.AtLeastTwo] :
    1 / OfNat.ofNat b ∈ approx (FloatingInterval.ofRat (1 / OfNat.ofNat b)) := by
  convert FloatingInterval.approx_ofRat _; simp only [one_div, Rat.cast_inv, Rat.cast_ofNat]

/-!
### `FloatingInterval` union
-/

/-- Union repoints to the larger of the two points -/
instance FloatingInterval.instUnion : Union FloatingInterval where
  union x y :=
    bif x.x == nan || y.x == nan then nan else
    bif x.s ≤ y.s then ⟨y.s, x.x.repoint y.s ∪ y.x⟩
    else ⟨x.s, x.x ∪ y.x.repoint x.s⟩

/-- `FloatingInterval.union` respects `approx` -/
lemma FloatingInterval.approx_union_left {x y : FloatingInterval} : approx x ⊆ approx (x ∪ y) := by
  simp only [instUnion, bif_eq_if, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.x = nan ∨ y.x = nan
  · rcases n with n | n; repeat simp [n]
  rcases not_or.mp n with ⟨n0,n1⟩
  simp only [n0, n1, or_self, ite_false]
  by_cases xy : x.s ≤ y.s
  · simp only [xy, ite_true, FloatingInterval.approx_def]
    refine subset_trans ?_ Interval.approx_union_left
    mono
  · simp only [xy, if_false]
    exact Interval.approx_union_left

/-- `FloatingInterval.union` respects `approx` -/
lemma FloatingInterval.approx_union_right {x y : FloatingInterval} : approx y ⊆ approx (x ∪ y) := by
  simp only [instUnion, bif_eq_if, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.x = nan ∨ y.x = nan
  · rcases n with n | n; repeat simp [n]
  rcases not_or.mp n with ⟨n0,n1⟩
  simp only [n0, n1, or_self, ite_false]
  by_cases xy : x.s ≤ y.s
  · simp only [xy, ite_true]
    exact Interval.approx_union_right
  · simp only [xy, if_false]; simp only [FloatingInterval.approx_def]
    refine subset_trans ?_ Interval.approx_union_right
    mono

/-- `FloatingInterval.union` propagates `nan` -/
@[simp] lemma FloatingInterval.union_nan {x : FloatingInterval} : x ∪ nan = nan := by
  simp only [instUnion, Bool.cond_decide, nan_x, beq_self_eq_true, Bool.or_true, Interval.union_nan,
    Interval.repoint_nan, cond_true]

/-- `FloatingInterval.union` propagates `nan` -/
@[simp] lemma FloatingInterval.nan_union {x : FloatingInterval} : nan ∪ x = nan := by
  simp only [instUnion, Bool.cond_decide, nan_x, beq_self_eq_true, Bool.true_or,
    Interval.repoint_nan, Interval.nan_union, cond_true]

/-!
### Crude floating point multiplication

These are not optimized, but currently I only use them a bit.  I'll likely want them more in
future, at which point I can improve them.
-/

/-- Adaptive precision `Interval * Interval` multiplication -/
@[irreducible] def FloatingInterval.mul (x y : FloatingInterval) : FloatingInterval :=
  bif x.x == nan || y.x == nan then nan else
  let s := x.x.abs.hi.log2
  let t := y.x.abs.hi.log2
  -- We have `|x| < 2^(s+1)` and `|y| < 2^(t+1)`, so `x * y < 2^(s + t + 2)`
  let u := s + t - 61
  bif u == nan then nan else x.x.mul y.x u.n

/-- Adaptive precision `Interval * Interval` multiplication -/
instance FloatingInterval.instMul : Mul FloatingInterval where
  mul x y := x.mul y

/-- See through the definition -/
lemma FloatingInterval.mul_def (x y : FloatingInterval) : x * y = x.mul y := rfl

/-- Multiplication propagates `nan` -/
@[simp] lemma FloatingInterval.mul_nan (x : FloatingInterval) : x * nan = nan := by
  rw [mul_def, mul]
  simp only [nan_x, beq_self_eq_true, Bool.or_true, Interval.abs_nan_hi, Fixed.log2_nan,
    Fixed.add_nan, Fixed.nan_add, Interval.lo_nan, Interval.mul_nan_lo, cond_true, Bool.cond_self]

/-- Multiplication propagates `nan` -/
@[simp] lemma FloatingInterval.nan_mul (x : FloatingInterval) : nan * x = nan := by
  rw [mul_def, mul]
  simp only [nan_x, beq_self_eq_true, Bool.true_or, Interval.abs_nan_hi, Fixed.log2_nan,
    Fixed.nan_add, Interval.lo_nan, Interval.nan_mul_lo, cond_true, Bool.cond_self]

/-- `FloatingInterval` multiplication is conservative -/
instance : ApproxMul FloatingInterval ℝ where
  approx_mul x y := by
    rw [FloatingInterval.mul_def, FloatingInterval.mul]
    simp only [bif_eq_if, beq_iff_eq, Bool.or_eq_true]
    generalize x.x.abs.hi.log2 + y.x.abs.hi.log2 - 61 = u
    by_cases n : x.x = nan ∨ y.x = nan ∨ u = nan
    · rcases n with n | n | n
      · simp only [n, Interval.lo_nan, FloatingInterval.approx_of_lo_eq_nan, true_or,
          Interval.nan_mul_lo, ite_true, FloatingInterval.nan_x, subset_univ]
      · simp only [n, Interval.lo_nan, FloatingInterval.approx_of_lo_eq_nan, or_true,
          Interval.mul_nan_lo, ite_true, FloatingInterval.nan_x, subset_univ]
      · simp only [n, ite_true, ite_self, FloatingInterval.nan_x, Interval.lo_nan,
          FloatingInterval.approx_of_lo_eq_nan, subset_univ]
    · simp only [not_or] at n
      rcases n with ⟨n0,n1,n2⟩
      simp only [ne_eq, neg_neg, n0, n1, n2, not_false_eq_true, Fixed.ne_nan_of_neg, ite_false,
        Interval.approx_toFloating, false_or, if_false]
      apply Interval.approx_mul

/-!
### Unit tests
-/

/-- Test that `FloatingInterval.ofRat` gives maximum precision  -/
@[irreducible] def floating_ofRat_test (x : ℚ) : Bool :=
  let f := FloatingInterval.ofRat x
  let good := fun x : Fixed f.s ↦ 2^62 ≤ x.n.abs && x.n.abs < 2^63
  good f.x.lo && good f.x.hi
lemma floating_ofRat_test0 : floating_ofRat_test 12873218.231231 = true := by native_decide
lemma floating_ofRat_test1 : floating_ofRat_test (-12873218.231231) = true := by native_decide
lemma floating_ofRat_test2 : floating_ofRat_test 178732 = true := by native_decide
lemma floating_ofRat_test3 : floating_ofRat_test 378732 = true := by native_decide
lemma floating_ofRat_test4 : floating_ofRat_test 4123 = true := by native_decide

/-- Test that multiplication gives near-maximum precision -/
@[irreducible] def floating_mul_test (x y : ℚ) : Bool :=
  let f := FloatingInterval.ofRat x * FloatingInterval.ofRat y
  2^61 ≤ f.x.abs.hi.n
lemma floating_mul_test0 : floating_mul_test 0.0071520 (-2015.777) := by native_decide
lemma floating_mul_test1 : floating_mul_test (-593.1319) 7.160858e-05 := by native_decide
lemma floating_mul_test2 : floating_mul_test (-2596.9072) 0.7278638 := by native_decide
lemma floating_mul_test3 : floating_mul_test (-1.092227) 98.18636 := by native_decide
