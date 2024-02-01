import Ray.Approx.UInt128

/-!
## `Int128`: 128-bit signed integers
-/

open Classical

/-- 128-bit twos complement signed integers -/
@[ext] structure Int128 where
  n : UInt128
  deriving DecidableEq, BEq

namespace Int128

@[pp_dot] def isNeg (x : Int128) : Bool := 2^63 ≤ x.n.hi

@[irreducible] def min : Int128 := ⟨⟨0, 2^63⟩⟩

/-!
### Conversion from other integer types
-/

@[coe] def of_lo (x : UInt64) : Int128 :=
  ⟨⟨x, 0⟩⟩

/-- `UInt64` coerces to `Int128` -/
instance : Coe UInt64 Int128 where
  coe := of_lo

/-- Conversion from `ℕ` -/
@[irreducible] def ofNat (x : ℕ) : Int128 :=
  ⟨⟨x, x >>> 64⟩⟩

/-!
### `ℤ` conversion
-/

/-- The `ℤ` that an `Int128` represents -/
@[coe] def toInt (x : Int128) : ℤ :=
  (x.n.toNat : ℤ) - (bif x.isNeg then 2^128 else 0)

/-- The `ℤ` that an `Int64` represents -/
instance : Coe Int128 ℤ where
  coe x := x.toInt

/-- If `hi = 0`, conversion is just `lo` -/
@[simp] lemma coe_of_hi_eq_zero {x : Int128} (h0 : x.n.hi = 0) : (x.n.lo.toNat : ℤ) = x := by
  have c : ¬(2:UInt64) ^ 63 ≤ 0 := by decide
  simp only [toInt, isNeg, h0, c, decide_False, bif_eq_if, ite_false, sub_zero, Nat.cast_inj,
    UInt128.toNat_def, UInt64.toNat_zero, zero_mul, zero_add]

/-- `isNeg` is nicer in terms of integers -/
@[simp] lemma isNeg_iff {x : Int128} : x.isNeg = decide ((x : ℤ) < 0) := by
  simp only [toInt, sub_neg]
  by_cases n : x.isNeg
  · simp only [n, cond_true, true_eq_decide_iff]
    exact lt_of_lt_of_le (Nat.cast_lt.mpr x.n.toNat_lt) (by norm_num)
  · simp only [n, cond_false, false_eq_decide_iff, not_lt, Nat.cast_nonneg]

/-!
### Additive group operations: negation, addition, subtraction
-/

-- These are just the underlying `UInt128` operations
instance : Neg Int128 where neg x := ⟨-x.n⟩
instance : Add Int128 where add x y := ⟨x.n + y.n⟩
instance : Sub Int128 where sub x y := ⟨x.n - y.n⟩

lemma coe_neg (x : Int128) : ((-x : Int128) : ℤ) = if x = .min then -2^127 else -(x : ℤ) := by
  
