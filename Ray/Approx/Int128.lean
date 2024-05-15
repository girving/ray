import Ray.Approx.UInt128

/-!
## `Int128`: 128-bit signed integers
-/

open Classical
open Set

/-- 128-bit twos complement signed integers -/
@[ext] structure Int128 where
  n : UInt128
  deriving DecidableEq, BEq

namespace Int128

@[irreducible, pp_dot] def isNeg (x : Int128) : Bool := 2^63 ≤ x.n.hi

@[irreducible] def min : Int128 := ⟨⟨0, 2^63⟩⟩

instance : Zero Int128 where zero := ⟨0⟩
@[simp] lemma n_zero : (0 : Int128).n = 0 := rfl

/-- Alternative `isNeg` characterization in terms of `n.toNat` -/
lemma isNeg_eq_le_toNat (x : Int128) : x.isNeg = decide (2^127 ≤ x.n.toNat) := by
  rw [isNeg]
  simp only [UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63, UInt128.toNat_def, decide_eq_decide]
  have lo := x.n.lo.toNat_lt
  norm_num only at lo ⊢
  omega

/-!
### Conversion from other integer types
-/

@[coe] def of_lo (x : UInt64) : Int128 :=
  ⟨⟨x, 0⟩⟩

/-- `UInt64` coerces to `Int128` -/
instance : Coe UInt64 Int128 where
  coe := of_lo

/-- Wrap around conversion from `ℕ` -/
@[irreducible] def ofNat (x : ℕ) : Int128 :=
  ⟨.ofNat x⟩

/-- Wrap around conversion from `ℤ` -/
@[irreducible] def ofInt (x : ℤ) : Int128 :=
  ⟨.ofInt x⟩

lemma n_ofInt (x : ℤ) : (Int128.ofInt x).n = .ofInt x := by
  rw [ofInt]

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

/-- `Int128 → ℤ → Int128` is the identity -/
@[simp] lemma ofInt_coe (x : Int128) : .ofInt (x : ℤ) = x := by
  rw [toInt]
  simp only [Int128.ext_iff, n_ofInt, bif_eq_if]
  split_ifs
  · rw [←UInt128.sub_ofInt, UInt128.ofInt_pow, sub_zero, UInt128.ofInt_toInt]
  · simp only [sub_zero, UInt128.ofInt_toInt]

/-- `ℤ → Int128 → ℤ` almost roundtrips -/
lemma coe_ofInt (x : ℤ) : (Int128.ofInt x : ℤ) = (x + 2^127) % 2^128 - 2^127 := by
  rw [ofInt, toInt, isNeg_eq_le_toNat]
  simp only [UInt128.toInt_ofInt, Bool.cond_decide, ←Nat.cast_le (α := ℤ), Nat.cast_pow,
    Nat.cast_ofNat]
  norm_num only
  split_ifs
  repeat omega

/-- `ofInt_coe` if we start with `UInt64` -/
@[simp] lemma ofInt_ofUInt64 (x : UInt64) : Int128.ofInt (x.toNat : ℤ) = x := by
  rw [Int128.ext_iff, ofInt, of_lo, UInt128.ofInt]
  simp only [Int.cast_ofNat, UInt64.cast_toNat, UInt128.mk.injEq, true_and, Int.cast_natCast]
  rw [Int.ediv_eq_zero_of_lt]
  · rfl
  · apply Nat.cast_nonneg
  · exact lt_of_lt_of_le (Nat.cast_lt.mpr x.toNat_lt) (by norm_num)

/-!
### Additive group operations: negation, addition, subtraction
-/

-- These are just the underlying `UInt128` operations
instance : Neg Int128 where neg x := ⟨-x.n⟩
instance : Add Int128 where add x y := ⟨x.n + y.n⟩
instance : Sub Int128 where sub x y := ⟨x.n - y.n⟩

-- Definition lemmas
lemma n_neg (x : Int128) : (-x).n = -x.n := rfl
lemma n_add (x y : Int128) : (x + y).n = x.n + y.n := rfl
lemma n_sub (x y : Int128) : (x - y).n = x.n - y.n := rfl

/-- `ofInt` commutes with `-` -/
@[simp] lemma neg_ofInt (x : ℤ) : .ofInt (-x) = -(Int128.ofInt x) := by
  simp only [Int128.ext_iff, n_neg, n_ofInt, UInt128.neg_ofInt]

/-- `ofInt` commutes with `+` -/
@[simp] lemma add_ofInt (x y : ℤ) : .ofInt (x + y) = .ofInt x + Int128.ofInt y := by
  simp only [Int128.ext_iff, n_add, n_ofInt, UInt128.add_ofInt]

/-- `ofInt` commutes with `-` -/
@[simp] lemma sub_ofInt (x y : ℤ) : .ofInt (x - y) = Int128.ofInt x - .ofInt y := by
  simp only [Int128.ext_iff, n_sub, n_ofInt, UInt128.sub_ofInt]

/-- `Int128` inherits the additive group structure from `UInt128` -/
instance : AddCommGroup Int128 where
  add_assoc x y z := by simp only [Int128.ext_iff, n_add, add_assoc]
  zero_add x := by simp only [Int128.ext_iff, n_add, zero_add, n_zero]
  add_zero x := by simp only [Int128.ext_iff, n_add, add_zero, n_zero]
  add_left_neg x := by simp only [Int128.ext_iff, n_add, n_neg, add_left_neg, n_zero]
  add_comm x y := by simp only [Int128.ext_iff, n_add, add_comm]
  zsmul := zsmulRec
  nsmul := nsmulRec

/-!
### `ℤ → Int128` is injective for small integers
-/

/-- Small integers roundtrip through `ℤ → Int128 → ℤ` -/
lemma coe_ofInt_of_abs_lt {x : ℤ} (sx : x ∈ Ico (-2^127) (2^127)) : (Int128.ofInt x : ℤ) = x := by
  simp only [coe_ofInt, abs_lt, mem_Ico] at sx ⊢
  norm_num only at sx ⊢
  omega

/-- Small integers are equal if their 128-bit wraps are equal -/
lemma eq_of_ofInt_eq {x y : ℤ} (e : Int128.ofInt x = .ofInt y)
    (sx : x ∈ Ico (-2^127) (2^127)) (sy : y ∈ Ico (-2^127) (2^127)) : x = y := by
  rw [←coe_ofInt_of_abs_lt sx, ←coe_ofInt_of_abs_lt sy, e]

/-- `coe` is small -/
lemma coe_small {x : Int128} : (x : ℤ) ∈ Ico (-2^127) (2^127) := by
  rw [toInt, bif_eq_if, mem_Ico]
  have h0 := x.n.toNat_lt
  split_ifs with h1
  all_goals {
    simp only [isNeg_eq_le_toNat, decide_eq_true_eq, not_le] at h1
    norm_num only at h0 h1 ⊢
    omega }
