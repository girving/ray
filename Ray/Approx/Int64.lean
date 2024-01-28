import Mathlib.Data.Real.Basic
import Ray.Approx.Bool
import Ray.Approx.Int
import Ray.Approx.UInt64

/-!
## 64-bit two's complement integers

Arithmetic wraps, so beware (not really, our uses are formally checked).
-/

open Set

/-- 64-bit two's complement integers -/
structure Int64 where
  n : UInt64
  deriving DecidableEq, BEq

/-- The sign bit of an `Int64` -/
@[pp_dot] def Int64.isNeg (x : Int64) : Bool := (1 <<< 63 : UInt64) ≤ x.n

def Int64.min : Int64 := ⟨1 <<< 63⟩

/-- The `ℤ` that an `Int64` represents -/
@[coe] def Int64.toInt (x : Int64) : ℤ :=
  (x.n.toNat : ℤ) - (((bif x.isNeg then 2^64 else 0) : ℕ) : ℤ)

/-- The `ℤ` that an `Int64` represents -/
instance : Coe Int64 ℤ where
  coe x := x.toInt

/-- The `ZMod (2^64)` that an `Int64` represents -/
noncomputable instance : Coe Int64 (ZMod (2^64)) where
  coe x := x.n.toNat

/-- Reduce `Int64` equality to `UInt64` equality -/
lemma Int64.ext_iff (x y : Int64) : x = y ↔ x.n = y.n := by
  induction' x with x; induction' y with y; simp only [mk.injEq]

/-- `Int64` has nice equality -/
instance : LawfulBEq Int64 where
  eq_of_beq {x y} e := by
    induction' x with x; induction' y with y
    simp only [BEq.beq] at e
    rw [eq_of_beq e]
  rfl {x} := beq_self_eq_true' x.n

-- Arithmetic that wraps
instance : Zero Int64 where zero := ⟨0⟩
instance : One Int64 where one := ⟨1⟩
instance : Neg Int64 where neg x := ⟨-x.n⟩
instance : Add Int64 where add x y := ⟨x.n + y.n⟩
instance : Sub Int64 where sub x y := ⟨x.n - y.n⟩
instance : Mul Int64 where mul x y := ⟨x.n * y.n⟩

-- Arithmetic definition lemmas
lemma Int64.zero_def : (0 : Int64) = ⟨0⟩ := rfl
lemma Int64.one_def : (1 : Int64) = ⟨1⟩ := rfl
lemma Int64.neg_def (x : Int64) : -x = ⟨-x.n⟩ := rfl
lemma Int64.add_def (x y : Int64) : x + y = ⟨x.n + y.n⟩ := rfl
lemma Int64.sub_def (x y : Int64) : x - y = ⟨x.n - y.n⟩ := rfl
lemma Int64.mul_def (x y : Int64) : x * y = ⟨x.n * y.n⟩ := rfl

-- Simplification lemmas
@[simp] lemma Int64.n_zero : (0 : Int64).n = 0 := rfl
@[simp] lemma Int64.isNeg_zero : (0 : Int64).isNeg = false := rfl
@[simp] lemma Int64.n_min : Int64.min.n = 2^63 := rfl
@[simp] lemma Int64.toNat_min : Int64.min.n.toNat = 2^63 := rfl
@[simp] lemma Int64.isNeg_min : Int64.min.isNeg = true := rfl
@[simp] lemma Int64.neg_min : -Int64.min = .min := rfl

/-- Fast conversion from `ℕ` -/
instance : NatCast Int64 where
  natCast n := ⟨(n : UInt64)⟩

/-- Fast conversion from `ℤ` -/
instance : IntCast Int64 where
  intCast n := ⟨(n : UInt64)⟩

/-- `Int64` is a commutative ring.
    We don't use `CommRing.ofMinimalAxioms, since we want our own `Sub` instance. -/
instance : CommRing Int64 where
  add_zero x := by simp only [Int64.add_def, Int64.zero_def, add_zero]
  zero_add x := by simp only [Int64.add_def, Int64.zero_def, zero_add]
  add_comm x y := by simp only [Int64.add_def, add_comm]
  add_assoc x y z := by simp only [Int64.add_def, add_assoc]
  add_left_neg x := by simp only [Int64.neg_def, Int64.add_def, add_left_neg, Int64.zero_def]
  mul_assoc x y z := by simp only [Int64.mul_def, mul_assoc]
  mul_comm x y := by simp only [Int64.mul_def, mul_comm]
  zero_mul x := by simp only [Int64.mul_def, Int64.zero_def, zero_mul]
  mul_zero x := by simp only [Int64.mul_def, Int64.zero_def, mul_zero]
  one_mul x := by simp only [Int64.mul_def, Int64.one_def, one_mul]
  mul_one x := by simp only [Int64.mul_def, Int64.one_def, mul_one]
  left_distrib x y z := by simp only [Int64.add_def, Int64.mul_def, left_distrib]
  right_distrib x y z := by simp only [Int64.add_def, Int64.mul_def, right_distrib]
  sub_eq_add_neg x y := by simp only [Int64.sub_def, Int64.add_def, Int64.neg_def, sub_eq_add_neg]
  natCast_zero := rfl
  natCast_succ := by
    intro n
    simp only [NatCast.natCast, Nat.cast_add, Nat.cast_one, Int64.one_def, Int64.add_def]
  intCast_ofNat := by
    intro n
    simp only [IntCast.intCast, Int.cast_ofNat, Int64.ext_iff, UInt64.eq_iff_toNat_eq]
    rfl
  intCast_negSucc := by
    intro n
    simp only [IntCast.intCast, Int.cast_negSucc, Int64.ext_iff, UInt64.eq_iff_toNat_eq]
    rfl

/-- Strict bool comparison on `Int64` -/
def Int64.blt (x y : Int64) :=
  x.isNeg > y.isNeg || (x.isNeg == y.isNeg && x.n < y.n)

/-- Nonstrict bool comparison on `Int64` -/
def Int64.ble (x y : Int64) := !(y.blt x)

/-- Strict comparison on `Int64` -/
instance : LT Int64 where
  lt x y := x.blt y

/-- Weak comparison on `Int64` -/
instance : LE Int64 where
  le x y := ¬(y < x)

/-- The definition of `<` -/
lemma Int64.lt_def (x y : Int64) :
    (x < y) = (x.isNeg > y.isNeg ∨ (x.isNeg = y.isNeg ∧ x.n < y.n)) := by
  simp only [LT.lt, blt, gt_iff_lt, Bool.and_eq_true, Bool.not_eq_true', Bool.decide_and,
    Bool.decide_coe, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]

/-- The definition of `≤` -/
lemma Int64.le_def (x y : Int64) :
    (x ≤ y) = ¬(y < x) := rfl

/-- `Int64` < is decidable -/
instance decidableLT : @DecidableRel Int64 (· < ·)
  | a, b => by dsimp [LT.lt]; infer_instance

/-- `Int64` ≤ is decidable -/
instance decidableLE : @DecidableRel Int64 (· ≤ ·)
  | a, b => by dsimp [LE.le]; infer_instance

/-- `blt` in terms of `lt` -/
lemma Int64.blt_eq_decide_lt (x y : Int64) : x.blt y = decide (x < y) := by
  simp only [LT.lt, Bool.decide_coe]

/-- Negation preserves `min` -/
@[simp] lemma Int64.neg_eq_min {x : Int64} : (-x) = min ↔ x = min := by
  have i : ∀ {x : Int64}, x = min → (-x) = min := by
    intro x h; simp only [h, neg_def, n_min]; decide
  by_cases a : x = min
  · simp only [a, neg_min]
  · by_cases b : (-x) = min
    · rw [b, ←neg_neg x, i b]
    · simp only [a, b]

/-- `min ≠ 0` -/
@[simp] lemma Int64.min_ne_zero : Int64.min ≠ 0 := by decide

/-- `0 ≠ min` -/
@[simp] lemma Int64.zero_ne_min : 0 ≠ Int64.min := by decide

-- Consequences of the sign bit being true or false
lemma Int64.coe_of_nonneg {x : Int64} (h : x.isNeg = false) : (x : ℤ) = x.n.toNat := by
  simp only [h, cond_false, Nat.cast_zero, sub_zero, Int64.toInt]
lemma Int64.coe_of_neg {x : Int64} (h : x.isNeg) : (x : ℤ) = x.n.toNat - ((2^64 : ℕ) : ℤ) := by
  simp only [h, cond_true, Nat.cast_zero, sub_zero, Int64.toInt]

/-- `isNeg` in terms of `≤` over `ℕ` -/
lemma Int64.isNeg_eq_le (x : Int64) : x.isNeg = decide (2^63 ≤ x.n.toNat) := by
  have e : 1 <<< 63 % UInt64.size = 2^63 := by decide
  simp only [isNeg, UInt64.le_iff_toNat_le, UInt64.toNat_cast, decide_eq_decide, e]

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_lt_coe (x y : Int64) : (x : ℤ) < (y : ℤ) ↔ x < y := by
  by_cases xs : x.isNeg
  · by_cases ys : y.isNeg
    · simp only [toInt, UInt64.toNat, UInt64.val_val_eq_toNat, xs, cond_true, Nat.cast_pow,
        Nat.cast_ofNat, ys, sub_lt_sub_iff_right, Nat.cast_lt, UInt64.toNat_lt_toNat, lt_def,
        gt_iff_lt, lt_self_iff_false, true_and, false_or]
    · simp only [toInt, xs, cond_true, Nat.cast_pow, Nat.cast_ofNat, ys, cond_false,
        CharP.cast_eq_zero, sub_zero, lt_def, gt_iff_lt, Bool.false_lt_true, false_and, or_false,
        iff_true]
      refine lt_of_lt_of_le ?_ (Nat.cast_nonneg _)
      simp only [sub_neg, UInt64.cast_toNat_lt_2_pow_64]
  · by_cases ys : y.isNeg
    · simp only [toInt, xs, cond_false, CharP.cast_eq_zero, sub_zero, ys, cond_true, Nat.cast_pow,
        Nat.cast_ofNat, lt_def, gt_iff_lt, Bool.lt_iff, and_self, false_and, or_self, iff_false,
        not_lt, tsub_le_iff_right]
      refine (lt_of_lt_of_le (UInt64.cast_toNat_lt_2_pow_64 _) ?_).le
      simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
    · simp only [toInt, UInt64.toNat, UInt64.val_val_eq_toNat, xs, cond_false, CharP.cast_eq_zero,
        sub_zero, ys, Nat.cast_lt, UInt64.toNat_lt_toNat, lt_def, gt_iff_lt, lt_self_iff_false,
        true_and, false_or]

/-- Converting to `ℤ` is under `2^63` -/
@[simp] lemma Int64.coe_lt_pow (x : Int64) : (x : ℤ) < 2^63 := by
  have h := UInt64.toNat_lt_2_pow_64 x.n
  simp only [toInt, bif_eq_if, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, CharP.cast_eq_zero]
  split_ifs with h0
  · linarith
  · simp only [isNeg_eq_le, decide_eq_true_eq, not_le] at h0
    simp only [sub_zero]; omega

/-- Converting to `ℤ` is at least `-2^63` -/
@[simp] lemma Int64.pow_le_coe (x : Int64) : -2^63 ≤ (x : ℤ) := by
  simp only [toInt, isNeg_eq_le, bif_eq_if, decide_eq_true_eq, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat, CharP.cast_eq_zero]
  split_ifs; repeat linarith

@[simp] lemma Int64.coe_min' : ((.min : Int64) : ℤ) = -(2:ℤ)^63 := rfl

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_le_coe (x y : Int64) : (x : ℤ) ≤ (y : ℤ) ↔ x ≤ y := by
  simp only [←not_lt, coe_lt_coe]; simp only [LE.le]

/-- We print `Int64`s as signed integers -/
instance : Repr Int64 where
  reprPrec x p := Repr.reprPrec (x : ℤ) p

/-- Approximate `Int64` by a `Float` -/
def Int64.toFloat (x : Int64) :=
  if x.isNeg then -(-x.n).toFloat else x.n.toFloat

-- An `Int64` is zero iff its inner `UInt64` is -/
lemma Int64.eq_zero_iff_n_eq_zero (x : Int64) : x = 0 ↔ x.n = 0 := by
  simp only [Int64.ext_iff, Int64.zero_def]

-- An `Int64` is not zero iff its inner `UInt64` is -/
lemma Int64.ne_zero_iff_n_ne_zero (x : Int64) : x ≠ 0 ↔ x.n ≠ 0 := by
  simp only [Ne.def, Int64.eq_zero_iff_n_eq_zero]

/-- Negation flips `.isNeg`, except at `0` and `.min` -/
lemma Int64.isNeg_neg {x : Int64} (x0 : x ≠ 0) (xn : x ≠ .min) : (-x).isNeg = !x.isNeg := by
  simp only [ne_eq, ext_iff, UInt64.eq_iff_toNat_eq, toNat_min, zero_def,
    UInt64.toNat_zero] at xn x0
  simp only [isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, neg_def,
    UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63, UInt64.toNat_neg, UInt64.eq_iff_toNat_eq,
    UInt64.toNat_zero, x0, ge_iff_le, ite_false, decide_eq_not_decide, not_le, decide_eq_true_eq]
  rw [Nat.le_sub_iff_add_le, add_comm, ←Nat.le_sub_iff_add_le]
  · simp only [UInt64.size, ge_iff_le]; norm_num
    exact Ne.le_iff_lt xn
  · norm_num
  · apply UInt64.le_size

-- Lemmas about `coe : Int64 → ℤ`
@[simp] lemma Int64.coe_zero : ((0 : Int64) : ℤ) = 0 := rfl
@[simp] lemma Int64.coe_one : ((1 : Int64) : ℤ) = 1 := rfl

/-- Equality is consistent with `ℤ` -/
@[simp] lemma Int64.coe_eq_coe (x y : Int64) : (x : ℤ) = (y : ℤ) ↔ x = y := by
  have e : 1 <<< 63 % UInt64.size = 2^63 := by rfl
  have n : (2:ℤ)^64 = ((2^64 : ℕ) : ℤ) := by rfl
  have xl : x.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
  have yl : y.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
  simp only [toInt, isNeg, UInt64.le_iff_toNat_le, UInt64.toNat_cast, e, Bool.cond_decide,
    Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat, CharP.cast_eq_zero, ext_iff, UInt64.eq_iff_toNat_eq]
  split_ifs
  · simp only [sub_left_inj, Nat.cast_inj]
  · simp only [sub_eq_iff_eq_add, sub_zero, n, ←Nat.cast_add, Nat.cast_inj]
    constructor; intro; omega; intro; omega
  · simp only [eq_sub_iff_add_eq, Nat.cast_inj, n, sub_zero, ←Nat.cast_add]
    constructor; intro; omega; intro; omega
  · simp only [sub_zero, Nat.cast_inj]

@[simp] lemma Int64.coe_eq_zero (x : Int64) : (x : ℤ) = 0 ↔ x = 0 := by
  rw [←coe_zero, coe_eq_coe]

/-- Converting to `ℤ` is more than `-2^63` if we're not `min` -/
@[simp] lemma Int64.pow_lt_coe {x : Int64} (n : x ≠ min) : -2^63 < (x : ℤ) := by
  refine Ne.lt_of_le ?_ (pow_le_coe x)
  rw [Ne.def, ←coe_min', coe_eq_coe]
  exact n.symm

/-!
### Conditions for `ℤ` conversion to commute with arithmetic
-/

/-- `Int64.neg` usually commutes with `ℤ` conversion -/
lemma Int64.coe_neg {x : Int64} (xn : x ≠ .min) : ((-x : Int64) : ℤ) = -x := by
  by_cases x0 : x = 0
  · simp only [x0, neg_zero, coe_zero]
  · have x0' : x.n ≠ 0 := by
      contrapose x0; simp only [ne_eq, not_not] at x0 ⊢; simp only [ext_iff, x0, n_zero]
    simp only [toInt, Int64.isNeg_neg x0 xn, Bool.cond_not, neg_sub]
    by_cases n : x.isNeg
    · simp only [neg_def, UInt64.toNat_neg, x0', ite_false, UInt64.le_size, Nat.cast_sub, n,
        cond_true, CharP.cast_eq_zero, sub_zero, Nat.cast_pow]
      rfl
    · simp only [neg_def, UInt64.toNat_neg, x0', ge_iff_le, ite_false, UInt64.le_size,
        Nat.cast_sub, n, cond_false, Nat.cast_pow, CharP.cast_eq_zero, zero_sub]
      simp only [UInt64.size_eq_pow, Nat.cast_pow, Nat.cast_ofNat, sub_sub_cancel_left]

/-- `ℤ` conversion commutes with add if `isNeg` matches the left argument -/
lemma Int64.coe_add_eq {x y : Int64} (h : (x + y).isNeg = x.isNeg) :
    ((x + y : Int64) : ℤ) = x + y := by
  simp only [Int64.isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
    decide_eq_decide, Int64.add_def] at h
  simp only [toInt, add_def, isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
    Bool.cond_eq_ite, decide_eq_true_eq, Nat.cast_ite, CharP.cast_eq_zero]
  by_cases xn : (2:UInt64)^63 ≤ x.n
  · simp only [xn, iff_true] at h
    by_cases yn : (2:UInt64)^63 ≤ y.n
    · simp only [h, ite_true, xn, yn, Int64.toInt]
      rw [UInt64.toNat_add_of_add_lt', UInt64.size]
      · ring
      · simp only [UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63] at xn yn
        have le : UInt64.size ≤ x.n.toNat + y.n.toNat := Nat.add_le_add xn yn
        simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add', not_lt.mpr le, ite_false, ge_iff_le,
          Nat.add_sub_lt_left (lt_of_lt_of_le (by norm_num) xn).ne', UInt64.lt_size]
    · simp only [h, ite_true, xn, yn, ite_false, sub_zero, Int64.toInt]
      rw [_root_.add_comm, UInt64.toNat_add_of_le_add]
      · simp only [Nat.cast_add]; ring
      · rw [_root_.add_comm] at h; exact le_trans (not_le.mp yn).le h
  · simp only [xn, iff_false, not_le] at h
    simp only [xn, not_le.mpr h, ite_false, sub_zero, Int64.toInt]
    by_cases yn : (2:UInt64)^63 ≤ y.n
    · simp only [yn, ite_true]
      rw [_root_.add_comm, UInt64.toNat_add_of_add_lt']
      · rw [_root_.add_comm] at h; simp only [UInt64.size, Nat.cast_ofNat]; ring
      · rw [_root_.add_comm]; exact lt_of_lt_of_le h yn
    · simp only [yn, ite_false, sub_zero]
      simp only [not_le, UInt64.lt_iff_toNat_lt, UInt64.toNat_2_pow_63] at xn yn
      have lt : x.n.toNat + y.n.toNat < UInt64.size :=
        lt_of_lt_of_le (Nat.add_lt_add xn yn) (by norm_num)
      simp only [UInt64.toNat_add', lt, ite_true, ge_iff_le, nonpos_iff_eq_zero, add_eq_zero,
        tsub_zero, Nat.cast_add]

/-- `ℤ` conversion commutes with add if `isNeg` matches the right argument -/
lemma Int64.coe_add_eq' {x y : Int64} (h : (x + y).isNeg = y.isNeg) :
    ((x + y : Int64) : ℤ) = x + y := by
  simp only [add_comm x, add_comm (x : ℤ)] at h ⊢; apply Int64.coe_add_eq h

/-- `ℤ` conversion commutes with add if the two arguments have different `isNeg`s -/
lemma Int64.coe_add_ne {x y : Int64} (h : x.isNeg ≠ y.isNeg) : ((x + y : Int64) : ℤ) = x + y := by
  have way : ∀ {x y : Int64}, x.isNeg → ¬y.isNeg → ((x + y : Int64) : ℤ) = x + y := by
    intro x y x0 y0
    simp only [Int64.isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
      decide_eq_true_eq, not_le] at x0 y0
    simp only [toInt, add_def, isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat,
      Bool.cond_eq_ite, decide_eq_true_eq, Nat.cast_ite, CharP.cast_eq_zero, x0, decide_True,
      ite_true, not_le.mpr y0, decide_False, ite_false, sub_zero]
    by_cases xy0 : (2:UInt64)^63 ≤ x.n + y.n
    · simp only [xy0, ite_true, Int64.toInt]
      rw [_root_.add_comm, UInt64.toNat_add_of_le_add, Nat.cast_add]
      · ring
      · rw [_root_.add_comm] at xy0
        exact le_trans y0.le xy0
    · simp only [xy0, ite_false, sub_zero, add_mul, mul_eq_mul_right_iff, or_false]
      rw [UInt64.toNat_add_of_add_lt']
      · simp only [UInt64.size_eq_pow, Nat.cast_add]; ring
      · exact lt_of_lt_of_le (not_le.mp xy0) x0
  by_cases x0 : x.isNeg
  · simp only [x0] at h; exact way x0 h.symm
  · simp only [x0] at h; rw [ne_comm, Ne.def, Bool.not_eq_false] at h
    rw [_root_.add_comm, _root_.add_comm (x : ℤ)]; exact way h x0

/-- `ℤ` conversion commutes with sub if the result is positive -/
lemma Int64.coe_sub_of_le_of_pos {x y : Int64} (yx : y ≤ x) (h : (x - y).isNeg = false) :
    ((x - y : Int64) : ℤ) = x - y := by
  simp only [sub_def, isNeg_eq_le, UInt64.toNat_sub', UInt64.size_eq_pow, decide_eq_false_iff_not,
    not_le, toInt, Int.ofNat_emod, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, bif_eq_if,
    decide_eq_true_eq, Nat.cast_ite, CharP.cast_eq_zero, Int64.le_def, Int64.lt_def,
    Bool.lt_iff, Bool.or_eq_true, decide_eq_decide, Bool.and_eq_true, beq_iff_eq, not_or,
    not_and_or, not_lt, UInt64.le_iff_toNat_le] at yx h ⊢
  have xs  : x.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
  have ys  : y.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
  generalize x.n.toNat = x at h xs yx
  generalize y.n.toNat = y at h ys yx
  have xc0 : 0 ≤ (x : ℤ) := by omega
  have yc0 : 0 ≤ (y : ℤ) := by omega
  have xcs : (x : ℤ) < 2^64 := by omega
  simp only [Nat.cast_sub ys.le, Nat.cast_pow, Nat.cast_ofNat]
  by_cases y0 : y = 0
  · simp only [y0, tsub_zero, Nat.cast_pow, Nat.cast_ofNat, Int.add_emod_self,
      Int.emod_eq_of_lt xc0 xcs, Nat.add_mod_right, xs, Nat.mod_eq_of_lt, CharP.cast_eq_zero,
      nonpos_iff_eq_zero, ite_false, sub_self, sub_zero]
  · by_cases c0 : x + (2 ^ 64 - y) < 2^64
    · have d0 : (x : ℤ) + (2^64 - y) < 2^64 := by omega
      have d1 : 0 ≤ (x : ℤ) + (2^64 - y) := by omega
      simp only [Nat.mod_eq_of_lt c0, Int.emod_eq_of_lt d1 d0] at h ⊢
      simp only [not_le.mpr h, ite_false, sub_zero]
      split_ifs with h0 h1 h2
      · omega
      · omega
      · omega
      · contrapose h; simp only [not_le, not_lt] at h2 ⊢
        exact le_trans (le_trans (by norm_num) (Nat.sub_le_sub_left h2.le _)) (Nat.le_add_left _ _)
    · simp only [not_lt] at c0
      have yx' : y ≤ x := by omega
      have e0 : x + (2 ^ 64 - y) - 2 ^ 64 = x - y := by
        rw [←Nat.add_sub_assoc ys.le, Nat.sub_right_comm, Nat.add_sub_assoc (le_refl _),
          Nat.sub_self,  Nat.add_zero]
      have e1 : (x + (2 ^ 64 - y)) % 2 ^ 64 = x - y := by
        rw [Nat.mod_eq]
        simp only [gt_iff_lt, zero_lt_two, pow_pos, c0, and_self, ite_true, e0,
          Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) xs)]
      have d0 : (x : ℤ) - y < 2^64 := by linarith
      have d1 : 0 ≤ (x : ℤ) - y := by linarith
      have d2 : (x : ℤ) + (2 ^ 64 - ↑y) = 2^64 + (x - y) := by ring
      have d3 : ((x : ℤ) + (2 ^ 64 - ↑y)) % 2 ^ 64 = ↑x - ↑y := by
        simp only [d2, Int.add_emod, Int.emod_self, zero_add, Int.emod_eq_of_lt d1 d0]
      simp only [e1] at h
      simp only [e1, not_le.mpr h, if_false, sub_zero, d3]
      split_ifs with h0 h1 h2
      · ring
      · simp only [h1, not_lt.mpr h0, or_self, h0, iff_false, not_true_eq_false, not_false_eq_true,
          true_or, and_true] at yx
      · linarith
      · ring

/-- Conversion to `ℤ` is the same as via `ℕ` if we're nonnegative -/
lemma Int64.toReal_toInt {x : Int64} (h : x.isNeg = false) : ((x : ℤ) : ℝ) = x.n.toNat := by
  simp only [toInt, h, cond_false, CharP.cast_eq_zero, sub_zero, Int.cast_ofNat]

/-- Conversion from `ℕ` is secretly the same as conversion to `UInt64` -/
@[simp] lemma Int64.ofNat_eq_coe (n : ℕ) : (n : Int64).n = n := by
  induction' n with n h
  · simp only [Nat.zero_eq, Nat.cast_zero, n_zero]
  · simp only [Nat.cast_succ, Int64.add_def, h]; rfl

/-- Conversion `ℕ → Int64 → ℤ` is the same as direct if we're small -/
lemma Int64.toInt_ofNat {n : ℕ} (h : n < 2^63) : ((n : Int64) : ℤ) = n := by
  have e : 1 <<< 63 % UInt64.size = 2^63 := by decide
  have lt : n < UInt64.size := lt_of_lt_of_le h (by norm_num)
  simp only [toInt, ofNat_eq_coe, UInt64.toNat_cast, Int.ofNat_emod, isNeg, if_false, sub_zero,
    UInt64.le_iff_toNat_le, e, bif_eq_if, decide_eq_true_eq, Nat.mod_eq_of_lt lt, not_le.mpr h,
    Int.ofNat_zero]

/-- Conversion `ℤ → Int64 → ℤ` is the same as direct if we're small -/
lemma Int64.toInt_ofInt {n : ℤ} (h : |n| < 2^63) : ((n : Int64) : ℤ) = n := by
  by_cases n0 : 0 ≤ n
  · have e : n = n.toNat := (Int.toNat_of_nonneg n0).symm
    rw [e] at h ⊢
    simp only [Nat.abs_cast] at h
    exact Int64.toInt_ofNat (by omega)
  · have e : n = -(-n).toNat := by rw [Int.toNat_of_nonneg (by omega), neg_neg]
    rw [e] at h ⊢
    simp only [abs_neg, Nat.abs_cast] at h
    simp only [Int.cast_neg, Int.cast_ofNat]
    rw [Int64.coe_neg]
    · simp only [neg_inj]; apply Int64.toInt_ofNat; omega
    · have e : (2 ^ 63 : ℤ) = (2 ^ 63 : ℕ) := by rfl
      rw [e, Nat.cast_lt] at h
      have cm : (min : ℤ) = -(2:ℤ)^63 := by rfl
      rw [Ne.def, ←Int64.coe_eq_coe, Int64.toInt_ofNat h, cm]
      omega

/-- Conversion to `ℤ` is the same as the underlying `toNat` if `isNeg = false` -/
lemma Int64.toInt_of_isNeg_eq_false {x : Int64} (h : x.isNeg = false) : (x : ℤ) = ↑x.n.toNat := by
  simp only [toInt, h, cond_false, CharP.cast_eq_zero, sub_zero]

/-- Conversion to `ℤ` is the same as the underlying `toNat` if we're small -/
lemma Int64.toInt_eq_toNat_of_lt {x : Int64} (h : x.n.toNat < 2^63) : (x : ℤ) = ↑x.n.toNat := by
  rw [Int64.toInt_of_isNeg_eq_false]
  simpa only [isNeg_eq_le, decide_eq_false_iff_not, not_le]

/-- `UInt64.log2` converts to `ℤ` as `toNat` -/
@[simp] lemma Int64.coe_log2 (n : UInt64) : ((⟨n.log2⟩ : Int64) : ℤ) = n.log2.toNat := by
  rw [Int64.toInt_eq_toNat_of_lt]
  simp only [UInt64.toNat_log2]
  exact lt_trans (UInt64.log2_lt_64 _) (by norm_num)

/-!
### Order lemmas
-/

/-- `Int64` `min` (must be defined before `LinearOrder`) -/
instance : Min Int64 where
  min x y := bif x.blt y then x else y

/-- `Int64` `max` (must be defined before `LinearOrder`) -/
instance : Max Int64 where
  max x y := bif x.blt y then y else x

/-- `Int64` is a linear order (though not an ordered algebraic structure) -/
instance : LinearOrder Int64 where
  le_refl x := by simp only [←Int64.coe_le_coe, le_refl]
  le_trans x y z := by simp only [←Int64.coe_le_coe]; apply le_trans
  le_antisymm x y := by
    simp only [←Int64.coe_le_coe, ←Int64.coe_eq_coe]; apply le_antisymm
  le_total x y := by simp only [←Int64.coe_le_coe]; apply le_total
  lt_iff_le_not_le x y := by
    simp only [←Int64.coe_lt_coe, ←Int64.coe_le_coe]; apply lt_iff_le_not_le
  decidableLE x y := by infer_instance
  min_def x y := by
    simp only [min, Int64.blt_eq_decide_lt, bif_eq_if, decide_eq_true_eq]
    split_ifs
    · rfl
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]
  max_def x y := by
    simp only [max, Int64.blt_eq_decide_lt, bif_eq_if, decide_eq_true_eq]
    split_ifs
    · rfl
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]; linarith
    · simp_all only [←Int64.coe_eq_coe, ←Int64.coe_lt_coe, ←Int64.coe_le_coe]

/-- `Int64.min` is the smallest element -/
@[simp] lemma Int64.min_le (x : Int64) : .min ≤ x := by
  have cm : (min : ℤ) = -(2:ℤ)^63 := by rfl
  have e : ((1 <<< 63 : ℕ) : UInt64).toNat = 2^63 := by rfl
  simp only [←Int64.coe_le_coe, cm]
  simp only [Int64.toInt, bif_eq_if, isNeg, UInt64.le_iff_toNat_le, e, decide_eq_true_eq]
  split_ifs with h
  · simp only [Nat.cast_pow, Nat.cast_ofNat, neg_le_sub_iff_le_add, ge_iff_le]
    have e : ((2^63 : ℕ) : ℤ) = (2:ℤ)^63 := by rfl
    have le : (2:ℤ) ^ 63 ≤ (x.n.toNat : ℤ) := by simpa only [←e, Nat.cast_le]
    exact le_trans (by norm_num) (add_le_add_right le _)
  · simp only [CharP.cast_eq_zero, sub_zero, ge_iff_le]
    exact le_trans (by norm_num) (Nat.cast_nonneg _)

/-- `Int64.min` is the smallest element -/
lemma Int64.eq_min_iff_min_lt (x : Int64) : x = .min ↔ x ≤ .min := by
  have h := min_le x
  constructor
  · intro h; simp only [h, le_refl]
  · intro h; apply le_antisymm; repeat assumption

lemma Int64.coe_nonneg {x : Int64} (h : x.isNeg = false) : 0 ≤ (x : ℤ) := by
  simp only [toInt, h, cond_false, CharP.cast_eq_zero, sub_zero, Nat.cast_nonneg]

lemma Int64.coe_nonpos_iff {x : Int64} : (x : ℤ) ≤ 0 ↔ x ≤ 0 := by
  rw [←Int64.coe_zero, coe_le_coe]

lemma Int64.coe_lt_zero {x : Int64} (h : x.isNeg) : (x : ℤ) < 0 := by
  simp only [toInt, h, cond_true, Nat.cast_pow, Nat.cast_ofNat, sub_neg,
    UInt64.cast_toNat_lt_2_pow_64]

lemma Int64.coe_lt_zero_iff {x : Int64} : (x : ℤ) < 0 ↔ x.isNeg := by
  constructor
  · intro h; contrapose h; simp only [Bool.not_eq_true, not_lt] at h ⊢; exact coe_nonneg h
  · exact coe_lt_zero

lemma Int64.coe_nonneg_iff {x : Int64} : 0 ≤ (x : ℤ) ↔ x.isNeg = false := by
  rw [←not_iff_not]; simp only [not_le, coe_lt_zero_iff, Bool.not_eq_false]

@[simp] lemma Int64.coe_pos_iff {x : Int64} : 0 < (x : ℤ) ↔ 0 < x := by
  have h := coe_lt_coe 0 x
  simpa only [coe_zero] using h

lemma Int64.isNeg_eq {x : Int64} : x.isNeg = decide (x < 0) := by
  by_cases n : x.isNeg
  · simp only [n, true_eq_decide_iff, ←coe_lt_coe, coe_zero, coe_lt_zero n]
  · simp only [n, false_eq_decide_iff, not_lt, ←coe_le_coe, coe_zero]
    simp only [Bool.not_eq_true] at n
    exact coe_nonneg n

@[simp] lemma Int64.natAbs_lt_pow_iff {x : Int64} : (x : ℤ).natAbs < 2^63 ↔ x ≠ min := by
  rw [←not_iff_not, not_not, not_lt]
  constructor
  · intro h
    rw [Int64.toInt] at h
    by_cases n : x.isNeg
    · simp only [n, cond_true, Nat.cast_pow, Nat.cast_ofNat] at h
      simp only [isNeg_eq_le, decide_eq_true_eq] at n
      have e : (x.n.toNat : ℤ) - 2 ^ 64 = -(2^64 - x.n.toNat : ℕ) := by norm_num
      simp only [e, Int.natAbs_neg, Int.natAbs_ofNat] at h
      simp only [ext_iff, n_min, UInt64.eq_iff_toNat_eq, UInt64.toNat_2_pow_63]
      linarith
    · simp only [Bool.not_eq_true] at n
      simp only [n, cond_false, CharP.cast_eq_zero, sub_zero, Int.natAbs_ofNat] at h
      simp only [isNeg_eq_le, decide_eq_false_iff_not, not_le] at n
      linarith
  · intro e; rw [e]; decide

/-- A sufficient condition for subtraction to decrease the value -/
lemma Int64.sub_le {x y : Int64} (y0 : y.isNeg = false) (h : min + y ≤ x) : x - y ≤ x := by
  simp only [isNeg_eq_le, decide_eq_false_iff_not, not_le, add_def, n_min, le_def, lt_def,
    UInt64.toNat_add, UInt64.toNat_2_pow_63, UInt64.size_eq_pow, gt_iff_lt, Bool.lt_iff,
    decide_eq_true_eq, Bool.decide_and, UInt64.lt_iff_toNat_lt, Bool.or_eq_true, Bool.and_eq_true,
    beq_iff_eq, decide_eq_decide, sub_def, UInt64.toNat_sub'] at y0 h ⊢
  have xs : x.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
  have ys : y.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
  generalize x.n.toNat = a at h xs
  generalize y.n.toNat = b at h ys y0
  clear x y
  have b0 : 2^63 + b < 2^64 := by linarith
  simp only [b0, Nat.mod_eq_of_lt, add_lt_iff_neg_left, not_lt_zero', false_and,
    le_add_iff_nonneg_right, zero_le, iff_true, false_or, not_and, not_lt] at h
  by_cases a3 : a < 2^63
  · simp only [not_le.mpr a3, and_false, false_iff, not_le, false_or, not_and, not_lt]
    by_cases ab : a < b
    · have e0 : (a + (2^64 - b)) = 2^64 - (b - a) := by omega
      have e1 : 2^64 - (b - a) < 2^64 := by omega
      simp only [e0, e1, Nat.mod_eq_of_lt, tsub_le_iff_right]
      omega
    · have e0 : a + (2^64 - b) = a - b + 2^64 := by omega
      have e1 : a - b < 2^64 := by omega
      simp only [e0, Nat.add_mod_right, Nat.mod_eq_of_lt e1, tsub_le_iff_right,
        le_add_iff_nonneg_right, zero_le, implies_true]
  · simp only [not_lt] at a3
    simp only [a3, forall_true_left] at h
    have e : a + (2^64 - b) = a - b + 2^64 := by omega
    have d0 : a - b < 2^64 := by omega
    have d1 : 2^63 ≤ a - b := by omega
    simp only [e, Nat.add_mod_right, d0, Nat.mod_eq_of_lt, not_lt.mpr d1, false_and, false_or,
      not_and, not_lt, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le, implies_true]

/-!
### Order operations: min, abs
-/

/-- Almost absolute value (maps `Int64.min → Int64.min`) -/
@[pp_dot] def Int64.abs (x : Int64) : UInt64 :=
  bif x.isNeg then -x.n else x.n

@[simp] lemma Int64.abs_zero : (0 : Int64).abs = 0 := rfl
@[simp] lemma Int64.abs_min : Int64.min.abs = Int64.min := rfl

/-- `abs` preserves 0 -/
@[simp] lemma Int64.abs_eq_zero_iff {x : Int64} : x.abs = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [Int64.abs] at h
    simp only [ext_iff, n_zero]
    generalize x.isNeg = b at h
    induction b
    · simpa only [cond_false] using h
    · simpa only [cond_true, neg_eq_zero] using h
  · intro h; simp only [h, abs_zero]

/-- `abs` preserves 0 -/
@[simp] lemma Int64.abs_ne_zero_iff {x : Int64} : x.abs ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne.def, Int64.abs_eq_zero_iff]

/-- `.abs` doesn't change if nonneg -/
lemma Int64.abs_eq_self {x : Int64} (h : x.isNeg = false) : x.abs.toInt = x := by
  simp only [abs, h, cond_false, toInt, CharP.cast_eq_zero, sub_zero]; rfl

/-- `.abs` negates if negative -/
lemma Int64.abs_eq_neg {x : Int64} (n : x.isNeg) : x.abs.toInt = -x := by
  simp only [UInt64.toInt, abs, n, UInt64.neg_def, Fin.neg, ge_iff_le, cond_true, toInt,
    Nat.cast_pow, Nat.cast_ofNat, neg_sub]
  trans ↑((UInt64.size - ↑x.n.val) % UInt64.size)
  · rfl
  · simp only [UInt64.size_eq_pow, ge_iff_le, Int.ofNat_emod, Fin.is_le', Nat.cast_sub,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [Int.emod_eq_of_lt]
    · rfl
    · simp only [sub_nonneg]
      trans ((2^64 : ℕ) : ℤ)
      · simp only [Nat.cast_le, Fin.is_le']
      · rfl
    · simp only [sub_lt_self_iff, Nat.cast_pos, Nat.pos_iff_ne_zero, ne_eq]
      contrapose n
      simp only [not_not, Bool.not_eq_true] at n ⊢
      have e : (x.n.val : ℕ) = x.n.toNat := rfl
      simp only [e] at n
      have x0 : x = 0 := by simp only [Int64.ext_iff, UInt64.eq_iff_toNat_eq, n]; rfl
      simp only [x0]
      rfl

/-- `.min` commutes  with `coe` -/
lemma Int64.coe_min {x y : Int64} : (Min.min (α := Int64) x y : ℤ) = Min.min (x : ℤ) y := by
  simp only [LinearOrder.min_def, coe_le_coe]
  by_cases xy : x ≤ y
  · simp only [xy, ite_true]
  · simp only [xy, ite_false]

/-- `.max` commutes  with `coe` -/
lemma Int64.coe_max {x y : Int64} : (Max.max (α := Int64) x y : ℤ) = Max.max (x : ℤ) y := by
  simp only [LinearOrder.max_def, coe_le_coe]
  by_cases xy : x ≤ y
  · simp only [xy, ite_true]
  · simp only [xy, ite_false]

/-- `.abs` is absolute value (`ℤ` version) -/
lemma Int64.coe_abs {x : Int64} : x.abs.toInt = |(x : ℤ)| := by
  by_cases n : x.isNeg
  · simp only [abs_eq_neg n, abs_of_neg (coe_lt_zero n)]
  · simp only [Bool.not_eq_true] at n
    simp only [UInt64.toInt, abs, n, cond_false, toInt, CharP.cast_eq_zero, sub_zero, Nat.abs_cast]

/-- `.abs` is absolute value (`ℕ` version) )-/
lemma Int64.toNat_abs {x : Int64} : x.abs.toNat = (x : ℤ).natAbs := by
  rw [←Nat.cast_inj (R := ℤ), Int.coe_natAbs]; exact coe_abs

/-- If we turn `abs` back into an `Int64`, it's abs except at `.min` -/
lemma Int64.coe_abs' {x : Int64} (n : x ≠ .min) : ((⟨x.abs⟩ : Int64) : ℤ) = |(x : ℤ)| := by
  by_cases x0 : x = 0
  · simp only [x0, coe_zero, abs_zero]; rfl
  have x0' : x.n ≠ 0 := by simpa only [ext_iff, n_zero] using x0
  by_cases xn : x.isNeg
  · simp only [abs, xn, cond_true, ← neg_def, toInt._eq_1, isNeg_neg x0 n, Bool.not_true, ←
      UInt64.size_eq_pow, cond_false, sub_zero, Nat.cast_zero]
    rw [abs_of_neg, neg_sub]
    · simp only [neg_def, UInt64.toNat_neg, x0', if_false]
      rw [Nat.cast_sub]
      exact UInt64.le_size _
    · simp only [sub_neg, Nat.cast_lt, UInt64.lt_size]
  · have xn' : (⟨x.n⟩ : Int64).isNeg ≠ true := xn
    simp only [toInt, abs, xn, cond_false, xn', CharP.cast_eq_zero, sub_zero, Nat.abs_cast]

/-- If we turn `abs` back into an `Int64`, it's negative only at `.min` -/
lemma Int64.abs_lt_zero {x : Int64} : ((⟨x.abs⟩ : Int64) : ℤ) < 0 ↔ x = .min := by
  by_cases e : x = .min
  · simp only [e, abs_min]; decide
  · simp only [coe_abs' e, e, iff_false, not_lt, abs_nonneg]

/-- `(-x).abs = x.abs` away from `min` -/
@[simp] lemma Int64.abs_neg {x : Int64} (n : x ≠ min) : (-x).abs = x.abs := by
  by_cases z : x = 0
  · simp only [z, neg_zero, abs_zero]
  rw [Int64.abs, Int64.abs]
  simp only [isNeg_neg z n, bif_eq_if, Bool.not_eq_true']
  simp only [neg_def, neg_neg]
  by_cases h : x.isNeg
  repeat simp only [h, ite_false, ite_true]

/-- `(-t).n.toNat = t` when converting negatives to `ℤ` -/
@[simp] lemma Int64.toNat_neg {x : Int64} (n : x.isNeg) : ((-x).n.toNat : ℤ) = -x := by
  by_cases x0 : x = 0
  · simp only [x0, isNeg_zero] at n
  · simp only [ext_iff, n_zero] at x0
    simp only [neg_def, UInt64.toNat_neg, x0, UInt64.size_eq_pow, ite_false,
      Nat.cast_sub (UInt64.toNat_lt_2_pow_64 _).le, Nat.cast_pow, Nat.cast_ofNat, neg_sub,
      toInt._eq_1, n, cond_true]

/-!
### Left and right shift
-/

/-- Shifting left is shifting the inner `UInt64` left -/
instance : HShiftLeft Int64 UInt64 Int64 where
  hShiftLeft x s := ⟨x.n <<< s⟩

lemma Int64.shiftLeft_def (x : Int64) (s : UInt64) : x <<< s = ⟨x.n <<< s⟩ := rfl

/-- Shifting left is multiplying by a power of two, in nice cases -/
lemma Int64.coe_shiftLeft {x : Int64} {s : UInt64} (s64 : s.toNat < 64)
    (xs : x.abs.toNat < 2 ^ (63 - s.toNat)) : ((x <<< s) : ℤ) = x * 2^s.toNat := by
  have e : ((1 <<< 63 : ℕ) : UInt64).toNat = 2^63 := by rfl
  simp only [Int64.shiftLeft_def, Int64.toInt, bif_eq_if, isNeg, UInt64.le_iff_toNat_le, e,
    UInt64.toNat_shiftLeft', Nat.mod_eq_of_lt s64, Int64.abs] at xs ⊢
  by_cases x0 : x.n = 0
  · simp only [x0, UInt64.toNat_zero, Nat.zero_mod, zero_mul, CharP.cast_eq_zero,
      nonpos_iff_eq_zero, decide_False, ite_false, sub_self]
  by_cases le : 2 ^ 63 ≤ x.n.toNat
  · generalize hy : 2^64 - x.n.toNat = y at xs
    have xy : x.n.toNat = 2^64 - y := by rw [←hy]; have h := x.n.toNat_lt_2_pow_64; omega
    simp only [le, decide_True, if_true, UInt64.toNat_neg, x0, UInt64.size_eq_pow, hy,
      ite_false] at xs
    have y0 : 0 < y := by have h := x.n.toNat_lt_2_pow_64; omega
    have xm : x.n.toNat % 2 ^ (64 - s.toNat) = 2 ^ (64 - s.toNat) - y := by
      have e : 2^64 - y = (2^(64 - s.toNat) * (2^s.toNat - 1) + (2^(64 - s.toNat) - y)) := by
        simp only [mul_tsub, ← pow_add, Nat.sub_add_cancel s64.le, mul_one]
        have h0 : 2^(64 - s.toNat) ≤ 2^64 := pow_le_pow_right (by norm_num) (by omega)
        have h1 : y ≤ 2 ^ (64 - s.toNat) :=
          le_trans xs.le (pow_le_pow_right (by norm_num) (by omega))
        omega
      rw [xy, e, Nat.mul_add_mod, Nat.mod_eq_of_lt]
      exact Nat.sub_lt (by positivity) y0
    have y63 : y * 2 ^ s.toNat ≤ 2^63 := by
      refine le_trans (Nat.mul_le_mul_right _ xs.le) ?_
      rw [←pow_add]
      have le : 63 - s.toNat + s.toNat ≤ 63 := by omega
      exact le_trans (pow_le_pow_right (by norm_num) le) (by norm_num)
    have yle : 2 ^ 63 ≤ 2 ^ 64 - y * 2 ^ s.toNat := by
      apply Nat.le_sub_of_add_le
      rw [add_comm, ←Nat.le_sub_iff_add_le (by norm_num)]
      exact y63
    simp only [le, xm, decide_true_eq_true, if_true, tsub_mul, ←pow_add,
      Nat.sub_add_cancel s64.le]
    simp only [yle, decide_True, ite_true, Nat.cast_pow, Nat.cast_ofNat, xy]
    rw [Nat.cast_sub, Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, sub_sub_cancel_left, neg_mul]
    · rw [←hy]; omega
    · exact le_trans y63 (by norm_num)
  · simp only [le, decide_False, ite_false] at xs
    have lt : x.n.toNat < 2 ^ (64 - s.toNat) :=
      lt_of_lt_of_le xs (Nat.pow_le_pow_of_le_right (by norm_num) (by omega))
    simp only [Nat.mod_eq_of_lt lt, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, decide_eq_true_eq,
      Nat.cast_ite, CharP.cast_eq_zero, le, decide_False, ite_false, sub_zero, sub_eq_self,
      ite_eq_right_iff, Nat.zero_lt_succ, pow_eq_zero_iff, OfNat.ofNat_ne_zero, imp_false, not_le]
    refine lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right xs (pow_pos (by norm_num) _)) ?_
    simp only [← pow_add]
    exact pow_le_pow_right (by norm_num) (by omega)

/-- `0 <<< s = 0` -/
@[simp] lemma Int64.zero_shiftLeft (s : UInt64) : (0 : Int64) <<< s = 0 := by
  simp only [shiftLeft_def, n_zero, UInt64.zero_shiftLeft]; rfl

/-!
### Right shift, rounding up or down
-/

/-- Shift right, rounding up or down -/
@[irreducible] def Int64.shiftRightRound (x : Int64) (s : UInt64) (up : Bool) : Int64 :=
  bif x.isNeg then
    -- We need arithmetic shifting, which is easiest to do by taking bitwise complement.
    -- However, this fails if `x = min`, so we handle that case separately.
    bif x == min then
      bif 64 ≤ s then bif up then 0 else -1
      else -⟨1 <<< (63 - s)⟩
    else
      -⟨(-x).n.shiftRightRound s !up⟩
  else
    ⟨x.n.shiftRightRound s up⟩

/-- `0.shiftRightRound = 0` -/
@[simp] lemma Int64.zero_shiftRightRound (s : UInt64) (up : Bool) :
    (0 : Int64).shiftRightRound s up = 0 := by
  rw [shiftRightRound]
  simp only [isNeg_zero, Bool.cond_decide, neg_zero, n_zero, UInt64.zero_shiftRightRound,
    cond_false, ext_iff]

/-- `Int64.isNeg` for powers of two -/
lemma Int64.isNeg_one_shift {s : UInt64} (s64 : s.toNat < 64) :
    (⟨1 <<< s⟩ : Int64).isNeg = decide (s.toNat = 63) := by
  simp only [isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, UInt64.le_iff_toNat_le,
    UInt64.toNat_2_pow_63, UInt64.toNat_shiftLeft', UInt64.toNat_one, Nat.mod_eq_of_lt s64,
    decide_eq_decide]
  rw [Nat.mod_eq_of_lt, one_mul, pow_le_pow_iff_right (by omega)]
  · constructor; intro; omega; intro; omega
  · exact one_lt_pow (by norm_num) (by omega)

/-- `ℤ` conversion for `UInt64` powers of two -/
lemma Int64.coe_one_shift {s : UInt64} (s63 : s.toNat < 63) :
    ((⟨1 <<< s⟩ : Int64) : ℤ) = 2^s.toNat := by
  have s64 : s.toNat < 64 := by omega
  have e : (1 <<< s : UInt64).toNat = 2^s.toNat := by
    simp only [UInt64.toNat_shiftLeft', UInt64.toNat_one, Nat.mod_eq_of_lt s64, ne_eq,
      pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_eq_right₀]
    exact Nat.mod_eq_of_lt (one_lt_pow (by norm_num) (by omega))
  simp only [toInt, e, Nat.cast_pow, Nat.cast_ofNat, isNeg_one_shift s64, s63.ne, decide_False,
    bif_eq_if, ite_false, CharP.cast_eq_zero, sub_zero]

/-- `ℤ` conversion for negated `Int64` powers of two -/
lemma Int64.coe_neg_one_shift {s : UInt64} (s63 : s.toNat < 63) :
    ((-⟨1 <<< s⟩ : Int64) : ℤ) = -2^s.toNat := by
  rw [Int64.coe_neg, Int64.coe_one_shift s63]
  have s64 : s.toNat < 64 := by omega
  simp only [ne_eq, ext_iff, n_min, UInt64.eq_iff_toNat_eq, UInt64.toNat_shiftLeft',
    UInt64.toNat_one, Nat.mod_eq_of_lt s64, UInt64.toNat_2_pow_63]
  rw [Nat.mod_eq_of_lt]
  · simp only [one_mul, gt_iff_lt, zero_lt_two, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
      pow_right_inj, s63.ne]
  · exact one_lt_pow (by norm_num) (by omega)

/-- Negated `ℤ` conversion for `UInt64` values -/
lemma Int64.coe_eq_toNat_of_lt {n : UInt64} (h : n.toNat < 2^63) :
    ((⟨n⟩ : Int64) : ℤ) = n.toNat := by
  simp only [toInt, neg_def, UInt64.toNat_neg, UInt64.size_eq_pow, Nat.cast_ite, CharP.cast_eq_zero,
    isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, UInt64.le_iff_toNat_le,
    UInt64.toNat_2_pow_63, bif_eq_if, decide_eq_true_eq]
  split_ifs with h0
  · omega
  · simp only [sub_zero]

/-- Negated `ℤ` conversion for `UInt64` values -/
lemma Int64.coe_neg_eq_neg_toNat_of_lt {n : UInt64} (h : n.toNat < 2^63) :
    ((-⟨n⟩ : Int64) : ℤ) = -n.toNat := by
  simp only [toInt, neg_def, UInt64.toNat_neg, UInt64.size_eq_pow, Nat.cast_ite, CharP.cast_eq_zero,
    isNeg, Nat.shiftLeft_eq, one_mul, Nat.cast_pow, Nat.cast_ofNat, UInt64.le_iff_toNat_le,
    UInt64.toNat_2_pow_63, bif_eq_if, decide_eq_true_eq]
  split_ifs with h0 h1 h2
  · omega
  · simp only [sub_self, h0, UInt64.toNat_zero, CharP.cast_eq_zero, neg_zero]
  · omega
  · contrapose h2
    simp only [not_le, not_lt]
    exact le_trans (by norm_num) (Nat.sub_le_sub_left h.le _)

/-- `Int64.shiftRightRound` rounds correctly -/
lemma Int64.coe_shiftRightRound (x : Int64) (s : UInt64) (up : Bool) :
    (x.shiftRightRound s up : ℤ) = (x : ℤ).rdiv (2^s.toNat) up := by
  rw [shiftRightRound, Int.rdiv]
  have t0 : (2 : ℤ) ≠ 0 := by decide
  have e1 : ((-1 : Int64) : ℤ) = -1 := rfl
  have e63 : (63 : UInt64).toNat = 63 := rfl
  have e64 : (64 : UInt64).toNat = 64 := rfl
  simp only [bif_eq_if, decide_eq_true_eq, beq_iff_eq, ← coe_lt_zero_iff,
    apply_ite (fun x : Int64 ↦ (x : ℤ)), coe_zero, e1, Nat.cast_pow, Nat.cast_ofNat]
  by_cases x0 : (x : ℤ) < 0
  · simp only [x0, ite_true]
    by_cases xm : x = .min
    · have me : ((.min : Int64) : ℤ) = -(2:ℤ)^63 := by decide
      simp only [xm, if_true, me]
      by_cases s64 : 64 ≤ s
      · simp only [s64, ite_true]
        simp only [UInt64.le_iff_toNat_le, e64] at s64
        induction up
        · simp only [ite_false, neg_neg, Nat.cast_pow, Nat.cast_ofNat, cond_false]
          rw [Int.ediv_eq_neg_one (by positivity)]
          exact pow_le_pow_right (by norm_num) (by omega)
        · simp only [ite_true, neg_neg, Nat.cast_pow, Nat.cast_ofNat, cond_true,
            zero_eq_neg]
          apply Int.ediv_eq_zero_of_lt (by positivity)
          exact pow_lt_pow_right (by norm_num) (by omega)
      · simp only [s64, ite_false, neg_neg]
        simp only [UInt64.le_iff_toNat_le, e64, not_le] at s64
        have s63 : s.toNat ≤ 63 := by omega
        have es : (63 - s).toNat = 63 - s.toNat := by
          rw [UInt64.toNat_sub, e63]
          simp only [UInt64.le_iff_toNat_le, e63]; omega
        by_cases s0 : s = 0
        · simp only [s0, sub_zero, UInt64.toNat_zero, pow_zero, Int.ediv_one, ite_self]; decide
        · simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_zero] at s0
          rw [Int64.coe_neg_one_shift, es]
          · simp only [Int.ediv_pow_of_le t0 s63, Int.neg_ediv_pow_of_le t0 s63, ite_self]
          · rw [es]; omega
    · simp only [xm, ite_false]
      have xnn : (-x).isNeg = false := by
        rw [isNeg_eq, decide_eq_false]
        rw [←Int64.coe_lt_coe, coe_zero, coe_neg xm]
        linarith
      have ult : ((-x).n.shiftRightRound s !up).toNat < 2 ^ 63 := by
        rw [isNeg, decide_eq_false_iff_not, not_le, UInt64.lt_iff_toNat_lt] at xnn
        exact lt_of_le_of_lt UInt64.shiftRightRound_le_self xnn
      rw [coe_neg_eq_neg_toNat_of_lt ult, UInt64.toNat_shiftRightRound']
      induction up
      · simp only [Bool.not_false, ite_true, Int.cast_neg_ceilDiv_eq_ediv, Nat.cast_pow,
          Nat.cast_ofNat, ite_false]
        refine congr_arg₂ _ ?_ rfl
        rw [←coe_of_nonneg, coe_neg xm, neg_neg]
        simp only [xnn, not_false_eq_true]
      · simp only [Bool.not_true, ite_false, Int.ofNat_ediv, Nat.cast_pow, Nat.cast_ofNat,
          ite_true, neg_inj]
        rw [←coe_of_nonneg, coe_neg xm]
        simp only [xnn, not_false_eq_true]
  · simp only [x0, ite_false]
    have xn : (x).isNeg = false := by
      rw [isNeg_eq, decide_eq_false]
      rw [←Int64.coe_lt_coe, coe_zero]
      linarith
    have xsn : (⟨UInt64.shiftRightRound x.n s up⟩ : Int64).isNeg = false := by
      simp only [isNeg, decide_eq_false_iff_not, not_le, UInt64.lt_iff_toNat_lt,
        UInt64.toNat_cast] at xn ⊢
      exact lt_of_le_of_lt (UInt64.shiftRightRound_le_self) xn
    rw [coe_of_nonneg xsn, UInt64.toNat_shiftRightRound']
    induction up
    · simp only [ite_false, Int.ofNat_ediv, Nat.cast_pow, Nat.cast_ofNat, coe_of_nonneg xn]
    · simp only [ite_true, Int.cast_ceilDiv_eq_neg_ediv, Nat.cast_pow, Nat.cast_ofNat,
        coe_of_nonneg xn]

/-- `Int64.shiftRightRound` reduces `abs` -/
lemma Int64.abs_shiftRightRound_le (x : Int64) (s : UInt64) (up : Bool) :
    |(x.shiftRightRound s up : ℤ)| ≤ |(x : ℤ)| := by
  simp only [ne_eq, coe_shiftRightRound, Nat.cast_pow, Nat.cast_ofNat, Int.abs_rdiv_le]

/-- `Int64.shiftRightRound` never produces `min` from scratch -/
lemma Int64.shiftRightRound_ne_min {x : Int64} (n : x ≠ min) (s : UInt64) (up : Bool) :
    x.shiftRightRound s up ≠ min := by
  contrapose n
  simp only [ne_eq, not_not] at n ⊢
  have h := abs_shiftRightRound_le x s up
  simp only [n, coe_min', _root_.abs_neg, abs_pow, abs_two, le_abs] at h
  rcases h with h | h
  · linarith [coe_lt_pow x]
  · rw [←coe_eq_coe, coe_min']
    apply le_antisymm
    · linarith
    · exact pow_le_coe _
