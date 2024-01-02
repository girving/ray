import Mathlib.Data.Real.Basic
import Ray.Approx.Bool
import Ray.Approx.UInt64

/-!
## 64-bit two's complement integers

Arithmetic wraps, so beware (not really, our uses are formally checked).
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

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
  x.n.toNat - bif x.isNeg then 2^64 else 0

/-- The `ℤ` that an `Int64` represents -/
instance : Coe Int64 ℤ where
  coe x := x.toInt

/-- The `ZMod (2^64)` that an `Int64` represents -/
noncomputable instance : Coe Int64 (ZMod (2^64)) where
  coe x := x.n.toNat

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
    (x < y) = (x.isNeg > y.isNeg || (x.isNeg == y.isNeg && x.n < y.n)) := rfl

/-- `Int64` < is decidable -/
instance decidableLT : @DecidableRel Int64 (· < ·)
  | a, b => by dsimp [LT.lt]; infer_instance

/-- `Int64` ≤ is decidable -/
instance decidableLE : @DecidableRel Int64 (· ≤ ·)
  | a, b => by dsimp [LE.le]; infer_instance

/-- `blt` in terms of `lt` -/
lemma Int64.blt_eq_decide_lt (x y : Int64) : x.blt y = decide (x < y) := by
  simp only [LT.lt, Bool.decide_coe]

-- Consequences of the sign bit being true or false
lemma Int64.coe_of_nonneg {x : Int64} (h : ¬x.isNeg) : (x : ℤ) = x.n.toNat := by
  simp only [Bool.not_eq_true] at h; simp only [h, cond_false, Nat.cast_zero, sub_zero, Int64.toInt]
lemma Int64.coe_of_neg {x : Int64} (h : x.isNeg) : (x : ℤ) = x.n.toNat - 2^64 := by
  simp only [h, cond_true, Nat.cast_zero, sub_zero, Int64.toInt]

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_lt_coe (x y : Int64) : (x : ℤ) < (y : ℤ) ↔ x < y := by
  by_cases xs : x.isNeg
  · by_cases ys : y.isNeg
    · simp only [UInt64.toNat, xs, cond_true, Nat.cast_pow, Nat.cast_ofNat, ys,
        sub_lt_sub_iff_right, Nat.cast_lt, Fin.val_fin_lt, lt_def, lt_self_iff_false, decide_False,
        beq_self_eq_true, Bool.true_and, Bool.false_or, decide_eq_true_eq, Int64.toInt]
      apply Fin.val_fin_lt
    · simp only [toInt, xs, cond_true, Nat.cast_pow, Nat.cast_ofNat, ys, cond_false,
        CharP.cast_eq_zero, sub_zero, lt_def, gt_iff_lt, Bool.false_lt_true, decide_True,
        Bool.true_or, iff_true]
      refine lt_of_lt_of_le ?_ (Nat.cast_nonneg _)
      simp only [sub_neg, UInt64.cast_toNat_lt_2_pow_64]
  · by_cases ys : y.isNeg
    · simp only [toInt, xs, cond_false, CharP.cast_eq_zero, sub_zero, ys, cond_true, Nat.cast_pow,
        Nat.cast_ofNat, lt_def, gt_iff_lt, Bool.lt_iff, and_self, decide_False, Bool.false_or,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, false_and, iff_false, not_lt,
        tsub_le_iff_right]
      refine (lt_of_lt_of_le (UInt64.cast_toNat_lt_2_pow_64 _) ?_).le
      simp only [le_add_iff_nonneg_left, Nat.cast_nonneg]
    · simp only [UInt64.toNat, xs, cond_false, Nat.cast_zero, sub_zero, ys, Nat.cast_lt,
        Fin.val_fin_lt, lt_def, lt_self_iff_false, decide_False, beq_self_eq_true, Bool.true_and,
        Bool.false_or, decide_eq_true_eq, Int64.toInt]
      apply Fin.val_fin_lt

/-- The ordering is consistent with `ℤ` -/
@[simp] lemma Int64.coe_le_coe (x y : Int64) : (x : ℤ) ≤ (y : ℤ) ↔ x ≤ y := by
  simp only [←not_lt, coe_lt_coe]; simp only [LE.le]

/-- We print `Int64`s as signed integers -/
instance : Repr Int64 where
  reprPrec x p := Repr.reprPrec (x : ℤ) p

/-- Approximate `Int64` by a `Float` -/
def Int64.toFloat (x : Int64) :=
  if x.isNeg then -(-x.n).toFloat else x.n.toFloat

/-- Reduce `Int64` equality to `UInt64` equality -/
lemma Int64.ext_iff (x y : Int64) : x = y ↔ x.n = y.n := by
  induction' x with x; induction' y with y; simp only [mk.injEq]

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
  have e : 1 <<< 63 % UInt64.size = 2^63 := rfl
  have n : (2:ℤ)^64 = ((2^64 : ℕ) : ℤ) := rfl
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

/-- Conversion to `ℤ` is the same as via `ℕ` if we're nonnegative -/
lemma Int64.toReal_toInt {x : Int64} (h : x.isNeg = false) : ((x : ℤ) : ℝ) = x.n.toNat := by
  simp only [toInt, h, cond_false, CharP.cast_eq_zero, sub_zero, Int.cast_ofNat]

/-!
### Order lemmas
-/

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

/-- `Int64.min` is the smallest element -/
@[simp] lemma Int64.min_le (x : Int64) : .min ≤ x := by
  have cm : (min : ℤ) = -(2:ℤ)^63 := rfl
  have e : ((1 <<< 63 : ℕ) : UInt64).toNat = 2^63 := rfl
  simp only [←Int64.coe_le_coe, cm]
  simp only [Int64.toInt, bif_eq_if, isNeg, UInt64.le_iff_toNat_le, e, decide_eq_true_eq]
  split_ifs with h
  · simp only [Nat.cast_pow, Nat.cast_ofNat, neg_le_sub_iff_le_add, ge_iff_le]
    have e : ((2^63 : ℕ) : ℤ) = (2:ℤ)^63 := rfl
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

lemma Int64.coe_lt_zero {x : Int64} (h : x.isNeg) : (x : ℤ) < 0 := by
  simp only [toInt, h, cond_true, Nat.cast_pow, Nat.cast_ofNat, sub_neg,
    UInt64.cast_toNat_lt_2_pow_64]

lemma Int64.coe_lt_zero_iff {x : Int64} : (x : ℤ) < 0 ↔ x.isNeg := by
  constructor
  · intro h; contrapose h; simp only [Bool.not_eq_true, not_lt] at h ⊢; exact coe_nonneg h
  · exact coe_lt_zero

lemma Int64.isNeg_eq {x : Int64} : x.isNeg = decide (x < 0) := by
  by_cases n : x.isNeg
  · simp only [n, true_eq_decide_iff, ←coe_lt_coe, coe_zero, coe_lt_zero n]
  · simp only [n, false_eq_decide_iff, not_lt, ←coe_le_coe, coe_zero]
    simp only [Bool.not_eq_true] at n
    exact coe_nonneg n

/-!
### Order operations: min, abs
-/

/-- `Int64` `min` -/
instance : Min Int64 where
  min x y := bif x.blt y then x else y

/-- Almost absolute value (maps `Int64.min → Int64.min`) -/
@[pp_dot] def Int64.abs (x : Int64) : UInt64 :=
  bif x.isNeg then -x.n else x.n

@[simp] lemma Int64.abs_min : Int64.min.abs = Int64.min := rfl

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

/-- `.abs` is absolute value -/
lemma Int64.coe_abs {x : Int64} : x.abs.toInt = |(x : ℤ)| := by
  by_cases n : x.isNeg
  · simp only [abs_eq_neg n, abs_of_neg (coe_lt_zero n)]
  · simp only [Bool.not_eq_true] at n
    simp only [UInt64.toInt, abs, n, cond_false, toInt, CharP.cast_eq_zero, sub_zero, Nat.abs_cast]

/-- If we turn `abs` back into an `Int64`, it's abs except at `.min` -/
lemma Int64.coe_abs' {x : Int64} (n : x ≠ .min) : ((⟨x.abs⟩ : Int64) : ℤ) = |(x : ℤ)| := by
  by_cases x0 : x = 0
  · simp only [x0, coe_zero, abs_zero]; rfl
  have x0' : x.n ≠ 0 := by simpa only [ext_iff, n_zero] using x0
  by_cases xn : x.isNeg
  · simp only [toInt, abs, xn, cond_true, UInt64.toNat_neg, x0', ge_iff_le, ite_false,
      UInt64.le_size, Nat.cast_sub, ← neg_def, isNeg_neg x0 n, Bool.not_true, ← UInt64.size_eq_pow,
      cond_false, CharP.cast_eq_zero, sub_zero]
    rw [abs_of_neg, neg_sub]
    simp only [sub_neg, Nat.cast_lt, UInt64.lt_size]
  · have xn' : (⟨x.n⟩ : Int64).isNeg ≠ true := xn
    simp only [toInt, abs, xn, cond_false, xn', CharP.cast_eq_zero, sub_zero, Nat.abs_cast]

/-- If we turn `abs` back into an `Int64`, it's negative only at `.min` -/
lemma Int64.abs_lt_zero {x : Int64} : ((⟨x.abs⟩ : Int64) : ℤ) < 0 ↔ x = .min := by
  by_cases e : x = .min
  · simp only [e, abs_min]; decide
  · simp only [coe_abs' e, e, iff_false, not_lt, abs_nonneg]
