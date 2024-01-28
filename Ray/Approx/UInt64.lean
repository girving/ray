import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.UInt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Ray.Approx.Nat
import Std.Data.Nat.Lemmas

/-!
## `UInt64` lemmas
-/

open Qq

attribute [pp_dot] UInt64.toNat

@[simp] lemma UInt64.toNat_zero : (0 : UInt64).toNat = 0 := rfl
@[simp] lemma UInt64.toNat_one : (1 : UInt64).toNat = 1 := rfl
lemma UInt64.size_eq_pow : UInt64.size = 2^64 := rfl

def UInt64.max : UInt64 := UInt64.size - 1
lemma UInt64.max_eq_pow_sub_one : UInt64.max = 2^64 - 1 := rfl

@[simp] lemma UInt64.toNat_lt_2_pow_64 (n : UInt64) : n.toNat < 2^64 := Fin.prop _
@[simp] lemma UInt64.cast_toNat_lt_2_pow_64 (n : UInt64) : (n.toNat : ℤ) < (2:ℤ)^64 := by
  have e : (2:ℤ)^64 = (2^64 : ℕ) := by norm_num
  rw [e, Nat.cast_lt]; apply UInt64.toNat_lt_2_pow_64

@[simp] lemma UInt64.toNat_lt_toNat (m n : UInt64) : m.toNat < n.toNat ↔ m < n := by
  simp only [LT.lt, UInt64.lt, UInt64.toNat]
@[simp] lemma UInt64.toNat_le_toNat (m n : UInt64) : m.toNat ≤ n.toNat ↔ m ≤ n := by
  simp only [LE.le, UInt64.le, UInt64.toNat]

lemma UInt64.le_iff_toNat_le (m n : UInt64) : m ≤ n ↔ m.toNat ≤ n.toNat := by
  simp only [LE.le, UInt64.le, toNat]

lemma UInt64.lt_iff_toNat_lt (m n : UInt64) : m < n ↔ m.toNat < n.toNat := by
  simp only [LT.lt, UInt64.lt, toNat]

lemma UInt64.eq_iff_toNat_eq (m n : UInt64) : m = n ↔ m.toNat = n.toNat := by
  constructor
  · intro e; rw [e]
  · intro e; exact UInt64.eq_of_val_eq (Fin.eq_of_val_eq e)

lemma UInt64.pos_iff_toNat_pos (n : UInt64) : 0 < n ↔ 0 < n.toNat := by
  rw [lt_iff_toNat_lt, toNat_zero]

lemma UInt64.ne_zero_iff_toNat_ne_zero {n : UInt64} : n ≠ 0 ↔ n.toNat ≠ 0 := by
  simp only [Ne.def, eq_iff_toNat_eq, toNat_zero]

@[simp] lemma UInt64.nonneg {n : UInt64} : 0 ≤ n := by
  simp only [le_iff_toNat_le, toNat_zero, zero_le]

@[simp] lemma UInt64.toNat_2_pow_63 : ((2 : UInt64) ^ 63).toNat = 2^63 := rfl
@[simp] lemma UInt64.toNat_2_pow_63' : (9223372036854775808 : UInt64).toNat = 2^63 := rfl

@[simp] lemma UInt32.size_pos : 0 < UInt32.size := by decide
@[simp] lemma UInt32.lt_size (n : UInt32) : n.toNat < UInt32.size := by
  simp only [toNat]; exact Fin.prop n.val
@[simp] lemma UInt32.le_size (n : UInt32) : n.toNat ≤ UInt32.size := by
  simp only [toNat]; exact Fin.is_le'

@[simp] lemma UInt64.size_pos : 0 < UInt64.size := by decide
@[simp] lemma UInt64.lt_size (n : UInt64) : n.toNat < UInt64.size := by
  simp only [toNat]; exact Fin.prop n.val
@[simp] lemma UInt64.le_size (n : UInt64) : n.toNat ≤ UInt64.size := by
  simp only [toNat]; exact Fin.is_le'
@[simp] lemma UInt64.le_size_sub_one (n : UInt64) : n.toNat ≤ UInt64.size - 1 :=
  Nat.le_pred_of_lt (lt_size _)

@[simp] lemma UInt64.toNat_neg (n : UInt64) :
    (-n).toNat = if n = 0 then 0 else UInt64.size - n.toNat := by
  induction' n with a
  simp only [toNat, neg_def, Fin.neg, ge_iff_le, eq_iff_toNat_eq, UInt64.zero_def, Fin.val_zero]
  by_cases a0 : (a : ℕ) = 0
  · simp only [a0, tsub_zero, Nat.mod_self, ite_true]
  · simp only [a0, if_false]; rw [Nat.mod_eq_of_lt]; apply Nat.sub_lt_of_pos_le
    · exact Nat.pos_of_ne_zero a0
    · exact Fin.is_le'

lemma UInt64.toNat_add (m n : UInt64) : (m + n).toNat = (m.toNat + n.toNat) % UInt64.size := by
  simp only [UInt64.toNat, UInt64.add_def]
  simp only [HAdd.hAdd, Add.add, Fin.add, Nat.add_eq]

lemma UInt64.toNat_add' (m n : UInt64) :
    (m + n).toNat = m.toNat + n.toNat - if m.toNat + n.toNat < size then 0 else size := by
  by_cases mn : m.toNat + n.toNat < size
  · simp only [mn, if_true, Nat.sub_zero]; rw [toNat_add, Nat.mod_eq_of_lt mn]
  · simp only [mn, if_false]; rw [toNat_add, Nat.mod_eq]
    rw [not_lt] at mn
    simp only [size_pos, true_and, mn, if_true]
    rw [Nat.mod_eq_of_lt]
    refine lt_of_le_of_lt (Nat.sub_le_sub_left n.le_size _) ?_
    rw [Nat.add_sub_cancel]; exact m.lt_size

lemma UInt64.add_wrap_iff (m n : UInt64) : m + n < m ↔ size ≤ m.toNat + n.toNat := by
  by_cases m0 : m = 0
  · simp only [m0, zero_add, toNat_zero]
    rw [←not_iff_not, not_le]
    simp only [lt_iff_toNat_lt, toNat_zero, not_lt_zero', not_false_eq_true, lt_size]
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add']
    simp only [eq_iff_toNat_eq, toNat_zero] at m0
    by_cases h : size ≤ m.toNat + n.toNat
    · simp only [not_lt.mpr h, ite_false, ge_iff_le, Nat.add_sub_lt_left m0, lt_size, h]
    · simp only [not_le] at h
      simp only [h, ite_true, ge_iff_le, nonpos_iff_eq_zero, add_eq_zero, tsub_zero,
        add_lt_iff_neg_left, not_lt_zero', false_iff, not_le]

/-- If `UInt64` doesn't wrap, addition commutes with `toNat` -/
lemma UInt64.toNat_add_of_le_add {m n : UInt64} (h : m ≤ m + n) :
    (m + n).toNat = m.toNat + n.toNat := by
  rw [UInt64.le_iff_toNat_le] at h
  rw [UInt64.toNat_add'] at h ⊢
  by_cases m0 : m.toNat = 0
  · simp only [m0, zero_add, lt_size, ite_true, ge_iff_le, nonpos_iff_eq_zero, tsub_zero]
  · by_cases mn : toNat m + toNat n < size
    · simp only [mn, if_true, Nat.sub_zero] at h ⊢
    · contrapose h; simp only [mn, if_false, not_le, Nat.add_sub_lt_left]
      rw [Nat.add_sub_lt_left m0]
      exact lt_size n

/-- If `UInt64` wraps, addition and `toNat` commute except for subtracting `size`
    (`AddGroupWithOne` version) -/
lemma UInt64.toNat_add_of_add_lt' {G : Type} [AddGroupWithOne G]
    {m n : UInt64} (h : m + n < m) :
    ((m + n).toNat : G) = m.toNat + n.toNat - size := by
  rw [UInt64.lt_iff_toNat_lt] at h
  rw [UInt64.toNat_add'] at h ⊢
  by_cases mn : toNat m + toNat n < size
  · contrapose h; simp only [mn, if_true, Nat.sub_zero, not_lt]; apply Nat.le_add_right
  · simp only [mn, ite_false, ge_iff_le]
    simp only [not_lt] at mn
    simp only [ge_iff_le, Nat.cast_sub mn, Nat.cast_add]

/-- If `UInt64` wraps, addition commutes with `toNat` except for subtracting `size` (`ℕ` version) -/
lemma UInt64.toNat_add_of_add_lt {m n : UInt64} (h : m + n < m) :
    (m + n).toNat = m.toNat + n.toNat - size := by
  rw [UInt64.lt_iff_toNat_lt] at h
  rw [UInt64.toNat_add'] at h ⊢
  by_cases mn : toNat m + toNat n < size
  · contrapose h; simp only [mn, if_true, Nat.sub_zero, not_lt]; apply Nat.le_add_right
  · simp only [mn, ite_false, ge_iff_le]

-- `UInt64` subtract wraps around
lemma UInt64.toNat_sub' {x y : UInt64} : (x - y).toNat = (x.toNat + (size - y.toNat)) % size := rfl

 -- If truncation doesn't occur, `-` commutes with `toNat`
lemma UInt64.toNat_sub {x y : UInt64} (h : y ≤ x) : (x - y).toNat = x.toNat - y.toNat := by
  rw [toNat_sub']
  rw [le_iff_toNat_le] at h
  rw [←Nat.add_sub_assoc (le_size _), add_comm, Nat.add_sub_assoc h]
  simp only [ge_iff_le, toNat_le_toNat, Nat.add_mod_left]
  rw [Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_size _)

 -- If truncation doesn't occur, `-` reduces
lemma UInt64.sub_le {x y : UInt64} (h : y ≤ x) : x - y ≤ x := by
  rw [le_iff_toNat_le, toNat_sub h]; apply Nat.sub_le

 /-- Adding 1 is usually adding one `toNat` -/
lemma UInt64.toNat_add_one {m : UInt64} (h : m.toNat ≠ 2^64-1) : (m + 1).toNat = m.toNat + 1 := by
  rw [toNat_add, toNat_one, Nat.mod_eq_of_lt]
  contrapose h; simp only [size_eq_pow, not_lt] at h
  simp only [ge_iff_le, ne_eq, not_not]
  exact le_antisymm (UInt64.le_size_sub_one _) (Nat.sub_le_of_le_add h)

/-- `UInt64` is a linear order (though not an ordered algebraic structure) -/
instance : LinearOrder UInt64 where
  le_refl x := by simp only [UInt64.le_iff_toNat_le]; rfl
  le_trans x y z := by simp only [UInt64.le_iff_toNat_le]; apply le_trans
  le_antisymm x y := by
    simp only [UInt64.le_iff_toNat_le, UInt64.eq_iff_toNat_eq]; apply le_antisymm
  le_total x y := by simp only [UInt64.le_iff_toNat_le]; apply le_total
  lt_iff_le_not_le x y := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]; apply lt_iff_le_not_le
  decidableLE x y := by infer_instance

/-- `UInt64` bitwise and is `ℕ` bitwise and -/
@[simp] lemma UInt64.toNat_land {x y : UInt64} : (x &&& y).toNat = x.toNat &&& y.toNat := by
  simp only [HAnd.hAnd, AndOp.and, UInt64.land, Fin.land, toNat]
  rw [Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt Nat.land_le_max (max_lt (Fin.prop _) (Fin.prop _))

/-- `UInt64` mod is `ℕ` mod -/
@[simp] lemma UInt64.toNat_mod {x y : UInt64} : (x % y).toNat = x.toNat % y.toNat := rfl

@[simp] lemma UInt64.land_eq_hand {x y : UInt64} : UInt64.land x y = x &&& y := rfl

@[simp] lemma UInt64.zero_land {x : UInt64} : 0 &&& x = 0 := by
  simp only [eq_iff_toNat_eq, toNat_land, toNat_zero, Nat.zero_and]

@[simp] lemma UInt64.toNat_mod_size (x : UInt64) : x.toNat % UInt64.size = x.toNat := by
  rw [Nat.mod_eq_of_lt]; exact lt_size x

lemma UInt64.toNat_shiftLeft' {x s : UInt64} :
    (x <<< s).toNat = x.toNat % 2^(64 - s.toNat % 64) * 2^(s.toNat % 64) := by
  generalize ht : s.toNat % 64 = t
  have lt : t < 64 := by rw [←ht]; exact Nat.mod_lt _ (by norm_num)
  have e0 : ((modn s 64).val : ℕ) = t := by rw [←ht]; rfl
  simp only [HShiftLeft.hShiftLeft, ShiftLeft.shiftLeft, UInt64.shiftLeft, Fin.shiftLeft]
  trans Nat.shiftLeft ↑x.1 ↑(modn s 64).1 % size
  · rfl
  · have e1 : (x.val : ℕ) = x.toNat := rfl
    simp only [e0, e1]
    trans x.toNat * 2^t % size
    · apply congr_arg₂ _ ?_ rfl
      apply Nat.shiftLeft_eq_mul_pow
    · have e2 : size = 2 ^ (64 - t) * 2 ^ t := by
        rw [←pow_add, Nat.sub_add_cancel lt.le, size_eq_pow]
      rw [e2]
      refine Nat.mod_mul_eq_mul_mod' _ _ _ ?_
      apply pow_ne_zero; norm_num

@[simp] lemma UInt64.shiftLeft_zero {x : UInt64} : x <<< 0 = x := by
  simp only [eq_iff_toNat_eq, toNat_shiftLeft', toNat_zero, Nat.zero_lt_succ, Nat.mod_eq_of_lt,
    tsub_zero, toNat_lt_2_pow_64, pow_zero, mul_one]

@[simp] lemma UInt64.zero_shiftLeft {x : UInt64} : 0 <<< x = 0 := by
  simp only [eq_iff_toNat_eq, toNat_shiftLeft', toNat_zero, gt_iff_lt, zero_lt_two, pow_pos,
    Nat.mod_eq_of_lt, zero_mul]

lemma UInt64.toNat_shiftLeft {x s : UInt64} (h : s < 64) :
    (x <<< s).toNat = x.toNat % 2^(64 - s.toNat) * 2^s.toNat := by
  have p : (64 : UInt64).toNat = 64 := rfl
  rw [lt_iff_toNat_lt, p] at h
  simp only [toNat_shiftLeft', Nat.mod_eq_of_lt h]

@[simp] lemma UInt64.toNat_shiftLeft32 {x : UInt64} :
    (x <<< 32).toNat = x.toNat % 2^32 * 2^32 := by
  simp only [HShiftLeft.hShiftLeft, ShiftLeft.shiftLeft, UInt64.shiftLeft, Fin.shiftLeft]
  trans Nat.shiftLeft ↑x.1 ↑(modn 32 64).1 % size
  · rfl
  · have e0 : ((modn 32 64).val : ℕ) = 32 := rfl
    have e1 : (x.val : ℕ) = x.toNat := rfl
    simp only [e0, e1]
    trans x.toNat * 2^32 % size
    · apply congr_arg₂ _ ?_ rfl
      apply Nat.shiftLeft_eq_mul_pow
    · exact Nat.mod_mul_eq_mul_mod _ _

@[simp] lemma UInt64.shiftRight_zero {x : UInt64} : x >>> 0 = x := by
  rw [UInt64.eq_iff_toNat_eq]
  trans x.toNat >>> 0 % size
  · rfl
  · simp only [Nat.shiftRight_zero, toNat_mod_size]

lemma UInt64.toNat_shiftRight' {x s : UInt64} : (x >>> s).toNat = x.toNat / 2^(s.toNat % 64) := by
  generalize ht : s.toNat % 64 = t
  have e0 : ((modn s 64).val : ℕ) = t := by rw [←ht]; rfl
  trans (↑x.1 : ℕ) >>> ↑(modn s 64).1 % size
  · rfl
  · rw [e0, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
    · rfl
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_size _)

lemma UInt64.toNat_shiftRight {x s : UInt64} (h : s < 64) :
    (x >>> s).toNat = x.toNat / 2^s.toNat := by
  have p : (64 : UInt64).toNat = 64 := rfl
  rw [lt_iff_toNat_lt, p] at h
  rw [UInt64.toNat_shiftRight', Nat.mod_eq_of_lt h]

@[simp] lemma UInt64.zero_shiftRight {x : UInt64} : 0 >>> x = 0 := by
  simp only [eq_iff_toNat_eq, toNat_shiftRight', toNat_zero, Nat.zero_div]

@[simp] lemma UInt64.testBit_eq_zero {x : UInt64} {i : ℕ} (h : 64 ≤ i) :
    Nat.testBit x.toNat i = false := by
  have i0 : 0 < 2^i := pow_pos (by norm_num) _
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, (Nat.div_eq_zero_iff i0).mpr]
  · rfl
  · refine lt_of_lt_of_le ?_ (pow_right_mono one_le_two h)
    exact toNat_lt_2_pow_64 x

@[simp] lemma UInt64.toNat_lor {x y : UInt64} : (x ||| y).toNat = x.toNat ||| y.toNat := by
  trans (x.toNat ||| y.toNat) % size
  · rfl
  · rw [Nat.mod_eq_of_lt]
    rw [Nat.lt_iff_le_pred size_pos]
    refine Nat.le_of_testBit_le fun i ↦ ?_
    simp only [Nat.testBit_lor, size_eq_pow, ge_iff_le, Nat.testBit_two_pow_sub_one]
    by_cases lt : i < 64
    · simp only [lt, decide_True, Bool.le_true]
    · simp only [lt, decide_False]
      simp only [not_lt] at lt
      simp only [testBit_eq_zero lt, Bool.or_self, le_refl]

@[simp] lemma UInt64.zero_or {x : UInt64} : 0 ||| x = x := by
  simp only [eq_iff_toNat_eq, toNat_lor, toNat_zero, Nat.or_zero]

@[simp] lemma UInt64.or_zero {x : UInt64} : 0 ||| x = x := by
  simp only [eq_iff_toNat_eq, toNat_lor, toNat_zero, Nat.or_zero]

lemma UInt64.toNat_lor_shifts {x y s : UInt64} (s0 : s ≠ 0) (s64 : s < 64) :
    (x >>> s).toNat ||| (y <<< (64-s)).toNat = (x >>> s).toNat + (y <<< (64-s)).toNat := by
  have six : (64 : UInt64).toNat = 64 := rfl
  refine Nat.lor_eq_add fun i ↦ ?_
  by_cases si : i < 64-s.toNat
  · right
    rw [toNat_shiftLeft, toNat_sub s64.le]
    simp only [ge_iff_le, toNat_le_toNat, Nat.testBit_mul_two_pow, tsub_le_iff_right,
      Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq, Bool.decide_and,
      Bool.decide_coe, Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not, not_le,
      not_lt, Nat.add_lt_of_lt_sub si, six, true_or]
    rw [lt_iff_toNat_lt, toNat_sub s64.le]
    apply Nat.sub_lt_self
    · rw [Nat.pos_iff_ne_zero]
      contrapose s0
      simpa only [ne_eq, eq_iff_toNat_eq, toNat_zero, not_not] using s0
    · rw [←le_iff_toNat_le]; exact s64.le
  · left
    simp only [ge_iff_le, not_lt] at si
    rw [toNat_shiftRight s64]
    apply Nat.testBit_eq_false_of_lt
    apply Nat.div_lt_of_lt_mul
    apply lt_of_lt_of_le (lt_size _)
    rw [size_eq_pow, ←pow_add]
    apply pow_right_mono one_le_two
    exact Nat.sub_le_iff_le_add'.mp si

@[simp] lemma UInt64.toNat_cast (n : ℕ) : (n : UInt64).toNat = n % UInt64.size := by
  simp only [toNat, UInt64.natCast_def, Fin.coe_ofNat_eq_mod]

@[simp] lemma UInt64.cast_toNat (n : UInt64) : (n.toNat : UInt64) = n := by
  simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_cast, UInt64.toNat_mod_size]

@[simp] lemma UInt64.toNat_log2 (n : UInt64) : n.log2.toNat = n.toNat.log2 := rfl

@[simp] lemma UInt64.log2_zero : (0 : UInt64).log2 = 0 := rfl

@[simp] lemma UInt64.log2_lt_64 (n : UInt64) : n.toNat.log2 < 64 := by
  by_cases n0 : n.toNat = 0
  · simp only [n0, Nat.log2_zero, Nat.zero_lt_succ]
  · simp only [Nat.log2_lt n0, toNat_lt_2_pow_64 n]

@[simp] lemma UInt64.log2_lt_64' (n : UInt64) : n.log2 < 64 := by
  rw [lt_iff_toNat_lt, toNat_log2]; exact log2_lt_64 _

lemma UInt64.toNat_add_of_le {x y : UInt64} (h : x ≤ .max - y) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt64.toNat_add']
  split_ifs with h1
  · simp only [tsub_zero]
  · exfalso
    have e : (2^64 - 1 : UInt64).toNat = 2^64 - 1 := by decide
    have yp : y.toNat < 2^64 := toNat_lt_2_pow_64 _
    simp only [max_eq_pow_sub_one, size_eq_pow, not_lt, le_iff_toNat_le] at h h1
    rw [UInt64.toNat_sub, e, Nat.le_sub_iff_add_le] at h
    · have b := le_trans h1 h
      norm_num at b
    · exact Nat.le_sub_one_of_lt yp
    · rw [le_iff_toNat_le, e]; exact Nat.le_sub_one_of_lt yp

lemma UInt64.pos_iff_ne_zero {x : UInt64} : 0 < x ↔ x ≠ 0 := by
  simp only [pos_iff_toNat_pos, Nat.pos_iff_ne_zero, ne_eq, eq_iff_toNat_eq, toNat_zero]

@[simp] lemma UInt64.toNat_max : UInt64.max.toNat = 2^64 - 1 := rfl

@[simp] lemma UInt64.le_max (n : UInt64) : n ≤ max := by
  rw [UInt64.le_iff_toNat_le, toNat_max]; exact Nat.le_of_lt_succ (lt_size _)

@[simp] lemma UInt64.toNat_le_pow_sub_one (n : UInt64) : n.toNat ≤ 2^64 - 1 :=
  Nat.le_of_lt_succ (toNat_lt_2_pow_64 _)

/-!
### Conversion from `UInt64` to `ZMod`
-/

@[pp_dot] def UInt64.toZMod (x : UInt64) : ZMod UInt64.size := x.toNat

noncomputable instance : Coe UInt64 (ZMod UInt64.size) where
  coe x := x.toZMod

@[simp] lemma UInt64.toZMod_toNat (x : UInt64) :
    (x.toNat : ZMod UInt64.size) = (x : ZMod UInt64.size) := rfl

@[simp] lemma UInt64.toZMod_add (x y : UInt64) :
    ((x + y : UInt64) : ZMod UInt64.size) = x + y := by
  simp only [toZMod, toNat_add, ZMod.nat_cast_mod, Nat.cast_add, toZMod_toNat]

@[simp] lemma UInt64.toZMod_mul (x y : UInt64) :
    ((x * y : UInt64) : ZMod UInt64.size) = x * y := by
  simp only [toZMod, toNat, mul_def, Fin.mul_def, ZMod.nat_cast_mod, Nat.cast_mul]

@[simp] lemma UInt64.toZMod_cast (x : ℕ) : ((x : UInt64) : ZMod UInt64.size) = x := by
  simp only [toZMod, toNat, natCast_def, Fin.coe_ofNat_eq_mod, ZMod.nat_cast_mod]

@[simp] lemma UInt64.toZMod_shiftLeft32 (x : UInt64) :
    (x <<< 32 : ZMod UInt64.size) = x * (2 : ZMod UInt64.size)^32 := by
  have e : (2^32)^2 = UInt64.size := by rfl
  rw [toZMod, UInt64.toNat_shiftLeft32, ←Nat.mod_mul_eq_mul_mod, e]
  simp only [ZMod.nat_cast_mod, Nat.cast_mul, toZMod_toNat, Nat.cast_pow, Nat.cast_ofNat]

/-!
### Add with carry
-/

/-- Add with carry, producing the `{0,1}` value as an `UInt64` -/
def addc (x y : UInt64) : UInt64 × UInt64 :=
  let z := x + y
  (z, if z < x then 1 else 0)

/-- Decompose an `addc` -/
lemma addc_eq (x y : UInt64) :
    ∃ a0 a2 : ℕ, a0 < 2^64 ∧ a2 < 2 ∧
      x.toNat + y.toNat = a2 * 2^64 + a0 ∧ addc x y = ((a0 : UInt64), (a2 : UInt64)) := by
  refine ⟨(x + y).toNat, (if x.toNat + y.toNat < UInt64.size then 0 else 1), UInt64.lt_size _,
    (by split_ifs; exact zero_lt_two; exact one_lt_two), ?_⟩
  by_cases lt : x.toNat + y.toNat < UInt64.size
  · simp only [lt, ite_true, zero_mul, UInt64.toNat_add', ge_iff_le, nonpos_iff_eq_zero,
      add_eq_zero, tsub_zero, zero_add, addc, Nat.cast_add, Nat.cast_zero, Prod.mk.injEq,
      UInt64.eq_iff_toNat_eq, UInt64.toNat_cast, UInt64.toNat_mod_size, ite_eq_right_iff, true_and]
    intro h; contrapose h
    rw [not_lt, UInt64.le_iff_toNat_le, UInt64.toNat_add']
    simp only [lt, ite_true, ge_iff_le, nonpos_iff_eq_zero, add_eq_zero, tsub_zero,
      le_add_iff_nonneg_right, zero_le]
  · simp only [lt, ite_false, one_mul, UInt64.toNat_add', ge_iff_le, addc, UInt64.lt_iff_toNat_lt,
      Nat.cast_one, Prod.mk.injEq, UInt64.eq_iff_toNat_eq, UInt64.toNat_cast, ite_eq_left_iff, not_lt,
      imp_false, not_le, UInt64.toNat_zero, UInt64.toNat_one]
    simp only [not_lt, UInt64.size_eq_pow] at lt
    have sub_lt : x.toNat + y.toNat - UInt64.size < UInt64.toNat x := by
      refine Nat.sub_lt_left_of_lt_add lt ?_
      rw [add_comm UInt64.size]
      apply Nat.add_lt_add''
      · rfl
      · exact UInt64.lt_size y
    rw [Nat.mod_eq_of_lt (lt_trans sub_lt (UInt64.lt_size _))]
    refine ⟨?_, rfl, sub_lt⟩
    zify
    simp only [ge_iff_le, lt, Nat.cast_sub, Nat.cast_add, UInt64.size_eq_pow, Nat.cast_pow,
      Nat.cast_two, true_and]
    ring

/-!
### Splitting `UInt64`s into 32-bit halves
-/

/-- Split a `UInt64` into low and high 32-bit values, both represented as `UInt64` -/
def split (x : UInt64) : UInt64 × UInt64 :=
  (x.toUInt32.toUInt64, x >>> 32)

@[simp] lemma UInt32.toNat_toUInt64 {x : UInt32} : x.toUInt64.toNat = x.toNat := by
  simp only [toUInt64, Nat.toUInt64, UInt64.ofNat, Fin.ofNat]
  trans toNat x % (18446744073709551615 + 1)
  · rfl
  · norm_num
    exact lt_of_lt_of_le (UInt32.lt_size x) (by norm_num)

@[simp] lemma UInt64.toNat_toUInt32 {x : UInt64} : x.toUInt32.toNat = x.toNat % 2^32 := by
  simp only [toUInt32, Nat.toUInt32, UInt32.ofNat, Fin.ofNat]
  trans toNat x % (4294967295 + 1)
  · rfl
  · rfl

@[simp] lemma UInt64.toNat_shiftRight32 {x : UInt64} : (x >>> 32).toNat = x.toNat / 2^32 := by
  simp only [HShiftRight.hShiftRight, ShiftRight.shiftRight, UInt64.shiftRight, Fin.shiftRight]
  trans Nat.shiftRight x.1 (modn 32 64).1 % size
  · rfl
  · have e0 : ((modn 32 64).val : ℕ) = 32 := rfl
    have e1 : (x.val : ℕ) = x.toNat := rfl
    simp only [e0, e1]
    trans x.toNat / 2^32 % size
    · apply congr_arg₂ _ ?_ rfl
      apply Nat.shiftRight_eq_div_pow
    · rw [Nat.mod_eq_of_lt]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) (lt_size _)

-- `split` in terms of `ℕ`
@[simp] lemma toNat_split_1 {x : UInt64} : (split x).1.toNat = x.toNat % 2^32 := by
  simp only [split, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
@[simp] lemma toNat_split_2 {x : UInt64} : (split x).2.toNat = x.toNat / 2^32 := by
  simp only [split, UInt64.toNat_shiftRight32]
@[simp] lemma toNat_split_1_lt {x : UInt64} : (split x).1.toNat < 2^32 := by
  simp only [toNat_split_1]; apply Nat.mod_lt; norm_num
@[simp] lemma toNat_split_2_lt {x : UInt64} : (split x).2.toNat < 2^32 := by
  simp only [toNat_split_2]
  have e : 2^32 = 2^64 / 2^32 := by norm_num
  nth_rw 2 [e]
  apply Nat.div_lt_of_lt_mul
  norm_num

-- Double %
@[simp] lemma mod_32_mod_64 (x : ℕ) : x % 2^32 % 2^64 = x % 2^32 := by
  rw [Nat.mod_eq_of_lt]; exact lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)

/-- Decompose a `UInt64` via `split` -/
lemma UInt64.eq_split (x : UInt64) :
    ∃ x0 x1 : ℕ, x0 < 2^32 ∧ x1 < 2^32 ∧
      x.toNat = x1 * 2^32 + x0 ∧ split x = ((x0 : UInt64), (x1 : UInt64)) := by
  refine ⟨(split x).1.toNat, (split x).2.toNat, toNat_split_1_lt, toNat_split_2_lt, ?_⟩
  simp only [toNat_split_1, toNat_split_2]
  constructor
  · exact (Nat.div_add_mod' _ _).symm
  · ext
    · simp only [toNat_split_1, toNat_cast, size_eq_pow, Nat.isUnit_iff, mod_32_mod_64]
    · simp only [toNat_split_2, toNat_cast]
      rw [Nat.mod_eq_of_lt]
      apply Nat.div_lt_of_lt_mul
      exact lt_trans (UInt64.lt_size _) (by norm_num)

/-!
### `ℤ` conversion
-/

@[pp_dot] def UInt64.toInt (x : UInt64) : ℤ := x.toNat

@[pp_dot] lemma UInt64.coe_toNat_sub {x y : UInt64} (h : y ≤ x) :
    ((x - y).toNat : ℤ) = x.toNat - y.toNat := by
  rw [UInt64.toNat_sub h, Nat.cast_sub]
  rwa [←UInt64.le_iff_toNat_le]

@[simp] lemma UInt64.toInt_zero : (0 : UInt64).toInt = 0 := rfl

/-!
### Shift right, rounding up or down
-/

/-- Shift right, rounding up or down correctly even for large `s` -/
@[irreducible] def UInt64.shiftRightRound (x : UInt64) (s : UInt64) (up : Bool) : UInt64 :=
  bif s == 0 then x
  else bif 64 ≤ s then bif x == 0 || !up then 0 else 1
  else
    let y := x >>> s
    bif up && x != y <<< s then y+1 else y

/-- `0.shiftRightRound = 0` -/
@[simp] lemma UInt64.zero_shiftRightRound (s : UInt64) (up : Bool) :
    (0 : UInt64).shiftRightRound s up = 0 := by
  rw [shiftRightRound]
  simp only [beq_self_eq_true, Bool.true_or, cond_true, zero_shiftRight, zero_shiftLeft,
    bne_self_eq_false, Bool.and_false, zero_add, cond_false, Bool.cond_self]

/-- Exact `ℕ` result of `UInt64.shiftRightRound` -/
lemma UInt64.toNat_shiftRightRound {x : UInt64} {s : UInt64} {up : Bool} :
    (x.shiftRightRound s up).toNat = (x.toNat + (if up then 2^s.toNat - 1 else 0)) / 2^s.toNat := by
  rw [UInt64.shiftRightRound]
  simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq, eq_iff_toNat_eq, toNat_zero, Bool.not_eq_true',
    Bool.and_eq_true, bne_iff_ne, ne_eq, toNat_shiftLeft', toNat_shiftRight', decide_eq_true_eq,
    apply_ite (f := fun x : UInt64 ↦ x.toNat), toNat_one, toNat_add]
  have p0 : 0 < 2^s.toNat := pow_pos (by norm_num) _
  by_cases s0 : s.toNat = 0
  · simp only [s0, Nat.zero_mod, pow_zero, Nat.div_one, tsub_zero, mul_one, ite_true, ge_iff_le,
      le_refl, tsub_eq_zero_of_le, ite_self, add_zero]
  · simp only [s0, ite_false]
    by_cases s64 : 64 ≤ s
    · simp only [s64, ite_true]
      have lt : x.toNat < 2 ^ s.toNat := by
        rw [UInt64.le_iff_toNat_le] at s64
        exact lt_of_lt_of_le (UInt64.toNat_lt_2_pow_64 _) (pow_le_pow_right (by norm_num) s64)
      induction up
      · simp only [or_true, ite_true, ite_false, add_zero]
        rw [Nat.div_eq_zero_of_lt lt]
      · by_cases x0 : x.toNat = 0
        · simp only [x0, or_false, ite_true, zero_add, Nat.two_pow_sub_one_div_two_pow, ge_iff_le,
            le_refl, tsub_eq_zero_of_le, pow_zero]
        · simp only [x0, or_self, ite_false, ite_true]
          rw [Nat.div_eq_sub_div (by omega) (by omega), Nat.div_eq_zero_of_lt (by omega)]
    · have slt : s.toNat < 64 := by rw [not_le, UInt64.lt_iff_toNat_lt] at s64; exact s64
      have dlt : x.toNat / 2 ^ s.toNat < 2 ^ (64 - s.toNat) := by
        apply Nat.div_lt_of_lt_mul
        simp only [←Nat.pow_add, Nat.add_sub_of_le slt.le, UInt64.toNat_lt_2_pow_64]
      simp only [s64, Nat.mod_eq_of_lt slt, Nat.mod_eq_of_lt dlt, ite_false]
      induction up
      · simp only [false_and, ite_false, add_zero]
      · simp only [true_and, ite_not, ite_true]
        generalize ha : x.toNat / 2^s.toNat = a
        generalize hb : x.toNat % 2^s.toNat = b
        rw [←Nat.div_add_mod x.toNat (2^s.toNat), ha,  hb, mul_comm _ a]
        simp only [add_right_eq_self]
        by_cases b0 : b = 0
        · simp only [b0, ite_true, add_zero, Nat.add_div p0, gt_iff_lt, zero_lt_two, pow_pos,
            Nat.mul_div_left, Nat.two_pow_sub_one_div_two_pow, ge_iff_le, le_refl,
            tsub_eq_zero_of_le, pow_zero, Nat.mul_mod_left, zero_add, self_eq_add_right,
            ite_eq_right_iff, one_ne_zero, imp_false, not_le, Nat.mod_lt _ p0]
        · have p2 : 2 ≤ 2^s.toNat := le_self_pow (by omega) (by omega)
          have a1 : a + 1 < size := by
            rw [←ha, size_eq_pow]
            have h : x.toNat < 2^64 := toNat_lt_2_pow_64 x
            exact lt_of_le_of_lt (add_le_add_right (Nat.div_le_div h.le p2 (by norm_num)) _)
              (by norm_num)
          simp only [b0, Nat.mod_eq_of_lt a1, ite_false]
          have e : a * 2^s.toNat + b + (2^s.toNat - 1) = a * 2^s.toNat + 2^s.toNat + (b - 1) := by
            omega
          have blt : b - 1 < 2^s.toNat := by
            rw [←hb]; exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ p0)
          rw [e, ←add_one_mul, Nat.add_div p0, Nat.mul_div_cancel _ p0, Nat.div_eq_zero_of_lt blt,
            add_zero, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt blt]
          simp only [self_eq_add_right, ite_eq_right_iff, one_ne_zero, imp_false, not_le, blt]

/-- Alternate version using `ceilDiv` -/
lemma UInt64.toNat_shiftRightRound' {x : UInt64} {s : UInt64} {up : Bool} :
    (x.shiftRightRound s up).toNat =
      if up then x.toNat ⌈/⌉ 2^s.toNat else x.toNat / 2^s.toNat := by
  rw [UInt64.toNat_shiftRightRound]
  induction up
  · simp only [ite_false, add_zero]
  · by_cases s0 : s.toNat = 0
    · simp only [s0, pow_zero, ge_iff_le, le_refl, tsub_eq_zero_of_le, ite_self, add_zero,
      Nat.div_one, ceilDiv_one]
    · rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc]
      · simp only [ite_true]
      · exact one_le_pow_of_one_le (by norm_num) _

/-- `UInt64.shiftRightRound` only makes things smaller -/
lemma UInt64.shiftRightRound_le_self {x : UInt64} {s : UInt64} {up : Bool} :
    (x.shiftRightRound s up).toNat ≤ x.toNat := by
  rw [UInt64.toNat_shiftRightRound']
  induction up
  · exact Nat.div_le_self x.toNat (2 ^ s.toNat)
  · simp only [ite_true, gt_iff_lt, zero_lt_two, pow_pos, ceilDiv_le_iff_le_smul, smul_eq_mul]
    exact Nat.le_mul_of_pos_left _ (by positivity)
