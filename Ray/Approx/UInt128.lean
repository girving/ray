import Mathlib.Data.Real.Archimedean
import Ray.Approx.Approx
import Ray.Approx.UInt64

/-!
## `UInt128`: 128-bit integers
-/

open Classical

/-!
### Definitions and basics
-/

@[ext]
structure UInt128 where
  lo : UInt64
  hi : UInt64
  deriving DecidableEq, BEq

def UInt128.size : ℕ := 2^128
def UInt128.max : UInt128 := ⟨UInt64.max, UInt64.max⟩

instance : Zero UInt128 where
  zero := ⟨0, 0⟩

instance : One UInt128 where
  one := ⟨1, 0⟩

@[pp_dot] def UInt128.toNat (x : UInt128) : ℕ :=
  (x.hi.toNat * 2^64) + x.lo.toNat

@[coe] def UInt128.toReal (x : UInt128) : ℝ := x.toNat

instance : Coe UInt128 ℝ where
  coe := UInt128.toReal

@[simp] lemma UInt128.toNat_zero : (0 : UInt128).toNat = 0 := rfl
@[simp] lemma UInt128.toNat_one : (1 : UInt128).toNat = 1 := rfl
@[simp] lemma UInt128.zero_lo : (0 : UInt128).lo = 0 := rfl
@[simp] lemma UInt128.zero_hi : (0 : UInt128).hi = 0 := rfl
@[simp] lemma UInt128.max_lo : UInt128.max.lo = UInt64.max := rfl
@[simp] lemma UInt128.max_hi : UInt128.max.lo = UInt64.max := rfl
lemma UInt128.max_eq_pow_sub_one : UInt128.max.toNat = 2^128 - 1 := rfl

@[simp] lemma UInt128.toReal_zero : ((0 : UInt128) : ℝ) = 0 := by
  simp only [toReal, toNat_zero, CharP.cast_eq_zero]

@[simp] lemma UInt128.toReal_one : ((1 : UInt128) : ℝ) = 1 := by
  simp only [toReal, toNat_one, Nat.cast_one]

lemma UInt128.lt_size (x : UInt128) : x.toNat < 2^128 := by
  have e : 2^128 = (2^64 - 1)*2^64 + 2^64 := by norm_num
  rw [e]
  refine Nat.add_lt_add'' (Nat.mul_le_mul_right _ ?_) (UInt64.lt_size _)
  exact Nat.le_pred_of_lt (UInt64.lt_size _)

lemma UInt128.coe_nonneg (x : UInt128) : 0 ≤ (x : ℝ) := by
  simp only [toReal, Nat.cast_nonneg]

lemma UInt128.coe_lt_size (x : UInt128) : (x : ℝ) < (2:ℝ)^128 := by
  refine lt_of_lt_of_le (b := ((2^128 : ℕ) : ℝ)) ?_ (by norm_num)
  simp only [toReal, Nat.cast_lt, UInt128.lt_size]

noncomputable instance {n : ℕ} : CoeTail UInt128 (ZMod n) where
  coe x := x.toNat

@[simp] lemma UInt128.toNat_max : UInt128.max.toNat = 2^128 - 1 := rfl

@[simp] lemma Nat.mod_mul_eq_mul_mod_128 (a : ℕ) : a * 2^64 % 2^128 = a % 2^64 * 2^64 :=
  Nat.mod_mul_eq_mul_mod _ _

@[simp] lemma UInt128.toNat_mod_pow_eq_lo (x : UInt128) : x.toNat % 2^64 = x.lo.toNat := by
  simp only [toNat, ←UInt64.size_eq_pow, Nat.add_mod, Nat.mul_mod_left, UInt64.toNat_mod_size,
    zero_add]

@[simp] lemma UInt128.toNat_div_pow_eq_hi (x : UInt128) : x.toNat / 2^64 = x.hi.toNat := by
  simp only [toNat, ← UInt64.size_eq_pow, UInt64.size_pos, Nat.add_div, Nat.mul_div_left,
    Nat.div_eq_zero_of_lt (UInt64.lt_size _), add_zero, Nat.mul_mod_left, UInt64.toNat_mod_size,
    zero_add, add_right_eq_self, ite_eq_right_iff, imp_false, not_le, UInt64.lt_size]

lemma UInt128.eq_iff_toNat_eq (x y : UInt128) : x = y ↔ x.toNat = y.toNat := by
  constructor
  · intro h; rw [h]
  · intro h; ext
    · rw [←UInt128.toNat_mod_pow_eq_lo x, ←UInt128.toNat_mod_pow_eq_lo y, h]
    · rw [←UInt128.toNat_div_pow_eq_hi x, ←UInt128.toNat_div_pow_eq_hi y, h]

def UInt128.blt (x y : UInt128) : Bool :=
  x.hi < y.hi || (x.hi == y.hi && x.lo < y.lo)

/-- `UInt128` has nice equality -/
instance : LawfulBEq UInt128 where
  eq_of_beq {x y} e := by
    induction' x with xlo xhi; induction' y with ylo yhi
    have g : ((xlo == ylo && xhi == yhi) = true) := e
    simp only [Bool.and_eq_true, beq_iff_eq] at g
    simp only [g.1, g.2]
  rfl {x} := by
    have e : (x == x) = (x.lo == x.lo && x.hi == x.hi) := rfl
    simp only [e, beq_self_eq_true, Bool.and_self]

/-!
### Conversion from `ℕ` to `UInt128`
-/

def UInt128.ofNat (x : ℕ) : UInt128 where
  lo := x
  hi := (x / 2^64 : ℕ)

@[simp] lemma UInt128.toNat_ofNat (x : ℕ) : (UInt128.ofNat x).toNat = x % 2^128 := by
  generalize hn : 2^64 = n
  have nn : 2^128 = n^2 := by rw [←hn]; norm_num
  simp only [toNat, ofNat, hn, UInt64.toNat_cast, UInt64.size_eq_pow, nn]
  apply Nat.div_mod_mul_add_mod_eq

/-!
### 128 bit increment
-/

def UInt128.succ (x : UInt128) : UInt128 :=
  let lo := x.lo + 1
  { lo := lo
    hi := x.hi + bif lo == 0 then 1 else 0 }

lemma UInt128.toNat_succ {x : UInt128} (h : x.toNat ≠ 2^128-1) : x.succ.toNat = x.toNat+1 := by
  have e : (2:UInt64)^64 = 0 := by rfl
  by_cases ll : x.lo = (2:UInt64)^64-1
  · simp only [succ, ll, e, zero_sub, add_left_neg, beq_self_eq_true, cond_true]
    by_cases hh : x.hi = (2:UInt64)^64-1
    · simp only [toNat, hh, ll, ge_iff_le, ne_eq] at h; contrapose h; decide
    · simp only [UInt64.eq_iff_toNat_eq] at hh
      simp only [toNat, UInt64.toNat_add_one hh, add_mul, one_mul, UInt64.toNat_zero, add_zero, ll]
      have c : (UInt64.toNat ((2:UInt64) ^ 64 - 1) : ℤ) = (2:ℤ)^64-1 := by rfl
      zify; rw [c]; ring
  · simp only [UInt64.eq_iff_toNat_eq] at ll
    simp only [toNat, succ, bif_eq_if, beq_iff_eq, UInt64.eq_iff_toNat_eq, UInt64.toNat_add_one ll,
      UInt64.toNat_zero, add_eq_zero, and_false, ite_false, add_zero]
    ring

lemma UInt128.coe_succ {x : UInt128} (h : (x:ℝ) ≠ (2:ℝ)^128-1) : (x.succ : ℝ) = x+1 := by
  rw [toReal, toReal, toNat_succ, Nat.cast_add_one]
  contrapose h; simp only [ge_iff_le, ne_eq, not_not] at h
  simp only [toReal, h, ge_iff_le, Nat.cast_sub, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    ne_eq, not_true, not_false_eq_true, not_not]
  norm_num

/-!
### 64 → 128 bit multiplication

We define the product of two `UInt64`s, as a 128-bit int.  Let `s = 2^32`.  Then we have

  `x = x1 s + x0`
  `y = y1 s + y0`
  `x y = x1 y1 s^2 + (x1 y0 + x0 y1) s + x0 y0`

Using `addc`, we have

  `x y = x1 y1 s^2 + (x1 y0 + x0 y1) s + x0 y0`
  `a1, a3 = addc (x1 y0) (x0 y1)`
  `x y = (a3 s + x1 y1) s^2 + a1 s + x0 y0`
  `b1, b2 = split a1`
  `x y = (a3 s + x1 y1 + b2) s^2 + b1 s + x0 y0`
  `c0, c2 = addc (x0 y0) b1`
  `x y = (a3 s + x1 y1 + b2 + c2) s^2 + c0`
-/

/-- All the bits of two `UInt64` multiplied together -/
@[irreducible] def mul128 (x y : UInt64) : UInt128 :=
  let (x0,x1) := split x
  let (y0,y1) := split y
  let (a1,a3) := addc (x1 * y0) (x0 * y1)
  let (b1,b2) := split a1
  let (c0,c2) := addc (x0 * y0) (b1 <<< 32)
  ⟨c0, (a3 <<< 32) + x1 * y1 + b2 + c2⟩

lemma mul_lt_32 {x y : ℕ} (xl : x < 2^32) (yl : y < 2^32) : x * y < UInt64.size :=
  lt_of_lt_of_le (Nat.mul_lt_mul' xl.le yl (by norm_num)) (by norm_num)

/-- `mul128` is correct mod `2^128` -/
lemma toNat_mul128_mod (x y : UInt64) : (mul128 x y).toNat % 2^128 = x.toNat * y.toNat % 2^128 := by
  rw [mul128]
  -- Split `x` and `y` into 32-bit halves
  rcases x.eq_split with ⟨x0,x1,x0s,x1s,x01,xs⟩
  rcases y.eq_split with ⟨y0,y1,y0s,y1s,y01,ys⟩
  simp only [x01, xs, y01, ys, ←Nat.cast_mul]
  clear x y xs ys x01 y01
  -- Decompose `addc (x1 * y0) (x0 * y1)` into `a1, a3`
  rcases addc_eq ↑(x1 * y0) ↑(x0 * y1) with ⟨a1, a3, a1s, _, a13n, a13e⟩
  simp only [UInt64.toNat_cast, Nat.mod_eq_of_lt (mul_lt_32 x1s y0s),
    Nat.mod_eq_of_lt (mul_lt_32 x0s y1s)] at a13n
  simp only [a13e, UInt128.toNat]
  -- Rewrite the result to use `a1, a3`
  have e : (x1 * 2^32 + x0) * (y1 * 2^32 + y0) =
      (x1 * y1 + a3 * 2^32) * 2^64 + a1 * 2^32 + x0 * y0 := by
    trans x1 * y1 * 2^64 + (x1 * y0 + x0 * y1) * 2^32 + x0 * y0
    · ring
    · rw [a13n]; ring
  rw [e]
  clear a13n a13e e
  -- Split `a1` into 32-bit halves
  rcases UInt64.eq_split a1 with ⟨b1,b2,b1s,_,b12,bs⟩
  simp only [UInt64.toNat_cast, UInt64.size_eq_pow, Nat.mod_eq_of_lt a1s] at b12
  simp only [bs]
  simp only [b12, add_mul _ _ (2^32), mul_assoc, (show 2^32 * 2^32 = 2^64 by norm_num), ←add_assoc,
    ←add_mul _ _ (2^64)]
  clear bs b12 a1s a1
  -- Decompose `addc (x0 * y0) (b1 <<< 32)` into `c0, c2`
  rcases addc_eq ↑(x0 * y0) ((b1 : UInt64) <<< 32) with ⟨c0, c2, c0s, _, c02n, c02e⟩
  have b1s' : b1 < UInt64.size := lt_trans b1s (by norm_num)
  simp only [UInt64.toNat_cast, Nat.mod_eq_of_lt (mul_lt_32 x0s y0s),
    UInt64.toNat_shiftLeft32, Nat.mod_eq_of_lt b1s', Nat.mod_eq_of_lt b1s,
    add_comm (x0 * y0) _] at c02n
  simp only [c02e, UInt64.toNat_cast, UInt64.size_eq_pow, Nat.mod_eq_of_lt c0s]
  rw [add_assoc _ _ (x0 * y0), c02n, ←add_assoc, ←add_mul]
  -- Reduce to high word
  rw [Nat.add_mod _ _ (2^128), Nat.add_mod _ c0 (2^128)]
  apply congr_arg₂ _ _ rfl
  apply congr_arg₂ _ _ rfl
  simp only [Nat.mod_mul_eq_mul_mod_128]
  apply congr_arg₂ _ _ rfl
  -- The rest is easy mod `2^64`
  rw [←Nat.ModEq, ←UInt64.size_eq_pow, ←ZMod.eq_iff_modEq_nat]
  simp only [Nat.cast_mul, add_comm, UInt64.toZMod_toNat, UInt64.toZMod_add, UInt64.toZMod_cast,
    UInt64.toZMod_mul, UInt64.toZMod_shiftLeft32, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]

/-- `mul128` is correct -/
@[simp] lemma toNat_mul128 (x y : UInt64) : (mul128 x y).toNat = x.toNat * y.toNat := by
  have h := toNat_mul128_mod x y
  rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at h
  · exact h
  · exact lt_of_lt_of_le (Nat.mul_lt_mul' (UInt64.lt_size _).le (UInt64.lt_size _) UInt64.size_pos)
      (by norm_num)
  · exact UInt128.lt_size _

/-!
### 128 bit shifting
-/

/-- Multiply by `2^(s % 128)`, discarding overflow bits -/
@[pp_dot] def UInt128.shiftLeft (x : UInt128) (s : UInt64) : UInt128 :=
  let s := s.land 127
  { lo := bif s < 64 then x.lo <<< s else 0
    hi := bif s == 0 then x.hi
          else bif s < 64 then x.hi <<< s ||| x.lo >>> (64-s)
          else x.lo <<< (s - 64) }

/-- Divide by `2^(s % 128)`, rounding down -/
@[pp_dot] def UInt128.shiftRight (x : UInt128) (s : UInt64) : UInt128 :=
  let s := s.land 127
  { lo := bif s == 0 then x.lo
          else bif s < 64 then x.lo >>> s ||| x.hi <<< (64-s)
          else x.hi >>> (s - 64)
    hi := bif s < 64 then x.hi >>> s else 0 }

/-- Divide by `2^s`, rounding up or down -/
@[pp_dot] def UInt128.shiftRightRound (x : UInt128) (s : UInt64) (up : Bool) : UInt128 :=
  bif s == 0 then x
  else bif 128 ≤ s then bif x == 0 || !up then 0 else 1
  else
    let y := x.shiftRight s
    bif up && x != y.shiftLeft s then y.succ else y

 /-- Multiply by `2^s`, saturating at `UInt128.max` if we overflow -/
@[pp_dot] def UInt128.shiftLeftSaturate (x : UInt128) (s : UInt64) : UInt128 :=
  bif bif 128 ≤ s then x != 0 else s != 0 && x.shiftRight (128-s) != 0 then UInt128.max
  else x.shiftLeft s

/-- `testBit` for `UInt128` -/
lemma UInt128.testBit_eq {x : UInt128} {i : ℕ} :
    x.toNat.testBit i = if i < 64 then x.lo.toNat.testBit i else x.hi.toNat.testBit (i-64) := by
  have z0 : ∀ j, j < 64 → Nat.testBit (x.hi.toNat * 2^64) j = false := by
    intro j h
    simp only [Nat.testBit_mul_two_pow, ge_iff_le, Bool.decide_and, Bool.decide_coe,
      Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not, not_le, h, true_or]
  have z1 : ∀ j, 64 ≤ j → Nat.testBit x.lo.toNat j = false := by
    intro j h
    refine Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (UInt64.toNat_lt_2_pow_64 _) ?_)
    exact pow_right_mono one_le_two h
  rw [UInt128.toNat, ←Nat.lor_eq_add]
  · simp only [Nat.testBit_lor]
    by_cases c : i < 64
    · simp only [Nat.testBit_mul_two_pow, not_le.mpr c, ge_iff_le, false_and, decide_False,
        Bool.false_or, c, ite_true]
    · simp only [Nat.testBit_mul_two_pow, not_lt.mp c, ge_iff_le, true_and, Bool.decide_coe,
        z1 _ (not_lt.mp c), Bool.or_false, c, ite_false]
  · intro j
    by_cases c : j < 64
    · simp only [z0 _ c, true_or]
    · simp only [z1 _ (not_lt.mp c), or_true]

/-- `testBit` is zero for large `i` -/
lemma UInt128.testBit_eq_zero {x : UInt128} {i : ℕ} (h : 128 ≤ i) :
    Nat.testBit x.toNat i = false := by
  have i64 : 64 ≤ i := le_trans (by norm_num) h
  have i64' : 64 ≤ i-64 := le_trans (by norm_num) (Nat.sub_le_sub_right h _)
  simp only [testBit_eq, UInt64.testBit_eq_zero i64, ge_iff_le, UInt64.testBit_eq_zero i64',
    ite_self]

-- Locally make this simp, following https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F-tactics/topic/simp_all.20removing.20a.20hypothesis.20before.20it.20can.20be.20used/near/409740178
attribute [local simp] Nat.mod_eq_of_lt

-- Lemmas for use in proving testBit equalities
lemma tb_eq {x : UInt64} {i j : ℕ} (ij : i = j ∨ 64 ≤ i ∧ 64 ≤ j) :
    Nat.testBit x.toNat i = Nat.testBit x.toNat j := by cases ij; repeat simp_all
lemma tb_ne {x y : UInt64} {i j : ℕ} (il : 64 ≤ i) (jl : 64 ≤ j) :
    Nat.testBit x.toNat i = Nat.testBit y.toNat j := by simp_all
lemma false_tb {x : UInt64} {i : ℕ} (il : 64 ≤ i) : false = Nat.testBit x.toNat i := by simp_all
lemma tb_false {x : UInt64} {i : ℕ} (il : 64 ≤ i) : Nat.testBit x.toNat i = false := by simp_all

-- Simplification lemmas for shift results
@[local simp] lemma p64 : (64 : UInt64).toNat = 64 := rfl
@[local simp] lemma p127 : (127 : UInt64).toNat = 127 := rfl
@[local simp] lemma p128 : (128 : UInt64).toNat = 128 := rfl
@[local simp] lemma p64s : (2^64 - 1 : UInt64).toNat = 2^64 - 1 := rfl
@[local simp] lemma ts0 {t : ℕ} (h : t < 64) : t < UInt64.size := lt_trans h (by norm_num)
@[local simp] lemma ts1 {t : ℕ} (h : t < 128) : t < UInt64.size := lt_trans h (by norm_num)
@[local simp] lemma shift0 {t : ℕ} (t0 : t ≠ 0) (t64 : t < 64) :
    (64 - (t : UInt64)).toNat % 64 = 64 - t := by
  rw [UInt64.toNat_sub]
  · norm_num
    simp only [p64, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts0 t64), ge_iff_le,
      Nat.mod_succ_eq_iff_lt]
    exact Nat.sub_lt (by norm_num) (Nat.pos_iff_ne_zero.mpr t0)
  · simp only [UInt64.le_iff_toNat_le, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts0 t64)]
    exact t64.le
@[local simp] lemma t127 {t : ℕ} (h : t < 128) : t &&& 127 = t := by
  nth_rw 2 [←Nat.mod_eq_of_lt h]; exact @Nat.land_eq_mod _ 7
@[local simp] lemma t127' {t : ℕ} (h : t < 128) : (t : UInt64) &&& 127 = ↑t := by
  simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_land, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts1 h),
    p127, t127 h]
@[local simp] lemma e0 {t : ℕ} (t0 : t ≠ 0) (t64 : t < 64) :
    (64 - (t : UInt64)).toNat % 64 = 64 - t := by
  rw [UInt64.toNat_sub]
  · simp only [p64, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts0 t64), ge_iff_le,
      Nat.mod_succ_eq_iff_lt]
    exact Nat.sub_lt (by norm_num) (Nat.pos_iff_ne_zero.mpr t0)
  · simp only [UInt64.le_iff_toNat_le, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts0 t64)]
    exact t64.le
@[local simp] lemma e1 {t : ℕ} (h : t < 64) : 64 - (64 - t) = t := Nat.sub_sub_self h.le
@[local simp] lemma e2 {t i : ℕ} (h : t < 64) : i - (64 - t) = i + t - 64 := by
  rw [Nat.sub_sub_assoc h.le]
@[local simp] lemma e3 {t : ℕ} (t64 : 64 ≤ t) (t128 : t < 128) :
    ((t : UInt64) - 64).toNat % 64 = t - 64 := by
  rw [UInt64.toNat_sub, p64, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts1 t128), Nat.mod_eq_of_lt]
  · omega
  · rw [UInt64.le_iff_toNat_le]
    simpa only [p64, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts1 t128)]
@[local simp] lemma e4 {t i : ℕ} (h : 64 ≤ t) : i + (t - 64) = i + t - 64 := by
  rw [Nat.add_sub_assoc h]
@[local simp] lemma e6 {t : ℕ} (t0 : t ≠ 0) (t64 : t < 64) :
    (64 - (t : UInt64)).toNat % 64 = 64 - t := by
  have t0' := Nat.pos_of_ne_zero t0
  rw [UInt64.toNat_sub, p64, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts0 t64), Nat.mod_eq_of_lt]
  · omega
  · rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_cast, Nat.mod_eq_of_lt (ts0 t64), p64, t64.le]
@[local simp] lemma e7 {t i : ℕ} (hi : 64 ≤ i) (ht : t < 64) : i - 64 + (64 - t) = i - t := by omega
@[local simp] lemma e8 {t i : ℕ} (ht : 64 ≤ t) : i - 64 - (t - 64) = i - t := by omega
@[local simp] lemma e9 {t : ℕ} (h : t < 128) : (128 - (t : UInt64)).toNat = 128 - t := by
  rw [UInt64.toNat_sub, p128, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts1 h)]
  simp only [UInt64.le_iff_toNat_le, UInt64.toNat_cast, Nat.mod_eq_of_lt (ts1 h), p128, h.le]
@[local simp] lemma e10 : (128 : UInt64) &&& 127 = 0 := rfl
@[local simp] lemma a1 {t i : ℕ} (t0 : t ≠ 0) (i64 : i < 64) : i + t - 64 < t := by
  simp only [add_comm _ t, Nat.add_sub_eq_sub_sub i64.le, imp_false, not_le]
  apply Nat.sub_lt (Nat.pos_of_ne_zero t0) (Nat.sub_pos_of_lt i64)
@[local simp] lemma a2 {x : UInt128} {t : ℕ} {x0 : x ≠ 0} (h : 128 ≤ t) :
    ¬x.toNat * 2^t ≤ 2 ^ 128 - 1 := by
  replace x0 : 0 < x.toNat := by
    simpa only [ne_eq, UInt128.eq_iff_toNat_eq, UInt128.toNat_zero, ← Nat.pos_iff_ne_zero] using x0
  replace h : 2^128 ≤ 2^t := Nat.pow_le_pow_right (by norm_num) h
  exact not_le.mpr (lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul (Nat.succ_le.mpr x0) h))
@[local simp] lemma a4 {t i : ℕ} (hi : i < 64) (ht : 64 ≤ t) : ¬t ≤ i := by omega
@[local simp] lemma a5 {t i : ℕ} (hi : i < 64) (ti : t < 64) : i - t < 64 - t := by omega

/-- `shiftLeft` is multiplication mod 2^128. -/
lemma UInt128.toNat_shiftLeft (x : UInt128) {s : UInt64} (sl : s < 128) :
    (x.shiftLeft s).toNat = x.toNat * 2^s.toNat % 2^128 := by
  generalize ht : s.toNat = t
  have st : s = (t : UInt64) := by rw [←ht, UInt64.cast_toNat]
  have t64' : t < UInt64.size := by rw [←ht]; exact UInt64.toNat_lt_2_pow_64 _
  simp only [st, UInt64.lt_iff_toNat_lt, UInt64.toNat_cast, Nat.mod_eq_of_lt t64', p128, st] at sl ⊢
  clear st ht s
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [shiftLeft, UInt64.land_eq_hand, t127' sl, UInt64.lt_iff_toNat_lt, UInt64.toNat_cast,
    Nat.mod_eq_of_lt t64', p64, bif_eq_if, beq_iff_eq, UInt64.eq_iff_toNat_eq,
    UInt64.toNat_zero, testBit_eq, apply_ite (f := UInt64.toNat), UInt64.toNat_shiftLeft',
    apply_ite (f := fun x ↦ Nat.testBit x i), Nat.testBit_mul_two_pow, Nat.testBit_mod_two_pow,
    Bool.and_eq_true, Nat.zero_testBit, UInt64.toNat_lor, decide_eq_true_iff, Bool.decide_and,
    UInt64.toNat_shiftRight', Bool.ite_eq_true_distrib, Bool.and_true, Bool.and_false,
    Bool.decide_coe, decide_and_eq_if', apply_decide, Bool.and_true, Bool.and_false]
  split_ifs
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · omega
  · simp_all
  · rfl
  · omega
  · rfl
  · rfl
  · simp_all
  · omega
  · omega
  · omega
  · omega
  · simp_all
  · rfl
  · omega
  · rfl
  · rfl
  · simp_all
  · simp_all
  · omega
  · rfl
  · rfl
  · simp_all
  · omega
  · simp_all
  · simp_all
  · apply tb_false; omega
  · simp_all; omega
  · simp_all; omega
  · simp_all [tsub_right_comm, apply_decide]; split_ifs; repeat omega
  · simp_all [tsub_right_comm]
  · simp_all; constructor; omega; apply tb_false; omega
  · simp_all [apply_decide]; split_ifs
    · omega
    · omega
    · intro; omega
  · simp_all
  · simp_all; omega
  · simp_all
  · simp_all; omega

/-- Shifting left by zero does nothing -/
@[simp] lemma UInt128.shiftLeft_zero (x : UInt128) : x.shiftLeft 0 = x := by
  have h : (0 : UInt64) < 64 := by decide
  simp only [shiftLeft, UInt64.land_eq_hand, UInt64.zero_land, h, decide_True,
    UInt64.shiftLeft_zero, cond_true, beq_self_eq_true, sub_zero, zero_sub]

/-- Shifting zero does nothing -/
@[simp] lemma UInt128.zero_shiftLeft (s : UInt64) : (0 : UInt128).shiftLeft s = 0 := by
  simp only [shiftLeft, UInt64.land_eq_hand, zero_lo, UInt64.zero_shiftLeft, Bool.cond_self,
    zero_hi, UInt64.zero_shiftRight, UInt64.zero_or, UInt128.ext_iff, and_self]

/-- `shiftRight` rounds down -/
lemma UInt128.toNat_shiftRight (x : UInt128) {s : UInt64} (sl : s < 128) :
    (x.shiftRight s).toNat = x.toNat / 2^s.toNat := by
  generalize ht : s.toNat = t
  have st : s = (t : UInt64) := by rw [←ht, UInt64.cast_toNat]
  have t64' : t < UInt64.size := by rw [←ht]; exact UInt64.toNat_lt_2_pow_64 _
  simp only [st, UInt64.lt_iff_toNat_lt, UInt64.toNat_cast, Nat.mod_eq_of_lt t64', p128, st] at sl ⊢
  clear st ht s
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  simp only [UInt128.shiftRight, UInt128.testBit_eq, bif_eq_if, beq_iff_eq, decide_eq_true_eq,
    apply_ite (f := UInt64.toNat), apply_ite (f := fun x ↦ Nat.testBit x i),
    apply_ite (f := fun x ↦ Nat.testBit x (i - 64)),
    UInt64.toNat_shiftRight', UInt64.toNat_lor, Nat.testBit_lor, Nat.testBit_div_two_pow,
    Nat.testBit_mul_two_pow, UInt64.toNat_shiftLeft', Nat.testBit_mod_two_pow, apply_decide,
    UInt64.land_eq_hand, UInt64.eq_iff_toNat_eq, UInt64.toNat_zero, UInt64.toNat_land, p127,
    UInt64.toNat_cast, Nat.mod_eq_of_lt t64', UInt64.lt_iff_toNat_lt, t127, p64, Bool.or_true,
    Bool.or_false, Nat.testBit_zero', t127' sl]
  split_ifs
  · apply tb_eq; omega
  · simp_all
  · simp_all
  · simp_all
  · apply tb_eq; omega
  · simp_all
  · simp_all; linarith
  · simp_all
  · simp_all; apply tb_ne; omega; omega
  · simp_all; apply tb_eq; omega
  · apply false_tb; omega
  · apply false_tb; omega

lemma UInt128.coe_shiftRight (x : UInt128) {s : UInt64} (sl : s < 128) :
    (x.shiftRight s : ℝ) = ↑(x.toNat / 2^s.toNat) := by
  rw [UInt128.toReal, UInt128.toNat_shiftRight _ sl]

/-- `shiftRightRound` rounds as desired -/
lemma UInt128.approx_shiftRightRound (x : UInt128) (s : UInt64) (up : Bool) :
    (x.shiftRightRound s up : ℝ) ∈ rounds {(x : ℝ) / (2:ℝ)^s.toNat} up := by
  have cp : (2:ℝ) ^ s.toNat = ((2:ℕ) ^ s.toNat : ℕ) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have z2 : ∀ {n}, (2:ℝ) ^ n ≠ 0 := fun {_} ↦ pow_ne_zero _ (by norm_num)
  simp only [shiftRightRound, bif_eq_if, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases s0 : s = 0
  · simp only [s0, ite_false, ite_true, UInt64.toNat_zero, pow_zero, div_one, mem_rounds_singleton,
      le_refl, ite_self]
  · simp only [s0, ite_false]
    have s1 : 1 ≤ s.toNat := by
      rw [UInt64.eq_iff_toNat_eq] at s0
      exact Nat.one_le_iff_ne_zero.mpr s0
    by_cases s128 : 128 ≤ s
    · simp only [s128, ite_true]
      by_cases x0 : x = 0
      · simp only [x0, true_or, ite_true, toReal_zero, zero_div, mem_rounds_singleton, le_refl,
          ite_self]
      · simp only [x0, false_or]
        have z : (x:ℝ) / (2:ℝ) ^ UInt64.toNat s < 1 := by
          rw [div_lt_one (pow_pos two_pos _)]
          refine lt_of_lt_of_le (UInt128.coe_lt_size _) ?_
          have e : UInt64.toNat 128 = 128 := rfl
          rw [UInt64.le_iff_toNat_le, e] at s128
          exact pow_right_mono (by norm_num) s128
        by_cases u : up
        · simp only [u, ite_false, toReal_one, mem_rounds_singleton, ite_true, z.le]
        · simp only [u, ite_true, toReal_zero, mem_rounds_singleton, ite_false, ge_iff_le]
          exact div_nonneg (coe_nonneg _) (pow_nonneg (by norm_num) _)
    · simp only [s128, ite_false, mem_rounds_singleton]
      simp only [not_le] at s128
      by_cases u : up
      · simp only [u, true_and, ite_not, apply_ite, ite_true]
        by_cases lh : x = (x.shiftRight s).shiftLeft s
        · simp only [← lh, ite_true, ge_iff_le]
          have lt : x.toNat / 2 ^ s.toNat * 2 ^ s.toNat < 2^128 :=
            lt_of_le_of_lt (Nat.div_mul_le_self _ _) (UInt128.lt_size _)
          simp only [UInt128.eq_iff_toNat_eq, UInt128.toNat_shiftLeft _ s128,
            UInt128.toNat_shiftRight _ s128, UInt128.toReal, Nat.mod_eq_of_lt lt] at lh ⊢
          nth_rw 1 [lh]
          simp only [Nat.cast_mul, Nat.isUnit_iff, Nat.cast_pow, Nat.cast_ofNat, ne_eq,
            mul_div_cancel _ z2, le_refl]
        · have nt : (x.shiftRight s).toNat ≠ 2^128-1 := by
            rw [UInt128.toNat_shiftRight _ s128]
            apply ne_of_lt
            apply lt_of_le_of_lt (Nat.div_le_div_right (UInt128.lt_size _).le)
            refine lt_of_le_of_lt (Nat.div_le_div_left (pow_right_mono one_le_two s1) two_pos) ?_
            norm_num
          simp only [lh, toReal._eq_1, UInt128.toNat_shiftRight _ s128, Nat.isUnit_iff,
            UInt128.toNat_succ nt, Nat.cast_add, Nat.cast_one, ite_false, ge_iff_le]
          rw [cp]
          apply Nat.cast_div_le_div_add_one
      · simp only [u, toReal, false_and, ite_false, UInt128.toNat_shiftRight _ s128,
          Nat.isUnit_iff, ge_iff_le]
        rw [le_div_iff (pow_pos two_pos _), cp, ←Nat.cast_mul, Nat.cast_le]
        apply Nat.div_mul_le_self

lemma UInt128.toNat_shiftLeftSaturate {x : UInt128} {s : UInt64}
    : (x.shiftLeftSaturate s).toNat = min (x.toNat * 2^s.toNat) UInt128.max.toNat := by
  generalize ht : s.toNat = t
  have st : s = (t : UInt64) := by rw [←ht, UInt64.cast_toNat]
  have t64 : t < UInt64.size := by rw [←ht]; exact UInt64.toNat_lt_2_pow_64 _
  have x128 : x.toNat < 2^128 := x.lt_size
  simp only [st, toNat_max]
  clear st ht s
  by_cases t0 : t = 0
  · simp only [shiftLeftSaturate, t0, Nat.cast_zero, (by decide : ¬128 ≤ (0 : UInt64)),
      decide_False, Bool.false_and, bne_self_eq_false, sub_zero, Bool.or_self, shiftLeft_zero,
      cond_false, pow_zero, mul_one]
    rw [min_eq_left (by omega)]
  by_cases t128 : t < 128
  · have t128' : (t : UInt64) < 128 := by
      simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_cast, Nat.mod_eq_of_lt t64, p128]
    have sub : 128 - (t : UInt64) < 128 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub t128'.le, p128, UInt64.toNat_cast,
        Nat.mod_eq_of_lt t64]
      omega
    simp only [shiftLeftSaturate, UInt64.le_iff_toNat_le, p128, UInt64.toNat_cast, t128, ts1,
      Nat.mod_eq_of_lt, not_le.mpr t128, decide_False, Bool.false_and, Bool.false_or, bif_eq_if,
      Bool.and_eq_true, bne_iff_ne, ne_eq, UInt64.eq_iff_toNat_eq, UInt64.toNat_zero, t0,
      not_false_eq_true, eq_iff_toNat_eq, UInt128.toNat_shiftRight _ sub, e9, toNat_zero,
      gt_iff_lt, zero_lt_two, pow_pos, Nat.div_eq_zero_iff, not_lt, true_and,
      apply_ite (f := fun x : UInt128 ↦ x.toNat), toNat_max, UInt128.toNat_shiftLeft _ t128',
      ge_iff_le, min_eq_left, if_false]
    split_ifs with c
    · rw [min_eq_right]
      refine le_trans ?_ (Nat.mul_le_mul_right _ c)
      simp only [← pow_add, Nat.sub_add_cancel t128.le]
      norm_num
    · simp only [not_le] at c
      replace c : x.toNat * 2 ^ t < 2 ^ 128 := by
        refine lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right c ?_) ?_
        · exact pow_pos (by norm_num) _
        · simp only [← pow_add, Nat.sub_add_cancel t128.le, le_refl]
      rw [Nat.mod_eq_of_lt c, min_eq_left (by omega)]
  · simp only [not_lt] at t128
    have t128' : 128 ≤ (t : UInt64) := by
      simpa only [UInt64.le_iff_toNat_le, p128, UInt64.toNat_cast, Nat.mod_eq_of_lt t64]
    simp only [shiftLeftSaturate, t128', decide_True, bif_eq_if, ite_true, bne_iff_ne, ne_eq,
      ite_not]
    split_ifs with x0
    · simp only [x0, zero_shiftLeft, toNat_zero, zero_mul, ge_iff_le, zero_le, min_eq_left]
    · rw [min_eq_right]
      · decide
      · have x1 : 1 ≤ x.toNat := by
          simp only [eq_iff_toNat_eq, toNat_zero] at x0
          omega
        exact le_trans (by norm_num) (Nat.mul_le_mul x1 (pow_right_mono (by norm_num) t128))

lemma UInt128.shiftLeftSaturate_eq {x : UInt128} {s : UInt64}
    : x.shiftLeftSaturate s = .ofNat (min (x.toNat * 2^s.toNat) UInt128.max.toNat) := by
  simp only [ge_iff_le, eq_iff_toNat_eq, toNat_shiftLeftSaturate, toNat_ofNat]
  rw [Nat.mod_eq_of_lt]; apply min_lt_of_right_lt; rw [toNat_max]; norm_num
