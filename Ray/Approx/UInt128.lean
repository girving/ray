import Mathlib.Data.Real.Archimedean
import Ray.Approx.Approx
import Ray.Approx.UInt64
import Ray.Misc.Int

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

@[irreducible, pp_dot] def UInt128.toNat (x : UInt128) : ℕ :=
  (x.hi.toNat <<< 64) + x.lo.toNat

@[coe] def UInt128.toReal (x : UInt128) : ℝ := x.toNat

instance : Coe UInt128 ℝ where
  coe := UInt128.toReal

@[simp] lemma UInt128.toNat_zero : (0 : UInt128).toNat = 0 := by rw [toNat]; rfl
@[simp] lemma UInt128.toNat_one : (1 : UInt128).toNat = 1 := by rw [toNat]; rfl
@[simp] lemma UInt128.zero_lo : (0 : UInt128).lo = 0 := rfl
@[simp] lemma UInt128.zero_hi : (0 : UInt128).hi = 0 := rfl
@[simp] lemma UInt128.max_lo : UInt128.max.lo = UInt64.max := rfl
@[simp] lemma UInt128.max_hi : UInt128.max.hi = UInt64.max := rfl
lemma UInt128.max_eq_pow_sub_one : UInt128.max.toNat = 2^128 - 1 := by rw [toNat]; rfl
lemma UInt128.toNat_def {x : UInt128} : x.toNat = (x.hi.toNat * 2^64) + x.lo.toNat := by
  rw [toNat, Nat.shiftLeft_eq]

@[simp] lemma UInt128.toReal_zero : ((0 : UInt128) : ℝ) = 0 := by
  simp only [toReal, toNat_zero, CharP.cast_eq_zero]

@[simp] lemma UInt128.toReal_one : ((1 : UInt128) : ℝ) = 1 := by
  simp only [toReal, toNat_one, Nat.cast_one]

lemma UInt128.lt_size (x : UInt128) : x.toNat < 2^128 := by
  have e : 2^128 = (2^64 - 1)*2^64 + 2^64 := by norm_num
  rw [e, toNat, Nat.shiftLeft_eq]
  refine Nat.add_lt_add'' (Nat.mul_le_mul_right _ ?_) (UInt64.lt_size _)
  exact Nat.le_pred_of_lt (UInt64.lt_size _)

lemma UInt128.coe_nonneg (x : UInt128) : 0 ≤ (x : ℝ) := by
  simp only [toReal, Nat.cast_nonneg]

lemma UInt128.coe_lt_size (x : UInt128) : (x : ℝ) < (2:ℝ)^128 := by
  refine lt_of_lt_of_le (b := ((2^128 : ℕ) : ℝ)) ?_ (by norm_num)
  simp only [toReal, Nat.cast_lt, UInt128.lt_size]

noncomputable instance {n : ℕ} : CoeTail UInt128 (ZMod n) where
  coe x := x.toNat

@[simp] lemma UInt128.toNat_max : UInt128.max.toNat = 2^128 - 1 := by rw [toNat]; rfl

@[simp] lemma Nat.mod_mul_eq_mul_mod_128 (a : ℕ) : a * 2^64 % 2^128 = a % 2^64 * 2^64 :=
  Nat.mod_mul_eq_mul_mod _ _

@[simp] lemma UInt128.toNat_mod_pow_eq_lo (x : UInt128) : x.toNat % 2^64 = x.lo.toNat := by
  simp only [toNat, Nat.shiftLeft_eq, ←UInt64.size_eq_pow, Nat.add_mod, Nat.mul_mod_left,
    UInt64.toNat_mod_size, zero_add]

@[simp] lemma UInt128.toNat_div_pow_eq_hi (x : UInt128) : x.toNat / 2^64 = x.hi.toNat := by
  simp only [toNat, Nat.shiftLeft_eq, ← UInt64.size_eq_pow, UInt64.size_pos, Nat.add_div,
    Nat.mul_div_left, Nat.div_eq_zero_of_lt (UInt64.lt_size _), add_zero, Nat.mul_mod_left,
    UInt64.toNat_mod_size, zero_add, add_right_eq_self, ite_eq_right_iff, imp_false, not_le,
    UInt64.lt_size]

lemma UInt128.eq_iff_toNat_eq (x y : UInt128) : x = y ↔ x.toNat = y.toNat := by
  constructor
  · intro h; rw [h]
  · intro h; ext
    · rw [←UInt128.toNat_mod_pow_eq_lo x, ←UInt128.toNat_mod_pow_eq_lo y, h]
    · rw [←UInt128.toNat_div_pow_eq_hi x, ←UInt128.toNat_div_pow_eq_hi y, h]

lemma UInt128.eq_zero_iff (x : UInt128) : x = 0 ↔ x.toNat = 0 := by
  simp only [←toNat_zero, ←UInt128.eq_iff_toNat_eq]

lemma UInt128.ne_zero_iff (x : UInt128) : x ≠ 0 ↔ x.toNat ≠ 0 := by
  simp only [Ne.def, ←eq_zero_iff]

@[simp] lemma UInt128.toNat_lo {x : UInt128} (h : x.toNat < 2^64) : x.lo.toNat = x.toNat := by
  rw [toNat_def] at h ⊢; norm_num; linarith

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

@[simp] lemma UInt128.toNat_lt (x : UInt128) : x.toNat < 2^128 := by
  simp only [toNat_def]
  have h0 := x.lo.toNat_lt
  have h1 := x.hi.toNat_lt
  norm_num only at h0 h1 ⊢
  omega

/-!
### Wrap around conversion from `ℕ, ℤ` to `UInt128`
-/

@[irreducible] def UInt128.ofNat (x : ℕ) : UInt128 where
  lo := x
  hi := (x / 2^64 : ℕ)

@[irreducible] def UInt128.ofInt (x : ℤ) : UInt128 where
  lo := x
  hi := (x / 2^64 : ℤ)

@[simp] lemma UInt128.toNat_ofNat (x : ℕ) : (UInt128.ofNat x).toNat = x % 2^128 := by
  generalize hn : 2^64 = n
  have nn : 2^128 = n^2 := by rw [←hn]; norm_num
  rw [ofNat]
  simp only [toNat, Nat.shiftLeft_eq, hn, UInt64.toNat_cast, UInt64.size_eq_pow, nn]
  apply Nat.div_mod_mul_add_mod_eq

@[simp] lemma UInt128.ofInt_toInt (x : UInt128) : .ofInt (x.toNat : ℤ) = x := by
  rw [toNat_def, ofInt, UInt128.ext_iff]
  have ep : (2 : ℤ)^64 = (2^64 : ℕ) := by norm_num
  have p0 : 0 < 2^64:= by norm_num
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, UInt64.cast_toNat, Int.cast_pow, Int.int_cast_ofNat, add_left_eq_self,
    UInt64.pow_eq_zero, mul_zero, true_and, UInt64.eq_iff_toNat_eq]
  simp only [ep, ←Nat.cast_mul, ←Nat.cast_add, ←Int.coe_nat_div, Nat.add_div p0,
    Nat.mul_div_cancel _ p0, Nat.mul_mod_left, zero_add, not_le.mpr (Nat.mod_lt _ p0),
    if_false, add_zero, Nat.div_eq_of_lt x.lo.toNat_lt, Int.cast_ofNat, UInt64.cast_toNat]

@[simp] lemma UInt128.toInt_ofInt (x : ℤ) : ((UInt128.ofInt x).toNat : ℤ) = x % 2^128 := by
  generalize hnn : (2:ℤ)^128 = nn
  generalize hn : (2:ℤ)^64 = n
  have n0 : 0 < n := by rw [←hn]; norm_num
  have s : nn = n^2 := by rw [←hn, ←hnn]; norm_num
  rw [ofInt]
  simp only [hn, toNat_def, Nat.cast_add, Nat.cast_mul, UInt64.toInt_intCast, Nat.cast_pow,
    Nat.cast_ofNat, s]
  rw [←Int.ediv_add_emod x n]
  generalize x / n = a
  generalize hb : x % n = b
  have b0 : 0 ≤ b := by rw [←hb]; exact Int.emod_nonneg _ n0.ne'
  have bn : b < n := by rw [←hb]; convert Int.emod_lt _ n0.ne'; rw [abs_of_nonneg n0.le]
  have an0 : 0 ≤ a % n * n := mul_nonneg (Int.emod_nonneg _ n0.ne') n0.le
  have ba0 : 0 ≤ b + a % n * n := add_nonneg b0 an0
  have ban : b + a % n * n < n^2 := by
    refine lt_of_le_of_lt (add_le_add (Int.le_sub_one_iff.mpr bn)
      (mul_le_mul_of_nonneg_right (Int.le_sub_one_iff.mpr (Int.emod_lt a n0.ne')) n0.le)) ?_
    simp only [abs_of_nonneg n0.le, sub_mul, one_mul, sub_add_sub_cancel', pow_two, sub_lt_self_iff,
      zero_lt_one]
  have bnn : b < n^2 := lt_of_le_of_lt (le_add_of_nonneg_right an0) ban
  have ann : a % n * n < n^2 := lt_of_le_of_lt (le_add_of_nonneg_left b0) ban
  simp only [mul_comm n, add_comm _ b, Int.add_mul_ediv_right _ _ n0.ne',
    Int.ediv_eq_zero_of_lt b0 bn, zero_add, Int.add_emod, Int.emod_eq_of_lt b0 bn,
    Int.mul_emod_left, add_zero, Int.emod_eq_of_lt b0 bnn, Int.emod_mul_eq_mul_emod _ _ n0,
    dvd_refl, Int.emod_emod_of_dvd]
  rw [Int.emod_eq_of_lt b0 bnn, Int.emod_eq_of_lt an0 ann, Int.emod_eq_of_lt ba0 ban]

@[simp] lemma UInt128.ofInt_zero : UInt128.ofInt 0 = 0 := by native_decide
@[simp] lemma UInt128.ofInt_pow : UInt128.ofInt (2^128) = 0 := by native_decide

/-!
### 128-bit increment
-/

@[irreducible] def UInt128.succ (x : UInt128) : UInt128 :=
  let lo := x.lo + 1
  { lo := lo
    hi := x.hi + bif lo == 0 then 1 else 0 }

@[simp] lemma UInt128.succ_max : max.succ = 0 := by
  rw [max, succ]; rfl

lemma UInt128.toNat_succ {x : UInt128} (h : x.toNat ≠ 2^128-1) : x.succ.toNat = x.toNat+1 := by
  have e : (2:UInt64)^64 = 0 := by rfl
  rw [succ]
  by_cases ll : x.lo = (2:UInt64)^64-1
  · simp only [ll, e, zero_sub, add_left_neg, beq_self_eq_true, cond_true]
    by_cases hh : x.hi = (2:UInt64)^64-1
    · simp only [toNat_def, hh, ll, ge_iff_le, ne_eq] at h; contrapose h; decide
    · simp only [UInt64.eq_iff_toNat_eq] at hh
      simp only [toNat, Nat.shiftLeft_eq, UInt64.toNat_add_one hh, add_mul, one_mul,
        UInt64.toNat_zero, add_zero, ll]
      have c : (UInt64.toNat ((2:UInt64) ^ 64 - 1) : ℤ) = (2:ℤ)^64-1 := by rfl
      zify; rw [c]; ring
  · simp only [UInt64.eq_iff_toNat_eq] at ll
    simp only [toNat, bif_eq_if, beq_iff_eq, UInt64.eq_iff_toNat_eq, UInt64.toNat_add_one ll,
      UInt64.toNat_zero, add_eq_zero, and_false, ite_false, add_zero]
    ring

lemma UInt128.toNat_succ' (x : UInt128) :
    x.succ.toNat = (if x.toNat = 2^128-1 then 0 else x.toNat + 1) := by
  split_ifs with h
  · have e : x = max := by rwa [eq_iff_toNat_eq, toNat_max]
    simp only [e, succ_max, toNat_zero]
  · exact toNat_succ h

lemma UInt128.coe_succ {x : UInt128} (h : (x:ℝ) ≠ (2:ℝ)^128-1) : (x.succ : ℝ) = x+1 := by
  rw [toReal, toReal, toNat_succ, Nat.cast_add_one]
  contrapose h; simp only [ge_iff_le, ne_eq, not_not] at h
  simp only [toReal, h, ge_iff_le, Nat.cast_sub, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    ne_eq, not_true, not_false_eq_true, not_not]
  norm_num

/-!
### Complement
-/

instance : Complement UInt128 where
  complement x := ⟨~~~x.lo, ~~~x.hi⟩

lemma UInt128.complement_def (x : UInt128) : ~~~x = ⟨~~~x.lo, ~~~x.hi⟩ := rfl
@[simp] lemma UInt128.complement_zero : ~~~(0 : UInt128) = UInt128.max := by decide

lemma UInt128.toNat_complement {x : UInt128} : (~~~x).toNat = 2^128 - 1 - x.toNat := by
  simp only [toNat_def, complement_def, UInt64.toNat_complement]
  have h0 := x.lo.toNat_lt
  have h1 := x.hi.toNat_lt
  norm_num only at h0 h1 ⊢
  omega

/-!
### Twos complement negation
-/

instance : Neg UInt128 where
  neg x := (~~~x).succ

lemma UInt128.neg_def (x : UInt128) : -x = (~~~x).succ := rfl

@[simp] lemma UInt128.neg_zero : -(0 : UInt128) = 0 := by
  simp only [neg_def, complement_zero, succ_max]

lemma UInt128.toNat_neg (x : UInt128) : (-x).toNat = if x = 0 then 0 else 2^128 - x.toNat := by
  by_cases x0 : x = 0
  · simp only [x0, neg_zero, toNat_zero, tsub_zero, ite_true]
  · simp only [neg_def, x0, ite_false]
    have h := x.toNat_lt
    rw [toNat_succ]
    · simp only [toNat_complement]
      omega
    · contrapose x0
      simp only [toNat_complement, ne_eq, not_not, eq_iff_toNat_eq, toNat_zero] at x0 ⊢
      omega

/-- `ofInt` commutes with `-` -/
@[simp] lemma UInt128.neg_ofInt (x : ℤ) : -(UInt128.ofInt x) = .ofInt (-x) := by
  generalize hn : (2 : ℤ)^128 = n
  have n0 : 0 < n := by rw [←hn]; norm_num
  simp only [eq_iff_toNat_eq, toNat_neg, toNat_zero, ← Nat.cast_inj (R := ℤ), toInt_ofInt, hn,
    CharP.cast_eq_zero, Nat.cast_ite, Nat.cast_sub (UInt128.toNat_lt _).le, Nat.cast_pow,
    Nat.cast_ofNat, Int.neg_emod]
  clear hn
  rw [←Int.ediv_add_emod x n]
  generalize x / n = a
  generalize hb : x % n = b
  have b0 : 0 ≤ b := by rw [←hb]; exact Int.emod_nonneg _ n0.ne'
  have bn : b < n := by rw [←hb]; exact Int.emod_lt_of_pos _ n0
  have e : n - (b + n * a) = n - b + -a * n := by ring
  simp only [add_comm _ b, Int.add_mul_emod_self_left, Int.emod_eq_of_lt b0 bn, e,
    Int.add_mul_emod_self]
  split_ifs with b0
  · simp only [b0, sub_zero, Int.emod_self]
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]

/-!
### 128-bit addition and (twos complement) subtraction
-/

@[irreducible] def UInt128.add (x y : UInt128) : UInt128 :=
  let (x0,x1) := addc x.lo y.lo
  ⟨x0, x1 + x.hi + y.hi⟩

instance : Add UInt128 where
  add := UInt128.add

instance : Sub UInt128 where
  sub x y := x + -y

lemma UInt128.add_def (x y : UInt128) : x + y = .add x y := rfl
lemma UInt128.sub_def (x y : UInt128) : x - y = x + -y := rfl

/-- `add` is modular -/
lemma UInt128.toNat_add (x y : UInt128) : (x + y).toNat = (x.toNat + y.toNat) % 2^128 := by
  generalize hn : 2^64 = n
  have hnn : 2^128 = n^2 := by rw [←hn]; norm_num
  have n0 : 0 < n := by rw [←hn]; norm_num
  rw [add_def, add]
  rcases addc_eq x.lo y.lo with ⟨u, v, un, _, xyuv, e⟩
  generalize hz : v + x.hi.toNat + y.hi.toNat = z
  simp only [hn] at un xyuv
  have m0 : x.hi.toNat * n + x.lo.toNat + (y.hi.toNat * n + y.lo.toNat) =
      (x.hi.toNat + y.hi.toNat) * n + (x.lo.toNat + y.lo.toNat) := by ring
  have m1 : (x.hi.toNat + y.hi.toNat) * n + (v * n + u) = z * n + u := by rw [←hz]; ring
  simp only [toNat_def, UInt64.toNat_add, UInt64.size_eq_pow, hn, Nat.mod_add_mod, hnn, e,
    UInt64.toNat_cast, m0, xyuv, hz, Nat.mod_eq_of_lt un, m1, ← Nat.mod_mul_eq_mul_mod]
  have lt : z * n % n^2 + u < n^2 := by
    rw [Nat.mod_mul_eq_mul_mod]
    refine lt_of_le_of_lt (add_le_add (Nat.mul_le_mul_right _ (Nat.le_pred_of_lt
      (Nat.mod_lt _ n0))) (Nat.le_pred_of_lt un)) ?_
    generalize hk : n - 1 = k
    have nk : n = k + 1 := by omega
    simp only [nk, Nat.pred_succ, mul_add_one, pow_two, add_one_mul, add_lt_add_iff_left,
      lt_add_iff_pos_right, zero_lt_one]
  have un2 : u < n^2 := lt_of_le_of_lt (Nat.le_add_left _ _) lt
  rw [Nat.add_mod, Nat.mod_eq_of_lt un2, Nat.mod_eq_of_lt lt]

/-- `ofInt` commutes with `+` -/
@[simp] lemma UInt128.add_ofInt (x y : ℤ) : UInt128.ofInt x + .ofInt y = .ofInt (x + y) := by
  simp only [eq_iff_toNat_eq, toNat_add, ← Nat.cast_inj (R := ℤ), Int.ofNat_emod, Nat.cast_add,
    toInt_ofInt, Nat.cast_pow, Nat.cast_ofNat, Int.add_emod_emod, Int.emod_add_emod]

/-- `ofInt` commutes with `-` -/
@[simp] lemma UInt128.sub_ofInt (x y : ℤ) : UInt128.ofInt x - .ofInt y = .ofInt (x - y) := by
  simp only [sub_def, neg_ofInt, add_ofInt, sub_eq_add_neg]

/-- `UInt128` inherits the additive group structure from `ℤ` -/
instance : AddCommGroup UInt128 where
  add_assoc x y z := by
    rw [←UInt128.ofInt_toInt x, ←UInt128.ofInt_toInt y, ←UInt128.ofInt_toInt z]
    simp only [UInt128.add_ofInt, add_assoc]
  zero_add x := by
    rw [←UInt128.ofInt_zero, ←UInt128.ofInt_toInt x]
    simp only [UInt128.add_ofInt, zero_add]
  add_zero x := by
    rw [←UInt128.ofInt_zero, ←UInt128.ofInt_toInt x]
    simp only [UInt128.add_ofInt, add_zero]
  add_left_neg x := by
    rw [←UInt128.ofInt_toInt x]
    simp only [UInt128.neg_ofInt, UInt128.add_ofInt, add_left_neg, UInt128.ofInt_zero]
  add_comm x y := by
    rw [←UInt128.ofInt_toInt x, ←UInt128.ofInt_toInt y]
    simp only [UInt128.add_ofInt, add_comm]

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
  lt_of_lt_of_le (Nat.mul_lt_mul_of_le_of_lt xl.le yl (by norm_num)) (by norm_num)

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
  simp only [a13e, UInt128.toNat, Nat.shiftLeft_eq]
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
  · exact lt_of_lt_of_le (Nat.mul_lt_mul_of_le_of_lt (UInt64.lt_size _).le (UInt64.lt_size _)
      UInt64.size_pos) (by norm_num)
  · exact UInt128.lt_size _

/-!
### 128 bit shifting
-/

/-- Multiply by `2^(s % 128)`, discarding overflow bits -/
@[irreducible, pp_dot] def UInt128.shiftLeft (x : UInt128) (s : UInt64) : UInt128 :=
  let s := s.land 127
  { lo := bif s < 64 then x.lo <<< s else 0
    hi := bif s == 0 then x.hi
          else bif s < 64 then x.hi <<< s ||| x.lo >>> (64-s)
          else x.lo <<< (s - 64) }

/-- Divide by `2^(s % 128)`, rounding down -/
@[irreducible, pp_dot] def UInt128.shiftRight (x : UInt128) (s : UInt64) : UInt128 :=
  let s := s.land 127
  { lo := bif s == 0 then x.lo
          else bif s < 64 then x.lo >>> s ||| x.hi <<< (64-s)
          else x.hi >>> (s - 64)
    hi := bif s < 64 then x.hi >>> s else 0 }

instance : HShiftLeft UInt128 UInt64 UInt128 where
  hShiftLeft x s := x.shiftLeft s

instance : HShiftRight UInt128 UInt64 UInt128 where
  hShiftRight x s := x.shiftRight s

lemma UInt128.shiftLeft_def (x : UInt128) (s : UInt64) : x <<< s = x.shiftLeft s := rfl
lemma UInt128.shiftRight_def (x : UInt128) (s : UInt64) : x >>> s = x.shiftRight s := rfl

/-- Divide by `2^s`, rounding up or down -/
@[irreducible, pp_dot] def UInt128.shiftRightRound (x : UInt128) (s : UInt64) (up : Bool) :
    UInt128 :=
  bif s == 0 then x
  else bif 128 ≤ s then bif x == 0 || !up then 0 else 1
  else
    let y := x >>> s
    bif up && x != y <<< s then y.succ else y

 /-- Multiply by `2^s`, saturating at `UInt128.max` if we overflow -/
@[irreducible, pp_dot] def UInt128.shiftLeftSaturate (x : UInt128) (s : UInt64) : UInt128 :=
  bif bif 128 ≤ s then x != 0 else s != 0 && x >>> (128-s) != 0 then UInt128.max
  else x <<< s

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
  rw [UInt128.toNat, Nat.shiftLeft_eq, ←Nat.lor_eq_add]
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
    (x <<< s).toNat = x.toNat * 2^s.toNat % 2^128 := by
  generalize ht : s.toNat = t
  have st : s = (t : UInt64) := by rw [←ht, UInt64.cast_toNat]
  have t64' : t < UInt64.size := by rw [←ht]; exact UInt64.toNat_lt_2_pow_64 _
  simp only [st, UInt64.lt_iff_toNat_lt, UInt64.toNat_cast, Nat.mod_eq_of_lt t64', p128, st] at sl ⊢
  clear st ht s
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  rw [shiftLeft_def, shiftLeft]
  simp only [UInt64.land_eq_hand, t127' sl, UInt64.lt_iff_toNat_lt, UInt64.toNat_cast,
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

/-- `shiftLeft` is multiplication mod 2^128. -/
lemma UInt128.toNat_shiftLeft' (x : UInt128) {s : UInt64} :
    (x <<< s).toNat = x.toNat * 2^(s.toNat % 128) % 2^128 := by
  have e : (s % 128).land 127 = s.land 127 := by
    have e : ∀ n : ℕ, n &&& 127 = n % 128 := fun _ ↦ Nat.land_eq_mod (k := 7)
    simp only [UInt64.land_eq_hand, UInt64.eq_iff_toNat_eq, UInt64.toNat_land, UInt64.toNat_mod,
      p128, p127, e, Nat.mod_mod]
  refine Eq.trans ?_ (toNat_shiftLeft (x := x) (s := s % 128) ?_)
  · rw [shiftLeft_def, shiftLeft_def, shiftLeft, shiftLeft, e]
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod, p128, gt_iff_lt, Nat.zero_lt_succ,
      Nat.mod_lt]

/-- Shifting left by zero does nothing -/
@[simp] lemma UInt128.shiftLeft_zero (x : UInt128) : x <<< (0 : UInt64) = x := by
  have h : (0 : UInt64) < 64 := by decide
  rw [shiftLeft_def, shiftLeft]
  simp only [UInt64.land_eq_hand, UInt64.zero_land, h, decide_True,
    UInt64.shiftLeft_zero, cond_true, beq_self_eq_true, sub_zero, zero_sub]

/-- Shifting zero does nothing -/
@[simp] lemma UInt128.zero_shiftLeft (s : UInt64) : (0 : UInt128) <<< s = 0 := by
  rw [shiftLeft_def, shiftLeft]
  simp only [UInt64.land_eq_hand, zero_lo, UInt64.zero_shiftLeft, Bool.cond_self,
    zero_hi, UInt64.zero_shiftRight, UInt64.zero_or, UInt128.ext_iff, and_self]

/-- `shiftRight` rounds down -/
lemma UInt128.toNat_shiftRight (x : UInt128) {s : UInt64} (sl : s < 128) :
    (x >>> s).toNat = x.toNat / 2^s.toNat := by
  generalize ht : s.toNat = t
  have st : s = (t : UInt64) := by rw [←ht, UInt64.cast_toNat]
  have t64' : t < UInt64.size := by rw [←ht]; exact UInt64.toNat_lt_2_pow_64 _
  simp only [st, UInt64.lt_iff_toNat_lt, UInt64.toNat_cast, Nat.mod_eq_of_lt t64', p128, st] at sl ⊢
  clear st ht s
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  rw [shiftRight_def, shiftRight]
  simp only [UInt128.testBit_eq, bif_eq_if, beq_iff_eq, decide_eq_true_eq,
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

/-- `shiftRight` rounds down -/
lemma UInt128.toNat_shiftRight' (x : UInt128) {s : UInt64} :
    (x >>> s).toNat = x.toNat / 2^(s.toNat % 128) := by
  have e : (s % 128).land 127 = s.land 127 := by
    have e : ∀ n : ℕ, n &&& 127 = n % 128 := fun _ ↦ Nat.land_eq_mod (k := 7)
    simp only [UInt64.land_eq_hand, UInt64.eq_iff_toNat_eq, UInt64.toNat_land, UInt64.toNat_mod,
      p128, p127, e, Nat.mod_mod]
  refine Eq.trans ?_ (toNat_shiftRight (x := x) (s := s % 128) ?_)
  · rw [shiftRight_def, shiftRight_def, shiftRight, shiftRight, e]
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_mod, p128, gt_iff_lt, Nat.zero_lt_succ,
      Nat.mod_lt]

lemma UInt128.coe_shiftRight (x : UInt128) {s : UInt64} (sl : s < 128) :
    (x >>> s : ℝ) = ↑(x.toNat / 2^s.toNat) := by
  rw [UInt128.toReal, UInt128.toNat_shiftRight _ sl]

/-- `shiftRightRound.toNat = rdiv` -/
lemma UInt128.toInt_shiftRightRound (x : UInt128) (s : UInt64) (up : Bool) :
    ((x.shiftRightRound s up).toNat : ℤ) = (x.toNat : ℤ).rdiv (2^s.toNat) up := by
  rw [shiftRightRound]
  simp only [UInt64.le_iff_toNat_le, p128, bif_eq_if, Bool.or_eq_true, beq_iff_eq, eq_iff_toNat_eq,
    toNat_zero, Bool.not_eq_true', Bool.and_eq_true, bne_iff_ne, ne_eq, toNat_shiftLeft',
    toNat_shiftRight', decide_eq_true_eq, UInt64.eq_iff_toNat_eq, UInt64.toNat_zero,
    apply_ite (f := fun x : UInt128 ↦ x.toNat), toNat_one, toNat_succ', Nat.cast_ite,
    CharP.cast_eq_zero, Nat.cast_one, Nat.cast_add, Int.ofNat_ediv, Nat.cast_pow, Nat.cast_ofNat]
  have d0 : 128 ≤ s.toNat → (x.toNat : ℤ) < 2 ^ s.toNat := by
    intro sh
    refine lt_of_lt_of_le (Nat.cast_lt.mpr (lt_size _)) ?_
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right (by norm_num) sh
  have d1 : x.toNat / 2 ^ s.toNat = 2 ^ 128 - 1 → s.toNat = 0 := by
    intro h; contrapose h; apply ne_of_lt; apply Nat.div_lt_of_lt_mul
    refine lt_of_lt_of_le (lt_size _) ?_
    refine le_trans ?_ (Nat.mul_le_mul_right _ (pow_le_pow_right (by norm_num)
      (Nat.pos_iff_ne_zero.mpr h)))
    decide
  have d2 : x.toNat / 2^s.toNat * 2^s.toNat < 2^128 :=
    lt_of_le_of_lt (Nat.div_mul_le_self _ _) (lt_size _)
  have d3 : ∀ n, (2:ℤ) ^ n = (2^n : ℕ) := by intro _; simp only [Nat.cast_pow, Nat.cast_ofNat]
  split_ifs with h0 h1 h2 h3 h4
  · simp only [h0, pow_zero, Int.rdiv_one]
  · rcases h2 with x0 | down
    · simp only [x0, CharP.cast_eq_zero, Int.zero_rdiv]
    · simp only [Int.rdiv, down, Nat.cast_pow, Nat.cast_ofNat, cond_false,
        Int.ediv_eq_zero_of_lt (Int.ofNat_nonneg _) (d0 h1)]
  · simp only [not_or, Bool.not_eq_false] at h2
    simp only [Int.rdiv, h2.2, Nat.cast_pow, Nat.cast_ofNat, cond_true, ← neg_eq_iff_eq_neg]
    exact (Int.ediv_eq_neg_one (Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr h2.1)) (d0 h1).le).symm
  · simp only [not_le] at h1
    simp only [h3.1, Nat.mod_eq_of_lt h1, true_and, Int.rdiv, Nat.cast_pow, Nat.cast_ofNat,
      cond_true, zero_eq_neg] at h3 h4
    contrapose h3
    simp only [d1 h4, pow_zero, Nat.div_one, mul_one, not_not] at h4 ⊢
    rw [h4]; decide
  · simp only [not_le] at h1; clear h4
    simp only [h3.1, Nat.mod_eq_of_lt h1, true_and, Int.rdiv, Nat.cast_pow, Nat.cast_ofNat,
      cond_true, Nat.mod_eq_of_lt d2] at h3 ⊢
    rw [eq_comm, ←Nat.dvd_iff_div_mul_eq] at h3
    rw [Int.neg_ediv_neg (by positivity)]
    simp only [d3, h3, Int.ofNat_dvd, not_false_eq_true]
  · simp only [not_le] at h1
    simp only [Nat.mod_eq_of_lt h1, not_and_or, not_not, Bool.not_eq_true,
      Nat.mod_eq_of_lt d2] at h3 ⊢
    rcases h3 with down | dv
    · simp only [Nat.mod_eq_of_lt h1, Int.rdiv, down, Nat.cast_pow, Nat.cast_ofNat, cond_false]
    · rw [dv]
      simp only [Nat.cast_mul, Int.ofNat_ediv, ne_eq, d3, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
        false_and, not_false_eq_true, Int.mul_ediv_cancel, Int.mul_rdiv_cancel]
      simp only [Nat.cast_pow, Nat.cast_ofNat, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
        false_and, not_false_eq_true, Int.mul_ediv_cancel]

/-- `shiftRightRound` rounds as desired -/
lemma UInt128.approx_shiftRightRound (x : UInt128) (s : UInt64) (up : Bool) :
    (x.shiftRightRound s up : ℝ) ∈ rounds {(x : ℝ) / (2:ℝ)^s.toNat} up := by
  have a := toInt_shiftRightRound x s up
  simp only [←Int.cast_inj (α := ℝ), Int.cast_Nat_cast] at a
  have e : (2:ℝ)^s.toNat = (2^s.toNat : ℕ) := by simp only [Nat.cast_pow, Nat.cast_ofNat]
  simp only [toReal, mem_rounds_singleton, a, e]
  induction up
  · exact Int.rdiv_le
  · exact Int.le_rdiv

lemma UInt128.toNat_shiftLeftSaturate {x : UInt128} {s : UInt64}
    : (x.shiftLeftSaturate s).toNat = min (x.toNat * 2^s.toNat) UInt128.max.toNat := by
  generalize ht : s.toNat = t
  have st : s = (t : UInt64) := by rw [←ht, UInt64.cast_toNat]
  have t64 : t < UInt64.size := by rw [←ht]; exact UInt64.toNat_lt_2_pow_64 _
  have x128 : x.toNat < 2^128 := x.lt_size
  simp only [st, toNat_max]
  clear st ht s
  by_cases t0 : t = 0
  · rw [shiftLeftSaturate]
    simp only [t0, Nat.cast_zero, (by decide : ¬128 ≤ (0 : UInt64)),
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
      · rw [toNat_max]
      · have x1 : 1 ≤ x.toNat := by
          simp only [eq_iff_toNat_eq, toNat_zero] at x0
          omega
        exact le_trans (by norm_num) (Nat.mul_le_mul x1 (pow_right_mono (by norm_num) t128))

lemma UInt128.shiftLeftSaturate_eq {x : UInt128} {s : UInt64}
    : x.shiftLeftSaturate s = .ofNat (min (x.toNat * 2^s.toNat) UInt128.max.toNat) := by
  simp only [ge_iff_le, eq_iff_toNat_eq, toNat_shiftLeftSaturate, toNat_ofNat]
  rw [Nat.mod_eq_of_lt]; apply min_lt_of_right_lt; rw [toNat_max]; norm_num

@[simp] lemma UInt128.zero_shiftRight {s : UInt64} : (0 : UInt128) >>> s = 0 := by
  rw [shiftRight_def, shiftRight]
  simp only [UInt64.land_eq_hand, zero_lo, UInt64.zero_shiftRight, zero_hi, UInt64.zero_shiftLeft,
    UInt64.zero_or, Bool.cond_self]
  rfl

@[simp] lemma UInt128.zero_shiftRightRound {s : UInt64} {up : Bool} :
    (0 : UInt128).shiftRightRound s up = 0 := by
  rw [shiftRightRound]
  simp only [beq_self_eq_true, Bool.true_or, cond_true, zero_shiftRight, zero_shiftLeft,
    bne_self_eq_false, Bool.and_false, cond_false, Bool.cond_self]

@[simp] lemma UInt128.shiftRightRound_zero {x : UInt128} {up : Bool} :
    x.shiftRightRound 0 up = x := by
  rw [shiftRightRound]
  simp only [beq_self_eq_true, shiftLeft_zero, Bool.cond_decide, cond_true]

/-!
### `log2`
-/

@[irreducible] def UInt128.log2 (x : UInt128) : UInt64 :=
  bif x.hi == 0 then x.lo.log2
  else x.hi.log2 + 64

@[simp] lemma UInt128.toNat_log2 (x : UInt128) : x.log2.toNat = x.toNat.log2 := by
  rw [log2, toNat]
  have e64 : (64 : UInt64).toNat = 64 := rfl
  simp only [bif_eq_if, beq_iff_eq, UInt64.le_iff_toNat_le, p127, Nat.shiftLeft_eq,
    apply_ite (f := fun x : UInt64 ↦ x.toNat), UInt64.toNat_log2, UInt64.toNat_add,
    UInt64.size_eq_pow, e64]
  split_ifs with h0
  · simp only [h0, UInt64.toNat_zero, zero_mul, zero_add]
  · have h0' := UInt64.ne_zero_iff_toNat_ne_zero.mp h0
    have s0 : x.hi.toNat * 2^64 + x.lo.toNat ≠ 0 := by positivity
    rw [Nat.mod_eq_of_lt]
    · apply le_antisymm
      · rw [Nat.le_log2 s0, pow_add]
        exact le_trans (Nat.mul_le_mul_right _ (Nat.log2_self_le h0')) (Nat.le_add_right _ _)
      · apply Nat.le_of_lt_succ
        rw [Nat.log2_lt s0]
        rw [Nat.succ_eq_add_one, add_assoc, add_comm _ 1, ←add_assoc, pow_add]
        have le : x.hi.toNat + 1 ≤ 2 ^ (x.hi.toNat.log2 + 1) := Nat.lt_log2_self
        refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_right _ le)
        simp only [add_one_mul, add_lt_add_iff_left, UInt64.toNat_lt_2_pow_64]
    · have h : x.hi.toNat.log2 < 64 := UInt64.log2_lt_64 x.hi
      norm_num; omega

@[simp] lemma UInt128.log2_le_127 (x : UInt128) : x.log2 ≤ 127 := by
  rw [log2]
  have e : (64 : UInt64).toNat = 64 := rfl
  simp only [bif_eq_if, beq_iff_eq, UInt64.le_iff_toNat_le, p127]
  split_ifs
  · simp only [UInt64.toNat_log2]
    have h := UInt64.log2_lt_64 x.lo
    omega
  · have h := UInt64.log2_lt_64 x.hi
    rw [UInt64.toNat_add, UInt64.toNat_log2, e, UInt64.size_eq_pow, Nat.mod_eq_of_lt]
    · omega
    · norm_num; omega

@[simp] lemma UInt128.log2_le_127' (x : UInt128) : x.toNat.log2 ≤ 127 := by
  have h := UInt128.log2_le_127 x
  simpa only [ge_iff_le, UInt64.le_iff_toNat_le, toNat_log2, p127] using h

@[simp] lemma UInt128.log2_zero : (0 : UInt128).log2 = 0 := by
  rw [log2]; simp only [zero_hi, beq_self_eq_true, zero_lo, UInt64.log2_zero, zero_add, cond_true]

@[simp] lemma UInt128.toNat_lo_of_log2_lt {x : UInt128} (h : x.toNat.log2 < 64) :
    x.lo.toNat = x.toNat := by
  by_cases x0 : x.toNat = 0
  · simp only [x0, zero_lt_two, pow_pos, toNat_lo]
  · rw [toNat_lo]
    rwa [Nat.log2_lt x0] at h

/-- Shifting some high bits down produces a small value -/
lemma UInt128.toNat_hi_shiftRightRound_le_hi {y : UInt64} {s : UInt64} {up : Bool} :
    ((⟨0, y⟩ : UInt128).shiftRightRound s up).hi.toNat ≤ y.toNat := by
  have h := UInt128.toInt_shiftRightRound ⟨0, y⟩ s up
  generalize (⟨0, y⟩ : UInt128).shiftRightRound s up = z at h
  contrapose h; simp only [not_le] at h
  apply ne_of_gt
  rw [←Int.cast_lt (α := ℝ)]
  refine lt_of_lt_of_le Int.rdiv_lt ?_
  simp only [UInt128.toNat_def, UInt64.toNat_zero, add_zero, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.int_cast_ofNat, Nat.cast_add,
    Int.cast_add]
  trans y.toNat * 2^64 + 1
  · exact add_le_add_right (div_le_self (by positivity) (one_le_pow_of_one_le (by norm_num) _)) _
  · have e : (2^64 : ℝ) = (2^64 : ℕ) := by norm_num
    simp only [e, ←Nat.cast_mul, ←Nat.cast_add_one, ←Nat.cast_add, Nat.cast_le]
    norm_num
    omega
