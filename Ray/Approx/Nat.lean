import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LibrarySearch
import Ray.Approx.Bool

/-!
## `ℕ` facts
-/

lemma Nat.add_sub_eq_sub_sub {m n k : ℕ} (nk : n ≤ k) : m + n - k = m - (k - n) := by
  omega

lemma Nat.add_sub_lt_left {m n k : ℕ} (m0 : m ≠ 0) : m + n - k < m ↔ n < k := by
  by_cases nk : n < k
  · simp only [ge_iff_le, nk, iff_true, Nat.add_sub_eq_sub_sub nk.le]
    exact Nat.sub_lt (Nat.pos_iff_ne_zero.mpr m0) (Nat.sub_pos_of_lt nk)
  · simp only [ge_iff_le, nk, iff_false, not_lt]
    simp only [not_lt] at nk; rw [Nat.add_sub_assoc nk]; exact le_add_right _ _

lemma Nat.bit_div2_eq (n : ℕ) : Nat.bit (Nat.bodd n) (Nat.div2 n) = n := by
  induction' n with n h
  · rfl
  · by_cases p : bodd n
    · simp only [bit, p, cond_true] at h
      simp only [bit, bodd_succ, p, Bool.not_true, div2_succ, cond_true, cond_false,
        Nat.bit0_succ_eq, ← Nat.bit1_eq_succ_bit0, h]
    · simp only [bit, p, cond_false] at h
      simp only [bit, bodd_succ, p, Bool.not_false, div2_succ, cond_false, cond_true,
        Nat.bit1_eq_succ_bit0, h]

lemma Nat.bit_le_bit {a b : Bool} {m n : ℕ} (ab : a ≤ b) (mn : m ≤ n) : bit a m ≤ bit b n := by
  induction a
  · induction b
    repeat simp only [bit_false, bit_true, bit0_le_bit0, bit0_le_bit1_iff, mn]
  · induction b
    · contrapose ab; decide
    · simp only [bit_true, bit1_le_bit1, mn]

@[simp] lemma Nat.testBit_zero' {i : ℕ} : testBit 0 i = false := by
  simp only [testBit, zero_shiftRight, and_one_is_mod, zero_mod, bne_self_eq_false]

lemma Nat.testBit_zero_eq_bodd {n : ℕ} : testBit n 0 = bodd n := by
  nth_rw 1 [←Nat.bit_div2_eq n]
  simp only [testBit_zero]

lemma Nat.div2_eq_shiftRight_one {n : ℕ} : n.div2 = n >>> 1 := by
  simp only [div2_val, shiftRight_succ, shiftRight_eq_div_pow, _root_.pow_zero, Nat.div_one]

@[simp] lemma Nat.testBit_div2 {n i : ℕ} : testBit n.div2 i = testBit n (i+1) := by
  simp only [testBit, Nat.div2_eq_shiftRight_one, ←Nat.shiftRight_add, add_comm]

lemma Nat.le_of_testBit_le {m n : ℕ} (h : ∀ i, m.testBit i ≤ n.testBit i) : m ≤ n := by
  revert h n
  induction' m using Nat.strong_induction_on with m p
  intro n h
  by_cases m0 : m = 0
  · simp only [m0, _root_.zero_le]
  · rw [← Nat.bit_div2_eq m, ← Nat.bit_div2_eq n]
    apply Nat.bit_le_bit
    · simp only [← testBit_zero_eq_bodd]; apply h
    · apply p
      · simp only [div2_val]
        exact Nat.div_lt_self (Nat.pos_iff_ne_zero.mpr m0) one_lt_two
      · intro i; simp only [testBit_div2]; apply h

lemma Nat.land_le_max {m n : ℕ} : m &&& n ≤ max m n := by
  apply Nat.le_of_testBit_le
  intro i
  simp only [testBit_land, ge_iff_le]
  by_cases mn : m ≤ n
  · by_cases b : testBit n i
    repeat simp only [b, Bool.and_false, ge_iff_le, mn, max_eq_right, Bool.le_true, le_refl]
  · by_cases b : testBit m i
    repeat simp only [b, Bool.true_and, Bool.false_and, ge_iff_le, (not_le.mp mn).le, max_eq_left,
      Bool.le_true, le_refl]

lemma Nat.bodd_sub {n k : ℕ} : bodd (n - k) = (_root_.xor (bodd n) (bodd k) && k ≤ n) := by
  by_cases kn : k ≤ n
  · simp only [ge_iff_le, kn, decide_True, Bool.and_true, decide_eq_true_eq]
    nth_rw 2 [←Nat.sub_add_cancel kn]
    generalize n - k = m
    simp only [bodd_add, Bool.xor_assoc, bne_self_eq_false, Bool.xor_false]
  · simp only [ge_iff_le, Nat.sub_eq_zero_of_le (not_le.mp kn).le, bodd_zero, kn, decide_False,
      Bool.and_false]

lemma Nat.bodd_sub_one {n : ℕ} : bodd (n-1) = decide (n ≠ 0 ∧ ¬bodd n) := by
  induction n
  · rfl
  · simp only [ge_iff_le, succ_sub_succ_eq_sub, nonpos_iff_eq_zero, tsub_zero, ne_eq, succ_ne_zero,
      not_false_eq_true, bodd_succ, Bool.not_eq_true', Bool.not_eq_false, true_and, Bool.decide_coe]

lemma Nat.bodd_two_pow {k : ℕ} : bodd (2^k) = decide (k = 0) := by
  induction' k with k
  · rfl
  · simp only [pow_succ, bodd_mul, bodd_succ, bodd_zero, Bool.not_false, Bool.not_true,
      Bool.and_false, succ_ne_zero, decide_False]

@[simp] lemma Nat.pow_div' {a m n : ℕ} (a0 : a ≠ 0) : a^(m + n) / a^n = a^m := by
  rw [Nat.pow_div]
  · simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
  · simp only [le_add_iff_nonneg_left, _root_.zero_le]
  · exact Nat.pos_of_ne_zero a0

@[simp] lemma Nat.pow_dvd' {a m n : ℕ} : a^n ∣ a^(m + n) := by
  induction' n with n h
  · simp only [zero_eq, _root_.pow_zero, add_zero, isUnit_one, IsUnit.dvd]
  · simp only [pow_succ, add_succ, IsUnit.mul_iff, ne_eq, Nat.isUnit_iff, add_eq_zero_iff, not_and]
    exact Nat.mul_dvd_mul_right h a

@[simp] lemma Nat.pow_mod' {a m n : ℕ} : a^(m + n) % a^n = 0 :=
  Nat.mod_eq_zero_of_dvd pow_dvd'

@[simp] lemma Nat.two_pow_sub_one_div_two_pow {n k : ℕ} : (2^n - 1) / 2^k = 2^(n-k) - 1 := by
  have k0 : 0 < 2^k := pow_pos (by norm_num : 0 < 2) _
  have k1 : ∀ k, 1 ≤ 2^k := fun _ ↦ Nat.one_le_pow _ _ (by norm_num)
  by_cases kn : k ≤ n
  · rw [←Nat.sub_add_cancel kn]; generalize n - k = n; clear kn
    simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right]
    induction' n with n h
    · simp only [zero_eq, zero_add, ge_iff_le, _root_.pow_zero, le_refl, tsub_eq_zero_of_le]
      rw [Nat.div_eq_zero_iff k0]
      exact Nat.pred_lt k0.ne'
    · simp only [succ_add, pow_succ, mul_two, Nat.add_sub_assoc (k1 _), Nat.add_div k0, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, pow_div', h, pow_mod', zero_add, add_right_eq_self,
        ite_eq_right_iff, one_ne_zero, imp_false, not_le, gt_iff_lt]
      exact Nat.mod_lt _ k0
  · simp only [not_le] at kn
    simp only [ge_iff_le, Nat.sub_eq_zero_of_le kn.le, _root_.pow_zero, le_refl, tsub_eq_zero_of_le,
      Nat.div_eq_zero_iff k0, gt_iff_lt]
    refine lt_of_lt_of_le ?_ (pow_right_mono one_le_two kn)
    simp only [ge_iff_le]
    trans 2^n
    · apply Nat.pred_lt; apply pow_ne_zero; norm_num
    · apply pow_lt_pow_right; norm_num; exact lt.base n

lemma Nat.mod_eq_sub {n k : ℕ} : n % k = n - k * (n / k) := by
  refine (Nat.sub_eq_of_eq_add ?_).symm
  rw [add_comm]
  exact (Nat.div_add_mod _ _).symm

lemma Nat.land_eq_mod {n k : ℕ} : n &&& (2^k-1) = n % 2^k := by
  revert n
  induction' k with k h
  · simp only [zero_eq, _root_.pow_zero, ge_iff_le, le_refl, tsub_eq_zero_of_le, and_zero, mod_one,
      forall_const]
  · intro n
    induction' n using Nat.binaryRec with b n _
    · simp only [ge_iff_le, zero_and, zero_mod]
    · specialize @h n
      refine Nat.eq_of_testBit_eq fun i ↦ ?_
      induction' i with i
      · simp only [and_pow_two_is_mod, zero_eq, testBit_mod_two_pow, zero_lt_succ, decide_True,
          testBit_zero, Bool.true_and]
      · simp only [and_pow_two_is_mod, testBit_mod_two_pow, succ_lt_succ_iff]

lemma Nat.add_lt_add' {a b c d : ℕ} (ac : a < c) (bd : b ≤ d) : a + b < c + d := by
  omega

lemma Nat.add_lt_add'' {a b c d : ℕ} (ac : a ≤ c) (bd : b < d) : a + b < c + d := by
  omega

lemma Nat.mod_mul_eq_mul_mod' (a n m : ℕ) (m0 : m ≠ 0) : a * n % (m * n) = a % m * n := by
  by_cases n0 : n = 0
  · simp only [n0, mul_zero, mod_self]
  · replace m0 := Nat.pos_of_ne_zero m0
    rw [←Nat.div_add_mod a m]
    generalize hb : a % m = b
    generalize a / m = c
    have bm : b < m := by rw [←hb]; exact mod_lt _ m0
    have bnn : b * n < m * n := Nat.mul_lt_mul_of_lt_of_le bm (le_refl _) (Nat.pos_of_ne_zero n0)
    rw [add_mul, Nat.mul_comm _ c, mul_assoc, add_mod, add_mod (c*m) b m]
    simp only [mul_mod_left, zero_add, mod_eq_of_lt bm, mod_eq_of_lt bnn]

lemma Nat.mod_mul_eq_mul_mod (a n : ℕ) : a * n % n^2 = a % n * n := by
  by_cases n0 : n = 0
  · simp only [n0, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mod_self,
      mod_zero]
  · rw [pow_two, Nat.mod_mul_eq_mul_mod' _ _ _ n0]

lemma Nat.div_mod_mul_add_mod_eq {a n : ℕ} : a / n % n * n + a % n = a % n^2 := by
  by_cases n0 : n = 0
  · simp only [n0, Nat.div_zero, mod_self, mul_zero, mod_zero, zero_add, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  · rw [←Nat.div_add_mod a n]
    have np : 0 < n := Nat.pos_of_ne_zero n0
    generalize hc : a % n = c
    generalize a / n = b
    rw [mul_comm n b]
    have cn : c < n := by rw [←hc]; exact mod_lt a np
    have bn : b * n % n = 0 := mul_mod_left b n
    have be : (b * n + c) / n = b := by
      simp only [Nat.add_div np, Nat.mul_div_cancel _ np, (Nat.div_eq_zero_iff np).mpr cn, add_zero,
        Nat.mul_mod_left, Nat.mod_eq_of_lt cn, zero_add, not_le.mpr cn, if_false]
    have ce : (b * n + c) % n = c := by
      rw [Nat.add_mod, bn, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt cn]
    have cnn : c % n^2 = c := by
      apply Nat.mod_eq_of_lt
      apply lt_of_lt_of_le cn
      rw [pow_two]
      apply Nat.le_mul_self
    have lt : b % n * n + c < n^2 := by
      apply lt_of_lt_of_le (add_lt_add_left cn _)
      rw [pow_two, mul_comm _ n, ←mul_add_one (α := ℕ)]
      apply Nat.mul_le_mul_left
      rw [Nat.add_one_le_iff]
      exact mod_lt b np
    rw [be, ce, Nat.add_mod, cnn, Nat.mod_mul_eq_mul_mod, Nat.mod_eq_of_lt lt]

lemma Nat.lor_eq_add {a b : ℕ} (h : ∀ i, testBit a i = false ∨ testBit b i = false) :
    a ||| b = a + b := by
  revert h b
  induction' a using Nat.binaryRec with c a ha
  · simp only [zero_testBit, true_or, forall_const, or_zero, zero_add, forall_true_left]
  · intro b h
    induction' b using Nat.binaryRec with d b _
    · simp only [zero_or, add_zero]
    · simp only [lor_bit]
      simp only [bit_val]
      simp only [← add_assoc, add_comm _ (2 * b)]
      simp only [← mul_add, add_comm _ a]
      rw [add_assoc]
      refine congr_arg₂ _ (congr_arg₂ _ rfl ?_) ?_
      · apply ha
        intro i
        simpa only [testBit_succ] using h (i+1)
      · specialize h 0
        simp only [testBit_zero] at h
        cases' h with h h
        · simp only [h, Bool.false_or, cond_false, zero_add]
        · simp only [h, Bool.or_false, cond_false, add_zero]

@[simp] lemma Nat.testBit_mul_two_pow {n k i : ℕ} :
    testBit (n * 2^k) i = decide (k ≤ i ∧ testBit n (i-k)) := by
  simp only [testBit, shiftRight_eq_div_pow]
  by_cases ki : k ≤ i
  · simp only [ki, ge_iff_le, true_and, eq_iff_iff]
    rw [←Nat.sub_add_cancel ki, pow_add]
    simp only [mul_comm _ (2 ^ k), ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero,
      tsub_eq_zero_iff_le, add_tsub_cancel_right]
    rw [Nat.mul_div_mul_left _ _ (pow_pos (by norm_num) k), Bool.decide_coe]
  · simp only [and_one_is_mod, ki, bne_iff_ne, ne_eq, mod_two_ne_zero, false_and, decide_False]
    simp only [not_le] at ki
    rw [←Nat.sub_add_cancel ki]
    simp only [add_succ, pow_succ', pow_add, ← mul_assoc, gt_iff_lt, zero_lt_two, pow_pos,
      mul_div_left]
    simp only [mul_comm _ 2, mul_assoc, mul_mod_right, bne_self_eq_false]

lemma Nat.mod_le' {n k : ℕ} (k0 : 0 < k) : n % k ≤ k-1 :=
  Nat.le_pred_of_lt (Nat.mod_lt _ k0)

lemma Nat.div_div {n a b : ℕ} : n / a / b = n / (a * b) := by
  by_cases a0 : 0 < a
  · by_cases b0 : 0 < b
    · have ba0 : 0 < b * a := Nat.mul_pos b0 a0
      rw [←Nat.div_add_mod n a, ←Nat.div_add_mod (n/a) b]
      generalize n / a / b = m
      simp only [mul_comm a, Nat.add_div a0, Nat.mul_div_cancel _ a0, mod_div_self, add_zero,
        mul_mod_left, mod_mod, zero_add, not_le.mpr (Nat.mod_lt _ a0), ite_false]
      rw [add_mul, mul_comm b, mul_assoc, add_assoc, add_comm (m * b), add_comm (m * (b * a)),
        Nat.add_mul_div_right _ _ b0, Nat.add_mul_div_right _ _ ba0, mod_div_self, zero_add]
      simp only [self_eq_add_left, Nat.div_eq_zero_iff ba0]
      have lt0 : n / a % b * a ≤ (b-1) * a := Nat.mul_le_mul_right _ (Nat.mod_le' b0)
      have lt1 : n % a ≤ a-1 := Nat.mod_le' a0
      refine lt_of_le_of_lt (add_le_add lt0 lt1) ?_
      rw [←Nat.add_sub_assoc (Nat.one_le_of_lt a0), ←Nat.succ_mul, Nat.succ_eq_add_one,
        Nat.sub_add_cancel (Nat.one_le_of_lt b0)]
      exact sub_lt ba0 (by norm_num)
    · simp only [not_lt, nonpos_iff_eq_zero] at b0
      simp only [b0, Nat.div_zero, mul_zero]
  · simp only [not_lt, nonpos_iff_eq_zero] at a0
    simp only [a0, Nat.div_zero, Nat.zero_div, zero_mul]

@[simp] lemma Nat.testBit_div_two_pow {n k i : ℕ} : testBit (n / 2^k) i = testBit n (i+k) := by
  induction' k with k h generalizing i
  · simp only [zero_eq, _root_.pow_zero, Nat.div_one, add_zero]
  · have e : n / 2^(k+1) = (n / 2^k).div2 := by rw [Nat.div2_val, pow_succ, ←Nat.div_div]
    rw [e, Nat.testBit_div2, h, add_assoc, add_comm _ k]

/-- A case where `+, %` commute -/
lemma Nat.add_mod_two_pow_disjoint {x y a b : ℕ} (ya : y < 2^a) :
    x * 2^a % 2^b + y % 2^b = (x * 2^a + y) % 2^b := by
  have c : ∀ i, testBit (x * 2^a) i = false ∨ testBit y i = false := by
    intro i
    by_cases ia : i < a
    · left
      simp only [testBit_mul_two_pow, ge_iff_le, Bool.decide_and, Bool.decide_coe,
        Bool.and_eq_false_eq_eq_false_or_eq_false, decide_eq_false_iff_not, not_le, ia, true_or]
    · right; exact testBit_eq_false_of_lt (lt_of_lt_of_le ya (pow_right_mono one_le_two (not_lt.mp ia)))
  refine Nat.eq_of_testBit_eq fun i ↦ ?_
  rw [←lor_eq_add c, ←lor_eq_add]
  · cases' c i with c c
    repeat simp only [testBit_lor, testBit_mod_two_pow, c, Bool.false_or, Bool.or_false,
      Bool.and_false]
  · intro i
    cases' c i with c c
    · left; simp only [testBit_mod_two_pow, c, Bool.and_false]
    · right; simp only [testBit_mod_two_pow, c, Bool.and_false]

lemma Nat.div_eq_zero_of_lt {m n : ℕ} (h : m < n) : m / n = 0 := by
  by_cases n0 : n = 0
  · simp only [n0, Nat.div_zero]
  · rwa [Nat.div_eq_zero_iff (Nat.pos_iff_ne_zero.mpr n0)]

lemma Nat.sub_le_sub {a b c d : ℕ} (ab : a ≤ c) (db : d ≤ b) : a - b ≤ c - d := by omega

lemma Nat.cast_div_le_div_add_one {𝕜 : Type} [LinearOrderedField 𝕜] [FloorRing 𝕜] {a b : ℕ} :
    (a : 𝕜) / b ≤ (a / b : ℕ) + 1 := by
  trans (⌈(a : 𝕜) / b⌉₊ : 𝕜)
  · apply le_ceil
  · rw [←Nat.cast_add_one, Nat.cast_le]
    refine le_trans (Nat.ceil_le_floor_add_one _) ?_
    rw [Nat.floor_div_eq_div]

lemma Nat.sub_sub_assoc {a b c : ℕ} (h : c ≤ b) : a + c - b = a - (b - c) := by omega

lemma Nat.le_add_div_mul {n k : ℕ} (k0 : 0 < k) : n ≤ (n + k - 1) / k * k := by
  rw [←Nat.div_add_mod n k]
  generalize n / k = a
  generalize hb : n % k = b
  have bk0 : 0 < b + k := by omega
  simp only [mul_comm k _, add_assoc, Nat.add_sub_assoc bk0, Nat.add_div k0,
    Nat.mul_div_cancel _ k0, mul_mod_left, zero_add, ge_iff_le, ←not_lt (b := k), Nat.mod_lt _ k0, not_true,
    if_false, add_zero, add_mul, add_le_add_iff_left]
  by_cases b0 : b = 0
  · simp only [b0, zero_add, _root_.zero_le]
  · trans k
    · rw [←hb]; exact (Nat.mod_lt _ k0).le
    · apply Nat.le_mul_of_pos_left
      refine Nat.div_pos ?_ k0
      omega

@[simp] lemma Nat.log2_zero : Nat.log2 0 = 0 := rfl

lemma Nat.two_pow_ne_zero {n : ℕ} : 2^n ≠ 0 := by
  apply pow_ne_zero; norm_num

attribute [simp] Nat.testBit_mod_two_pow

/-!
### Divide and shift with controllable rounding
-/

/-- Divide, rounding up or down -/
def Nat.rdiv (n k : ℕ) (up : Bool) : ℕ :=
  (bif up then n + (k-1) else n) / k

/-- Shift right, rounding up or down -/
@[irreducible] def Nat.shiftRightRound (n k : ℕ) (up : Bool) : ℕ :=
  (bif up then n + ((1 <<< k) - 1) else n) >>> k

lemma Nat.shiftRightRound_eq_rdiv (n k : ℕ) (up : Bool) :
    n.shiftRightRound k up = n.rdiv (2^k) up := by
  rw [shiftRightRound]
  simp only [shiftLeft_eq, one_mul, bif_eq_if, shiftRight_eq_div_pow, rdiv]

/-- `rdiv` rounds down if desired -/
lemma Nat.rdiv_le {a b : ℕ} : (a.rdiv b false : ℝ) ≤ a / b := by
  simp only [rdiv, cond_false]
  by_cases b0 : b = 0
  · simp only [b0, Nat.cast_zero, Nat.div_zero, cast_zero, div_zero, le_refl]
  · rw [le_div_iff]
    · rw [←Nat.cast_mul, Nat.cast_le]
      exact div_mul_le_self a b
    · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)

/-- `rdiv` rounds up if desired -/
lemma Nat.le_rdiv {a b : ℕ} : (a / b : ℝ) ≤ a.rdiv b true := by
  simp only [rdiv, cond_true]
  by_cases b0 : b = 0
  · simp only [b0, cast_zero, div_zero, ge_iff_le, _root_.zero_le, tsub_eq_zero_of_le, add_zero,
      Nat.div_zero, le_refl]
  · rw [div_le_iff (Nat.cast_pos.mpr (Nat.pos_of_ne_zero b0)), ←Nat.cast_mul, Nat.cast_le]
    have lt : b - 1 < b := by omega
    rw [add_div (by omega), div_eq_of_lt lt, add_zero, mod_eq_of_lt lt]
    by_cases z : a % b = 0
    · simp only [z, zero_add, not_le.mpr lt, ite_false, add_zero, ge_iff_le]
      refine (Nat.div_mul_cancel ((Nat.dvd_iff_mod_eq_zero _ _).mpr z)).symm.le
    · simp only [←Nat.pos_iff_ne_zero] at z
      have le : b ≤ a % b + (b - 1) := by omega
      simp only [le, ite_true, ge_iff_le, add_one_mul]
      nth_rw 1 [←Nat.div_add_mod a b, mul_comm b]
      simp only [add_le_add_iff_left]
      exact (Nat.mod_lt _ (by omega)).le

lemma Nat.rdiv_le_rdiv {a b : ℕ} {u0 u1 : Bool} (u01 : u0 ≤ u1) :
    a.rdiv b u0 ≤ a.rdiv b u1 := by
  induction u0
  · induction u1
    · rfl
    · rw [←Nat.cast_le (α := ℝ)]
      exact le_trans Nat.rdiv_le Nat.le_rdiv
  · simp only [Bool.eq_true_of_true_le u01, le_refl]

@[simp] lemma Nat.zero_rdiv {b : ℕ} {up : Bool} : (0 : ℕ).rdiv b up = 0 := by
  rw [rdiv]
  induction up
  · simp only [zero_add, cond_false, Nat.zero_div]
  · simp only [zero_add, cond_true]
    by_cases b0 : b = 0
    · simp only [b0, _root_.zero_le, tsub_eq_zero_of_le, Nat.div_zero]
    · exact Nat.div_eq_of_lt (by omega)

/-- `rdiv` by 0 is 0 -/
@[simp] lemma Nat.rdiv_zero {a : ℕ} {up : Bool} : a.rdiv 0 up = 0 := by
  rw [rdiv]; simp only [_root_.zero_le, tsub_eq_zero_of_le, add_zero, Bool.cond_self, Nat.div_zero]

/-- `rdiv` by 1 does nothing -/
@[simp] lemma Nat.rdiv_one {a : ℕ} {up : Bool} : a.rdiv 1 up = a := by
  rw [rdiv]
  induction up
  repeat simp only [le_refl, tsub_eq_zero_of_le, add_zero, Bool.cond_self, Nat.div_one]

/-- `rdiv` never rounds up by much -/
lemma Nat.rdiv_lt {a b : ℕ} {up : Bool} : (a.rdiv b up : ℝ) < a / b + 1 := by
  by_cases b0 : b = 0
  · simp only [b0, rdiv_zero, cast_zero, div_zero, zero_add, zero_lt_one]
  refine lt_of_le_of_lt (Nat.cast_le.mpr (Nat.rdiv_le_rdiv (Bool.le_true up))) ?_
  simp only [rdiv, cond_true]
  have b0 : 0 < (b : ℝ) := by positivity
  have bb : b-1 < b := by omega
  rw [←mul_lt_mul_iff_of_pos_right b0]
  simp only [add_one_mul, div_mul_cancel _ b0.ne', ←Nat.cast_add, ←Nat.cast_mul, Nat.cast_lt]
  refine lt_of_le_of_lt (Nat.div_mul_le_self _ _) ?_
  omega

/-- Prove `rdiv ≤` in terms of a multiplication inequality -/
lemma Nat.rdiv_le_of_le_mul {a b c : ℕ} {up : Bool} (h : a ≤ c * b) : a.rdiv b up ≤ c := by
  by_cases b0 : b = 0
  · simp only [b0, rdiv_zero, _root_.zero_le]
  · refine le_trans (rdiv_le_rdiv (Bool.le_true _)) ?_
    have b0' : 0 < b := pos_iff_ne_zero.mpr b0
    simp only [rdiv, cond_true, Nat.div_le_iff_le_mul_add_pred b0']
    linarith

/-- Prove `≤ rdiv` in terms of a multiplication inequality -/
lemma Nat.le_rdiv_of_mul_le {a b c : ℕ} {up : Bool} (b0 : 0 < b) (h : c * b ≤ a) :
    c ≤ a.rdiv b up := by
  refine le_trans ?_ (rdiv_le_rdiv (Bool.false_le _))
  simpa only [rdiv, cond_false, le_div_iff_mul_le b0]
