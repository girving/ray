import Ray.Approx.Floating.Abs
import Ray.Approx.Floating.Neg
import Ray.Approx.Floating.Standardization

open Pointwise

/-!
## Floating point addition and subtraction

To add, we shift the smaller number to near the bigger number, perform a 128-bit addition, and
normalize the result.
-/

open Set
open scoped Real
namespace Floating

/-!
### Normalization starting with 128 bits
-/

/-- Adjust an exponent for addition.  The result is `(t, d+1)`, where `d - 65` is the amount
    to shift left by, and `t` is the final exponent. -/
@[irreducible] def add_adjust (l s : UInt64) : UInt64 × UInt64 :=
  bif l == 127 then ⟨s+1, 0⟩ else
  let (s, d) := lower (126 - l) s
  (s, d + 1)

/-- Abbreviation for our expanded `n` value -/
def add_n (r : UInt128) (s : UInt64) (up : Bool) : Int64 :=
  ⟨(if 65 ≤ (add_adjust r.log2 s).2
    then r.lo <<< ((add_adjust r.log2 s).2 - 65)
    else (r.shiftRightRound (65 - (add_adjust r.log2 s).2) up).lo)⟩

/-- The difference result expressed as a difference -/
lemma add_adjust_2_eq {r : UInt128} {s : UInt64} (g : r.log2 ≠ 127 ∨ s ≠ UInt64.max) :
    ((add_adjust r.log2 s).2.toNat : ℤ) = s.toNat + 1 - (add_adjust r.log2 s).1.toNat := by
  rw [add_adjust]
  simp only [bif_eq_if, beq_iff_eq]
  split_ifs with h
  · simp only [h, ne_eq, not_true_eq_false, UInt64.eq_iff_toNat_eq, UInt64.toNat_max, false_or] at g
    simp only [UInt64.toNat_zero, CharP.cast_eq_zero, UInt64.toNat_add_one g, Nat.cast_add,
      Nat.cast_one, sub_self]
  · have d0 : (lower (126 - r.log2) s).2.toNat < 2^64-1 := by
      refine lt_of_le_of_lt (low_d_le _ _) ?_
      rw [UInt64.toNat_sub, u126]; norm_num; omega
      simp only [UInt64.eq_iff_toNat_eq, u127, UInt64.le_iff_toNat_le, u126] at h ⊢
      exact Nat.le_of_lt_succ (Ne.lt_of_le h r.log2_le_127)
    simp only [UInt64.toNat_add_one d0.ne, low_s_2_eq, Nat.cast_add_one,
      Nat.cast_sub ((UInt64.le_iff_toNat_le _ _).mp (low_le_s _ _))]
    ring

/-- `add_adjust` produces small `d + 1` -/
lemma adjust_d_le (r : UInt128) (s : UInt64) :
    (add_adjust r.log2 s).2.toNat ≤ 127 - r.toNat.log2 := by
  rw [add_adjust]; simp only [bif_eq_if, beq_iff_eq, UInt64.cast_toNat]
  split_ifs with h
  · simp only [UInt64.toNat_zero, zero_le]
  · simp only
    have d0 : r.toNat.log2 ≤ 126 := by
      simp only [UInt64.eq_iff_toNat_eq, UInt128.toNat_log2, u127] at h
      have le := UInt128.log2_le_127' r
      omega
    have d1 : r.log2 ≤ 126 := by simpa only [UInt64.le_iff_toNat_le, UInt128.toNat_log2, u126]
    have d2 : (lower (126 - r.log2) s).2.toNat + 1 ≤ 127 - r.toNat.log2 := by
      refine le_trans (add_le_add_right (low_d_le _ _) _) ?_
      rw [UInt64.toNat_sub d1, u126, UInt128.toNat_log2]
      omega
    rwa [UInt64.toNat_add, UInt64.toNat_one, UInt64.size_eq_pow, Nat.mod_eq_of_lt]
    exact lt_of_le_of_lt (le_trans d2 (Nat.sub_le _ _)) (by norm_num)

/-- `add_adjust` doesn't overflow `r` -/
lemma adjust_r_lt_128 (r : UInt128) (s : UInt64) :
    r.toNat < 2 ^ (128 - (add_adjust r.log2 s).2.toNat) := by
  have h0 := adjust_d_le r s
  have h1 := UInt128.log2_le_127' r
  refine lt_of_lt_of_le Nat.lt_log2_self ?_
  exact pow_le_pow_right (by norm_num) (by omega)

/-- `add_adjust` normalizes `r` -/
lemma adjust_le_r {r : UInt128} {s : UInt64} (r0 : r.toNat ≠ 0)
    (s0 : (add_adjust r.log2 s).1.toNat ≠ 0) :
    2 ^ (127 - (add_adjust r.log2 s).2.toNat) ≤ r.toNat := by
  refine le_trans ?_ (Nat.log2_self_le r0)
  apply pow_le_pow_right (by norm_num)
  rw [add_adjust] at s0 ⊢
  simp only [bif_eq_if, beq_iff_eq, UInt64.eq_iff_toNat_eq, UInt128.toNat_log2, u127, ne_eq,
    tsub_le_iff_right] at s0 ⊢
  by_cases e : r.toNat.log2 = 127
  · simp only [e, ite_true, UInt64.toNat_zero, add_zero, le_refl] at s0 ⊢
  · simp only [e, ite_false] at s0 ⊢
    rw [lower] at s0 ⊢
    simp only [bif_eq_if, decide_eq_true_eq] at s0 ⊢
    by_cases s126 : s < 126 - UInt128.log2 r
    · simp only [s126, ite_true, UInt64.toNat_zero, not_true_eq_false] at s0
    · have d0 : 126 - r.log2 + 1 = 127 - r.log2 := by ring
      simp only [s126, ite_false, sub_sub_cancel, d0, UInt64.toNat_sub (UInt128.log2_le_127 r),
        u127, UInt128.toNat_log2, Nat.add_sub_cancel' (UInt128.log2_le_127' _), le_refl]

/-- `add_adjust` doesn't overflow `r` -/
lemma adjust_mul_lt_128 (r : UInt128) (s : UInt64) :
    r.toNat * 2 ^ (add_adjust r.log2 s).2.toNat < 2 ^ 128 := by
  have h0 := adjust_d_le r s
  refine lt_of_lt_of_le (mul_lt_mul_of_pos_right (adjust_r_lt_128 r s) (by positivity)) ?_
  rw [←pow_add]
  exact pow_le_pow_right (by norm_num) (by omega)

/-- `add_adjust` normalizes `r` -/
lemma adjust_le_mul {r : UInt128} {s : UInt64} (r0 : r.toNat ≠ 0)
    (s0 : (add_adjust r.log2 s).1.toNat ≠ 0) :
    2^127 ≤ r.toNat * 2 ^ (add_adjust r.log2 s).2.toNat := by
  refine le_trans ?_ (Nat.mul_le_mul_right _ (adjust_le_r r0 s0))
  simp only [← pow_add]
  exact pow_le_pow_right (by norm_num) (by omega)

lemma adjust_lo_eq {r : UInt128} {s : UInt64} (a65 : 65 ≤ (add_adjust r.log2 s).2.toNat) :
    r.lo.toNat = r.toNat := by
  apply UInt128.toNat_lo
  exact lt_of_lt_of_le (adjust_r_lt_128 r s) (pow_le_pow_right (by norm_num) (by omega))

/-- `add_adjust` doesn't make `r` too big -/
lemma adjust_shift_le_63 (r : UInt128) (s : UInt64) (up : Bool)
    (a65 : (add_adjust r.log2 s).2.toNat < 65) :
    (r.shiftRightRound (65 - (add_adjust r.log2 s).2) up).toNat ≤ 2^63 := by
  apply Nat.le_of_lt_succ
  rw [←Nat.cast_lt (α := ℤ), UInt128.toInt_shiftRightRound]
  rw [←Int.cast_lt (α := ℝ)]
  refine lt_of_lt_of_le Int.rdiv_lt ?_
  simp only [Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_succ, Int.cast_add,
    Int.cast_pow, Int.cast_ofNat, Int.cast_one, ← le_sub_iff_add_le, add_sub_cancel_right]
  have a65' : (add_adjust r.log2 s).2 < 65 := by simpa only [UInt64.lt_iff_toNat_lt, u65]
  rw [div_le_iff (by positivity), ←pow_add, UInt64.toNat_sub a65'.le, u65,
    ←Nat.add_sub_assoc a65.le]
  have lt := adjust_r_lt_128 r s
  simp only [← Nat.cast_lt (α := ℝ), Nat.cast_pow, Nat.cast_ofNat] at lt
  exact lt.le

/-- `add_adjust` doesn't make `r` too big -/
lemma adjust_lo_shift_le_63 (r : UInt128) (s : UInt64) (up : Bool)
    (a65 : (add_adjust r.log2 s).2.toNat < 65) :
    (r.shiftRightRound (65 - (add_adjust r.log2 s).2) up).lo.toNat ≤ 2^63 := by
  have h := adjust_shift_le_63 r s up a65
  rwa [UInt128.toNat_lo (lt_of_le_of_lt h (by norm_num))]

/-- `add_n` produces small `n` values -/
lemma add_n_le (r : UInt128) (s : UInt64) (up : Bool) : (add_n r s up).n.toNat ≤ 2^63 := by
  rw [add_n]
  simp only [Ne, UInt64.eq_iff_toNat_eq, up63]
  have r_lt := adjust_r_lt_128 r s
  have mul_lt := adjust_mul_lt_128 r s
  generalize ha : add_adjust r.log2 s = a at r_lt mul_lt
  by_cases a65 : 65 ≤ a.2
  · have d0 : a.2.toNat - 65 < 64 := by have le := adjust_d_le r s; rw [ha] at le; omega
    have d1 : 65 ≤ a.2.toNat := by simpa only [UInt64.le_iff_toNat_le, u65] using a65
    have d2 : 0 < 2^65 := by norm_num
    have d3 : r.lo.toNat = r.toNat := by rw [←ha] at d1; exact adjust_lo_eq d1
    simp only [a65, ite_true, UInt64.toNat_shiftLeft', UInt64.toNat_sub a65, u65,
      Nat.mod_eq_of_lt d0, ← Nat.sub_sub_assoc d1, gt_iff_lt, d3]
    rw [Nat.mod_eq_of_lt]
    · rw [←mul_le_mul_iff_of_pos_right d2, mul_assoc, ←pow_add, ←pow_add, Nat.sub_add_cancel d1]
      exact mul_lt.le
    · exact lt_of_lt_of_le r_lt (pow_le_pow_right (by norm_num) (by omega))
  · simp only [a65, ite_false, gt_iff_lt]
    simp only [← ha, not_le, UInt64.lt_iff_toNat_lt, u65] at a65
    simp only [←ha, adjust_lo_shift_le_63 _ _ _ a65]

/-- `add_n` produces small `n` values -/
lemma add_n_lt (r : UInt128) (s : UInt64) (up : Bool) (n63 : (add_n r s up).n ≠ 2^63) :
    (add_n r s up).n.toNat < 2^63 := by
  refine Ne.lt_of_le ?_ (add_n_le r s up)
  simpa only [Ne, UInt64.eq_iff_toNat_eq, up63] using n63

/-- `add_adjust` never produces `n = .min` -/
lemma add_n_ne_min (r : UInt128) (s : UInt64) (up : Bool) (n63 : (add_n r s up).n ≠ 2^63) :
    add_n r s up ≠ .min := by
  rw [←Int64.natAbs_lt_pow_iff]
  have h := add_n_lt r s up n63
  have n : (add_n r s up).isNeg = false := by
    simp only [Int64.isNeg_eq_le, not_le.mpr h, decide_false_eq_false]
  rwa [Int64.toInt, n, cond_false, Nat.cast_zero, sub_zero, Int.natAbs_ofNat]

/-- `add_n` respects `ℕ` conversion -/
lemma coe_add_n (r : UInt128) (s : UInt64) (up : Bool) :
    ((add_n r s up).n.toNat : ℤ) =
      ((r.toNat : ℤ) * 2^(add_adjust r.log2 s).2.toNat).rdiv (2 ^ 65) up := by
  rw [add_n]
  have d0 := adjust_d_le r s
  have d1 := adjust_r_lt_128 r s
  generalize ha : (add_adjust r.log2 s).2 = a at d0 d1
  by_cases a65 : 65 ≤ a
  · simp only [a65, ite_true]
    have d2 : ∀ n, (2 : ℤ)^n = (2^n : ℕ) := by intro _; simp only [Nat.cast_pow, Nat.cast_ofNat]
    have d3 : ∀ {n}, 2^n ≠ 0 := by intro _; positivity
    have d4 : 65 ≤ a.toNat := by simpa only [UInt64.le_iff_toNat_le, u65] using a65
    have d5 : r.lo.toNat = r.toNat := UInt128.toNat_lo_of_log2_lt (by omega)
    have d6 : r.lo.toNat < 2^63 := by
      by_cases r0 : r.toNat = 0
      · simp only [r0, zero_lt_two, pow_pos, UInt128.toNat_lo]
      · rw [UInt128.toNat_lo_of_log2_lt (by omega)]; rw [←Nat.log2_lt r0]; omega
    have d8 : r.toNat < 2^(63 - (a - 65).toNat) := by
      rw [UInt64.toNat_sub a65, u65, ←Nat.sub_sub_assoc d4]; exact d1
    have d9 : ((⟨r.lo⟩ : Int64) : ℤ) = r.toNat := by
      simpa only [Int64.toInt, Int64.isNeg_eq_le, not_le.mpr d6, decide_False, cond_false,
        CharP.cast_eq_zero, sub_zero, Nat.cast_inj]
    have d12 : r.toNat < 2^(64 - (a - 65).toNat) :=
      lt_of_lt_of_le d8 (pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right (by norm_num) _))
    have d11 : a - 65 < 64 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub a65, u65, u64]
      refine lt_of_le_of_lt (Nat.sub_le_sub_right d0 _) ?_
      refine lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.sub_le _ _) _) ?_
      norm_num
    rw [UInt64.toNat_shiftLeft d11, d5, Nat.mod_eq_of_lt d12]
    generalize hd : a.toNat - 65 = d
    have d50 : a.toNat = d + 65 := by rw [←hd, Nat.sub_add_cancel d4]
    simp only [d9, d50, UInt64.toNat_sub a65, u65, Nat.add_sub_cancel, pow_add, ←mul_assoc,
      Int.mul_rdiv_cancel d3, d2, Nat.cast_mul]
  · simp only [a65, ite_false]
    have a65' : a.toNat < 65 := by simpa only [not_le, UInt64.lt_iff_toNat_lt, u65] using a65
    have d2 : (r.shiftRightRound (65 - a) up).toNat ≤ 2 ^ 63 := by
      rw [←ha] at a65' ⊢; exact adjust_shift_le_63 r s up a65'
    have d3 : (r.shiftRightRound (65 - a) up).toNat < 2^64 := lt_of_le_of_lt d2 (by norm_num)
    simp only [UInt128.toNat_lo d3, UInt128.toInt_shiftRightRound,
      UInt64.toNat_sub (not_le.mp a65).le, u65]
    rw [←Nat.pow_div a65'.le (by norm_num), Int.rdiv_div (pow_dvd_pow _ a65'.le),
      Nat.cast_pow, Nat.cast_ofNat]

/-- `add_n` respects `ℤ` conversion -/
lemma coe_add_z {r : UInt128} {s : UInt64} {up : Bool}
    (n63 : (add_n r s up).n ≠ 2^63) :
    (add_n r s up : ℤ) = ((r.toNat : ℤ) * 2^(add_adjust r.log2 s).2.toNat).rdiv (2 ^ 65) up := by
  refine Eq.trans ?_ (coe_add_n r s up)
  rw [Int64.coe_of_nonneg]
  simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, add_n_lt r s up n63]

/-- `add_adjust` results in normalized `n` -/
lemma add_n_norm (r : UInt128) (s : UInt64) (up : Bool) :
    add_n r s up ≠ 0 → add_n r s up ≠ .min → (add_adjust r.log2 s).1 ≠ 0 →
      2^62 ≤ (add_n r s up).n := by
  intro r0 _ s0
  simp only [UInt64.le_iff_toNat_le, up62, ←Nat.cast_le (α := ℤ), coe_add_n]
  refine le_trans ?_ (Int.rdiv_le_rdiv (Bool.false_le _))
  have tp : ∀ n, (2 : ℤ)^n = (2^n : ℕ) := by simp only [Nat.cast_pow, Nat.cast_ofNat, forall_const]
  simp only [Int.rdiv, cond_false, tp, ←Nat.cast_mul, ←Nat.cast_div, ←Int.natCast_div, Nat.cast_le]
  rw [Nat.le_div_iff_mul_le (by positivity), ←pow_add]
  refine adjust_le_mul ?_ (UInt64.ne_zero_iff_toNat_ne_zero.mp s0)
  contrapose r0
  simp only [ne_eq, not_not, ←UInt128.eq_zero_iff] at r0 ⊢
  rw [add_n]
  simp only [r0, UInt128.log2_zero, UInt128.zero_lo, UInt64.zero_shiftLeft,
    UInt128.zero_shiftRightRound, ite_self]
  rfl

/-- Turn an almost normalized (`n ≤ 2^63`) value into a `Floating`, shifting right by at most 1 -/
@[irreducible] def small_shift (n s : UInt64) (up : Bool)
    (le_n : (⟨n⟩ : Int64) ≠ 0 → (⟨n⟩ : Int64) ≠ .min → s ≠ 0 → 2^62 ≤ n.toNat)
    (n_le : n.toNat ≤ 2^63) : Floating :=
  if n63 : n = 2^63 then
    bif s = .max then nan else {
      n := 2^62
      s := s + 1
      zero_same := by intro z; contrapose z; decide
      nan_same := by intro n; contrapose n; decide
      norm := by intro _ _ _; decide }
  else if n0 : n = 0 then 0
  else {
    n := ⟨n⟩
    s := s
    zero_same := by intro z; clear n63; contrapose n0; rw [Int64.ext_iff] at z; exact not_not.mpr z
    nan_same := by intro m; rw [Int64.ext_iff] at m; exfalso; exact n63 m
    norm := by
      intro n0 nm s0
      rw [Int64.abs_eq_self', UInt64.le_iff_toNat_le, up62]
      · exact le_n n0 nm s0
      · simpa only [UInt64.eq_iff_toNat_eq, UInt64.toNat_2_pow_63, Int64.isNeg_eq_le,
          decide_eq_false_iff_not, not_le, n_le.lt_iff_ne, ne_eq] using n63 }

/-- Turn an `r * 2^(s - 64 - 2^63)` value into a `Floating` -/
@[irreducible] def add_shift_r (r : UInt128) (s : UInt64) (up : Bool) :
    Floating :=
  let l := r.log2
  bif l == 127 && s == .max then nan else
  let t := add_adjust l s
  let n := bif 65 ≤ t.2 then r.lo <<< (t.2 - 65) else (r.shiftRightRound (65 - t.2) up).lo
  small_shift n t.1 up
    (by simp only [n, Bool.cond_decide]; apply add_n_norm r s up)
    (by simp only [n, Bool.cond_decide]; exact add_n_le r s up)

/-- `small_shift` is correct -/
lemma val_small_shift {n s : UInt64} {up : Bool}
    {le_n : (⟨n⟩ : Int64) ≠ 0 → (⟨n⟩ : Int64) ≠ .min → s ≠ 0 → 2^62 ≤ n.toNat}
    {n_le : n.toNat ≤ 2^63}
    (sn : small_shift n s up le_n n_le ≠ nan) :
    (small_shift n s up le_n n_le).val = (n.toNat : ℝ) * 2^((s.toNat : ℤ) - 2^63) := by
  rw [small_shift] at sn ⊢
  by_cases n63 : n = 2^63
  · simp only [n63, Bool.cond_decide, dite_true, ne_eq, ite_eq_left_iff, not_forall,
      exists_prop] at sn
    rw [val]
    have e : ((2^62 : Int64) : ℤ) = 2^62 := by decide
    simp only [n63, sn.1, decide_False, cond_false, dite_true, e, Int.cast_pow, Int.cast_ofNat,
      UInt64.toInt, UInt64.toNat_add_one' sn.1, Nat.cast_add, Nat.cast_one, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow, Nat.cast_ofNat, UInt64.toNat_2_pow_63,
      Nat.cast_pow, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj]
    ring
  · simp only [n63, Bool.cond_decide, dite_false]
    by_cases n0 : n = 0
    · simp only [n0, dite_true, val_zero, UInt64.toNat_zero, CharP.cast_eq_zero, zero_mul]
    · rw [val]
      simp only [n0, dite_false]
      simp only [UInt64.eq_iff_toNat_eq, UInt64.toNat_2_pow_63, Ne] at n63
      have nn : (⟨n⟩ : Int64).isNeg = false := by
        simp only [Int64.isNeg_eq_le, not_le.mpr (Ne.lt_of_le n63 n_le), decide_False]
      simp only [Int64.coe_of_nonneg nn, Int.cast_natCast, UInt64.toInt]


/-- `add_shift_r` rounds in the correct direction -/
lemma val_add_shift_r (r : UInt128) (s : UInt64) (up : Bool) :
    (r : ℝ) * 2^((s.toNat : ℤ) - 64 - 2^63) ∈ rounds (approx (add_shift_r r s up)) !up := by
  have t0 : (2 : ℝ) ≠ 0 := by norm_num
  generalize hn : add_n r s up = n
  generalize ht : add_adjust r.log2 s = t
  rw [add_shift_r]
  have hn' := hn
  simp only [bif_eq_if, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, add_n, ht] at hn' ⊢
  have hn'' : (if 65 ≤ t.2 then r.lo <<< (t.2 - 65) else (r.shiftRightRound (65 - t.2) up).lo) =
      n.n := by simp only [←hn']
  simp only [hn, hn', hn'']; clear hn'
  by_cases over : r.log2 = 127 ∧ s = UInt64.max
  · simp only [over, UInt64.toNat_max, gt_iff_lt, zero_lt_two, pow_pos, Nat.cast_pred,
      Nat.cast_pow, Nat.cast_ofNat, and_self, ite_true, approx_nan, rounds_univ, mem_univ]
  simp only [over, ite_false]
  simp only [not_and_or] at over
  refine rounds_of_ne_nan (fun sn ↦ ?_)
  rw [val_small_shift sn]
  have en := coe_add_n r s up
  simp only [hn, ht, ←Int.cast_inj (α := ℝ), Int.cast_natCast] at en
  simp only [en]
  induction up
  · simp only [Bool.not_false, ite_true]
    refine le_trans (mul_le_mul_of_nonneg_right Int.rdiv_le two_zpow_pos.le) ?_
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow,
      Nat.cast_ofNat, UInt128.toReal, mul_div_assoc, mul_assoc, ←zpow_natCast, ←zpow_sub₀ t0,
      ←zpow_add₀ t0]
    refine mul_le_mul_of_nonneg_left (zpow_le_of_le (by norm_num) ?_) (Nat.cast_nonneg _)
    rw [←ht, add_adjust_2_eq over]
    linarith
  · simp only [Bool.not_true, ite_false, ge_iff_le]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right Int.le_rdiv two_zpow_pos.le)
    simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow,
      Nat.cast_ofNat, UInt128.toReal, mul_div_assoc, mul_assoc, ←zpow_natCast, ←zpow_sub₀ t0,
      ←zpow_add₀ t0]
    refine mul_le_mul_of_nonneg_left (zpow_le_of_le (by norm_num) ?_) (Nat.cast_nonneg _)
    rw [←ht, add_adjust_2_eq over]
    linarith

/-!
### High 64 bit - 128 bit subtraction
-/

/-- `x * 2^64 - y` -/
@[irreducible, inline] def hi_sub_128 (x : UInt64) (y : UInt128) : UInt128 :=
  let z := -y
  ⟨z.lo, x + z.hi⟩

/-- `hi_sub_128` is correct -/
lemma toNat_hi_sub_128 {x : UInt64} {y : UInt128} (yx : y.toNat ≤ x.toNat * 2^64) :
    (hi_sub_128 x y).toNat = x.toNat * 2^64 - y.toNat := by
  rw [hi_sub_128]
  by_cases y0 : y = 0
  · simp only [y0, UInt128.neg_zero, UInt128.zero_lo, UInt128.zero_hi, add_zero, UInt128.toNat_def,
      UInt64.toNat_zero, zero_mul, tsub_zero]
  -- Replace -y with z
  have ze : y.toNat = 2^128 - (-y).toNat := by
    have h := UInt128.toNat_neg y
    simp only [y0, ite_false] at h
    rw [h, Nat.sub_sub_self y.toNat_lt.le]
  rw [ze] at yx ⊢
  generalize -y = z at yx
  simp only [UInt128.toNat_def] at yx ⊢
  clear y0 ze y
  -- Deal with `(x + z.hi).toNat`
  have xz0 : 2^64 ≤ x.toNat + z.hi.toNat := by
    have h := z.lo.toNat_lt
    norm_num only at yx h ⊢
    omega
  have xz1 : x.toNat + z.hi.toNat < 2^65 := by
    have h0 := x.toNat_lt
    have h1 := z.hi.toNat_lt
    norm_num only at h0 h1 ⊢
    omega
  have xz2 : (x + z.hi).toNat = x.toNat + z.hi.toNat - 2^64 := by
    rw [UInt64.toNat_add, UInt64.size_eq_pow]
    nth_rw 1 [←Nat.sub_add_cancel xz0, Nat.add_mod_right, Nat.mod_eq_of_lt]
    exact Nat.sub_lt_right_of_lt_add xz0 xz1
  rw [xz2]; clear xz1 xz2
  -- Unfortunately omega chokes on this, so I have to do it manually
  have e : 2^64 * 2^64 = 2^128 := by norm_num
  have z0 := z.toNat_lt.le; rw [UInt128.toNat_def] at z0
  have z1 : 2^128 ≤ x.toNat * 2^64 + z.hi.toNat * 2^64 := by
    rw [←add_mul]; exact le_trans (by norm_num) (Nat.mul_le_mul_right _ xz0)
  simp only [Nat.mul_sub_right_distrib, add_mul, e, ←Nat.sub_sub_assoc z0, ←Nat.sub_add_comm z1,
    add_assoc]

/-!
### Addition (definition)
-/

/-- Exactly rounded floating point addition, with `0 < x` and special cases removed -/
@[irreducible, pp_dot, inline] def add_to_128 (x y : Floating) (up : Bool) : UInt128 :=
  let yn := y.n.isNeg
  let z := bif yn then -y.n else y.n
  let y := (⟨0, z.n⟩ : UInt128).shiftRightRound (x.s - y.s) (up != yn)
  bif yn then hi_sub_128 x.n.n y else ⟨y.lo, x.n.n + y.hi⟩

/-- Exactly rounded floating point addition, with `0 < x` and special cases removed -/
@[irreducible, pp_dot, inline] def pos_add (x y : Floating) (up : Bool) : Floating :=
  add_shift_r (add_to_128 x y up) x.s up

/-- Exactly rounded floating point addition, with most special cases removed -/
@[irreducible, pp_dot, inline] def add_core (x y : Floating) (up : Bool) : Floating :=
  -- Arrange for x to be positive
  let (z, x, y) := bif x.n.isNeg then (true, -x, -y) else (false, x, y)
  -- Add
  let r := pos_add x y (up != z)
  -- Restore the sign of x
  bif z then -r else r

/-- Absolute value comparison, ignoring special cases -/
@[irreducible, pp_dot] def add_bigger (x y : Floating) : Bool :=
  bif x.s == y.s then y.n.abs ≤ x.n.abs else y.s < x.s

/-- Exactly rounded floating point addition -/
@[irreducible, pp_dot] def add (x y : Floating) (up : Bool) : Floating :=
  -- Handle special cases
  bif x == 0 || y == nan then y else
  bif y == 0 || x == nan then x else
  -- Arrange for x to have the larger exponent
  let (x, y) := bif x.add_bigger y then (x, y) else (y, x)
  -- Add
  add_core x y up

/-!
### Addition is correct
-/

/-- `add_bigger` doesn't care about sign -/
@[simp] lemma add_bigger_neg {x y : Floating} : (-x).add_bigger (-y) = x.add_bigger y := by
  rw [add_bigger, add_bigger]
  simp only [s_neg, n_neg, Int64.abs_neg]

/-- `add_bigger` doesn't care about abs -/
@[simp] lemma add_bigger_abs {x y : Floating} : x.add_bigger y.abs = x.add_bigger y := by
  rw [add_bigger, add_bigger]
  simp only [s_neg, n_neg, Int64.abs_neg, n_abs, Int64.abs_abs, s_abs]

/-- `add_bigger` is antisymmetric -/
@[simp] lemma not_add_bigger {x y : Floating} (h : ¬x.add_bigger y) :
    y.add_bigger x := by
  rw [add_bigger] at h ⊢
  simp only [bif_eq_if, beq_iff_eq, Bool.ite_eq_true_distrib, decide_eq_true_eq] at h ⊢
  by_cases e : x.s = y.s
  · simp only [e, lt_self_iff_false, ite_true, not_le] at h ⊢
    exact h.le
  · simp only [e, ite_false, not_lt, Ne.symm e] at h ⊢
    exact Ne.lt_of_le e h

lemma add_bigger_s {x y : Floating} (h : x.add_bigger y) : y.s ≤ x.s := by
  by_cases e : x.s = y.s
  · simp only [e, le_refl]
  · rw [add_bigger] at h
    simp only [bif_eq_if, beq_iff_eq, e, ite_false, decide_eq_true_eq] at h
    exact h.le

lemma add_bigger_n {x y : Floating} (h : x.add_bigger y) (xn : x.n.isNeg = false) (e : x.s = y.s) :
    y.n.abs ≤ x.n.n := by
  rw [add_bigger] at h
  simpa only [e, beq_self_eq_true, Int64.abs_eq_self' xn, lt_self_iff_false, decide_False,
    bif_eq_if, ite_true, decide_eq_true_eq] using h

/-- The shifting we do of `y` in `add_to_128` produces a small value -/
lemma add_to_128_shift_lt {y : Int64} {s : UInt64} {up : Bool} (yn : y.isNeg = false) :
    ((⟨0, y.n⟩ : UInt128).shiftRightRound s up).hi.toNat < 2^63 := by
  simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le] at yn
  exact lt_of_le_of_lt UInt128.toNat_hi_shiftRightRound_le_hi yn

/-- The shifting we do of `y` in `add_to_128` produces a small value -/
lemma add_to_128_shift_le {x y : Floating} (xy : x.add_bigger y) {up : Bool}
    (xn : x.n.isNeg = false) (yn : y.n.isNeg = false) :
    ((⟨0, y.n.n⟩ : UInt128).shiftRightRound (x.s - y.s) up).toNat ≤ x.n.n.toNat * 2^64 := by
  have h := UInt128.toInt_shiftRightRound ⟨0, y.n.n⟩ (x.s - y.s) up
  generalize hs : x.s - y.s = s at h
  generalize (⟨0, y.n.n⟩ : UInt128).shiftRightRound s up = z at h
  contrapose h; simp only [not_le] at h
  apply ne_of_gt
  refine lt_of_le_of_lt ?_ (Nat.cast_lt.mpr h)
  clear h z
  by_cases s0 : x.s = y.s
  · simp only [s0, sub_self] at hs
    simp only [← Int64.abs_eq_self' yn, UInt128.toNat_def, UInt64.toNat_zero, add_zero,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← hs, pow_zero, Int.rdiv_one, ←
      Int64.abs_eq_self' xn, gt_iff_lt, zero_lt_two, pow_pos, mul_le_mul_right, Nat.cast_le,
      UInt64.toNat_le_toNat]
    rw [add_bigger, s0] at xy
    simpa only [beq_self_eq_true, lt_self_iff_false, decide_False, cond_true,
      decide_eq_true_eq] using xy
  · have yxs : y.s < x.s := (Ne.symm s0).lt_of_le (add_bigger_s xy)
    have yxs' := (UInt64.lt_iff_toNat_lt _ _).mp yxs
    have s0 : 0 < s.toNat := by rw [←hs, UInt64.toNat_sub yxs.le]; omega
    by_cases x0 : x = 0
    · simp only [x0, s_zero, UInt64.toNat_zero, not_lt_zero'] at yxs'
    have le_x : 2^62 ≤ x.n.n.toNat := by
      rw [←Int64.abs_eq_self' xn]; exact x.norm' x0 (Nat.not_eq_zero_of_lt yxs)
    rw [←Int.cast_le (α := ℝ)]
    simp only [UInt128.toNat_def, UInt64.toNat_zero, add_zero, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_ofNat]
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr le_x) (by positivity))
    have e0 : ∀ n, (2:ℤ)^n = (2^n : ℕ) := by simp only [Nat.cast_pow, Nat.cast_ofNat, forall_const]
    have e1 : ∀ n, (2^n  : ℝ) = (2^n : ℕ) := by simp only [Nat.cast_pow, Nat.cast_ofNat, forall_const]
    by_cases slt : s.toNat ≤ 64
    · nth_rw 1 [←Nat.sub_add_cancel slt]
      rw [pow_add, ←mul_assoc, e0, e0, Int.mul_rdiv_cancel (pow_ne_zero _ (by norm_num))]
      simp only [e0, e1, ←Nat.cast_mul, ←Nat.cast_add_one, ←Nat.cast_add, Nat.cast_lt,
        Int.cast_natCast]
      rw [Nat.cast_le]
      simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le] at yn
      refine le_trans (Nat.mul_le_mul_right _ yn.le) ?_
      simp only [←pow_add, ←Nat.add_sub_assoc slt]
      exact pow_le_pow_right (by norm_num) (by omega)
    · refine le_trans Int.rdiv_lt.le ?_
      trans y.n.n.toNat + 1
      · simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow,
          Nat.cast_ofNat, add_le_add_iff_right, mul_div_assoc]
        simp only [not_le] at slt
        refine mul_le_of_le_one_right (Nat.cast_nonneg _) ?_
        exact div_le_one_of_le (pow_le_pow_right (by norm_num) slt.le) (by norm_num)
      · simp only [e0, e1, ←Nat.cast_mul, ←Nat.cast_add_one, ←Nat.cast_add, Nat.cast_le]
        refine le_trans (add_le_add_right y.n.n.toNat_lt.le _) ?_
        refine le_trans ?_ (Nat.le_add_right _ _)
        norm_num

/-- Common alternative spelling of `val` -/
@[simp] lemma mul_64_pow (x : ℝ) (s : ℤ) : x * 2^64 * 2 ^ (s - 64 - 2^63) = x * 2 ^ (s - 2^63) := by
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  have e : (2:ℝ)^(64 : ℤ) = 2^64 := zpow_ofNat _ 64
  simp only [zpow_sub₀ t0, div_eq_mul_inv, mul_assoc, mul_eq_mul_left_iff, e]
  simp only [← mul_assoc, mul_comm _ ((2:ℝ)^64)⁻¹, mul_eq_mul_right_iff, inv_eq_zero]
  rw [inv_mul_cancel (by norm_num)]
  simp only [one_mul, true_or]

/-- Common alternative spelling of `val` -/
lemma val_64 (x : Floating) : x.val = (x.n : ℝ) * 2^64 * 2 ^ ((x.s.toNat : ℤ) - 64 - 2^63) := by
  rw [mul_64_pow, val]; rfl

/-- `add_to_128` rounds in the correct direction -/
lemma val_add_to_128 {x y : Floating} (up : Bool) (yn : y ≠ nan) (y0 : y ≠ 0)
    (xy : x.add_bigger y) (x0' : x.n.isNeg = false) :
    x.val + y.val ∈
      rounds {((add_to_128 x y up) : ℝ) * 2^((x.s.toNat : ℤ) - 64 - 2^63)} !up := by
  rw [add_to_128]
  simp only [mem_rounds_singleton, Bool.not_eq_true', UInt128.toReal, UInt128.toNat_def]
  have t0 : (2:ℝ) ≠ 0 := by norm_num
  have pe : (2:ℝ)^((x.s.toNat : ℤ) - 64 - 2^63) = (2^64)⁻¹ * 2^((x.s.toNat : ℤ) - 2^63) := by
    simp only [zpow_sub₀ t0, zpow_natCast, div_eq_mul_inv, ← mul_assoc, mul_eq_mul_right_iff,
      inv_eq_zero]
    left; rw [mul_comm]; rfl
  have xe : x.val = (x.n.n.toNat : ℝ) * 2^((x.s.toNat : ℤ) - 2^63) := by
    rw [val, Int64.coe_of_nonneg x0', UInt64.toInt]; rfl
  have yxs : y.s ≤ x.s := add_bigger_s xy
  have yxs' : y.s.toNat ≤ x.s.toNat := by rwa [←UInt64.le_iff_toNat_le]
  have he : ∀ y, (⟨0,y⟩ : UInt128).toNat = y.toNat * 2^64 := by
    intro y; simp only [UInt128.toNat_def, UInt64.toNat_zero, add_zero]
  generalize hu : (bif y.n.isNeg then -y.n else y.n) = u
  have uy : u = y.abs.n := by
    simp only [← hu, Int64.neg_def, bif_eq_if, n_abs, Int64.abs, Int64.ext_iff,
      apply_ite (f := fun x : Int64 ↦ x.n)]
  have un : u.isNeg = false := by
    by_cases h : y.n.isNeg
    · simp only [←hu, h, cond_true, Int64.isNeg_neg (y.n_ne_zero y0) (y.n_ne_min yn), Bool.not_true]
    · simp only [Bool.not_eq_true] at h; simp only [← hu, h, cond_false]
  have um : u ≠ .min := by
    rw [←hu, bif_eq_if]; split_ifs
    repeat simp only [ne_eq, Int64.neg_eq_min, y.n_ne_min yn, not_false_eq_true]
  generalize hz : (⟨0, u.n⟩ : UInt128).shiftRightRound (x.s - y.s) (up != y.n.isNeg) = z
  generalize hv : (z.hi.toNat : ℝ) + z.lo.toNat * (2^64)⁻¹ = v
  have zx : z.toNat ≤ x.n.n.toNat * 2^64 := by
    rw [←hz, uy, ←s_abs (x := y)]
    refine add_to_128_shift_le ?_ x0' ?_
    · simpa only [add_bigger_abs]
    · simp only [n_abs, Int64.isNeg_abs (y.n_ne_min yn)]
  have zh : z.hi.toNat < 2^63 := by rw [←hz]; exact add_to_128_shift_lt un
  have hv' : v * 2^64 = z.toNat := by
    simp only [← hv, add_mul, ne_eq, Nat.zero_lt_succ, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
      not_false_eq_true, inv_mul_cancel_right₀, UInt128.toNat_def, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
  have a := UInt128.approx_shiftRightRound ⟨0, u.n⟩ (x.s - y.s) (up != y.n.isNeg)
  simp only [UInt128.toReal, hz, ← hv', mul_comm _ ((2:ℝ)^64), he, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, UInt64.toNat_sub yxs, mul_div_assoc ((2:ℝ)^64), mem_rounds_singleton,
    zero_lt_two, pow_pos, mul_le_mul_left, Bool.xor_false] at a
  simp only [Bool.not_eq_true', ← Int64.toReal_toInt un, pow_sub₀ _ t0 yxs', ← div_eq_mul_inv, ←
    div_mul, ← mul_div_right_comm, div_le_iff two_pow_pos, le_div_iff two_pow_pos] at a
  by_cases yn : y.n.isNeg = false
  · simp only [yn, cond_false, Bool.xor_false, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, UInt64.toNat_add, UInt64.size_eq_pow, Bool.not_eq_true] at hz hu a ⊢
    have xz : x.n.n.toNat + z.hi.toNat < 2^64 := by
      simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le] at x0'; linarith
    simp only [Nat.mod_eq_of_lt xz, Nat.cast_add, pe, ← mul_assoc, add_mul _ _ _⁻¹, ne_eq,
      Nat.zero_lt_succ, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_inv_cancel_right₀, add_assoc, hv]
    simp only [add_mul, ← xe, add_le_add_iff_left]
    rw [val, hu, UInt64.toInt]
    simp only [zpow_sub₀ t0, zpow_natCast, div_eq_mul_inv, ← mul_assoc, neg_le_neg_iff, gt_iff_lt,
      inv_pos, two_zpow_pos, mul_le_mul_right]
    induction up; repeat exact a
  · simp only [yn, cond_true, Bool.xor_true, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ←UInt128.toNat_def, Bool.not_eq_true'] at hu a ⊢
    replace hu : y.n = -u := by rw [←hu, neg_neg]
    rw [toNat_hi_sub_128 zx]
    have e : ((x.n.n.toNat * 2^64 - z.toNat : ℕ) : ℤ) = (x.n.n.toNat : ℤ) * 2^64 - z.toNat := by
      omega
    rw [←Int.cast_inj (α := ℝ), Int.cast_natCast] at e
    simp only [e, ← Int64.coe_of_nonneg x0', Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat, Int.cast_ofNat, sub_mul, ←val_64, sub_le_add_iff_left,
      add_le_sub_iff_left, ←hv', Int.cast_natCast]
    rw [val, hu, Int64.coe_neg um, Int.cast_neg, neg_mul, mul_64_pow]
    simp only [zpow_sub₀ t0, zpow_natCast, div_eq_mul_inv, ← mul_assoc, neg_le_neg_iff, gt_iff_lt,
      inv_pos, two_zpow_pos, mul_le_mul_right]
    exact a

/-- `pos_add` rounds in the correct direction -/
lemma val_pos_add {x y : Floating} {up : Bool} (yn : y ≠ nan) (y0 : y ≠ 0) (xy : x.add_bigger y)
    (x0' : x.n.isNeg = false) :
    x.val + y.val ∈ rounds (approx (x.pos_add y up)) !up := by
  rw [pos_add]
  have h0 := val_add_to_128 up yn y0 xy x0'
  generalize hz : add_to_128 x y up = z at h0
  have h1 := val_add_shift_r z x.s up
  generalize hw : add_shift_r z x.s up = w at h1
  by_cases wn : w = nan
  · simp only [wn, approx_nan, rounds_univ, mem_univ]
  · simp only [approx_eq_singleton wn, mem_rounds_singleton, Bool.not_eq_true'] at h1 h0 ⊢
    induction up
    · simp only [ite_true, ge_iff_le] at h0 h1 ⊢; linarith
    · simp only [ite_false, ge_iff_le] at h0 h1 ⊢; linarith

/-- `add_core` rounds in the correct direction -/
lemma val_add_core {x y : Floating} {up : Bool} (xn : x ≠ nan) (yn : y ≠ nan) (x0 : x ≠ 0)
    (y0 : y ≠ 0) (xy : x.add_bigger y) :
    x.val + y.val ∈ rounds (approx (x.add_core y up)) !up := by
  rw [add_core]
  simp only [bif_eq_if]
  by_cases z : x.n.isNeg
  · simp only [z, ite_true, Bool.xor_true, approx_neg, rounds_neg, Bool.not_not, mem_neg,
      neg_add_rev, add_comm _ (-x).val, ←val_neg xn, ←val_neg yn]
    nth_rw 2 [←Bool.not_not up]
    apply val_pos_add
    repeat simpa only [ne_eq, neg_eq_nan_iff, neg_eq_zero_iff, s_neg, n_neg,
      Int64.isNeg_neg (x.n_ne_zero x0) (x.n_ne_min xn), Bool.not_eq_false', add_bigger_neg]
  · simp only [z, ite_false, Bool.xor_false]
    simp only [Bool.not_eq_true] at z
    exact val_pos_add yn y0 xy z

/-- `add` rounds in the correct direction -/
lemma approx_add (x y : Floating) (up : Bool) :
    approx x + approx y ⊆ rounds (approx (x.add y up)) !up := by
  rw [add]
  generalize hs : (if x.add_bigger y then (x, y) else (y, x)) = s
  simp only [bif_eq_if, beq_iff_eq, Bool.or_eq_true]
  by_cases x0 : x = 0
  · simp only [x0, ne_eq, zero_ne_nan, not_false_eq_true, approx_eq_singleton, val_zero,
      singleton_add, zero_add, image_id', true_or, or_false, ite_true]
    apply subset_rounds
  simp only [x0, false_or]
  by_cases yn : y = nan
  · simp only [yn, approx_nan, ite_true, rounds_univ, subset_univ]
  simp only [yn, if_false]
  by_cases y0 : y = 0
  · simp only [y0, ne_eq, zero_ne_nan, not_false_eq_true, approx_eq_singleton, val_zero,
      add_singleton, add_zero, image_id', true_or, ite_true]
    apply subset_rounds
  by_cases xn : x = nan
  · simp only [xn, approx_nan, or_true, true_or, ite_true, rounds_univ, subset_univ]
  simp only [ne_eq, xn, not_false_eq_true, approx_eq_singleton, yn, add_singleton, image_singleton,
    or_self, ite_false, singleton_subset_iff]
  simp only [x0, y0, ite_false]
  by_cases xy : x.add_bigger y
  · simp only [xy, ite_true] at hs
    simp only [or_self, xy, ite_true, ite_false]
    exact val_add_core xn yn x0 y0 xy
  · simp only [xy, ite_false] at hs
    simp only [add_comm _ y.val, or_self, xy, ite_false]
    exact val_add_core yn xn y0 x0 (not_add_bigger xy)

/-- `add` propagates `nan` -/
@[simp] lemma add_nan {x : Floating} {up : Bool} : x.add nan up = nan := by
  rw [add]; simp only [beq_self_eq_true, Bool.or_true, cond_true]

/-- `add` propagates `nan` -/
@[simp] lemma nan_add {x : Floating} {up : Bool} : (nan : Floating).add x up = nan := by
  rw [add]
  simp only [beq_self_eq_true, Bool.or_true, bif_eq_if, ite_true, Bool.or_eq_true, beq_iff_eq,
    nan_ne_zero, false_or, ite_eq_right_iff, imp_self]

/-- `add` propagates `nan` -/
lemma ne_nan_of_add {x y : Floating} {up : Bool} (n : x.add y up ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n; simp only [ne_eq, not_and_or, not_not] at n ⊢
  rw [add]; simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  rcases n with n | n
  · simp only [n, nan_ne_zero, false_or, or_true, ite_true, ite_eq_right_iff, imp_self]
  · simp only [n, or_true, nan_ne_zero, false_or, ite_true]

/-- `add _ _ false` rounds down -/
lemma add_le {x y : Floating} (n : x.add y false ≠ nan) :
    (x.add y false).val ≤ x.val + y.val := by
  have h := approx_add x y false
  rcases ne_nan_of_add n with ⟨n0, n1⟩
  simpa only [approx_eq_singleton n0, approx_eq_singleton n1, add_singleton,
    image_singleton, approx_eq_singleton n, Bool.not_false, singleton_subset_iff,
    mem_rounds_singleton, ite_true] using h

/-- `add _ _ true` rounds up -/
lemma le_add {x y : Floating} (n : x.add y true ≠ nan) :
    x.val + y.val ≤ (x.add y true).val := by
  have h := approx_add x y true
  rcases ne_nan_of_add n with ⟨n0, n1⟩
  simpa only [approx_eq_singleton n0, approx_eq_singleton n1, add_singleton,
    image_singleton, approx_eq_singleton n, Bool.not_true, singleton_subset_iff,
    mem_rounds_singleton, ite_false] using h

/-!
### Subtraction

We use `x - y = x + -y`.
-/

@[irreducible, pp_dot] def sub (x y : Floating) (up : Bool) : Floating :=
  x.add (-y) up

/-- Definition lemma for easy of use -/
lemma sub_eq_add_neg (x y : Floating) (up : Bool) : x.sub y up = x.add (-y) up := by rw [sub]

/-- `sub` rounds in the correct direction -/
lemma approx_sub (x y : Floating) (up : Bool) :
    approx x - approx y ⊆ rounds (approx (x.sub y up)) !up := by
  rw [sub_eq_add_neg, _root_.sub_eq_add_neg, ←approx_neg]
  apply approx_add

/-- `sub` propagates `nan` -/
@[simp] lemma sub_nan {x : Floating} {up : Bool} : x.sub nan up = nan := by
  simp only [sub_eq_add_neg, neg_nan, add_nan]

/-- `sub` propagates `nan` -/
@[simp] lemma nan_sub {x : Floating} {up : Bool} : (nan : Floating).sub x up = nan := by
  simp only [sub_eq_add_neg, nan_add]

/-- `sub` propagates `nan` -/
lemma ne_nan_of_sub {x y : Floating} {up : Bool} (n : x.sub y up ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  rw [sub_eq_add_neg] at n
  have h := ne_nan_of_add n
  rwa [Ne, Ne, neg_eq_nan_iff, ←Ne] at h

/-- `sub _ _ false` rounds down -/
lemma sub_le {x y : Floating} (n : x.sub y false ≠ nan) :
    (x.sub y false).val ≤ x.val - y.val := by
  have yn := (ne_nan_of_sub n).2
  simp only [sub_eq_add_neg, ne_eq, _root_.sub_eq_add_neg, ← val_neg yn, ge_iff_le] at n ⊢
  exact add_le n

/-- `sub _ _ true` rounds up -/
lemma le_sub {x y : Floating} (n : x.sub y true ≠ nan) :
    x.val - y.val ≤ (x.sub y true).val := by
  have yn := (ne_nan_of_sub n).2
  simp only [sub_eq_add_neg, ne_eq, _root_.sub_eq_add_neg, ← val_neg yn, ge_iff_le] at n ⊢
  exact le_add n
