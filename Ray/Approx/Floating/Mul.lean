import Ray.Approx.Bool
import Ray.Approx.Floating.Abs
import Ray.Approx.Floating.Neg
import Ray.Approx.Int128

open Pointwise

/-!
## Floating point multiplication

For floating point, multiplication is easier than addition, as the exponent adds.
If `z = x * y`, we have

  `z.n * 2^(z.s - 2^63) = x.n * y.n * 2^(x.s + y.s - 2^63 - 2^63)`
-/

open Set
open scoped Real
namespace Floating

/-!
### Auxiliary lemmas
-/

/-- The limit for our 64 bit → 128 bit multiplication -/
def mul_n_max : ℕ := (2^63 - 1) ^ 2

/-- Our `64 → 128` bit integer multiplication doesn't get too big -/
lemma mul_n_le {x y : Floating} (x0 : 0 ≤ x.val) (y0 : 0 ≤ y.val) :
    (mul128 x.n.n y.n.n).toNat ≤ mul_n_max := by
  rw [toNat_mul128, mul_n_max, pow_two]
  have hx := n_lt_of_nonneg x0
  have hy := n_lt_of_nonneg y0
  exact Nat.mul_le_mul (by omega) (by omega)

/-!
### Normalization of the inner integer multiplication
-/

/-- Normalize a 128-bit `n` into a 64-bit one, rounding and shifting as necessary.
    We also return how much we shifted left by. -/
@[irreducible, inline] def mul_norm (n : UInt128) (up : Bool) : UInt64 × UInt64 :=
  let t := n.log2
  let s := 126 - t
  -- Shift left to normalize
  let z : UInt128 := n <<< s
  -- Round to a single word
  let r : UInt64 := z.hi + bif z.lo != 0 && up then 1 else 0
  -- If we round up too much, shift down by one
  bif r == 2^63 then (2^62, s - 1) else (r, s)

/-- `mul_norm` returns a normalized, correctly rounded value.

    I think writing a bunch of separate lemmas in `Add.lean` made the result super long.
    Part of that is that the situation was very non-modular, as the component routine
    semantics were very coupled.  Here in `Mul.lean` things are hopefully better factored,
    and ideally that means only `mul_norm` needs to know the internals of the `mul_norm` proof. -/
lemma mul_norm_correct (n : UInt128) (up : Bool) (n0 : n ≠ 0) (lo : n.toNat ≤ mul_n_max) :
    (mul_norm n up).1.toNat ∈ Ico (2^62) (2^63) ∧
      (n.toNat : ℝ) ∈ rounds {
        ((mul_norm n up).1.toNat : ℝ) * 2 ^ (64 - ((mul_norm n up).2.toNat : ℤ))} !up := by
  rw [mul_norm]
  generalize ht : n.log2 = t
  generalize hs : 126 - t = s
  generalize hz : n <<< s = z
  generalize hb : (bif z.lo != 0 && up then (1 : UInt64) else 0) = b
  generalize hr : z.hi + b = r
  generalize hp : (bif r == 2^63 then (2^62, s - 1) else (r, s)) = p
  simp only [hz, Bool.and_eq_true, bne_iff_ne, ne_eq, hr, mem_Ico, hb, hs, hp]
  simp only [UInt64.eq_iff_toNat_eq, UInt128.toNat_log2, UInt128.eq_iff_toNat_eq,
    UInt128.toNat_shiftLeft', UInt64.toNat_add, UInt64.size_eq_pow,
    apply_ite (f := fun x : UInt64 ↦ x.toNat), UInt64.toNat_zero,
    UInt64.toNat_one, beq_iff_eq, up63] at ht hz hb hr hs hp
  rw [UInt128.ne_zero_iff] at n0
  have t0 : (2 : ℝ) ≠ 0 := by norm_num
  have t_le : t.toNat ≤ 126 := by
    rw [←ht, ←Nat.lt_succ_iff, Nat.log2_lt n0]; exact lt_of_le_of_lt lo (by norm_num [mul_n_max])
  have t_le' : t ≤ 126 := by simp only [UInt64.le_iff_toNat_le, u126, t_le]
  simp only [UInt64.toNat_sub t_le', u126] at hs
  have s_lt : s.toNat < 128 := by rw [←hs]; omega
  have nt' : n.toNat * 2^s.toNat < 2^127 := by
    refine lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (by positivity)) ?_
    simp only [ht, ← pow_add, ←hs]
    exact pow_le_pow_right (by norm_num) (by omega)
  have nt : n.toNat * 2^s.toNat < 2^128 := lt_trans nt' (by norm_num)
  have b1 : b.toNat ≤ 1 := by rw [←hb, bif_eq_if]; split_ifs; repeat norm_num
  simp only [UInt64.toNat_sub t_le', u126, Nat.mod_eq_of_lt s_lt, Nat.mod_eq_of_lt nt] at hz
  have z_lt : z.toNat < 2^127 := by rwa [←hz]
  have r_le : z.hi.toNat + b.toNat ≤ 2^63 := by
    rw [UInt128.toNat_def] at z_lt
    contrapose z_lt; simp only [not_le, not_lt] at z_lt ⊢
    have zh63 : 2^63 ≤ z.hi.toNat := by omega
    exact le_trans (le_trans (by norm_num) (Nat.mul_le_mul_right _ zh63)) (Nat.le_add_right _ _)
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt r_le (by norm_num))] at hr
  rw [hr] at r_le
  have le_z : 2^126 ≤ z.toNat := by
    rw [←hz, ←hs, ←ht]
    refine le_trans ?_ (Nat.mul_le_mul_right _ (Nat.log2_self_le n0))
    rw [←pow_add]
    exact pow_le_pow_right (by norm_num) (by omega)
  have le_r : 2^62 ≤ r.toNat := by
    rw [←hr]
    refine le_trans ?_ (Nat.le_add_right _ _)
    rw [UInt128.toNat_def] at le_z
    have zl := z.lo.toNat_lt
    norm_num only at le_z zl ⊢
    omega
  simp only [rounds, mem_singleton_iff, Bool.not_eq_true', exists_eq_left, mem_setOf_eq]
  by_cases r_eq : r == 2^63
  · simp only [r_eq, cond_true] at hp
    simp only [←hp]
    constructor
    · decide
    · simp only [beq_iff_eq] at r_eq
      have not_up : up = true := by
        contrapose r_eq
        apply ne_of_lt
        simp only [Bool.not_eq_true] at r_eq
        simp only [r_eq, Bool.and_false, cond_false, UInt64.toNat_zero] at hb
        simp only [←hb, add_zero] at hr
        simp only [UInt64.lt_iff_toNat_lt, ←hr, UInt64.toNat_2_pow_63]
        simp only [UInt128.toNat_def] at z_lt
        have zl := z.lo.toNat_lt
        norm_num only at z_lt zl ⊢
        omega
      simp only [not_up, Bool.and_true, up62, Nat.cast_pow, Nat.cast_ofNat, ite_false] at hb ⊢
      clear not_up up
      have s1 : 1 ≤ s.toNat := by
        rw [Nat.one_le_iff_ne_zero]
        contrapose r_eq
        apply ne_of_lt
        simp only [ne_eq, not_not] at r_eq
        simp only [r_eq, pow_zero, mul_one, tsub_eq_zero_iff_le, ←UInt128.eq_iff_toNat_eq] at hz
        simp only [UInt64.lt_iff_toNat_lt, ←hz, ←hr, UInt64.toNat_2_pow_63]
        simp only [UInt128.toNat_def, mul_n_max] at lo
        refine lt_of_le_of_lt (Nat.add_le_add_left b1 _) ?_
        norm_num only at lo ⊢
        omega
      have s1' : 1 ≤ s := by simpa only [UInt64.le_iff_toNat_le, UInt64.toNat_one]
      simp only [UInt64.toNat_sub s1', UInt64.toNat_one, Nat.cast_sub s1, Nat.cast_one,
        pow_mul_zpow t0, Nat.cast_ofNat, ge_iff_le]
      simp only [← hs, Nat.cast_sub t_le, Nat.cast_ofNat, Nat.cast_one]
      ring_nf
      rw [add_comm, ←Nat.cast_add_one, zpow_natCast, ←Nat.cast_two, ←Nat.cast_pow, Nat.cast_le, ←ht]
      exact Nat.lt_log2_self.le
  · simp only [r_eq, cond_false] at hp
    simp only [beq_iff_eq, UInt64.eq_iff_toNat_eq, up63] at r_eq
    simp only [← hp, le_r, r_le.lt_of_ne r_eq, and_self, true_and]
    have hz' : (n.toNat : ℝ) = z.toNat / 2 ^ s.toNat := by
      simp only [← hz, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ne_eq, pow_eq_zero_iff',
        OfNat.ofNat_ne_zero, false_and, not_false_eq_true, mul_div_cancel_right₀]
    have ep : (2:ℝ) ^ (64:ℤ) = 2^64 := zpow_ofNat _ _
    induction up
    · simp only [Bool.and_false, cond_false, UInt64.toNat_zero] at hb
      simp only [←hr, ←hb, add_zero, zpow_sub₀ t0, ep, zpow_natCast, ←mul_div_assoc, hz', ite_true]
      simp only [UInt128.toNat_def, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        add_div, le_add_iff_nonneg_right, ge_iff_le]
      positivity
    · by_cases l0 : z.lo = 0
      · simp only [l0, bne_self_eq_false, Bool.and_true, cond_false, UInt64.toNat_zero] at hb
        simp only [← hr, ← hb, add_zero, zpow_sub₀ t0, ep, zpow_natCast, hz', z.toNat_def, l0,
          UInt64.toNat_zero, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_assoc, le_refl,
          ite_self]
      · simp only [Bool.and_true, bif_eq_if, bne_iff_ne, ne_eq, l0, not_false_eq_true, ite_true,
          UInt64.toNat_one] at hb
        simp only [← hr, ← hb, Nat.cast_add, Nat.cast_one, zpow_sub₀ t0, ep, zpow_natCast, ←
          mul_div_assoc, add_one_mul, hz', z.toNat_def, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          div_le_div_right two_pow_pos, add_le_add_iff_left, ite_false, ge_iff_le]
        exact le_trans (Nat.cast_le.mpr z.lo.toNat_lt.le) (by norm_num)

/-!
### The definition of multiplication
-/

/-- Build a `Floating` with value `n * 2^s`, rounding if necessary -/
@[irreducible, inline] def mul_finish (n : UInt64) (s : Int128) (up : Bool)
    (norm : n.toNat ∈ Ico (2^62) (2^63)) : Floating :=
  bif s.n.hi == 0 then { -- Exponent is already 64 bits, so not much to do
    n := ⟨n⟩
    s := s.n.lo
    zero_same := by
      intro n0
      simp only [Int64.ext_iff, Int64.n_zero] at n0
      simp only [n0, UInt64.toNat_zero, mem_Ico, nonpos_iff_eq_zero, gt_iff_lt, zero_lt_two,
        pow_pos, and_true] at norm
    nan_same := by
      intro nm
      simp only [Int64.ext_iff, Int64.n_min] at nm
      simp only [nm, UInt64.toNat_2_pow_63, mem_Ico, lt_self_iff_false, and_false] at norm
    norm := by
      intro _ _ _
      simp only [mem_Ico] at norm
      rw [Int64.abs_eq_self']
      · simp only [UInt64.le_iff_toNat_le, up62, norm.1]
      · simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, norm.2] }
  else bif s.isNeg then bif up then min_norm else 0  -- Flush denormals for now
  else nan -- Overflow, exponent too big

/-- Twos complement, 128-bit exponent `e = xs + ys + t + 64 - 2^63` -/
@[irreducible, inline] def mul_exponent (xs ys t : UInt64) : Int128 :=
  xs + ys - t - .ofNat (2^63 - 64)

/-- Multiply two nonnegative, non-nan `Floating`s -/
@[irreducible, inline] def mul_of_nonneg (x y : Floating) (up : Bool)
    (x0 : 0 ≤ x.val) (y0 : 0 ≤ y.val) : Floating :=
  let z := mul128 x.n.n y.n.n  -- `z * 2^(x.s + y.s - 2^64)`.
  if z0 : z = 0 then 0 else
  let n := mul_norm z up  -- `n.1 * 2^(x.s + y.s + n.2 - 62 - 2^64)`
  let e := mul_exponent x.s y.s n.2  -- `n.1 * 2^e`
  mul_finish n.1 e up (mul_norm_correct z up z0 (mul_n_le x0 y0)).1

/-- Floating point multiply -/
@[irreducible] def mul (x y : Floating) (up : Bool) : Floating :=
  if n : x = nan ∨ y = nan then nan else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_nonneg x.abs y.abs (up != p)
    (abs_nonneg (not_or.mp n).1) (abs_nonneg (not_or.mp n).2)
  bif p then -z else z

/-!
### Multiplication is correct
-/

/-- `mul_finish` is correct -/
lemma mul_finish_correct (n : UInt64) (s : Int128) (up : Bool)
    (norm : n.toNat ∈ Ico (2^62) (2^63)) :
    (n.toNat : ℝ) * 2^((s : ℤ) - 2^63) ∈ rounds (approx (mul_finish n s up norm)) !up := by
  -- TODO
  sorry
  /-
  rw [mul_finish]
  simp only [bif_eq_if, beq_iff_eq]
  have nn : (⟨n⟩ : Int64).isNeg = false := by
    simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, norm.2]
  by_cases h0 : s.n.hi = 0
  · simp only [approx, h0, ite_true, apply_ite (f := fun s : Set ℝ ↦ rounds s !up), rounds_univ,
      mem_ite_univ_left, mem_rounds_singleton, Bool.not_eq_true']
    intro _
    rw [val]
    simp only [UInt64.toInt, Int64.coe_of_nonneg nn, Int.cast_natCast, Int128.coe_of_hi_eq_zero h0,
      le_refl, ite_self]
  · simp only [h0, ite_false]
    by_cases sn : s.isNeg
    · simp only [sn, ite_true]
      induction up
      · simp only [ite_false, ne_eq, zero_ne_nan, not_false_eq_true, approx_eq_singleton, val_zero,
          Bool.not_false, mem_rounds_singleton, gt_iff_lt, two_zpow_pos, mul_nonneg_iff_of_pos_right,
          Nat.cast_nonneg, ite_true]
      · simp only [ite_true, ne_eq, min_norm_ne_nan, not_false_eq_true, approx_eq_singleton,
          val_min_norm, Bool.not_true, mem_rounds_singleton, ite_false]
        refine le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr norm.2.le) two_zpow_pos.le) ?_
        simp only [Nat.cast_pow, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          pow_mul_zpow]
        apply zpow_le_of_le (by norm_num)
        simp only [Int128.isNeg_iff, decide_eq_true_eq] at sn
        omega
    · simp only [sn, ite_false, approx_nan, rounds_univ, mem_univ]
  -/

/-- `mul_exponent` is correct -/
lemma mul_exponent_eq (xs ys t : UInt64) :
    (mul_exponent xs ys t : ℤ) = xs.toNat + ys.toNat + 64 - t.toNat - 2 ^ 63 := by
  rw [mul_exponent]
  refine Int128.eq_of_ofInt_eq ?_ Int128.coe_small ?_
  · have e : Int128.ofNat (2^63 - 64) = .ofInt (2^63) - .ofInt 64 := by rfl
    simp only [e, Int128.ofInt_coe, Int128.sub_ofInt, Int128.add_ofInt, Int128.ofInt_ofUInt64]
    abel
  · have hx := xs.toInt_mem_Ico
    have hy := ys.toInt_mem_Ico
    have ht := t.toInt_mem_Ico
    norm_num only [mem_Ico] at hx hy ht ⊢
    omega

/-- `mul_of_nonneg` rounds in the correct direction -/
lemma approx_mul_of_nonneg {x y : Floating} {up : Bool} {x0 : 0 ≤ x.val} {y0 : 0 ≤ y.val} :
    approx x * approx y ⊆ rounds (approx (mul_of_nonneg x y up x0 y0)) !up := by
  have t0 : (2 : ℝ) ≠ 0 := by norm_num
  by_cases n : mul_of_nonneg x y up x0 y0 = nan
  · simp only [n, approx_nan, rounds_univ, subset_univ]
  simp only [ne_eq, ne_nan_of_nonneg x0, not_false_eq_true, approx_eq_singleton,
    ne_nan_of_nonneg y0, mul_singleton, image_singleton, n, singleton_subset_iff,
    mem_rounds_singleton, Bool.not_eq_true']
  generalize hz : (mul128 x.n.n y.n.n) = z
  generalize hm : mul_norm z up = m
  generalize he : mul_exponent x.s y.s m.2 = e
  have ce := mul_exponent_eq x.s y.s m.2
  rw [mul_of_nonneg] at n ⊢
  simp only [hz, hm, he] at ce n ⊢
  have ze : x.val * y.val = (z.toNat : ℝ) * 2^((x.s.toNat : ℤ) + y.s.toNat - 2^64) := by
    simp only [x0, val_of_nonneg, two_zpow_pos, mul_nonneg_iff_of_pos_right, Nat.cast_nonneg, y0]
    rw [UInt128.eq_iff_toNat_eq, toNat_mul128] at hz
    rw [←mul_assoc, mul_right_comm _ ((2:ℝ)^_), ←Nat.cast_mul, hz, mul_assoc, ←zpow_add₀ t0]
    ring_nf
  rw [ze]
  by_cases z0 : z = 0
  · simp only [z0, dite_true, val_zero, UInt128.toNat_zero, CharP.cast_eq_zero, zero_mul, le_refl,
      ite_self]
  · simp only [z0, dite_false] at n ⊢
    have mn_le := mul_n_le x0 y0
    simp only [hz] at mn_le
    have cn := mul_norm_correct z up z0 mn_le
    simp only [hm, mem_Ico, mem_rounds_singleton, Bool.not_eq_true'] at cn
    have cf := mul_finish_correct m.1 e up cn.1
    simp only [approx_eq_singleton n, mem_rounds_singleton, Bool.not_eq_true'] at cf
    replace cn := cn.2
    induction up
    · simp only [← le_div_iff two_zpow_pos, ite_true, UInt64.toInt, Int.cast_ofNat] at cn cf ⊢
      refine le_trans cf (le_trans (mul_le_mul_of_nonneg_right cn two_zpow_pos.le) ?_)
      simp only [← le_div_iff two_zpow_pos, div_le_iff two_zpow_pos, mul_assoc, mul_div_assoc,
        ←zpow_sub₀ t0, ←zpow_add₀ t0, ce]
      refine le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_zpow_of_nonneg (by norm_num)
        (le_of_eq ?_))
      ring
    · simp only [← div_le_iff two_zpow_pos, ite_false, UInt64.toInt, Int.cast_ofNat] at cn cf ⊢
      refine le_trans (le_trans ?_ (mul_le_mul_of_nonneg_right cn two_zpow_pos.le)) cf
      simp only [←le_div_iff two_zpow_pos, div_le_iff two_zpow_pos, mul_assoc, mul_div_assoc,
        ←zpow_sub₀ t0, ←zpow_add₀ t0, mul_comm_div, ce]
      refine le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_zpow_of_nonneg (by norm_num)
        (le_of_eq ?_))
      ring

/-- `mul` rounds in the correct direction -/
lemma approx_mul (x y : Floating) (up : Bool) :
    approx x * approx y ⊆ rounds (approx (x.mul y up)) !up := by
  rw [mul]
  by_cases n : x = nan ∨ y = nan
  · rcases n with n | n; repeat simp [n]
  rcases not_or.mp n with ⟨xn, yn⟩
  generalize hz : (decide (x.val < 0) != decide (y.val < 0)) = z
  simp only [ne_eq, xn, not_false_eq_true, approx_eq_singleton, yn, mul_singleton, image_singleton,
    or_self, bif_eq_if, isNeg_iff, hz, dite_false, singleton_subset_iff]
  by_cases ze : z = true
  · simp only [ze, bne_iff_ne, ne_eq, decide_eq_decide, Bool.xor_true, ite_true, approx_neg,
      rounds_neg, Bool.not_not, mem_neg] at hz ⊢
    nth_rw 2 [←Bool.not_not up]
    apply approx_mul_of_nonneg
    have e : -(x.val * y.val) = |x.val| * |y.val| := by
      by_cases x0 : x.val < 0
      · simp only [x0, true_iff, not_lt] at hz
        rw [←neg_mul, abs_of_neg x0, _root_.abs_of_nonneg hz]
      · simp only [x0, false_iff, not_lt, not_le] at hz
        simp only [not_lt] at x0
        rw [←neg_mul, neg_mul_comm, abs_of_neg hz, _root_.abs_of_nonneg x0]
    rw [e]
    exact mul_mem_mul (by mono) (by mono)
  · simp only [ze, Bool.xor_false, ite_false]
    simp only [Bool.not_eq_true] at ze
    simp only [ze, Bool.bne_eq_false, decide_eq_decide] at hz
    apply approx_mul_of_nonneg
    have e : x.val * y.val = |x.val| * |y.val| := by
      by_cases x0 : x.val < 0
      · rw [abs_of_neg x0, abs_of_neg (hz.mp x0), neg_mul_neg]
      · simp only [x0, false_iff, not_lt] at hz
        rw [_root_.abs_of_nonneg (not_lt.mp x0), _root_.abs_of_nonneg hz]
    rw [e]
    exact mul_mem_mul (by mono) (by mono)

/-!
### Additional multiplication lemmas
-/

/-- `mul` propagates `nan` -/
@[simp] lemma mul_nan {x : Floating} {up : Bool} : x.mul nan up = nan := by
  rw [mul]
  simp only [or_true, isNeg_iff, n_nan, Int64.isNeg_min, Bool.xor_true, abs_nan, Bool.cond_not,
    Bool.cond_decide, dite_true]

/-- `mul` propagates `nan` -/
@[simp] lemma nan_mul {x : Floating} {up : Bool} : (nan : Floating).mul x up = nan := by
  rw [mul]
  simp only [true_or, bif_eq_if, n_nan, Int64.isNeg_min, isNeg_iff, Bool.true_xor,
    Bool.not_eq_true', decide_eq_false_iff_not, not_lt, abs_nan, dite_true]

/-- `mul` propagates `nan` -/
lemma ne_nan_of_mul {x y : Floating} {up : Bool} (n : x.mul y up ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n; simp only [ne_eq, not_and_or, not_not] at n ⊢
  rw [mul]; simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  rcases n with n | n
  · simp only [n, true_or, n_nan, Int64.isNeg_min, isNeg_iff, Bool.true_xor, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt, abs_nan, dite_true]
  · simp only [n, or_true, isNeg_iff, n_nan, Int64.isNeg_min, Bool.xor_true, Bool.not_eq_true',
      decide_eq_false_iff_not, not_lt, abs_nan, dite_true]

/-- `mul _ _ false` rounds down -/
lemma mul_le {x y : Floating} (n : x.mul y false ≠ nan) :
    (x.mul y false).val ≤ x.val * y.val := by
  have h := approx_mul x y false
  rcases ne_nan_of_mul n with ⟨n0, n1⟩
  simpa only [approx_eq_singleton n0, approx_eq_singleton n1, mul_singleton,
    image_singleton, approx_eq_singleton n, Bool.not_false, singleton_subset_iff,
    mem_rounds_singleton, ite_true] using h

/-- `mul _ _ true` rounds up -/
lemma le_mul {x y : Floating} (n : x.mul y true ≠ nan) :
    x.val * y.val ≤ (x.mul y true).val := by
  have h := approx_mul x y true
  rcases ne_nan_of_mul n with ⟨n0, n1⟩
  simpa only [approx_eq_singleton n0, approx_eq_singleton n1, mul_singleton,
    image_singleton, approx_eq_singleton n, Bool.not_true, singleton_subset_iff,
    mem_rounds_singleton, ite_false] using h
