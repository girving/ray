import Mathlib.Data.Real.Basic
import Ray.Approx.Approx
import Ray.Approx.Fixed
import Ray.Approx.Float
import Ray.Approx.Int
import Ray.Approx.Int64
import Ray.Approx.UInt128
import Ray.Misc.Real

open Pointwise

/-!
## Floating point arithmetic

The floating point number `⟨n,s⟩` represents `n * 2^s`, where `n s : Int64`.
-/

open Set
open scoped Real

/-!
## `Floating` basics
-/

/-- Floating point number -/
structure Floating where
  /-- Unscaled value -/
  n : Int64
  /-- Binary exponent -/
  s : Int64
  /-- `0` has a single, standardized representation -/
  zero_same : n = 0 → s = 0
  /-- `nan` has a single, standardized representation -/
  nan_same : n = .min → s = 0
  /-- If we're not `0`, `nan`, or denormalized, the high bit of `n` is set -/
  norm : n ≠ 0 → n ≠ .min → s ≠ .min → 2^62 ≤ n.abs
  deriving DecidableEq

instance : BEq Floating where
  beq x y := x.n == y.n && x.s == y.s

lemma Floating.beq_def {x y : Floating} : (x == y) = (x.n == y.n && x.s == y.s) := rfl

instance : LawfulBEq Floating where
  eq_of_beq {x y} e := by
    induction x
    induction y
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq] at e
    simp only [e.1, e.2]
  rfl {x} := by
    induction x
    simp only [Floating.beq_def, Bool.and_eq_true, beq_iff_eq, true_and]

lemma Floating.ext_iff {x y : Floating} : x = y ↔ x.n = y.n ∧ x.s = y.s := by
  induction x; induction y; simp only [mk.injEq]

/-- Standard floating point nan -/
instance : Nan Floating where
  nan := ⟨.min, 0, by decide, by decide, by decide⟩

/-- The `ℝ` that a `Fixed` represents, if it's not `nan` -/
@[pp_dot] noncomputable def Floating.val (x : Floating) : ℝ :=
  ((x.n : ℤ) : ℝ) * (2 : ℝ)^(x.s : ℤ)

/-- `Fixed` approximates `ℝ` -/
instance : Approx Floating ℝ where
  approx x := if x = nan then univ else {x.val}

/-- `0` has a standard representation -/
instance : Zero Floating where
  zero := ⟨0, 0, by decide, by decide, by decide⟩

/-- Approximate `Floating` by a `Float` -/
@[irreducible, pp_dot] def Floating.toFloat (x : Floating) : Float :=
  bif x == nan then Float.nan else x.n.toFloat.scaleB x.s

/-- We print `Fixed s` as an approximate floating point number -/
instance : Repr Floating where
  reprPrec x _ := x.toFloat.toStringFull

-- Definition lemmas
@[simp] lemma Floating.n_zero : (0 : Floating).n = 0 := rfl
@[simp] lemma Floating.s_zero : (0 : Floating).s = 0 := rfl
@[simp] lemma Floating.n_nan : (nan : Floating).n = .min := rfl
@[simp] lemma Floating.s_nan : (nan : Floating).s = 0 := rfl

/-- `nan` could be anything -/
@[simp] lemma Floating.approx_nan : approx (nan : Floating) = univ := rfl

@[simp] lemma Floating.val_zero : (0 : Floating).val = 0 := by
  simp only [val, n_zero, Int64.coe_zero, Int.cast_zero, s_zero, zpow_zero, mul_one]

/-- `0 ≠ nan` -/
@[simp] lemma Floating.zero_ne_nan : (0 : Floating) ≠ nan := by decide

/-- `0` is just zero -/
@[simp] lemma Floating.approx_zero : approx (0 : Floating) = {0} := by
  simp only [approx, zero_ne_nan, val_zero, ite_false]

/-- If we're not `nan`, `approx` is a singleton -/
@[simp] lemma Floating.approx_eq_singleton {x : Floating} (n : x ≠ nan) : approx x = {x.val} := by
  simp only [approx, n, ite_false]

/-- If we're not nan, `x.n ≠ .min` -/
lemma Floating.n_ne_min {x : Floating} (n : x ≠ nan) : x.n ≠ .min := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.nan_same n⟩

/-- If we're not zero, `x.n ≠ 0` -/
lemma Floating.n_ne_zero {x : Floating} (n : x ≠ 0) : x.n ≠ 0 := by
  contrapose n
  simp only [ne_eq, not_not, ext_iff, n_nan, s_nan, not_and, not_forall, exists_prop] at n ⊢
  exact ⟨n, x.zero_same n⟩

/-!
### Negation
-/

instance : Neg Floating where
  neg x := {
    n := -x.n
    s := x.s
    zero_same := by intro h; simp only [neg_eq_zero] at h; exact x.zero_same h
    nan_same := by intro h; simp only [Int64.neg_eq_min] at h; exact x.nan_same h
    norm := by
      intro z n d
      simp only [ne_eq, neg_eq_zero, Int64.neg_eq_min] at z n
      simp only [ne_eq, n, not_false_eq_true, Int64.abs_neg, z, x.norm, d] }

@[simp] lemma Floating.n_neg {x : Floating} : (-x).n = -x.n := rfl
@[simp] lemma Floating.s_neg {x : Floating} : (-x).s = x.s := rfl

/-- Negation propagates `nan` -/
@[simp] lemma Floating.neg_nan : (-nan : Floating) = nan := by
  simp only [Floating.ext_iff, Floating.n_neg, Floating.n_nan, Int64.neg_min, Floating.s_neg,
    Floating.s_nan, and_self]

/-- Negation preserves `nan` -/
@[simp] lemma Floating.neg_eq_nan_iff {x : Floating} : -x = nan ↔ x = nan := by
  simp only [ext_iff, n_neg, n_nan, Int64.neg_eq_min, s_neg, s_nan]

/-- Negation flips `.val`, except at `nan` -/
@[simp] lemma Floating.val_neg {x : Floating} (n : x ≠ nan) : (-x).val = -x.val := by
  rw [Floating.val, Floating.val]
  simp only [n_neg, s_neg, ←neg_mul, Int64.coe_neg (x.n_ne_min n), Int.cast_neg]

/-!
### Simplification lemmas used below
-/

@[simp] private lemma u62 : (62 : UInt64).toNat = 62 := rfl
@[simp] private lemma u64 : (64 : UInt64).toNat = 64 := rfl
@[simp] private lemma up62 : (2^62 : UInt64).toNat = 2^62 := rfl
@[simp] private lemma up63 : (2^63 : UInt64).toNat = 2^63 := rfl
@[simp] private lemma ua2 : (2 : ℤ).natAbs = 2 := rfl

/-!
### Standardization: build a `Floating` out of `n s : Int64`
-/

/-- Decrease an `s` enough to normalize `n`, saturating at `s = .min`.
    We return `(t, s - t)` where `t` is the normalized exponent. -/
@[irreducible] def Floating.low_s (n s : Int64) : Int64 × UInt64 :=
  let g := 62 - n.abs.log2  -- How much we'd like to shift `n` by
  let t := bif s < .min + ⟨g⟩ then .min else s - ⟨g⟩
  ⟨t, s.n - t.n⟩

@[simp] lemma Floating.log2_g_le_62 {n : Int64} (nm : n ≠ .min) : n.abs.log2 ≤ 62 := by
  by_cases n0 : n = 0
  · simp only [n0, Int64.abs_zero, UInt64.log2_zero, UInt64.nonneg]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_log2, u62]
  suffices h : n.abs.toNat.log2 < 63 by omega
  refine (Nat.log2_lt ?_).mpr ?_
  · simpa only [←UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_ne_zero_iff]
  · rwa [Int64.toNat_abs, Int64.natAbs_lt_pow_iff]

@[simp] lemma Floating.log2_g_le_62' {n : Int64} (nm : n ≠ .min) : n.abs.toNat.log2 ≤ 62 := by
  rw [←u62, ←UInt64.toNat_log2, ←UInt64.le_iff_toNat_le]; exact log2_g_le_62 nm

@[simp] lemma Floating.s_coe_g {n : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    ((⟨62 - n.abs.log2⟩ : Int64) : ℤ) = (62 : ℤ) - n.abs.toNat.log2 := by
  rw [Int64.coe_of_nonneg]
  · rw [UInt64.toNat_sub (log2_g_le_62 nm), u62, Nat.cast_sub]
    · simp only [Nat.cast_ofNat, UInt64.toNat_log2]
    · exact log2_g_le_62' nm
  · rw [Int64.isNeg_eq_le]
    simp only [decide_eq_false_iff_not, not_le]
    rw [UInt64.toNat_sub, u62, UInt64.toNat_log2]
    · norm_num; omega
    · rw [UInt64.le_iff_toNat_le, UInt64.toNat_log2, u62]
      suffices h : n.abs.toNat.log2 < 63 by omega
      refine (Nat.log2_lt ?_).mpr ?_
      · simpa only [←UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_ne_zero_iff]
      · rwa [Int64.toNat_abs, Int64.natAbs_lt_pow_iff]

/-- `low_s` returns small shifts -/
@[simp] lemma Floating.low_d_le {n : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) (s : Int64) :
    (low_s n s).2.toNat ≤ 62 - n.abs.toNat.log2 := by
  rw [low_s]
  simp only [bif_eq_if, decide_eq_true_eq]
  have cg := s_coe_g n0 nm
  have le := log2_g_le_62 nm
  have le' := log2_g_le_62' nm
  split_ifs with h
  · rw [←Int64.coe_lt_coe, Int64.coe_add_eq, Int64.coe_min', cg] at h
    have s0 : (s : ℤ) < 0 := by norm_num at h; omega
    simp only [Int64.coe_lt_zero_iff, Int64.isNeg_eq_le, decide_eq_true_eq] at s0
    simp only [Int64.toInt, Int64.isNeg_eq_le, s0, decide_True, cond_true, Nat.cast_pow,
      Nat.cast_ofNat, lt_neg_add_iff_add_lt] at h
    have slt : ↑s.n.toNat < 2^63 + 62 - n.abs.toNat.log2 := by norm_num at s0 h ⊢; omega
    rw [UInt64.toNat_sub]
    · simp only [Int64.n_min, UInt64.toNat_2_pow_63]
      refine le_trans (Nat.sub_le_sub_right slt.le _) ?_
      rw [Nat.add_sub_assoc le', Nat.add_sub_cancel_left]
    · simpa only [Int64.n_min, UInt64.le_iff_toNat_le, UInt64.toNat_2_pow_63]
    · simp only [Int64.add_def, Int64.n_min, Int64.isNeg_eq_le, UInt64.toNat_2_pow_63, le_refl,
        decide_True, decide_eq_true_eq]
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt, up63]
      · apply Nat.le_add_right
      · rw [up63, UInt64.toNat_sub le, u62, UInt64.toNat_log2, UInt64.size_eq_pow]
        norm_num; omega
  · simp only [Int64.sub_def, sub_sub_cancel, gt_iff_lt]
    rw [UInt64.toNat_sub le, u62, UInt64.toNat_log2]

/-- `low_s` returns shifts under `62` -/
@[simp] lemma Floating.low_d_le_62 {n : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) (s : Int64) :
    (low_s n s).2.toNat ≤ 62 :=
  le_trans (low_d_le n0 nm s) (Nat.sub_le _ _)

/-- `low_s` returns shifts under `64` -/
@[simp] lemma Floating.low_d_lt_64 {n : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) (s : Int64) :
    (low_s n s).2.toNat < 64 :=
  lt_of_le_of_lt (low_d_le_62 n0 nm s) (by norm_num)

/-- `low` doesn't overflow -/
@[simp] lemma Floating.low_lt {n : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) (s : Int64) :
    n.abs.toNat * 2 ^ (low_s n s).2.toNat < 2 ^ 63 := by
  refine lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_log2_self (n := n.abs.toNat))
    (Nat.pow_le_pow_of_le_right (by positivity) (low_d_le n0 nm s)) (by positivity)) ?_
  simp only [← Nat.pow_add, ←Nat.add_sub_assoc (log2_g_le_62' nm)]
  exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)

/-- `low` doesn't overflow -/
@[simp] lemma Floating.low_lt' {n : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) (s : Int64) :
    |(n : ℤ) * 2 ^ (low_s n s).2.toNat| < 2 ^ 63 := by
  have h := low_lt n0 nm s
  generalize (low_s n s).2.toNat = k at h
  refine lt_of_le_of_lt (abs_mul _ _).le ?_
  simp only [←Int.coe_natAbs, ←Int64.toNat_abs, abs_pow, abs_two]
  rw [←Nat.cast_lt (α := ℤ)] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- `low_s` respects `ℤ` conversion -/
lemma Floating.coe_low_s {n s : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    ((n <<< (low_s n s).2 : Int64) : ℤ) = (n : ℤ) * 2^(low_s n s).2.toNat := by
  rw [Int64.coe_shiftLeft (low_d_lt_64 n0 nm s)]
  have d := low_d_le_62 n0 nm s
  rw [←Nat.pow_div (by omega) (by norm_num), Nat.lt_div_iff_mul_lt, mul_comm]
  · exact low_lt n0 nm s
  · rw [Nat.pow_dvd_pow_iff_le_right (by omega)]; omega

-- DO NOT SUBMIT: Do we need this?
/-- `low_s.2` in terms of `low_s.1` -/
lemma Floating.low_s_2_eq (n s : Int64) : (low_s n s).2 = s.n - (low_s n s).1.n := by rw [low_s]

/-- `low_s.2` in terms of `low_s.1`, expressed in terms of `ℤ` -/
lemma Floating.low_s_2_eq' {n s : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    ((low_s n s).2.toNat : ℤ) = s - (low_s n s).1 := by
  have le := low_d_le n0 nm s
  rw [low_s] at le ⊢
  generalize hg : 62 - UInt64.log2 n.abs = g at le
  simp only [Bool.cond_decide] at le ⊢
  generalize ht : (if s < .min + { n := g } then .min else s - { n := g }) = t at le
  replace le : (s.n - t.n).toNat < 2^63 :=
    lt_of_le_of_lt (le_trans le (Nat.sub_le _ _)) (by norm_num)
  have stn : (⟨s.n - t.n⟩ : Int64).isNeg = false := by
    simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le]; omega
  trans ((s - t : Int64) : ℤ)
  · simp only [Int64.toInt, Int64.sub_def, stn, bif_eq_if, ite_false, CharP.cast_eq_zero, sub_zero]
  · refine Int64.coe_sub_of_le_of_pos ?_ stn
    rw [←ht]
    split_ifs with h
    · apply Int64.min_le
    · refine Int64.sub_le ?_ (not_lt.mp h)
      simp only [← hg, Int64.isNeg_eq_le, UInt64.toNat_sub (log2_g_le_62 nm), u62,
        UInt64.toNat_log2, decide_eq_false_iff_not, not_le]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (by norm_num)

/-- `of_ns` satisfies `zero_same` -/
lemma Floating.of_ns_zero_same {n s : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    n <<< (low_s n s).2 = 0 → (low_s n s).1 = 0 := by
  intro z; contrapose z
  simp only [←Int64.coe_eq_coe, Int64.coe_zero, coe_low_s n0 nm, mul_eq_zero, not_or]
  constructor
  · simp only [Int64.coe_eq_zero, n0, not_false_eq_true]
  · simp only [pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, not_false_eq_true]

/-- `of_ns` doesn't create `nan` -/
lemma Floating.of_ns_ne_nan {n s : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    n <<< (low_s n s).2 ≠ .min := by
  intro m; contrapose m
  have h := low_lt' n0 nm s
  simp only [abs_lt] at h
  rw [←Int64.coe_eq_coe, coe_low_s n0 nm, Int64.coe_min']
  exact ne_of_gt h.1

/-- `of_ns` satisfies `nan_same` -/
lemma Floating.of_ns_nan_same {n s : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    n <<< (low_s n s).2 = .min → (low_s n s).1 = 0 := by
  simp only [of_ns_ne_nan n0 nm, IsEmpty.forall_iff]

/-- `of_ns` satisfies `norm` -/
lemma Floating.of_ns_norm {n s : Int64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    n <<< (low_s n s).2 ≠ 0 → n <<< (low_s n s).2 ≠ Int64.min →
      (low_s n s).1 ≠ Int64.min → 2 ^ 62 ≤ (n <<< (low_s n s).2).abs := by
  intro _ _ sm
  rw [UInt64.le_iff_toNat_le, up62, Int64.toNat_abs, coe_low_s n0 nm, Int.natAbs_mul,
    Int.natAbs_pow, ua2, ←Int64.toNat_abs]
  rw [low_s] at sm ⊢
  simp only [Bool.cond_decide, ne_eq, ite_eq_left_iff, not_lt, not_forall, exists_prop] at sm ⊢
  generalize hd : s.n - (s - ⟨62 - n.abs.log2⟩).n = d
  simp only [not_lt.mpr sm.1, if_false, hd]
  have a0 : n.abs.toNat ≠ 0 := by
    simpa only [ne_eq, ← UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_eq_zero_iff]
  refine le_trans ?_ (Nat.mul_le_mul_right _ (Nat.log2_self_le a0))
  rw [←pow_add]
  refine Nat.pow_le_pow_of_le_right (by norm_num) ?_
  rw [←hd]
  simp only [Int64.sub_def, sub_sub_cancel]
  rw [UInt64.toNat_sub (log2_g_le_62 nm), u62]
  omega

/-- Construct a `Floating` given possibly non-standardized `n s : Int64` -/
@[irreducible] def Floating.of_ns (n s : Int64) : Floating :=
  if nm : n = .min then nan else
  if n0 : n = 0 then 0 else
  -- If `n` is small, we decrease `s` until either `n` has the high bit set or `s = .min`
  let t := low_s n s
  { n := n <<< t.2
    s := t.1
    zero_same := of_ns_zero_same n0 nm
    nan_same := of_ns_nan_same n0 nm
    norm := of_ns_norm n0 nm }

/-- `of_ns` propagates `nan` -/
@[simp] lemma Floating.of_ns_nan (s : Int64) : of_ns .min s = nan := by
  rw [of_ns]; simp only [Int64.min_ne_zero, dite_false, dite_true]

/-- `of_ns` propagates `0` -/
@[simp] lemma Floating.of_ns_zero (s : Int64) : of_ns 0 s = 0 := by
  rw [of_ns]; simp only [Int64.zero_ne_min, dite_true, dite_eq_ite, ite_false]

/-- `of_ns` preserves `val` -/
lemma Floating.val_of_ns {n s : Int64} (nm : n ≠ .min) :
    (of_ns n s).val = (n : ℤ) * 2^(s : ℤ) := by
  rw [of_ns, val]
  simp only [nm, dite_false]
  by_cases n0 : n = 0
  · simp only [n0, Int64.zero_shiftLeft, dite_true, n_zero, Int64.coe_zero, Int.cast_zero, s_zero,
      zpow_zero, mul_one, zero_mul]
  simp only [n0, dite_false, coe_low_s n0 nm, Int.cast_mul, Int.cast_pow, Int.int_cast_ofNat]
  simp only [low_s_2_eq' n0 nm, mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow,
    mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj, Int.cast_eq_zero,
    Int64.coe_eq_zero, n0, or_false]
  ring_nf

/-- `of_ns` doesn't create `nan` -/
@[simp] lemma Floating.of_ns_eq_nan_iff {n s : Int64} : of_ns n s = nan ↔ n = .min := by
  constructor
  · intro nm; contrapose nm
    rw [of_ns, ext_iff]
    by_cases n0 : n = 0
    · simp only [n0, Int64.zero_ne_min, Int64.zero_shiftLeft, dite_true, dite_eq_ite, ite_false,
        n_zero, n_nan, s_zero, s_nan, and_true, not_false_eq_true]
    · simp only [nm, n0, dite_false, n_nan, of_ns_ne_nan n0 nm, s_nan, false_and, not_false_eq_true]
  · intro h; rw [h, of_ns_nan]

/-- `of_ns` doesn't create `nan` -/
@[simp] lemma Floating.of_ns_ne_nan_iff {n s : Int64} : of_ns n s ≠ nan ↔ n ≠ .min := by
  simp only [ne_eq, of_ns_eq_nan_iff]

/-!
### Coersion from fixed point to floating point
-/

/-- `Fixed s` to `Floating` by hiding `s` -/
@[irreducible, coe] def Fixed.toFloating {s : Int64} (x : Fixed s) : Floating :=
  .of_ns x.n s

/-- Coersion from `Fixed s` to `Floating` -/
instance {s : Int64} : CoeHead (Fixed s) Floating where
  coe x := x.toFloating

/-- To prove `a ∈ approx (x : Floating)`, we prove `a ∈ approx x` -/
@[mono] lemma Floating.mem_approx_coe {s : Int64} {x : Fixed s} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : Floating) := by
  rw [Fixed.toFloating]
  by_cases n : x = nan
  · simp only [n, Fixed.nan_n, of_ns_nan, approx_nan, mem_univ]
  · have nm : x.n ≠ .min := by simpa only [ne_eq, Fixed.ext_iff, Fixed.nan_n] using n
    simp only [Fixed.approx_eq_singleton n, mem_singleton_iff,
      approx_eq_singleton (of_ns_ne_nan_iff.mpr nm)] at ax ⊢
    rw [ax, Fixed.val, val_of_ns nm]

/-!
### Scale by changing the exponent
-/

/-- Scale by changing the exponent -/
@[irreducible, pp_dot] def Floating.scaleB (x : Floating) (t : Fixed 0) : Floating :=
  let k : Fixed 0 := ⟨x.s⟩ + t
  bif k == nan then nan else
  of_ns x.n k.n

/-- `Floating.scaleB` is conservative -/
@[mono] lemma Floating.mem_approx_scaleB {x : Floating} {t : Fixed 0} {x' t' : ℝ}
    (xm : x' ∈ approx x) (tm : t' ∈ approx t) : x' * 2^t' ∈ approx (x.scaleB t) := by
  rw [Floating.scaleB]
  have t0 : 0 < (2 : ℝ) := by norm_num
  generalize hk : (⟨x.s⟩ + t : Fixed 0) = k
  by_cases xn : x = nan
  · simp only [xn, n_nan, of_ns_nan, Bool.cond_self, approx_nan, mem_univ]
  by_cases kn : k = nan
  · simp only [kn, beq_self_eq_true, Fixed.nan_n, cond_true, approx_nan, mem_univ]
  by_cases tn : t = nan
  · simp only [← hk, tn, Fixed.add_nan, not_true_eq_false] at kn
  simp only [ne_eq, xn, tn, not_false_eq_true, approx_eq_singleton, mem_singleton_iff,
    Fixed.approx_eq_singleton] at xm tm
  simp only [apply_ite (f := fun f : Floating ↦ x.val * 2^t' ∈ approx f), approx_nan, mem_univ, xm,
    approx_eq_singleton (of_ns_ne_nan_iff.mpr (x.n_ne_min xn)), mem_singleton_iff,
    val_of_ns (x.n_ne_min xn), kn, if_false, tm, bif_eq_if, beq_iff_eq]
  rw [Floating.val]
  simp only [mul_assoc, ←Real.rpow_int_cast, ←Real.rpow_add, t0, Fixed.val_of_s0]
  refine congr_arg₂ _ rfl (congr_arg₂ _ rfl ?_)
  simp only [←hk] at kn ⊢
  have h := Fixed.val_add kn
  simp only [Fixed.val_of_s0] at h
  exact h.symm

/-!
### Addition and subtraction

To add, we shift the smaller number to near the bigger number, perform a 128-bit addition, and
normalize the result.
-/

/-- Shift `y` into a 128-bit value whose upper half aligns with `x`
    We assume no zeros or nans, and that `y.s ≤ x.s`. -/
@[irreducible, pp_dot] def Floating.shift_y (x y : Floating) (up : Bool) : UInt128 :=
  (⟨y.n, 0⟩ : UInt128).shiftRightRound (x.s.n - y.s.n) up

@[irreducible, pp_dot] def Floating.add (x y : Floating) (up : Bool) : Floating :=
  -- Handle `0` and `nan`
  bif x == nan || y == nan then nan else
  bif x == 0 then y else
  bif y == 0 then x else
  -- Arrange for x to have the larger exponent
  let (x, y) := if x.s ≤ y.s then (y, x) else (x, y)
  -- Arrange for x to be positive
  let (z, x, y) := bif x.n.isNeg then (true, -x, -y) else (false, x, y)
  -- Perform the addition, shifting `y` to be near `x`
  let y := x.shift_y y up
  let r : UInt128 := ⟨y.lo, x.n + y.hi⟩
  -- Our mathematical result is now
  --   `r * 2^(x.s - 64)`
  let r := sorry
  -- Restore the sign of x
  bif z then -r else r
