import Ray.Approx.Floating.Basic

/-!
## Floating point standardization: build a `Floating` out of `n : Int64`, s : UInt64`
-/

open Set
open scoped Real
namespace Floating

/-- Decrease `s` by `g` if possible, saturating at `s = 0`.
    We return `(t, s - t)` where `t` is the normalized exponent. -/
@[irreducible, specialize] def lower (g s : UInt64) : UInt64 × UInt64 :=
  let t := bif s < g then 0 else s - g
  ⟨t, s - t⟩

/-- `lower` returns small shifts -/
@[simp] lemma low_d_le (g s : UInt64) : (lower g s).2.toNat ≤ g.toNat := by
  rw [lower]
  simp only [bif_eq_if, decide_eq_true_eq]
  split_ifs with h
  · simp only [sub_zero, UInt64.toNat_le_toNat, h.le]
  · apply le_of_eq; ring_nf

/-- `lower` reduces the exponent -/
lemma low_le_s (g s : UInt64) : (lower g s).1 ≤ s := by
  rw [lower]
  simp only [bif_eq_if, decide_eq_true_eq]
  split_ifs with h
  · exact UInt64.nonneg
  · simp only [not_lt] at h
    exact UInt64.sub_le h

/-- `lower` reduces the exponent -/
lemma low_le_s' {g s : UInt64} : (lower g s).1.toNat ≤ s.toNat :=
  (UInt64.le_iff_toNat_le _ _).mp (low_le_s g s)

/-- `lower.2` in terms of `lower.1`, expressed in terms of `ℕ` -/
lemma low_s_2_eq {g s : UInt64} : (lower g s).2.toNat = s.toNat - (lower g s).1.toNat := by
  have e : (lower g s).2 = s - (lower g s).1 := by rw [lower]
  rw [e, UInt64.toNat_sub (low_le_s _ s)]

@[simp] lemma log2_g_le_62 {n : Int64} (nm : n ≠ .min) : n.abs.log2 ≤ 62 := by
  by_cases n0 : n = 0
  · simp only [n0, Int64.abs_zero, UInt64.log2_zero, UInt64.nonneg]
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_log2, u62]
  suffices h : n.abs.toNat.log2 < 63 by omega
  refine (Nat.log2_lt ?_).mpr ?_
  · simpa only [←UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_ne_zero_iff]
  · rwa [Int64.toNat_abs, Int64.natAbs_lt_pow_iff]

@[simp] lemma log2_g_le_62' {n : Int64} (nm : n ≠ .min) : n.abs.toNat.log2 ≤ 62 := by
  rw [←u62, ←UInt64.toNat_log2, ←UInt64.le_iff_toNat_le]; exact log2_g_le_62 nm

/-- `lower` returns shifts under `62` -/
@[simp] lemma low_d_le_62 {n : Int64} (nm : n ≠ .min) (s : UInt64) :
    (lower (62 - n.abs.log2) s).2.toNat ≤ 62 := by
  refine le_trans (low_d_le _ s) ?_
  rw [UInt64.toNat_sub (log2_g_le_62 nm), u62]
  apply Nat.sub_le

/-- `low` doesn't overflow -/
@[simp] lemma low_lt {n : Int64} (nm : n ≠ .min) (s : UInt64) :
    n.abs.toNat * 2 ^ (lower (62 - n.abs.log2) s).2.toNat < 2 ^ 63 := by
  refine lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_log2_self (n := n.abs.toNat))
    (Nat.pow_le_pow_of_le_right (by positivity) (low_d_le _ s)) (by positivity)) ?_
  simp only [← Nat.pow_add, ←Nat.add_sub_assoc (log2_g_le_62' nm), UInt64.toNat_log2,
    UInt64.toNat_sub (log2_g_le_62 nm), u62]
  exact Nat.pow_le_pow_of_le_right (by norm_num) (by omega)

/-- `low` doesn't overflow -/
@[simp] lemma low_lt' {n : Int64} (nm : n ≠ .min) (s : UInt64) :
    |(n : ℤ) * 2 ^ (lower (62 - n.abs.log2) s).2.toNat| < 2 ^ 63 := by
  have h := low_lt nm s
  generalize (lower n s).2.toNat = k at h
  refine lt_of_le_of_lt (abs_mul _ _).le ?_
  simp only [←Int.natCast_natAbs, ←Int64.toNat_abs, abs_pow, abs_two]
  rw [←Nat.cast_lt (α := ℤ)] at h
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- `lower` respects `ℤ` conversion -/
lemma coe_low_s {n : Int64} {s : UInt64} (nm : n ≠ .min) :
    ((n <<< (lower (62 - n.abs.log2) s).2 : Int64) : ℤ) =
      (n : ℤ) * 2^(lower (62 - n.abs.log2) s).2.toNat := by
  rw [Int64.coe_shiftLeft (lt_of_le_of_lt (low_d_le_62 nm s) (by norm_num))]
  have d := low_d_le_62 nm s
  rw [←Nat.pow_div (by omega) (by norm_num), Nat.lt_div_iff_mul_lt, mul_comm]
  · exact low_lt nm s
  · rw [Nat.pow_dvd_pow_iff_le_right (by omega)]; omega

/-- `of_ns` doesn't create `nan` -/
lemma of_ns_ne_nan {n : Int64} {s : UInt64} (nm : n ≠ .min) :
    n <<< (lower (62 - n.abs.log2) s).2 ≠ .min := by
  intro m; contrapose m
  have h := low_lt' nm s
  simp only [abs_lt] at h
  rw [←Int64.coe_eq_coe, coe_low_s nm, Int64.coe_min']
  exact ne_of_gt h.1

/-- `of_ns` satisfies `norm` -/
lemma of_ns_norm {n : Int64} {s : UInt64} (n0 : n ≠ 0) (nm : n ≠ .min) :
    n <<< (lower (62 - n.abs.log2) s).2 ≠ 0 → n <<< (lower (62 - n.abs.log2) s).2 ≠ Int64.min →
      (lower (62 - n.abs.log2) s).1 ≠ 0 → 2 ^ 62 ≤ (n <<< (lower (62 - n.abs.log2) s).2).abs := by
  intro _ _ sm
  rw [UInt64.le_iff_toNat_le, up62, Int64.toNat_abs, coe_low_s nm, Int.natAbs_mul,
    Int.natAbs_pow, ua2, ←Int64.toNat_abs]
  rw [lower] at sm ⊢
  simp only [Bool.cond_decide, ne_eq, ite_eq_left_iff, not_lt, not_forall, exists_prop] at sm ⊢
  generalize hd : s - (s - (62 - n.abs.log2)) = d
  simp only [not_lt.mpr sm.1, if_false, hd]
  have a0 : n.abs.toNat ≠ 0 := by
    simpa only [ne_eq, ← UInt64.ne_zero_iff_toNat_ne_zero, Int64.abs_eq_zero_iff]
  refine le_trans ?_ (Nat.mul_le_mul_right _ (Nat.log2_self_le a0))
  rw [←pow_add]
  refine Nat.pow_le_pow_of_le_right (by norm_num) ?_
  rw [←hd]
  simp only [Int64.sub_def, sub_sub_cancel]
  rw [UInt64.toNat_sub (log2_g_le_62 nm), u62]
  simp only [UInt64.toNat_log2]
  omega

/-- Construct a `Floating` given possibly non-standardized `n, s` -/
@[irreducible] def of_ns (n : Int64) (s : UInt64) : Floating :=
  if nm : n = .min then nan else
  if n0 : n = 0 then 0 else
  -- If `n` is small, we decrease `s` until either `n` has the high bit set or `s = 0`
  let t := lower (62 - n.abs.log2) s
  { n := n <<< t.2
    s := t.1
    zero_same := by
      intro z; contrapose z
      simp only [←Int64.coe_eq_coe, Int64.coe_zero, coe_low_s nm, mul_eq_zero, not_or,
        pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, not_false_eq_true, and_true]
      simp only [Int64.coe_eq_zero, n0, not_false_eq_true]
    nan_same := by simp only [of_ns_ne_nan nm, IsEmpty.forall_iff]
    norm := of_ns_norm n0 nm }

/-- `of_ns` propagates `nan` -/
@[simp] lemma of_ns_nan (s : UInt64) : of_ns .min s = nan := by
  rw [of_ns]; simp only [Int64.min_ne_zero, dite_false, dite_true]

/-- `of_ns` propagates `0` -/
@[simp] lemma of_ns_zero (s : UInt64) : of_ns 0 s = 0 := by
  rw [of_ns]; simp only [Int64.zero_ne_min, dite_true, dite_eq_ite, ite_false]

/-- `of_ns` preserves `val` -/
lemma val_of_ns {n : Int64} {s : UInt64} (nm : n ≠ .min) :
    (of_ns n s).val = (n : ℤ) * 2^(s.toInt - 2^63) := by
  rw [of_ns, val]
  simp only [nm, dite_false]
  by_cases n0 : n = 0
  · simp only [n0, Int64.zero_shiftLeft, dite_true, n_zero, Int64.coe_zero, Int.cast_zero, s_zero,
      zero_mul]
  simp only [n0, dite_false, coe_low_s nm, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  simp only [low_s_2_eq, mul_assoc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_mul_zpow,
    mul_eq_mul_left_iff, gt_iff_lt, zero_lt_two, OfNat.ofNat_ne_one, zpow_inj, Int.cast_eq_zero,
    Int64.coe_eq_zero, n0, or_false, Nat.cast_sub low_le_s', UInt64.toInt]
  ring_nf

/-- `of_ns` doesn't create `nan` -/
@[simp] lemma of_ns_eq_nan_iff {n : Int64} {s : UInt64} : of_ns n s = nan ↔ n = .min := by
  constructor
  · intro nm; contrapose nm
    rw [of_ns, ext_iff]
    by_cases n0 : n = 0
    · simp only [n0, Int64.zero_ne_min, Int64.zero_shiftLeft, dite_true, dite_eq_ite, ite_false,
        n_zero, n_nan, s_zero, s_nan, false_and, not_false_eq_true]
    · simp only [nm, n0, dite_false, n_nan, of_ns_ne_nan nm, s_nan, false_and, not_false_eq_true]
  · intro h; rw [h, of_ns_nan]

/-- `of_ns` doesn't create `nan` -/
@[simp] lemma of_ns_ne_nan_iff {n : Int64} {s : UInt64} : of_ns n s ≠ nan ↔ n ≠ .min := by
  simp only [ne_eq, of_ns_eq_nan_iff]

/-!
### Coersion from fixed point to floating point
-/

/-- `Fixed s` to `Floating` by hiding `s` -/
@[irreducible, coe] def _root_.Fixed.toFloating {s : Int64} (x : Fixed s) : Floating :=
  .of_ns x.n (s.n + 2^63)

/-- Coersion from `Fixed s` to `Floating` -/
instance {s : Int64} : CoeHead (Fixed s) Floating where
  coe x := x.toFloating

/-- To prove `a ∈ approx (x : Floating)`, we prove `a ∈ approx x` -/
@[mono] lemma mem_approx_coe {s : Int64} {x : Fixed s} {a : ℝ}
    (ax : a ∈ approx x) : a ∈ approx (x : Floating) := by
  rw [Fixed.toFloating]
  by_cases n : x = nan
  · simp only [n, Fixed.nan_n, of_ns_nan, approx_nan, mem_univ]
  · have nm : x.n ≠ .min := by simpa only [ne_eq, Fixed.ext_iff, Fixed.nan_n] using n
    simp only [Fixed.approx_eq_singleton n, mem_singleton_iff,
      approx_eq_singleton (of_ns_ne_nan_iff.mpr nm)] at ax ⊢
    rw [ax, Fixed.val, val_of_ns nm]
    simp only [Int64.toInt, Int64.isNeg_eq_le, bif_eq_if, decide_eq_true_eq, Nat.cast_ite,
      Nat.cast_pow, Int.cast_sub, Int.cast_ofNat, Int.cast_ite,
      Int.cast_pow, Int.cast_ofNat, Int.cast_zero, UInt64.toInt, UInt64.toNat_add,
      UInt64.toNat_2_pow_63, Int.ofNat_emod, Nat.cast_add, mul_eq_mul_left_iff,
      zero_lt_two, ne_eq, not_false_eq_true, zpow_inj, UInt64.size_eq_pow, Nat.cast_pow,
      Nat.cast_two]
    left
    have sp : s.n.toNat < 2^64 := UInt64.toNat_lt_2_pow_64 _
    by_cases le : 2^63 ≤ s.n.toNat
    · have d0 : (s.n.toNat : ℤ) + 2^63 = (s.n.toNat - 2^63) + 2^64 := by ring
      have d1 : 0 ≤ (s.n.toNat : ℤ) - 2^63 := by linarith
      have d2 : (s.n.toNat : ℤ) - 2^63 < 2^64 := by linarith
      simp only [le, CharP.cast_eq_zero, ite_true, gt_iff_lt, zero_lt_two, ne_eq,
        OfNat.ofNat_ne_one, not_false_eq_true, zpow_inj, d0, Int.add_emod_self,
        Int.emod_eq_of_lt d1 d2]
      ring
    · simp only [le, CharP.cast_eq_zero, ite_false, sub_zero, zpow_natCast]
      have d0 : 0 ≤ (s.n.toNat : ℤ) + 2^63 := by omega
      have d1 : (s.n.toNat : ℤ) + 2^63 < 2^64 := by linarith
      simp only [Int.emod_eq_of_lt d0 d1, add_sub_cancel_right, zpow_natCast]
