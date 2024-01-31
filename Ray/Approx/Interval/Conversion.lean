import Ray.Approx.Interval.Basic

open Classical
open Pointwise

/-!
## Conversion to `Interval` from `ℕ`, `ℤ`, `ℚ`, and `ofScientific`
-/

open Set
open scoped Real

/-- `ℕ` converts to `Interval` -/
@[irreducible] def ofNat (n : ℕ) : Interval := ⟨.ofNat n false, .ofNat n true⟩

/-- `ℤ` converts to `Interval` -/
@[irreducible] def ofInt (n : ℤ) : Interval := ⟨.ofInt n false, .ofInt n true⟩

/-- `ℚ` converts to `Interval` -/
@[irreducible] def ofRat (x : ℚ) : Interval := ⟨.ofRat x false, .ofRat x true⟩

/-- Conversion from `ofScientific` -/
instance : OfScientific Interval where
  ofScientific x u t := .ofRat (OfScientific.ofScientific x u t)

/-- We use the general `.ofNat` routine for `1`, to handle overflow -/
instance : One Interval := ⟨.ofNat 1⟩

lemma one_def : (1 : Interval) = .ofNat 1 := rfl

/-- Conversion from `ℕ` literals to `Interval` -/
instance {n : ℕ} [n.AtLeastTwo] : OfNat Interval n := ⟨.ofNat n⟩

/-- `.ofNat` is conservative -/
@[mono] lemma approx_ofNat (n : ℕ) : ↑n ∈ approx (.ofNat n : Interval) := by
  rw [ofNat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofNat n false : Fixed s) = nan ∨ (.ofNat n true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofNat_le g.1, Fixed.le_ofNat g.2⟩

/-- `.ofInt` is conservative -/
@[mono] lemma approx_ofInt (n : ℤ) : ↑n ∈ approx (.ofInt n : Interval) := by
  rw [ofInt]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofInt n false : Fixed s) = nan ∨ (.ofInt n true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofInt_le g.1, Fixed.le_ofInt g.2⟩

/-- `.ofRat` is conservative -/
@[mono] lemma approx_ofRat (x : ℚ) : ↑x ∈ approx (.ofRat x : Interval) := by
  rw [ofRat]; simp only [approx, mem_ite_univ_left, mem_Icc]
  by_cases g : (.ofRat x false : Fixed s) = nan ∨ (.ofRat x true : Fixed s) = nan
  · simp only [g, not_true_eq_false, IsEmpty.forall_iff]
  · simp only [g, not_false_eq_true, forall_true_left]
    simp only [not_or] at g
    exact ⟨Fixed.ofRat_le g.1, Fixed.le_ofRat g.2⟩

/-- `approx_ofRat` for rational literals `a / b` -/
@[mono] lemma ofNat_div_mem_approx_ofRat {a b : ℕ} [a.AtLeastTwo] [b.AtLeastTwo] :
    OfNat.ofNat a / OfNat.ofNat b ∈
      approx (.ofRat (OfNat.ofNat a / OfNat.ofNat b) : Interval) := by
  convert approx_ofRat _; simp only [Rat.cast_div, Rat.cast_ofNat]

/-- `approx_ofRat` for rational literals `1 / b` -/
@[mono] lemma one_div_ofNat_mem_approx_ofRat {b : ℕ} [b.AtLeastTwo] :
    1 / OfNat.ofNat b ∈ approx (.ofRat (1 / OfNat.ofNat b) : Interval) := by
  convert approx_ofRat _; simp only [one_div, Rat.cast_inv, Rat.cast_ofNat]

/-- `ofRat` conversion is conservative -/
@[mono] lemma approx_ofScientific (x : ℕ) (u : Bool) (t : ℕ) :
    ↑(OfScientific.ofScientific x u t : ℚ) ∈
      approx (OfScientific.ofScientific x u t : Interval) := by
  simp only [OfScientific.ofScientific]
  apply approx_ofRat

/-- `1 : Interval` is conservative -/
@[mono] lemma approx_one : 1 ∈ approx (1 : Interval) := by
  rw [←Nat.cast_one]
  apply approx_ofNat

/-- `1 : Interval` is conservative, `⊆` version since this appears frequently -/
@[mono] lemma subset_approx_one : {1} ⊆ approx (1 : Interval) := by
  simp only [singleton_subset_iff]; exact approx_one

/-- `n.lo ≤ n` -/
lemma ofNat_le (n : ℕ) : (.ofNat n : Interval).lo.val ≤ n := by
  simp only [ofNat]
  by_cases n : (.ofNat n false : Fixed s) = nan
  · simp only [n, Fixed.val_nan]
    exact le_trans (neg_nonpos.mpr (zpow_nonneg (by norm_num) _)) (Nat.cast_nonneg _)
  · exact le_trans (Fixed.ofNat_le n) (by norm_num)

/-- `n ≤ n.hi` unless we're `nan` -/
lemma le_ofNat (n : ℕ) (h : (.ofNat n : Interval).hi ≠ nan) :
    n ≤ (.ofNat n : Interval).hi.val := by
  rw [ofNat] at h ⊢; exact Fixed.le_ofNat h

/-- `1.lo ≤ 1` -/
lemma one_le : (1 : Interval).lo.val ≤ 1 := by
  simpa only [Nat.cast_one] using ofNat_le 1 (s := s)

/-- `1 ≤ 1.hi` unless we're `nan` -/
lemma le_one (n : (1 : Interval).hi ≠ nan) : 1 ≤ (1 : Interval).hi.val := by
  rw [one_def, ofNat] at n ⊢
  refine le_trans (by norm_num) (Fixed.le_ofNat n)
