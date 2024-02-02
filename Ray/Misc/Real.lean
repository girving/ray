import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Pointwise.Interval
import Mathlib.Tactic.Linarith.Frontend

open Classical
open Pointwise

/-!
## `ℝ` lemmas
-/

open Set
open scoped Real

/-- Simplify to case assuming not `nan` -/
lemma mem_if_univ_iff {x : ℝ} {u : Set ℝ} {p : Prop} {dp : Decidable p} :
    x ∈ @ite _ p dp univ u ↔ ¬p → x ∈ u := by
  by_cases n : p
  repeat simp only [n, ite_true, ite_false, mem_univ, not_true_eq_false, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left]

/-- Simplify to case assuming not `nan` -/
lemma subset_if_univ_iff {t u : Set ℝ} {p : Prop} {dp : Decidable p} :
    t ⊆ @ite _ p dp univ u ↔ ¬p → t ⊆ u := by
  by_cases n : p
  repeat simp only [n, ite_true, ite_false, subset_univ, not_true_eq_false, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left]

/-- Reals are either `≤ 0` or `≥ 0` -/
lemma nonpos_or_nonneg (x : ℝ) : x ≤ 0 ∨ 0 ≤ x := by
  by_cases p : 0 ≤ x
  · right; assumption
  · left; linarith

/-- The range of nonzero multiplication is `univ` -/
@[simp] lemma range_mul_right_eq_univ {a : ℝ} (a0 : a ≠ 0) : range (fun x ↦ x * a) = univ := by
  simp only [eq_univ_iff_forall, mem_range]
  intro x; use x / a
  simp only [div_mul_cancel _ a0]

/-- Multiplying by a nonzero preserves `univ` -/
@[simp] lemma Set.univ_mul_singleton {a : ℝ} (a0 : a ≠ 0) : univ * ({a} : Set ℝ) = univ := by
  simp only [mul_singleton, image_univ, range_mul_right_eq_univ a0]

/-- Multiplying an `Icc` by a positive number produces the expected `Icc` -/
@[simp] lemma Set.Icc_mul_singleton {a b x : ℝ} (x0 : 0 < x) :
    Icc a b * {x} = Icc (a * x) (b * x) := by
  simp only [mul_singleton]
  ext y; simp only [mem_image, mem_Icc]
  constructor
  · intro ⟨z, ⟨hz1, hz2⟩, hz3⟩; exact ⟨by nlinarith, by nlinarith⟩
  · intro ⟨h0,h1⟩; use y / x
    simp only [le_div_iff x0, h0, div_le_iff x0, h1, and_self, div_mul_cancel _ x0.ne']

/-- Negative `c` version of `image_mul_right_Icc` -/
theorem image_mul_right_Icc_of_neg {a b c : ℝ} (c0 : c < 0) :
    (fun x ↦ x * c) '' Icc a b = Icc (b * c) (a * c) := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · intro ⟨y,⟨ay,yb⟩,yc⟩; rw [←yc]; constructor
    · exact mul_le_mul_of_nonpos_right yb c0.le
    · exact mul_le_mul_of_nonpos_right ay c0.le
  · intro ⟨bc,ac⟩; use x/c; refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [le_div_iff_of_neg c0]
    · simpa only [div_le_iff_of_neg c0]
    · simp only [div_mul_cancel _ c0.ne]

/-- A simple lemma that we use a lot -/
@[simp] lemma two_pow_pos {n : ℕ} : 0 < (2:ℝ) ^ n := pow_pos (by norm_num) _

/-- A simple lemma that we use a lot -/
@[simp] lemma two_zpow_pos {n : ℤ} : 0 < (2:ℝ) ^ n := zpow_pos_of_pos (by norm_num) _

/-- The range of two power multiplication is `univ` -/
@[simp] lemma range_mul_two_zpow_eq_univ {n : ℤ} : range (fun x : ℝ ↦ x * 2^n) = univ :=
  range_mul_right_eq_univ two_zpow_pos.ne'

/-- Multiplying an `Icc` by a two power is nice -/
@[simp] lemma Set.Icc_mul_two_zpow {a b : ℝ} {n : ℤ} :
    Icc a b * {2^n} = Icc (a * 2^n) (b * 2^n) := Icc_mul_singleton two_zpow_pos

/-- `Icc` commutes with `⁻¹` if we're positive -/
lemma Set.inv_Icc {a b : ℝ} (a0 : 0 < a) (b0 : 0 < b) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by
  ext x
  simp only [mem_inv, mem_Icc, and_comm]
  by_cases x0 : x ≤ 0
  · have i0 : x⁻¹ ≤ 0 := inv_nonpos.mpr x0
    simp only [(by linarith : ¬a ≤ x⁻¹), false_and, false_iff, not_and, not_le,
      lt_of_le_of_lt x0 (inv_pos.mpr b0), implies_true]
  · simp only [not_le] at x0
    simp only [le_inv x0 a0, inv_le b0 x0]

/-- `mono` friendly version of `Set.mem_inv` -/
@[mono] lemma Set.mem_inv_of_mem {x : ℝ} {s : Set ℝ} (m : x ∈ s) : x⁻¹ ∈ s⁻¹ := by
  rw [Set.mem_inv, inv_inv]; exact m

/-- `pow` and `zpow` multiply via addition -/
lemma pow_mul_zpow {a : ℝ} (a0 : a ≠ 0) (b : ℕ) (c : ℤ) : a^b * a^c = a^(b + c) := by
  simp only [← zpow_ofNat, zpow_add₀ a0]

/-- `zpow` and `pow` divide via subtraction -/
lemma zpow_mul_pow {a : ℝ} (a0 : a ≠ 0) (b : ℤ) (c : ℕ) : a^b * a^c = a^(b + c) := by
  simp only [← zpow_ofNat, zpow_add₀ a0]

/-- `pow` and `zpow` multiply via addition -/
lemma zpow_div_pow {a : ℝ} (a0 : a ≠ 0) (b : ℤ) (c : ℕ) : a^b / a^c = a^(b - c) := by
  simp only [← zpow_ofNat, zpow_sub₀ a0]

/-- `-` and `⁻¹` commute on `Set ℝ` -/
@[simp] lemma Set.inv_neg {s : Set ℝ} : (-s)⁻¹ = -s⁻¹ := by
  ext x; simp only [_root_.inv_neg, mem_neg, mem_inv]

/-- Make `x ^ (7 : ℝ)` simplify to `x ^ (7 : ℕ)` (when literals are involved) -/
@[simp] lemma Real.rpow_ofNat {x : ℝ} {n : ℕ} [Nat.AtLeastTwo n] :
    x ^ (no_index (OfNat.ofNat n) : ℝ) = x ^ (OfNat.ofNat n) := Real.rpow_nat_cast _ _

/-- `x - y ≤ x + z ↔ -y ≤ z` -/
@[simp] lemma sub_le_add_iff_left (x y z : ℝ) : x - y ≤ x + z ↔ -y ≤ z := by
  simp only [sub_eq_add_neg, add_le_add_iff_left]

/-- `x + y ≤ x - z ↔ y ≤ -z` -/
@[simp] lemma add_le_sub_iff_left (x y z : ℝ) : x + y ≤ x - z ↔ y ≤ -z := by
  simp only [sub_eq_add_neg, add_le_add_iff_left]

set_option maxHeartbeats 1000000 in
/-- Rewrite `Icc * Icc ⊆ Icc` in terms of inequalities -/
lemma Icc_mul_Icc_subset_Icc {a b c d x y : ℝ} (ab : a ≤ b) (cd : c ≤ d) :
    Icc a b * Icc c d ⊆ Icc x y ↔
      x ≤ a * c ∧ x ≤ a * d ∧ x ≤ b * c ∧ x ≤ b * d ∧
      a * c ≤ y ∧ a * d ≤ y ∧ b * c ≤ y ∧ b * d ≤ y := by
  have am : a ∈ Icc a b := left_mem_Icc.mpr ab
  have bm : b ∈ Icc a b := right_mem_Icc.mpr ab
  have cm : c ∈ Icc c d := left_mem_Icc.mpr cd
  have dm : d ∈ Icc c d := right_mem_Icc.mpr cd
  simp only [←image2_mul, image2_subset_iff]
  constructor
  · intro h
    simp only [mem_Icc (a := x)] at h
    exact ⟨(h _ am _ cm).1, (h _ am _ dm).1, (h _ bm _ cm).1, (h _ bm _ dm).1,
           (h _ am _ cm).2, (h _ am _ dm).2, (h _ bm _ cm).2, (h _ bm _ dm).2⟩
  · simp only [mem_Icc]
    rintro ⟨xac,xad,xbc,xbd,acy,ady,bcy,bdy⟩ u ⟨au,ub⟩ v ⟨cv,vd⟩
    all_goals cases nonpos_or_nonneg c
    all_goals cases nonpos_or_nonneg d
    all_goals cases nonpos_or_nonneg u
    all_goals cases nonpos_or_nonneg v
    all_goals exact ⟨by nlinarith, by nlinarith⟩

/-- Rewrite `Icc^2 ⊆ Icc` in terms of inequalities -/
lemma sqr_Icc_subset_Icc {a b x y : ℝ} :
    (fun x ↦ x^2) '' Icc a b ⊆ Icc x y ↔ ∀ u, a ≤ u → u ≤ b → x ≤ u^2 ∧ u^2 ≤ y := by
  simp only [subset_def, mem_image, mem_Icc, forall_exists_index, and_imp]
  constructor
  · intro h u au ub; exact h _ u au ub rfl
  · intro h u v av vb vu; rw [←vu]; exact h v av vb
