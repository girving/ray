-- Simple theorems

import algebra.group_power.ring
import analysis.special_functions.pow
import data.real.basic
import data.complex.basic
import measure_theory.integral.circle_integral
import tactic.linarith.frontend
open tactic.interactive (nlinarith)
open complex (abs has_zero)
open_locale nnreal

namespace simple

lemma abs_sub_ge (a b : ℂ) : abs (a + b) ≥ abs a - abs b := begin
  let h := complex.abs_add (a + b) (-b),
  simp at h,
  linarith,
end

lemma abs_sub_ge' {a b : ℂ} : abs (a + b) ≥ abs a - abs b := abs_sub_ge _ _

lemma le_to_ge {X : Type} [linear_order X] {a b : X} (h : a ≤ b) : b ≥ a := h
lemma ge_to_le {X : Type} [linear_order X] {a b : X} (h : a ≥ b) : b ≤ a := h
lemma lt_to_gt {X : Type} [linear_order X] {a b : X} (h : a < b) : b > a := h
lemma gt_to_lt {X : Type} [linear_order X] {a b : X} (h : a > b) : b < a := h

lemma sq_bound (x : ℝ) : (1 + x)^2 ≥ 1 + 2*x := begin
  have h : (1 + x)^2 = 1 + 2*x + x^2 := by ring,
  nlinarith
end

lemma sq_increasing {x y : ℝ} (p : 0 ≤ x) (h : x ≤ y) : x^2 ≤ y^2 := by nlinarith
lemma mul_increasing {x y z : ℝ} (p : 0 ≤ x) (h : y ≤ z) : x * y ≤ x * z := mul_le_mul_of_nonneg_left h p
lemma nat_nonneg (n : ℕ) : 0 ≤ (↑n : ℝ) := by simp

lemma large_div_nat (a b : ℝ) (h : a > 0) : ∃ n : ℕ, a * n ≥ b := begin
  existsi (nat.ceil (b / a)),
  have e : a * (b / a) = b := calc a * (b / a) = b / a * a : by ring
                            ... = b : div_mul_cancel b (ne_of_gt h),
  nth_rewrite 1 ←e,
  refine mul_le_mul_of_nonneg_left _ _,
  exact nat.le_ceil _,
  apply le_of_lt,
  assumption
end

lemma gap {x y : ℝ} (h : x < y) : ∃ s : ℝ, s > 0 ∧ x + s ≤ y := begin
  have sp := sub_lt_sub_right h x,
  set s := y - x with q,
  have xx : x - x = 0 := by ring,
  rw [←q, xx] at sp,
  existsi s,
  constructor,
  assumption,
  linarith
end

lemma not_all {A : Type} {p : A → Prop} (_ : ¬∀ x : A, p x) : ∃ x : A, ¬(p x) := by finish

lemma not_false (p : Prop) : ¬p ↔ (p → false) := by finish
lemma not_lt {x y : ℝ} : (x < y → false) ↔ (x ≥ y) := begin
  rw (not_false (x < y)).symm,
  finish
end

lemma coe_increasing {a b : ℕ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := nat.cast_le.mpr h
lemma coe_pow_ge_one {n : ℕ} : 1 ≤ (2^n : ℝ) := begin
  induction n with n,
  norm_num,
  transitivity (2^n : ℝ),
  assumption,
  have h : 2^n.succ = 2*2^n := pow_succ _ _,
  have he : (2^n.succ : ℝ) = (2*2^n : ℝ) := rfl,
  rw he, linarith
end

lemma real_nnreal_ennreal (r : ℝ) : ennreal.of_real r = ↑r.to_nnreal := rfl
lemma nnreal_ennreal_coe_lt {a : ennreal} {b : nnreal} (h : a < b) : a.to_nnreal < b := begin
  rw ←with_top.coe_lt_coe,
  calc ↑(a.to_nnreal) ≤ a : ennreal.coe_to_nnreal_le_self
  ... < ↑b : h
end
lemma to_nnreal_pos {a b c : ennreal} (ab : a < b) (bc : b < c) : 0 < b.to_nnreal := begin
  apply ennreal.to_nnreal_pos,
  refine ne_of_gt _,
  calc 0 ≤ a : by simp
  ... < b : ab,
  refine ne_of_lt _,
  calc b < c : bc
  ... ≤ ⊤ : by simp
end

lemma inv_nonneg {x : ℝ} (h : x ≥ 0) : x⁻¹ ≥ 0 := inv_nonneg.mpr h

lemma pow_inv (x : ℝ) (n : ℕ) : (x^n)⁻¹ = x⁻¹^n := begin by_cases x = 0, simp, field_simp end

lemma div_pow_inv (x y : ℝ) (n : ℕ) : x / y^n = x * y⁻¹^n := begin
  calc x / y^n = (y^n)⁻¹ * x : (inv_mul_eq_div (y^n) x).symm
  ... = y⁻¹^n * x : by rw (pow_inv y n)
  ... = x * y⁻¹^n : by ring
end

lemma abs_sub (z w : ℂ) : abs (z - w) ≤ abs z + abs w := begin
  set n := -w,
  have h0 : z - w = z + n := rfl,
  have h1 : abs w = abs n := (complex.abs_neg w).symm,
  rw [h0, h1], exact complex.abs_add z n
end

lemma abs_sub' {z w : ℂ} : abs (z - w) ≤ abs z + abs w := abs_sub z w

lemma abs_le_zero {z : ℂ} (h : abs z ≤ 0) : z = 0 :=
  complex.abs_eq_zero.mp (le_antisymm (complex.abs_nonneg z) h).symm

lemma sqr_pos {x : ℝ} (h : x > 0) : x^2 > 0 := pow_pos h 2

lemma zero_lt_bit1 {A : Type} [linear_ordered_semiring A] {a : A} : 0 < a → 0 < bit1 a := begin
  rw [bit1, bit0], intro, apply add_pos, apply add_pos, assumption, assumption, norm_num
end

lemma zero_le_bit1 {A : Type} [linear_ordered_semiring A] {a : A} : 0 ≤ a → 0 ≤ bit1 a := begin
  rw [bit1, bit0], intro, apply add_nonneg, apply add_nonneg, assumption, assumption, norm_num
end

lemma ring_sub_pos {A : Type} [linear_ordered_ring A] {a b : A} (h : a < b) : 0 < b - a := begin
  simp, assumption
end

lemma ring_sub_le_sub {A : Type} [linear_ordered_ring A] {a b c d : A}
    (ac : a ≤ c) (db : d ≤ b): a - b ≤ c - d := sub_le_sub ac db

lemma ring_add_le_add {A : Type} [linear_ordered_ring A] {a b c d : A}
    (ac : a ≤ c) (bd : b ≤ d) : a + b ≤ c + d := add_le_add ac bd

lemma ring_add_nonneg {A : Type} [linear_ordered_ring A] {a b : A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := add_nonneg ha hb

lemma ring_sub_nonneg {A : Type} [linear_ordered_ring A] {a b : A} (h : b ≤ a) : 0 ≤ a - b := sub_nonneg.mpr h

lemma ring_add_lt_add_left {A : Type} [linear_ordered_ring A] {a b c : A}
    (h : b < c) : a + b < a + c := add_lt_add_left h a

lemma ring_add_lt_add_right {A : Type} [linear_ordered_ring A] {a b c : A}
    (h : b < c) : b + a < c + a := add_lt_add_right h a

theorem pow_pos' {A : Type} [ordered_semiring A] {a : A} {n : ℕ} (h : 0 < a) : 0 < a^n := pow_pos h _
theorem pow_nonneg' {A : Type} [ordered_semiring A] {a : A} {n : ℕ} (h : 0 ≤ a) : 0 ≤ a^n := pow_nonneg h _

lemma finset_complex_abs_sum_le (N : finset ℕ) (f : ℕ → ℂ)
    : abs (N.sum (λ n, f n)) ≤ N.sum (λ n, abs (f n)) :=
begin
  induction N using finset.induction with n N Nn h, {
    simp
  }, {
    rw finset.sum_insert Nn,
    rw finset.sum_insert Nn,
    transitivity abs (f n) + abs (N.sum (λ n, f n)), {
      exact complex.abs_add _ _
    }, {
      apply add_le_add_left, assumption
    }
  }
end

lemma div_self {K : Type} [division_ring K] {a : K} (h : a ≠ 0) : a / a = 1 :=
  by rw [div_eq_mul_inv, mul_inv_cancel h]

lemma div_cancel_le {x : ℝ} : x * x⁻¹ ≤ 1 := begin
  rw ←div_eq_mul_inv,
  exact div_self_le_one x,
end

lemma ne_iff_not_eq {T : Type} {a b : T} : ¬(a = b) ↔ a ≠ b := begin
  have q := eq_or_ne a b,
  finish
end

lemma div_le_div_right {a b c : ℝ} : c ≥ 0 → a ≤ b → a / c ≤ b / c := begin
  intros c0 ab,
  by_cases cnz : c = 0, { rw cnz, simp },
  rw ne_iff_not_eq at cnz,
  refine (div_le_div_right _).mpr ab,
  exact lt_of_le_of_ne c0 cnz.symm
end

lemma subset_union_sdiff (A B : finset ℕ) : B ⊆ A ∪ B \ A := begin
  rw finset.subset_iff, intros x Bx,
  rw [finset.mem_union, finset.mem_sdiff],
  finish
end

lemma le_add_nonneg_right {a b : ℝ} : 0 ≤ b → a ≤ a + b := le_add_of_le_of_nonneg (le_refl a)
lemma le_add_nonneg_left {a b : ℝ} : 0 ≤ b → a ≤ b + a := begin
  rw add_comm, exact le_add_nonneg_right
end

lemma div_le_one {a b : ℝ} : 0 ≤ b → a ≤ b → a / b ≤ 1 := begin
  intros b0 ab,
  by_cases z : b = 0, {
    rw z, simp
  }, {
    refine (div_le_one _).mpr _,
    have z : b ≠ 0 := z,
    exact lt_of_le_of_ne b0 z.symm,
    assumption
  }
end

lemma real_abs_nonneg {a : ℝ} : |a| ≥ 0 := abs_nonneg _

lemma nat_real_coe_le_coe {n m : ℕ} : n ≤ m → (n : ℝ) ≤ (m : ℝ) := begin
  exact nat.cast_le.mpr
end

lemma pow_div {z : ℂ} {n : ℕ} (z0 : z ≠ 0) : z ^ (n+1) / z = z ^ n := begin
  rw pow_succ,
  calc z * z^n / z = z / z * z^n : (div_mul_eq_mul_div _ _ _).symm
  ... = 1 * z^n : by rw div_self z0
  ... = z^n : by ring
end

-- (z ^ a) ^ n = z ^ (a * n)
lemma pow_mul_nat {z w : ℂ} {n : ℕ} : (z ^ w) ^ n = z ^ (w * n) := begin
  by_cases z0 : z = 0, {
    rw z0,
    by_cases w0 : w = 0, { rw w0, simp },
    by_cases n0 : n = 0, { rw n0, simp },
    have wn0 : w * n ≠ 0 := mul_ne_zero w0 (nat.cast_ne_zero.mpr n0),
    rw complex.zero_cpow w0,
    rw complex.zero_cpow wn0,
    exact zero_pow' n n0
  },
  rw complex.cpow_def_of_ne_zero z0,
  rw complex.cpow_def_of_ne_zero z0,
  rw ←complex.exp_nat_mul,
  ring_nf
end

lemma continuous_on.circle_map (c : ℂ) (r : ℝ) (s : set ℝ) : continuous_on (circle_map c r) s :=
  continuous.continuous_on (continuous_circle_map _ _)

-- Version of continuous_on.comp for f ∘ g that puts everything about g after :,
-- to behave well under apply_rules.
lemma continuous_on.comp_left {B C : Type} [topological_space B] [topological_space C]
    {s : set B} {f : B → C} (fc : continuous_on f s)
    : ∀ (A : Type) [tA : topological_space A] (t : set A) (g : A → B),
      @continuous_on A B tA _ g t → set.maps_to g t s → @continuous_on A C tA _ (λ a, f (g a)) t :=
  λ A tA t g gc m, @continuous_on.comp _ _ _ tA _ _ _ _ _ _ fc gc m

lemma continuous_complex_abs : continuous complex.abs := begin
  rw metric.continuous_iff, intros z e ep,
  existsi [e, ep], intros w wz,
  rw real.dist_eq,
  rw complex.dist_eq at wz,
  have h := abs_norm_sub_norm_le w z,
  simp at h,
  exact lt_of_le_of_lt h wz,
end

end simple