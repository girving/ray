-- λ x, max b (log x)

import analysis.special_functions.pow.complex
import data.complex.basic
import data.real.basic

import tactics

open complex (abs)
open_locale real
open set (univ Ici)
noncomputable theory

variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E]

-- max b (log x)
def max_log (b x : ℝ) : ℝ := (max b.exp x).log

lemma max_exp_pos {b x : ℝ} : max b.exp x > 0 := lt_of_lt_of_le (real.exp_pos _) (by bound)
@[simp] lemma le_max_log (b x : ℝ) : b ≤ max_log b x := begin rw [max_log, real.le_log_iff_exp_le max_exp_pos], bound end
lemma max_log_eq_b {b x : ℝ} (h : b.exp ≥ x) : max_log b x = b := by simp [max_log, max_eq_left h]
lemma max_log_eq_log {b x : ℝ} (h : b.exp ≤ x) : max_log b x = x.log := by simp [max_log, max_eq_right h]
lemma max_log_le {b x y : ℝ} (yb : b ≤ y) (xy : x ≤ y.exp) : max_log b x ≤ y := begin
  rw [max_log, real.log_le_iff_le_exp max_exp_pos], apply max_le, apply real.exp_le_exp.mpr yb, exact xy,
end
lemma le_exp_max_log (b x : ℝ) : x ≤ (max_log b x).exp := begin rw [max_log, real.exp_log max_exp_pos], bound end

-- Extracting underlying bounds from max_log bounds
lemma le_of_max_log_le {b x y : ℝ} (m : max_log b x ≤ y) : x ≤ y.exp := begin
  rw [max_log, real.log_le_iff_le_exp max_exp_pos] at m, exact le_of_max_le_right m,
end

-- max_log is increasing
lemma monotone_max_log (b : ℝ) : monotone (λ x, max_log b x) := begin
  simp_rw max_log, intros x y xy, simp, rw real.log_le_log max_exp_pos max_exp_pos, apply max_le_max (le_refl _) xy,
end

lemma continuous_max_log (b : ℝ) : continuous (λ x, max_log b x) := begin
  simp_rw max_log, rw continuous_iff_continuous_at, intro x,
  apply continuous_at.comp, refine continuous_at.log _ (ne_of_gt max_exp_pos),
  apply continuous_at_id, apply continuous.continuous_at, continuity,
end

-- max b (log ‖f z‖) is continuous for continuous f
theorem continuous_on.max_log_norm {f : ℂ → E} {s : set ℂ}
    (fc : continuous_on f s) (b : ℝ) : continuous_on (λ z, max_log b ‖f z‖) s :=
  (continuous_max_log b).comp_continuous_on fc.norm

-- log is Lipschitz away from 0
lemma lipschitz_on_with.log (b : ℝ) : lipschitz_on_with (-b).exp.to_nnreal real.log (Ici b.exp) := begin
  rw lipschitz_on_with_iff_dist_le_mul,
  have half : ∀ x y : ℝ, y ≥ b.exp → x ≥ y → |x.log - y.log| ≤ (-b).exp * |x - y|, {
    intros x y yb xy,
    have yp : y > 0 := lt_of_lt_of_le (real.exp_pos _) yb,
    have xp : x > 0 := lt_of_lt_of_le yp xy,
    have yi : (-b).exp ≥ y⁻¹, { rw real.exp_neg, bound [real.exp_pos] },
    rw abs_of_nonneg (sub_nonneg.mpr xy),
    rw abs_of_nonneg (sub_nonneg.mpr ((real.log_le_log yp xp).mpr xy)),
    rw ←real.log_div (ne_of_gt xp) (ne_of_gt yp),
    rw real.log_le_iff_le_exp (div_pos xp yp),
    transitivity (y⁻¹ * (x - y)).exp, swap, bound [real.exp_le_exp.mpr],
    have e : y⁻¹ * (x - y) = x/y - 1 := by field_simp [ne_of_gt yp],
    rw e,
    have e1 := real.add_one_le_exp (x/y - 1),
    simp at e1, exact e1,
  },
  intros x xs y ys,
  simp at xs ys ⊢,
  rw max_eq_left (le_of_lt (real.exp_pos _)),
  simp_rw real.dist_eq,
  by_cases xy : x ≥ y, { exact half x y ys xy },
  simp at xy,
  rw [←neg_sub y x, abs_neg],
  rw [←neg_sub y.log x.log, abs_neg],
  exact half y x xs (le_of_lt xy),
end

-- max_log is Lipschitz
theorem lipschitz_with.max_log (b : ℝ) : lipschitz_with (-b).exp.to_nnreal (max_log b) := begin
  rw ←lipschitz_on_univ,
  have h := (lipschitz_on_with.log b).comp ((lipschitz_with.id.const_max (b.exp)).lipschitz_on_with univ) (by simp),
  have e : real.log ∘ max (real.exp b) = max_log b, { funext x, simp [max_log] },
  simp at h, simpa [e],
end
