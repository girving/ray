import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Ray.Dynamics.Multibrot.Specific

/-!
## `Complex.log (1 + z) ≤ -Real.log (1 - abs z)` for `abs z < 1`
-/

open Complex (abs)
open Set

/-- Bound `Complex.log (1 + z)` in terms of `Real.log`.

    It feels like this lemma should have an algebraic proof, but I don't see it:
      https://math.stackexchange.com/questions/4844828 -/
lemma Complex.abs_log_one_add_le {z : ℂ} (z1 : abs z < 1) :
    abs (Complex.log (1 + z)) ≤ -Real.log (1 - abs z) := by
  have m1 : ∀ t : ℝ, t ≤ 1 → t * abs z < 1 :=
    fun _ m ↦ Right.mul_lt_one_of_le_of_lt_of_nonneg m z1 (Complex.abs.nonneg _)
  have dc : ∀ t : ℝ, t ∈ uIcc 0 1 →
      HasDerivAt (fun t : ℝ ↦ Complex.log (1 + t*z)) (z / (1 + t*z)) t := by
    intro t m
    apply HasDerivAt.clog_real
    · exact ((hasDerivAt_mul_const _).const_add _).comp_ofReal
    · apply Complex.mem_slitPlane_of_norm_lt_one
      simp only [norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal]
      simp only [ge_iff_le, zero_le_one, uIcc_of_le, mem_Icc] at m
      apply m1; simp only [abs_le]; exact ⟨by linarith, m.2⟩
  have dr : ∀ t : ℝ, t ∈ uIcc 0 1 →
      HasDerivAt (fun t : ℝ ↦ -Real.log (1 - t * abs z)) (- (-abs z / (1 - t * abs z))) t := by
    intro t m
    simp only [ge_iff_le, zero_le_one, uIcc_of_le, mem_Icc] at m
    exact (((hasDerivAt_mul_const _).const_sub _).log ((sub_pos.mpr (m1 _ m.2)).ne')).neg
  have ic : IntervalIntegrable (fun t ↦ z / (1 + t*z)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_const.div (Continuous.continuousOn (by continuity))
    intro t ⟨t0,t1⟩
    rw [←Complex.abs.ne_zero_iff]
    apply ne_of_gt
    calc abs (1 + t*z)
      _ ≥ Complex.abs 1 - abs (t*z) := Complex.abs.le_add _ _
      _ = 1 - |t| * abs z := by simp only [map_one, map_mul, Complex.abs_ofReal]
      _ > 0 := by refine sub_pos.mpr (m1 _ (abs_le.mpr ⟨by linarith, t1⟩))
  simp only [neg_div, neg_neg] at dr
  have ir : IntervalIntegrable (fun t ↦ abs z / (1 - t * abs z)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply continuousOn_const.div (Continuous.continuousOn (by continuity))
    intro t ⟨_,t1⟩; exact ne_of_gt (sub_pos.mpr (m1 _ t1))
  have fc := intervalIntegral.integral_eq_sub_of_hasDerivAt dc ic
  have fr := intervalIntegral.integral_eq_sub_of_hasDerivAt dr ir
  simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, add_zero, Complex.log_one,
    sub_zero, Real.log_one, neg_zero] at fc fr
  rw [←fc, ←fr, ←Complex.norm_eq_abs]
  clear dc dr fc fr
  apply le_trans (intervalIntegral.norm_integral_le_integral_norm zero_le_one) ?_
  apply intervalIntegral.integral_mono_on zero_le_one ic.norm ir
  intro t ⟨t0,t1⟩
  simp only [norm_div, Complex.norm_eq_abs]
  apply div_le_div_of_nonneg_left (Complex.abs.nonneg _) (sub_pos.mpr (m1 _ t1)) ?_
  calc abs (1 + t * z)
    _ ≥ Complex.abs 1 - abs (t * z) := Complex.abs.le_add _ _
    _ = 1 - t * abs z := by
      simp only [map_one, map_mul, Complex.abs_ofReal, _root_.abs_of_nonneg t0]

/-- The real version is simpler, but we'll use the complex version anyways -/
lemma Real.abs_log_one_add_le {x : ℝ} (x1 : |x| < 1) :
    |Real.log (1 + x)| ≤ -Real.log (1 - |x|) := by
  have h := Complex.abs_log_one_add_le (z := x) ?_
  · rw [←Complex.ofReal_one, ←Complex.ofReal_add, ←Complex.ofReal_log, Complex.abs_ofReal,
      Complex.abs_ofReal] at h
    · exact h
    · simp only [abs_lt] at x1; linarith
  · simpa only [Complex.abs_ofReal]

/-- Our bound is monotonic -/
lemma Real.neg_log_one_sub_mono {x y : ℝ} (xy : x ≤ y) (y1 : y < 1) :
    -Real.log (1 - x) ≤ -Real.log (1 - y) :=
  neg_le_neg (Real.log_le_log (by linarith) (by linarith))

/-- Our bound is `≤ 2` for `x ≤ 1/2` -/
lemma neg_log_one_sub_le_two {x : ℝ} (x2 : x ≤ 1/2) : -Real.log (1 - x) ≤ 2 := by
  apply le_trans (Real.neg_log_one_sub_mono x2 (by linarith)) ?_
  rw [neg_le, Real.le_log_iff_exp_le]
  · exact (exp_neg_ofNat_lt).le
  · norm_num

/-- Variable linear bound on `-log (1 - x)`.
    This is intended to be used with a concrete value for `c`, so that `norm_num` can work.  -/
lemma neg_log_one_sub_le_linear {x c : ℝ} (x0 : 0 ≤ x) (c1 : 1 < c)
    (xc : x ≤ min 1 (((c - 1) * 2)⁻¹ + 1)⁻¹) : -Real.log (1 - x) ≤ c * x := by
  rcases le_min_iff.mp xc with ⟨x1,xc⟩
  by_cases xz : x = 0
  · simp only [xz, sub_zero, Real.log_one, neg_zero, mul_zero, le_refl]
  by_cases xe : x = 1
  · simp only [xe, sub_self, Real.log_zero, neg_zero, mul_one]; linarith
  replace x1 := Ne.lt_of_le xe x1
  have x0' : 0 < x := (Ne.symm xz).lt_of_le x0
  have c1p : 0 < (c - 1) * 2 := mul_pos (sub_pos.mpr c1) (by norm_num)
  have x1p : 0 < 1 - x := by linarith
  have h := Complex.norm_log_one_add_sub_self_le (z := -x)
    (by simp only [norm_neg, Complex.norm_eq_abs, Complex.abs_ofReal, abs_of_nonneg x0]; exact x1)
  simp only [Complex.norm_eq_abs, Complex.abs_ofReal, ←Complex.ofReal_one, ←Complex.ofReal_add,
    ←Complex.ofReal_log x1p.le, ←Complex.ofReal_sub, abs_le, abs_of_nonneg x0, ←Complex.ofReal_neg,
    ←sub_eq_add_neg, abs_neg] at h
  replace h : -Real.log (1 - x) ≤ x + x^2 * (1 - x)⁻¹ / 2 := by linarith
  apply le_trans h
  rw [pow_two, mul_assoc, mul_div_assoc, ←mul_one_add, mul_comm x _]
  apply mul_le_mul_of_nonneg_right _ x0
  nth_rw 1 [←inv_inv x]
  rw [←mul_inv, mul_sub, mul_one, inv_mul_cancel₀ xz]
  rw [add_comm, ←le_sub_iff_add_le, div_le_iff₀ (by norm_num)]
  apply inv_le_of_inv_le₀ c1p
  rw [le_sub_iff_add_le, le_inv_comm₀ (add_pos (inv_pos.mpr c1p) (by norm_num)) x0']
  exact xc
