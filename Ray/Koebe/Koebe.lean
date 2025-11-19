import Ray.Dynamics.Multiple
import Ray.Koebe.Bieberbach

/-!
## Koebe quarter theorem

If `f : ball 0 1 → ℂ` is analytic and injective, its image contains `ball (f 0) (‖f' 0‖ / 4)`.

The proof follows Wikipedia: https://en.wikipedia.org/wiki/Koebe_quarter_theorem
-/

open Classical
open Complex (arg)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped ContDiff Topology NNReal
noncomputable section

variable {f : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- The Koebe quarter theorem, `f 0 = 0, f' 0 = 1` case -/
theorem koebe_quarter_special (fa : AnalyticOnNhd ℂ f (ball 0 1)) (inj : InjOn f (ball 0 1))
    (f0 : f 0 = 0) (d0 : deriv f 0 = 1) : ball 0 4⁻¹ ⊆ f '' (ball 0 1) := by
  intro w wm
  contrapose wm
  simp only [Metric.mem_ball, dist_zero_right, not_lt]
  have m0 : 0 ∈ ball (0 : ℂ) 1 := by simp only [Metric.mem_ball, dist_self, zero_lt_one]
  have w0 : w ≠ 0 := by
    contrapose wm
    simp only [wm]
    exact ⟨0, m0, f0⟩
  -- If `w` is not an output of `f`, we construct an auxiliary `h` using the missed value
  set h : ℂ → ℂ := fun z ↦ w * f z / (w - f z)
  have fw : ∀ x ∈ ball 0 1, f x ≠ w := by
    simpa only [sub_ne_zero, mem_image, not_exists, not_and, ne_comm (a := w)] using wm
  have sub0 : ∀ x ∈ ball 0 1, w - f x ≠ 0 := by simpa [sub_ne_zero, ne_comm (a := w)] using fw
  have ha : AnalyticOnNhd ℂ h (ball 0 1) :=
    (analyticOnNhd_const.mul fa).div (analyticOnNhd_const.sub fa) sub0
  -- `h` is injective
  have f0' : ∀ z ∈ ball 0 1, f z = 0 ↔ z = 0 :=
    fun z m ↦ by simpa only [f0] using inj.eq_iff m (y := 0) m0
  have h0 : h 0 = 0 := by simp only [f0, mul_zero, sub_zero, zero_div, h]
  have h0' : ∀ z ∈ ball 0 1, h z = 0 ↔ z = 0 := by
    intro z m
    simp only [h, div_eq_zero_iff, mul_eq_zero, w0, false_or, sub0 _ m, or_false, f0' z m]
  have hinj : InjOn h (ball 0 1) := by
    intro x xm y ym e
    by_cases x0 : x = 0
    · grind only [= mem_image]
    · have fx0 : f x ≠ 0 := by grind only [= mem_image]
      have fy0 : f y ≠ 0 := by grind only [= mem_image]
      simp only [mul_div_assoc, mul_eq_mul_left_iff, w0, or_false, h] at e
      rw [← inv_inj] at e
      simp only [inv_div, sub_div, div_self fx0, div_self fy0, sub_left_inj] at e
      field_simp [w0] at e
      exact (inj.eq_iff xm ym).mp e.symm
  -- Evaluate the derivatives of `h` to second order
  have df0 := (fa 0 m0).differentiableAt
  have dh : ∀ z ∈ ball 0 1, deriv h z = w ^ 2 * deriv f z / (w - f z) ^ 2 := by
    intro z m
    have df := (fa z m).differentiableAt
    simp only [h]
    rw [deriv_fun_div (by fun_prop) (by fun_prop)]
    · simp only [deriv_const_mul_field', mul_right_comm _ (deriv f z), mul_sub, ← pow_two,
        deriv_const_sub, mul_neg, sub_neg_eq_add, ← add_mul, sub_add_cancel]
    · exact sub0 _ m
  have dh0 : deriv h 0 = 1 := by
    simp only [dh _ m0, d0, mul_one, f0, sub_zero, ← div_pow, div_self w0, one_pow]
  have ddh0 : deriv (deriv h) 0 = deriv (deriv f) 0 + 2 * w⁻¹ := by
    have ee : (fun z ↦ deriv h z) =ᶠ[𝓝 0] (fun z ↦ w ^ 2 * deriv f z / (w - f z) ^ 2) :=
      EqOn.eventuallyEq_of_mem dh (isOpen_ball.mem_nhds m0)
    simp only [ee.deriv_eq]
    have dd : DifferentiableAt ℂ (fun z ↦ deriv f z) 0 := (fa 0 m0).deriv.differentiableAt
    rw [deriv_fun_div (by fun_prop) (by fun_prop), deriv_fun_pow (by fun_prop)]
    · simp only [deriv_const_mul_field', f0, sub_zero, d0, mul_one, Nat.cast_ofNat,
        Nat.add_one_sub_one, pow_one, deriv_const_sub, mul_neg, sub_neg_eq_add, add_div, ← pow_mul,
        Nat.reduceMul]
      ring_nf
      have e0 : w ^ 3 * w⁻¹ ^ 4 * 2 = 2 * w⁻¹ := by field_simp [w0]
      have e1 : w ^ 4 * deriv (deriv f) 0 * w⁻¹ ^ 4 = deriv (deriv f) 0 := by field_simp [w0]
      simp only [e0, e1, add_comm, mul_comm _ (2 : ℂ)]
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, sub0 _ m0]
  -- Bieberbach applied to both `f` and `h` completes the proof
  have bf := bieberbach fa inj f0 d0
  have bh := bieberbach ha hinj h0 dh0
  simp only [ddh0] at bh
  rw [inv_le_comm₀ (by norm_num) (by positivity), ← norm_inv]
  calc ‖w⁻¹‖
    _ = ‖deriv (deriv f) 0 + 2 * w⁻¹ - deriv (deriv f) 0‖ / 2 := by simp
    _ ≤ (‖deriv (deriv f) 0 + 2 * w⁻¹‖ + ‖deriv (deriv f) 0‖) / 2 := by bound
    _ ≤ (4 + 4) / 2 := by bound
    _ = 4 := by norm_num

/-- Affine image of a ball -/
lemma affine_image_ball {a s c : ℂ} (s0 : s ≠ 0) :
    (fun z ↦ a + s * z) '' ball c r = ball (a + s * c) (r * ‖s‖) := by
  have s0' : 0 < ‖s‖ := by positivity
  ext z
  simp only [mem_image, Metric.mem_ball, dist_eq_norm]
  constructor
  · intro ⟨w, wr, wz⟩
    simp only [← wz, add_sub_add_left_eq_sub, ← mul_sub, mul_comm r, norm_mul]
    bound
  · intro lt
    refine ⟨(z - a) / s, ?_, ?_⟩
    · rw [← mul_lt_mul_iff_right₀ s0']
      simpa only [← norm_mul, mul_sub, mul_div_cancel₀ _ s0, mul_comm, sub_add_eq_sub_sub] using lt
    · simp only [mul_div_cancel₀ _ s0, add_sub_cancel]

/-- The Koebe quarter theorem, general affine case -/
lemma koebe_quarter' (fa : AnalyticOnNhd ℂ f (ball c r)) (inj : InjOn f (ball c r)) :
    ball (f c) (r * ‖deriv f c‖ / 4) ⊆ f '' (ball c r) := by
  by_cases r0 : r ≤ 0
  · simp only [Metric.ball_eq_empty.mpr r0, image_empty, subset_empty_iff, Metric.ball_eq_empty]
    simp only [mul_div_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg r0 (by bound)
  replace r0 : 0 < r := by linarith
  have cr : c ∈ ball c r := by simp only [Metric.mem_ball, dist_self, r0]
  have d0 : deriv f c ≠ 0 := inj.deriv_ne_zero isOpen_ball cr (fa c cr)
  have rd0 : r * deriv f c ≠ 0 := by simp [d0, r0.ne']
  set g : ℂ → ℂ := fun z ↦ (f (c + r * z) - f c) / (r * deriv f c)
  have ga : AnalyticOnNhd ℂ g (ball 0 1) := by
    intro z m
    refine AnalyticAt.div (((fa (c + r * z) ?_).comp_of_eq (by fun_prop) (by rfl)).sub
      analyticAt_const) analyticAt_const rd0
    simpa [abs_of_pos r0] using mul_lt_of_lt_one_right r0 m
  have ginj : InjOn g (ball 0 1) := by
    intro z zm w wm e
    simp only [Metric.mem_ball, dist_zero_right] at zm wm
    have zm' : c + r * z ∈ ball c r := by simpa [abs_of_pos r0] using mul_lt_of_lt_one_right r0 zm
    have wm' : c + r * w ∈ ball c r := by simpa [abs_of_pos r0] using mul_lt_of_lt_one_right r0 wm
    simp only [g] at e
    field_simp [d0, r0.ne'] at e
    simp only [sub_left_inj] at e
    simpa [r0.ne'] using (inj.eq_iff zm' wm').mp e
  have g0 : g 0 = 0 := by simp [g]
  have dg0 : deriv g 0 = 1 := by
    simp only [deriv_div_const, deriv_sub_const_fun, div_eq_one_iff_eq rd0, g]
    rw [deriv_comp_mul_left (c := (r : ℂ)) (f := fun z ↦ f (c + z)), deriv_comp_const_add]
    simp only [mul_zero, add_zero, smul_eq_mul]
  have k := koebe_quarter_special ga ginj g0 dg0
  have ik := image_mono (f := fun z ↦ f c + r * deriv f c * z) k
  simp only [image_image, g, mul_div_cancel₀ _ rd0, add_sub_cancel, affine_image_ball rd0, mul_zero,
    add_zero, ← div_eq_inv_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r0] at ik
  rw [← image_image (g := f), affine_image_ball (by simp [r0.ne'])] at ik
  simp only [mul_zero, add_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r0, one_mul] at ik
  exact ik

/-- The Koebe quarter theorem, unit ball case -/
theorem koebe_quarter (fa : AnalyticOnNhd ℂ f (ball 0 1)) (inj : InjOn f (ball 0 1)) :
    ball (f 0) (‖deriv f 0‖ / 4) ⊆ f '' (ball 0 1) := by
  simpa only [one_mul] using koebe_quarter' fa inj
