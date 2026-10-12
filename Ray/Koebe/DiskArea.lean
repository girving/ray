module
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Order.MonotoneConvergence
import Ray.Analytic.Analytic
import Ray.Analytic.Holomorphic
import Ray.Misc.Bound
import Ray.Misc.Circle
import Ray.Misc.Complex

/-!
## The area of a conformal image of the disk

Let `f` be analytic and injective on the open unit disk, with power series `f z = ∑ a n * z ^ n`.
Then the area of the image of the disk of radius `r < 1` is

  `volume (f '' ball 0 r) = ∑ n, π * n * ‖a n‖ ^ 2 * r ^ (2 * n)`

and letting `r → 1` by monotone convergence, the area of the image of the whole disk is

  `volume (f '' ball 0 1) = ∑ n, π * n * ‖a n‖ ^ 2`

in `ℝ≥0∞`, where both sides may be infinite (e.g., for the Koebe function).

The proof is the change of variables formula with Jacobian `‖f'‖ ^ 2`, polar coordinates, and
orthogonality of `exp (n * t * I)` on circles (Parseval for `f'` on each circle `‖z‖ = s`).

This is the interior counterpart of Grönwall's exterior area theorem (`Ray.Koebe.Gronwall`). Its
main use is computing areas of hyperbolic components of the Mandelbrot set: if `W` is a hyperbolic
component with multiplier map `λ_W : W → 𝔻`, then `λ_W⁻¹ = ∑ b n * λ ^ n` is a conformal
map from the disk onto `W`, so `area W = π * ∑ n, n * ‖b n‖ ^ 2`. We state the results with
coefficients `iteratedDeriv n f 0 / n.factorial` (as in `Ray.Multibrot.Area`) and with
`HasFPowerSeriesOnBall` coefficients `p.coeff n`.
-/

open Complex (exp I)
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open Metric (ball closedBall)
open Set
open scoped ComplexConjugate ENNReal NNReal Real Topology
noncomputable section

namespace DiskArea

variable {f g : ℂ → ℂ} {r s : ℝ} {z : ℂ}

/-!
### Power series preliminaries
-/

/-- Taylor coefficients at the origin -/
def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

lemma eball_one : Metric.eball (0 : ℂ) 1 = ball 0 1 := by
  simpa using Metric.eball_ofReal (x := (0 : ℂ)) (ε := 1)

/-- An analytic function on the unit disk has a power series on the whole disk -/
lemma exists_series (fa : AnalyticOnNhd ℂ f (ball 0 1)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall f p 0 1 ∧
      ∀ n, p.coeff n = coeff f n := by
  obtain ⟨p, fp⟩ := (analyticOnNhd_ball_iff_hasFPowerSeriesOnBall (c := 0) (r := 1)
    (by norm_num)).mp (by rw [eball_one]; exact fa)
  exact ⟨p, fp, fun n ↦ fp.hasFPowerSeriesAt.coeff_eq_iteratedDeriv_div n⟩

/-- Taylor series on the unit disk -/
lemma hasSum_coeff (fa : AnalyticOnNhd ℂ f (ball 0 1)) (z1 : ‖z‖ < 1) :
    HasSum (fun n ↦ coeff f n * z ^ n) (f z) := by
  obtain ⟨p, fp, pc⟩ := exists_series fa
  have h := fp.hasSum (y := z) (by rw [eball_one]; simpa using z1)
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff, pc, smul_eq_mul,
    mul_comm (z ^ _)] using h

/-- Taylor coefficients decay geometrically -/
lemma summable_coeff (fa : AnalyticOnNhd ℂ f (ball 0 1)) (s0 : 0 ≤ s) (s1 : s < 1) :
    Summable (fun n ↦ ‖coeff f n‖ * s ^ n) := by
  obtain ⟨p, fp, pc⟩ := exists_series fa
  have h := p.summable_norm_mul_pow (r := s.toNNReal) ?_
  · simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef, pc, Real.coe_toNNReal _ s0]
      using h
  · refine lt_of_lt_of_le ?_ fp.r_le
    rw [ENNReal.coe_lt_one_iff, Real.toNNReal_lt_one]
    exact s1

/-- Taylor coefficients of the derivative -/
lemma coeff_deriv (n : ℕ) : coeff (deriv f) n = ((n + 1 : ℕ) : ℂ) * coeff f (n + 1) := by
  simp only [coeff, iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

/-!
### Area as an integral of `‖f'‖ ^ 2`
-/

/-- Change of variables: the area of `f '' ball 0 r` is the integral of `‖f'‖ ^ 2` -/
lemma volume_real_image_eq (fa : AnalyticOnNhd ℂ f (ball 0 1)) (inj : InjOn f (ball 0 1))
    (r1 : r ≤ 1) : volume.real (f '' ball 0 r) = ∫ z in ball 0 r, ‖deriv f z‖ ^ 2 := by
  have sub : ball (0 : ℂ) r ⊆ ball 0 1 := Metric.ball_subset_ball r1
  have ie : ∫ z in f '' ball 0 r, (1 : ℝ) = volume.real (f '' ball 0 r) • 1 :=
    MeasureTheory.setIntegral_const _
  simp only [smul_eq_mul, mul_one] at ie
  rw [← ie]
  have gd : ∀ z ∈ ball (0 : ℂ) r, HasFDerivWithinAt f (fderiv ℝ f z) (ball 0 r) z :=
    fun z m ↦ (fa z (sub m)).restrictScalars.hasStrictFDerivAt.hasFDerivAt.hasFDerivWithinAt
  have ed : ∀ z ∈ ball (0 : ℂ) r, |(fderiv ℝ f z).det| = ‖deriv f z‖ ^ 2 :=
    fun z m ↦ by simp only [Complex.fderiv_det (fa z (sub m)).differentiableAt, abs_sq]
  rw [MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul volume
    Metric.isOpen_ball.measurableSet gd (inj.mono sub)]
  simp only [smul_eq_mul, mul_one]
  exact MeasureTheory.setIntegral_congr_fun Metric.isOpen_ball.measurableSet ed

/-- `polarCoord.symm` in terms of `circleMap` -/
lemma polarCoord_symm_eq (p : ℝ × ℝ) : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  simp [circleMap_zero, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- Integrals over disks in polar coordinates -/
lemma integral_ball_eq (F : ℂ → ℝ) (Fc : ContinuousOn F (closedBall 0 r)) (r0 : 0 ≤ r) :
    ∫ z in ball 0 r, F z = ∫ s in 0..r, s * ∫ t in -π..π, F (circleMap 0 s t) := by
  have S : MeasurableSet (Iio r ×ˢ (univ : Set ℝ)) := measurableSet_Iio.prod MeasurableSet.univ
  rw [← MeasureTheory.integral_indicator Metric.isOpen_ball.measurableSet,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have ie : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
      p.1 • (ball (0 : ℂ) r).indicator F (Complex.polarCoord.symm p) =
        (Iio r ×ˢ univ).indicator (fun p : ℝ × ℝ ↦ p.1 * F (circleMap 0 p.1 p.2)) p := by
    intro p m
    simp only [mem_prod, mem_Ioi] at m
    simp only [polarCoord_symm_eq, indicator, Metric.mem_ball, dist_zero_right,
      norm_circleMap_zero, abs_of_pos m.1, mem_prod, mem_Iio, mem_univ, and_true, smul_eq_mul]
    split_ifs <;> simp
  rw [MeasureTheory.setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) ie,
    MeasureTheory.setIntegral_indicator S]
  have te : Ioi (0 : ℝ) ×ˢ Ioo (-π) π ∩ Iio r ×ˢ univ = Ioo 0 r ×ˢ Ioo (-π) π := by
    ext ⟨a, b⟩
    simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_Iio, mem_univ, and_true]
    tauto
  rw [te, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.setIntegral_prod]
  · rw [intervalIntegral.integral_of_le r0, MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun s _ ↦ ?_)
    simp only
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      MeasureTheory.integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_const_mul]
  · have c : ContinuousOn (fun p : ℝ × ℝ ↦ p.1 * F (circleMap 0 p.1 p.2))
        (Icc 0 r ×ˢ Icc (-π) π) := by
      refine continuousOn_fst.mul (Fc.comp ?_ ?_)
      · simp only [circleMap_zero]
        exact Continuous.continuousOn (by fun_prop)
      · intro p m
        simp only [mem_prod, mem_Icc] at m
        simp [norm_circleMap_zero, abs_of_nonneg m.1.1, m.1.2]
    exact (c.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

/-!
### Parseval on circles
-/

/-- Terms of the double series for `‖g‖ ^ 2` on a circle -/
def term (g : ℂ → ℂ) (s t : ℝ) (p : ℕ × ℕ) : ℂ :=
  coeff g p.1 * conj (coeff g p.2) * s ^ (p.1 + p.2) * exp (((p.1 - p.2 : ℤ) : ℂ) * t * I)

lemma norm_exp_int_mul_I (k : ℤ) (t : ℝ) : ‖exp ((k : ℂ) * t * I)‖ = 1 := by
  rw [show (k : ℂ) * t = ((k * t : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Parseval for an analytic function on a circle -/
lemma hasSum_circle (ga : AnalyticOnNhd ℂ g (ball 0 1)) (s0 : 0 ≤ s) (s1 : s < 1) :
    HasSum (fun n ↦ 2 * π * ‖coeff g n‖ ^ 2 * s ^ (2 * n))
      (∫ t in -π..π, ‖g (circleMap 0 s t)‖ ^ 2) := by
  set c := coeff g
  have sc := summable_coeff ga s0 s1
  have zs : ∀ t, ‖circleMap 0 s t‖ < 1 := by simp [norm_circleMap_zero, abs_of_nonneg s0, s1]
  -- Pointwise double series
  have h : ∀ t, HasSum (term g s t) (g (circleMap 0 s t) * conj (g (circleMap 0 s t))) := by
    intro t
    have hz := hasSum_coeff ga (zs t)
    have hz' := Complex.hasSum_conj'.mpr hz
    have nz : ∀ n, ‖c n * circleMap 0 s t ^ n‖ = ‖c n‖ * s ^ n := by
      simp [norm_circleMap_zero, abs_of_nonneg s0]
    have sm := summable_mul_of_summable_norm (f := fun n ↦ c n * circleMap 0 s t ^ n)
      (g := fun n ↦ conj (c n * circleMap 0 s t ^ n)) (by simpa only [nz] using sc)
      (by simpa only [Complex.norm_conj, nz] using sc)
    refine (hz.mul hz' sm).congr_fun ?_
    intro ⟨n, m⟩
    have u0 : exp (t * I) ≠ 0 := Complex.exp_ne_zero _
    have cu : conj (exp (t * I)) = (exp (t * I))⁻¹ := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
        Complex.exp_neg]
    have eu : exp (((n - m : ℤ) : ℂ) * t * I) = exp (t * I) ^ n * (exp (t * I) ^ m)⁻¹ := by
      rw [mul_assoc, Complex.exp_int_mul, zpow_sub₀ u0, zpow_natCast, zpow_natCast,
        div_eq_mul_inv]
    simp only [term, eu, circleMap_zero, map_mul, map_pow, Complex.conj_ofReal, cu]
    ring
  -- Integrate term by term
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -π)
    (b := π) (F := fun p t ↦ term g s t p)
    (f := fun t ↦ g (circleMap 0 s t) * conj (g (circleMap 0 s t)))
    (fun p _ ↦ (‖c p.1‖ * s ^ p.1) * (‖c p.2‖ * s ^ p.2)) ?_ ?_ ?_ ?_ ?_
  rotate_left
  · intro p
    exact (by unfold term; fun_prop : Continuous fun t ↦ term g s t p).aestronglyMeasurable
  · intro p
    refine Filter.Eventually.of_forall fun t _ ↦ le_of_eq ?_
    simp only [term, norm_mul, Complex.norm_conj, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg s0, norm_exp_int_mul_I, mul_one, pow_add]
    ring
  · exact Filter.Eventually.of_forall fun t _ ↦
      Summable.mul_of_nonneg sc sc (fun n ↦ by positivity) (fun n ↦ by positivity)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun t _ ↦ h t
  -- Only the diagonal survives
  have ti : ∀ p : ℕ × ℕ, ∫ t in -π..π, term g s t p =
      if p.1 = p.2 then ((2 * π * ‖c p.1‖ ^ 2 * s ^ (2 * p.1) : ℝ) : ℂ) else 0 := by
    intro ⟨n, m⟩
    simp only [term, intervalIntegral.integral_const_mul, integral_exp_mul_I, sub_eq_zero,
      Nat.cast_inj]
    by_cases nm : n = m
    · subst nm
      simp only [↓reduceIte, Complex.mul_conj']
      push_cast
      ring
    · simp [nm]
  have re : (∫ t in -π..π, g (circleMap 0 s t) * conj (g (circleMap 0 s t))) =
      ((∫ t in -π..π, ‖g (circleMap 0 s t)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.mul_conj', ← Complex.ofReal_pow, intervalIntegral.integral_ofReal]
  simp only [ti, re] at hi
  rw [← Complex.hasSum_ofReal]
  have hd := (Function.Injective.hasSum_iff (g := fun n : ℕ ↦ (n, n))
    (fun a b e ↦ by simpa using e) ?_).mpr hi
  · simp only [Function.comp_def, ↓reduceIte] at hd
    exact hd
  intro ⟨n, m⟩ nm
  simp only [mem_range, Prod.mk.injEq, not_exists, not_and] at nm
  simp only [ite_eq_right_iff]
  intro e
  exact absurd e (nm n rfl)

/-!
### Integrating over radii
-/

/-- The integral of `‖g‖ ^ 2` over a disk, in polar coordinates -/
lemma hasSum_disk (ga : AnalyticOnNhd ℂ g (ball 0 1)) (r0 : 0 ≤ r) (r1 : r < 1) :
    HasSum (fun n ↦ π * ‖coeff g n‖ ^ 2 * r ^ (2 * n + 2) / (n + 1))
      (∫ s in 0..r, s * ∫ t in -π..π, ‖g (circleMap 0 s t)‖ ^ 2) := by
  set c := coeff g
  have hr := (hasSum_circle ga r0 r1).summable
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := r) (F := fun n s ↦ s * (2 * π * ‖c n‖ ^ 2 * s ^ (2 * n)))
    (f := fun s ↦ s * ∫ t in -π..π, ‖g (circleMap 0 s t)‖ ^ 2)
    (fun n _ ↦ r * (2 * π * ‖c n‖ ^ 2 * r ^ (2 * n))) ?_ ?_ ?_ ?_ ?_
  rotate_left
  · intro n
    exact (by fun_prop : Continuous fun s : ℝ ↦ s * (2 * π * ‖c n‖ ^ 2 * s ^ (2 * n)))
      |>.aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun s m ↦ ?_
    simp only [uIoc_of_le r0, mem_Ioc] at m
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := m.1.le; positivity)]
    have := m.1.le
    have := m.2
    gcongr
  · exact Filter.Eventually.of_forall fun s _ ↦ hr.mul_left r
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun s m ↦ ?_
    simp only [uIoc_of_le r0, mem_Ioc] at m
    exact (hasSum_circle ga m.1.le (by linarith)).mul_left s
  convert hi using 1
  funext n
  have e : ∀ s : ℝ, s * (2 * π * ‖c n‖ ^ 2 * s ^ (2 * n)) =
      (2 * π * ‖c n‖ ^ 2) * s ^ (2 * n + 1) := fun s ↦ by ring
  simp only [e, intervalIntegral.integral_const_mul, integral_pow]
  simp only [ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  push_cast
  field_simp
  ring

/-- Monotone convergence for `ℝ≥0∞` series -/
lemma iSup_tsum {u : ℕ → ℕ → ℝ≥0∞} (mono : ∀ n, Monotone (fun k ↦ u k n)) :
    ⨆ k, ∑' n, u k n = ∑' n, ⨆ k, u k n := by
  simp only [ENNReal.tsum_eq_iSup_sum]
  rw [iSup_comm]
  congr 1
  funext s
  exact (ENNReal.finsetSum_iSup_of_monotone mono).symm

/-- Sums of `ofReal` are finite iff the series is summable -/
lemma tsum_ofReal_ne_top_iff {a : ℕ → ℝ} (a0 : ∀ n, 0 ≤ a n) :
    ∑' n, ENNReal.ofReal (a n) ≠ ⊤ ↔ Summable a := by
  simp only [ENNReal.ofReal, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe,
    Real.coe_toNNReal _ (a0 _)]

end DiskArea

open DiskArea

/-!
### The area formula
-/

/-- The area of the image of a disk of radius `r < 1` under an injective analytic map -/
public theorem hasSum_volume_image_ball {f : ℂ → ℂ} {r : ℝ}
    (fa : AnalyticOnNhd ℂ f (ball 0 1)) (inj : InjOn f (ball 0 1)) (r0 : 0 ≤ r) (r1 : r < 1) :
    HasSum (fun n ↦ π * n * ‖iteratedDeriv n f 0 / n.factorial‖ ^ 2 * r ^ (2 * n))
      (volume.real (f '' ball 0 r)) := by
  have da := fa.deriv
  rw [volume_real_image_eq fa inj r1.le, integral_ball_eq _ ?_ r0]
  · have h := hasSum_disk da r0 r1
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, zero_mul,
      sub_zero]
    convert h using 1
    funext n
    simp only [coeff_deriv, norm_mul, Complex.norm_natCast]
    simp only [coeff]
    push_cast
    field_simp
    ring
  · exact (da.continuousOn.norm.pow 2).mono (Metric.closedBall_subset_ball r1)

/-- The area of the image of the unit disk under an injective analytic map, in `ℝ≥0∞` -/
public theorem volume_image_ball_one {f : ℂ → ℂ} (fa : AnalyticOnNhd ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) :
    volume (f '' ball 0 1) =
      ∑' n, ENNReal.ofReal (π * n * ‖iteratedDeriv n f 0 / n.factorial‖ ^ 2) := by
  set a : ℕ → ℝ := fun n ↦ π * n * ‖iteratedDeriv n f 0 / n.factorial‖ ^ 2
  have a0 : ∀ n, 0 ≤ a n := fun n ↦ by positivity
  set ρ : ℕ → ℝ := fun k ↦ 1 - 1 / (k + 1)
  have ρ0 : ∀ k, 0 ≤ ρ k := fun k ↦ by
    simp only [ρ, sub_nonneg]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]) (by positivity)
  have ρ1 : ∀ k, ρ k < 1 := fun k ↦ by
    simp only [ρ]
    linarith [(by positivity : 0 < 1 / ((k : ℝ) + 1))]
  have ρm : Monotone ρ := fun j k jk ↦ by
    simp only [ρ]
    gcongr
  have ρt : Tendsto ρ atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_sub (1 : ℝ)
  have U : ball (0 : ℂ) 1 = ⋃ k, ball 0 (ρ k) := by
    ext z
    simp only [mem_iUnion, mem_ball_zero_iff]
    constructor
    · intro z1
      exact (ρt.eventually (lt_mem_nhds z1)).exists
    · rintro ⟨k, zk⟩
      exact zk.trans (ρ1 k)
  have mono : Monotone (fun k ↦ f '' ball 0 (ρ k)) :=
    fun j k jk ↦ image_mono (Metric.ball_subset_ball (ρm jk))
  rw [U, image_iUnion, mono.measure_iUnion]
  have vk : ∀ k, volume (f '' ball 0 (ρ k)) = ∑' n, ENNReal.ofReal (a n * ρ k ^ (2 * n)) := by
    intro k
    have h := hasSum_volume_image_ball fa inj (ρ0 k) (ρ1 k)
    rw [← MeasureTheory.ofReal_measureReal ?_, ← h.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by have := ρ0 k; positivity) h.summable]
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_mono
      (image_mono Metric.ball_subset_closedBall))
    exact ((isCompact_closedBall 0 (ρ k)).image_of_continuousOn
      (fa.continuousOn.mono (Metric.closedBall_subset_ball (ρ1 k)))).measure_lt_top.ne
  simp only [vk]
  rw [iSup_tsum]
  · congr 1
    funext n
    refine iSup_eq_of_tendsto ?_ ?_
    · intro j k jk
      have := ρ0 j
      exact ENNReal.ofReal_le_ofReal (by gcongr; exact ρm jk)
    · simpa only [one_pow, mul_one] using
        ENNReal.tendsto_ofReal ((ρt.pow (2 * n)).const_mul (a n))
  · intro n j k jk
    have := ρ0 j
    exact ENNReal.ofReal_le_ofReal (by gcongr; exact ρm jk)

/-- The area of the image of the unit disk under an injective analytic map, finite version -/
public theorem hasSum_volume_image_ball_one {f : ℂ → ℂ} (fa : AnalyticOnNhd ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) (fin : volume (f '' ball 0 1) ≠ ⊤) :
    HasSum (fun n ↦ π * n * ‖iteratedDeriv n f 0 / n.factorial‖ ^ 2)
      (volume.real (f '' ball 0 1)) := by
  have a0 : ∀ n : ℕ, 0 ≤ π * n * ‖iteratedDeriv n f 0 / n.factorial‖ ^ 2 :=
    fun n ↦ by positivity
  rw [volume_image_ball_one fa inj] at fin
  have s := (tsum_ofReal_ne_top_iff a0).mp fin
  rw [MeasureTheory.measureReal_def, volume_image_ball_one fa inj,
    ← ENNReal.ofReal_tsum_of_nonneg a0 s, ENNReal.toReal_ofReal (tsum_nonneg a0)]
  exact s.hasSum

/-- The image of the unit disk has finite area iff the area series converges -/
public theorem volume_image_ball_one_ne_top_iff {f : ℂ → ℂ}
    (fa : AnalyticOnNhd ℂ f (ball 0 1)) (inj : InjOn f (ball 0 1)) :
    volume (f '' ball 0 1) ≠ ⊤ ↔
      Summable (fun n : ℕ ↦ π * n * ‖iteratedDeriv n f 0 / n.factorial‖ ^ 2) := by
  rw [volume_image_ball_one fa inj]
  exact tsum_ofReal_ne_top_iff (fun n ↦ by positivity)

/-!
### `HasFPowerSeriesOnBall` versions
-/

lemma HasFPowerSeriesOnBall.analyticOnNhd_ball_one {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (fp : HasFPowerSeriesOnBall f p 0 1) :
    AnalyticOnNhd ℂ f (ball 0 1) :=
  fun _ m ↦ fp.analyticAt_of_mem (by rwa [eball_one])

lemma HasFPowerSeriesOnBall.coeff_eq {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (fp : HasFPowerSeriesOnBall f p 0 1) (n : ℕ) :
    p.coeff n = iteratedDeriv n f 0 / n.factorial :=
  fp.hasFPowerSeriesAt.coeff_eq_iteratedDeriv_div n

/-- The area of the image of a disk of radius `r < 1` under an injective analytic map -/
public theorem HasFPowerSeriesOnBall.hasSum_volume_image_ball {f : ℂ → ℂ} {r : ℝ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (fp : HasFPowerSeriesOnBall f p 0 1)
    (inj : InjOn f (ball 0 1)) (r0 : 0 ≤ r) (r1 : r < 1) :
    HasSum (fun n ↦ π * n * ‖p.coeff n‖ ^ 2 * r ^ (2 * n))
      (volume.real (f '' ball 0 r)) := by
  simpa only [fp.coeff_eq] using _root_.hasSum_volume_image_ball fp.analyticOnNhd_ball_one inj r0 r1

/-- The area of the image of the unit disk under an injective analytic map, in `ℝ≥0∞` -/
public theorem HasFPowerSeriesOnBall.volume_image_ball_one {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (fp : HasFPowerSeriesOnBall f p 0 1)
    (inj : InjOn f (ball 0 1)) :
    volume (f '' ball 0 1) = ∑' n, ENNReal.ofReal (π * n * ‖p.coeff n‖ ^ 2) := by
  simpa only [fp.coeff_eq] using _root_.volume_image_ball_one fp.analyticOnNhd_ball_one inj

/-- The area of the image of the unit disk under an injective analytic map, finite version -/
public theorem HasFPowerSeriesOnBall.hasSum_volume_image_ball_one {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (fp : HasFPowerSeriesOnBall f p 0 1)
    (inj : InjOn f (ball 0 1)) (fin : volume (f '' ball 0 1) ≠ ⊤) :
    HasSum (fun n ↦ π * n * ‖p.coeff n‖ ^ 2) (volume.real (f '' ball 0 1)) := by
  simpa only [fp.coeff_eq] using
    _root_.hasSum_volume_image_ball_one fp.analyticOnNhd_ball_one inj fin

/-!
### Regions parameterised conformally by the disk

E.g., hyperbolic components `W` of the Mandelbrot set, with `φ` the inverse multiplier map.
-/

/-- The area of a region `W = φ '' ball 0 1` with `φ` conformal on the disk -/
public theorem volume_eq_of_conformal {φ : ℂ → ℂ} {W : Set ℂ}
    (fa : AnalyticOnNhd ℂ φ (ball 0 1)) (inj : InjOn φ (ball 0 1)) (e : φ '' ball 0 1 = W) :
    volume W = ∑' n, ENNReal.ofReal (π * n * ‖iteratedDeriv n φ 0 / n.factorial‖ ^ 2) :=
  e ▸ volume_image_ball_one fa inj

/-- The area of a region `W = φ '' ball 0 1` with `φ` conformal on the disk, finite version -/
public theorem hasSum_volume_of_conformal {φ : ℂ → ℂ} {W : Set ℂ}
    (fa : AnalyticOnNhd ℂ φ (ball 0 1)) (inj : InjOn φ (ball 0 1)) (e : φ '' ball 0 1 = W)
    (fin : volume W ≠ ⊤) :
    HasSum (fun n ↦ π * n * ‖iteratedDeriv n φ 0 / n.factorial‖ ^ 2) (volume.real W) :=
  e ▸ hasSum_volume_image_ball_one fa inj (e ▸ fin)

/-- The area of a region `W = φ '' ball 0 1` with `φ` conformal on the disk -/
public theorem HasFPowerSeriesOnBall.volume_eq_of_conformal {φ : ℂ → ℂ} {W : Set ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (fp : HasFPowerSeriesOnBall φ p 0 1)
    (inj : InjOn φ (ball 0 1)) (e : φ '' ball 0 1 = W) :
    volume W = ∑' n, ENNReal.ofReal (π * n * ‖p.coeff n‖ ^ 2) :=
  e ▸ fp.volume_image_ball_one inj

/-- The area of a region `W = φ '' ball 0 1` with `φ` conformal on the disk, finite version -/
public theorem HasFPowerSeriesOnBall.hasSum_volume_of_conformal {φ : ℂ → ℂ} {W : Set ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (fp : HasFPowerSeriesOnBall φ p 0 1)
    (inj : InjOn φ (ball 0 1)) (e : φ '' ball 0 1 = W) (fin : volume W ≠ ⊤) :
    HasSum (fun n ↦ π * n * ‖p.coeff n‖ ^ 2) (volume.real W) :=
  e ▸ fp.hasSum_volume_image_ball_one inj (e ▸ fin)

