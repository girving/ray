module
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Ray.Multibrot.Area
public import Ray.Multibrot.Basic
public import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Ray.Koebe.Gronwall

/-!
## The area near the Mandelbrot set with small Green's function

Write `ψ(w) = w * pray d w⁻¹ = w + ∑ b_n w^{-n}` for the exterior map of the Multibrot set.  Applying
Grönwall's area theorem to `ψ` restricted to `|w| > R` bounds the area of the shell
`{c ∉ M : potential c > 1/R}` by `π (R^2 - 1) + π ∑ n |b_n|^2 (1 - R^{-2n})`.  Splitting the series at
`N` then bounds the shell area by `π (R^2 - 1) + 2π N log R + π T(N)`, where `T(N) = ∑_{n > N} n |b_n|^2`
is the tail of the area series.
-/

open MeasureTheory
open RiemannSphere
open Metric (ball isOpen_ball mem_ball)
open Set
open scoped OnePoint Pointwise Real RiemannSphere Topology

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-- The coefficients of `ψ(w) = w * pray d w⁻¹ = w + ∑ b_n w^{-n}`, as they appear in Grönwall's theorem -/
@[expose] public def bcoeff (d : ℕ) [Fact (2 ≤ d)] (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1) (pray d) 0 / (n + 1).factorial

/-- `pray` rescaled by `R`, so that `z * prayR d R z⁻¹ = ψ(R z) / R` -/
def prayR (d : ℕ) [Fact (2 ≤ d)] (R : ℝ) (z : ℂ) : ℂ := pray d ((R : ℂ)⁻¹ * z)

lemma norm_inv_R_le {R : ℝ} (R1 : 1 ≤ R) : ‖((R : ℂ)⁻¹)‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  exact inv_le_one_of_one_le₀ R1

lemma mapsTo_mul_inv_R {R : ℝ} (R1 : 1 ≤ R) :
    MapsTo ((R : ℂ)⁻¹ * ·) (ball (0 : ℂ) 1) (ball 0 1) := by
  intro z hz
  simp only [mem_ball, dist_zero_right] at hz ⊢
  rw [norm_mul]
  calc ‖((R : ℂ)⁻¹)‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact norm_inv_R_le R1
    _ < 1 := by linarith

lemma prayR_analytic {R : ℝ} (R1 : 1 ≤ R) : AnalyticOnNhd ℂ (prayR d R) (ball 0 1) := by
  intro z m
  exact (pray_analyticOnNhd _ (mapsTo_mul_inv_R R1 m)).comp (analyticAt_const.mul analyticAt_id)

@[simp] lemma prayR_zero {R : ℝ} : prayR d R 0 = 1 := by simp [prayR]

/-- Rescaling multiplies the `n`th derivative by `R^{-n}` -/
lemma iteratedDeriv_prayR {R : ℝ} (R1 : 1 ≤ R) (n : ℕ) :
    iteratedDeriv n (prayR d R) 0 = ((R : ℂ)⁻¹) ^ n * iteratedDeriv n (pray d) 0 := by
  have o : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have m0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have cd : ContDiffOn ℂ n (pray d) (ball 0 1) := pray_analyticOnNhd.contDiffOn o.uniqueDiffOn
  have e := iteratedDerivWithin_comp_const_smul (hx := m0) (h := o.uniqueDiffOn) cd ((R : ℂ)⁻¹)
    (mapsTo_mul_inv_R R1)
  rw [iteratedDerivWithin_of_isOpen o m0, mul_zero, iteratedDerivWithin_of_isOpen o m0] at e
  change iteratedDeriv n (fun z ↦ pray d ((R : ℂ)⁻¹ * z)) 0 = _
  simpa [smul_eq_mul] using e

lemma bcoeff_prayR {R : ℝ} (R1 : 1 ≤ R) (n : ℕ) :
    iteratedDeriv (n + 1) (prayR d R) 0 / (n + 1).factorial = ((R : ℂ)⁻¹) ^ (n + 1) * bcoeff d n := by
  rw [iteratedDeriv_prayR R1, bcoeff, mul_div_assoc]

/-- The rescaled map is `ψ(R z) / R` -/
lemma prayR_eq {R : ℝ} (R1 : 1 ≤ R) (z : ℂ) :
    z * prayR d R z⁻¹ = (R : ℂ)⁻¹ * ((R * z) * pray d (R * z)⁻¹) := by
  have R0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  simp only [prayR, mul_inv]
  field_simp

lemma prayR_inj {R : ℝ} (R1 : 1 ≤ R) : InjOn (fun z ↦ z * prayR d R z⁻¹) (norm_Ioi 1) := by
  intro z zm w wm e
  have R0 : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  simp only [prayR_eq R1] at e
  have m : ∀ {z : ℂ}, z ∈ norm_Ioi 1 → (R : ℂ) * z ∈ norm_Ioi 1 := by
    intro z m
    simp only [norm_Ioi, mem_ofPred_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < R)] at m ⊢
    nlinarith
  have := pray_inj (d := d) (m zm) (m wm) (mul_left_cancel₀ (inv_ne_zero R0) e)
  exact mul_left_cancel₀ R0 this

/-- The exterior map `ψ(w) = w * pray d w⁻¹ = w + ∑ b_n w^{-n}` -/
@[expose] public def psi (d : ℕ) [Fact (2 ≤ d)] (w : ℂ) : ℂ := w * pray d w⁻¹

lemma mem_norm_Ioi' {z : ℂ} {r : ℝ} : z ∈ norm_Ioi r ↔ r < ‖z‖ := by simp [norm_Ioi]

/-- The rescaled image's complement is the rescaled complement of `ψ(|w| > R)` -/
lemma compl_image_prayR {R : ℝ} (R1 : 1 ≤ R) :
    ((fun z ↦ z * prayR d R z⁻¹) '' norm_Ioi 1)ᶜ = (R⁻¹ : ℝ) • (psi d '' norm_Ioi R)ᶜ := by
  have R0 : R ≠ 0 := by positivity
  have Rc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr R0
  have Rp : 0 < R := by linarith
  ext c
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero R0), inv_inv, mem_compl_iff, mem_compl_iff,
    not_iff_not, Complex.real_smul]
  constructor
  · rintro ⟨z, zm, rfl⟩
    refine ⟨R * z, ?_, ?_⟩
    · rw [mem_norm_Ioi'] at zm ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Rp]
      nlinarith
    · simp only [psi, prayR_eq R1]; field_simp
  · rintro ⟨w, wm, e⟩
    refine ⟨w / R, ?_, ?_⟩
    · rw [mem_norm_Ioi'] at wm ⊢
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Rp, one_lt_div Rp]
      exact wm
    · simp only [prayR_eq R1]
      have wR : (R : ℂ) * (w / R) = w := by field_simp
      rw [wR]
      simp only [psi] at e
      rw [e]; field_simp

lemma volume_real_smul {r : ℝ} (r0 : 0 ≤ r) (A : Set ℂ) :
    volume.real (r • A) = r ^ 2 * volume.real A := by
  simp only [Measure.real, Measure.addHaar_smul_of_nonneg _ r0, Complex.finrank_real_complex,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ r ^ 2)]

lemma volume_compl_psi_ne_top {R : ℝ} (R1 : 1 ≤ R) : volume (psi d '' norm_Ioi R)ᶜ ≠ ⊤ := by
  have fin := gronwall_volume_ne_top (prayR_analytic (d := d) R1) prayR_zero (prayR_inj R1)
  rw [compl_image_prayR R1, Measure.addHaar_smul_of_nonneg _ (by positivity)] at fin
  have R0 : (0 : ℝ) < R⁻¹ ^ Module.finrank ℝ ℂ := by
    have : 0 < R := by linarith
    positivity
  intro h
  rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr R0).ne'] at fin
  exact fin rfl

/-- Grönwall's theorem at radius `R`: `π R^2 - area (ψ(|w| > R))ᶜ = ∑ π n |b_n|^2 R^{-2n}` -/
lemma hasSum_R {R : ℝ} (R1 : 1 ≤ R) :
    HasSum (fun n ↦ π * n * ‖bcoeff d n‖ ^ 2 * (R⁻¹) ^ (2 * n))
      (π * R ^ 2 - volume.real (psi d '' norm_Ioi R)ᶜ) := by
  have g := gronwall_volume_sum (prayR_analytic (d := d) R1) prayR_zero (prayR_inj R1)
  simp only [bcoeff_prayR R1, compl_image_prayR R1, volume_real_smul (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ R))] at g
  have Rp : 0 < R := by linarith
  have e : ∀ n : ℕ, π * n * ‖((R : ℂ)⁻¹) ^ (n + 1) * bcoeff d n‖ ^ 2 =
      R⁻¹ ^ 2 * (π * n * ‖bcoeff d n‖ ^ 2 * (R⁻¹) ^ (2 * n)) := by
    intro n
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Rp]
    ring
  simp only [e] at g
  have g2 := g.mul_left (R ^ 2)
  convert g2 using 1
  · funext n; field_simp
  · field_simp

/-- The area series of the Mandelbrot set, in terms of `bcoeff` -/
lemma hasSum_one : HasSum (fun n ↦ π * n * ‖bcoeff d n‖ ^ 2) (π - volume.real (multibrot d)) := by
  simpa [bcoeff] using multibrot_volume_sum (d := d)

/-- The area of the shell `(ψ(|w| > R))ᶜ \ M` is `π (R^2 - 1) + ∑ π n |b_n|^2 (1 - R^{-2n})` -/
public theorem hasSum_shell {R : ℝ} (R1 : 1 ≤ R) :
    HasSum (fun n ↦ π * n * ‖bcoeff d n‖ ^ 2 * (1 - (R⁻¹) ^ (2 * n)))
      (volume.real ((psi d '' norm_Ioi R)ᶜ \ multibrot d) - π * (R ^ 2 - 1)) := by
  have sub : multibrot d ⊆ (psi d '' norm_Ioi R)ᶜ := by
    rw [← compl_compl (multibrot d), multibrot_eq_pray, compl_subset_compl]
    rintro _ ⟨w, wm, rfl⟩
    exact ⟨w, by rw [mem_norm_Ioi'] at wm ⊢; linarith, rfl⟩
  rw [measureReal_sdiff sub isCompact_multibrot.isClosed.measurableSet (volume_compl_psi_ne_top R1)]
  convert hasSum_one.sub (hasSum_R (d := d) R1) using 1
  · funext n; ring
  · ring

/-- `ψ(w)` has potential `1 / |w|` -/
lemma potential_psi {w : ℂ} (w1 : 1 < ‖w‖) : potential d (psi d w : 𝕊) = ‖w‖⁻¹ := by
  have m : w ∈ norm_Ioi 1 := mem_norm_Ioi'.mpr w1
  have m' : w⁻¹ ∈ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_zero_right, norm_inv]; exact inv_lt_one_of_one_lt₀ w1
  rw [psi, ← ray_inv_eq_pray m, ← norm_bottcher, bottcher_ray m', norm_inv]

/-- Points outside `M` with potential above `1/R` lie in the shell -/
public lemma mem_shell {R : ℝ} (R1 : 1 ≤ R) {c : ℂ} (m : c ∉ multibrot d) (p : R⁻¹ < potential d c) :
    c ∈ (psi d '' norm_Ioi R)ᶜ \ multibrot d := by
  refine ⟨?_, m⟩
  rintro ⟨w, wm, rfl⟩
  rw [mem_norm_Ioi'] at wm
  rw [potential_psi (by linarith)] at p
  have : ‖w‖⁻¹ < R⁻¹ := inv_strictAnti₀ (by linarith) wm
  linarith

end
