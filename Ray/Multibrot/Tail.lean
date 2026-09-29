module
public import Ray.Multibrot.Shell
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Ray.Multibrot.CuspArea

/-!
## The tail of the Mandelbrot area series decays slower than any power

Write `ψ(w) = w + ∑ b_n w^{-n}` for the exterior map of the Mandelbrot set, so that its area is
`π (1 - ∑ n |b_n|^2)`.  We prove that the tail `T(N) = ∑_{n > N} n |b_n|^2` satisfies

  `T(2^k) ≥ 1 / (2 · 10^8 (2k + 1)^6)`

for all large `k`.  Since `T` is decreasing, `T(N) ≳ (log N)^{-6}`, which is not `O(N^{-a})` for any
`a > 0`: truncations of the area series converge slower than any power of the number of terms.

The proof combines three pieces:
1. `Ray.Multibrot.Shell`: the area of `{c ∉ M : potential c > 1/R}` is at most
   `π (R^2 - 1) + 2π N log R + π T(N)`.
2. `Ray.Multibrot.Cusp`: near the cusp `c = 1/4`, parameters `1/4 + s^2 + h` with `|h| ≤ s^3 / 10^4`
   escape, but only after `≍ 1/s` iterations, so their potential is near `1`.
3. Choosing `s = 1/(2k+1)`, `R = exp (4 / 4^k)`, `N = 2^k` makes the disk of such parameters (area
   `π s^6 / 10^8`) fit inside the shell, while the non-tail terms are `O(2^{-k})`.
-/

open MeasureTheory Metric Set Filter
open scoped Real Topology OnePoint RiemannSphere

noncomputable section

/-- The tail `T(N) = ∑_{n > N} n |b_n|^2` of the Mandelbrot area series -/
@[expose] public def areaTail (N : ℕ) : ℝ :=
  ∑' n, if N < n then (n : ℝ) * ‖bcoeff 2 n‖ ^ 2 else 0

namespace AreaTail

/-- The terms `n |b_n|^2` -/
def x (n : ℕ) : ℝ := n * ‖bcoeff 2 n‖ ^ 2

lemma x_nonneg (n : ℕ) : 0 ≤ x n := by unfold x; positivity

lemma hasSum_x : HasSum x ((π - volume.real (multibrot 2)) / π) := by
  have h := (hasSum_one (d := 2)).div_const π
  convert h using 1
  funext n; unfold x; field_simp

lemma summable_x : Summable x := hasSum_x.summable

lemma tsum_x_le : ∑' n, x n ≤ 1 := by
  rw [hasSum_x.tsum_eq, div_le_one Real.pi_pos]
  linarith [measureReal_nonneg (μ := volume) (s := multibrot 2)]

/-- The tail terms -/
def tailTerm (N n : ℕ) : ℝ := if N < n then x n else 0

lemma summable_tailTerm (N : ℕ) : Summable (tailTerm N) :=
  summable_x.of_nonneg_of_le (fun n ↦ by unfold tailTerm; split_ifs <;> simp [x_nonneg])
    (fun n ↦ by unfold tailTerm; split_ifs <;> simp [x_nonneg])

lemma areaTail_eq (N : ℕ) : areaTail N = ∑' n, tailTerm N n := by
  simp only [areaTail, tailTerm, x]

/-- `1 - R^{-2n} ≤ 2 n log R` -/
lemma one_sub_le {R : ℝ} (R1 : 1 ≤ R) (n : ℕ) : 1 - R⁻¹ ^ (2 * n) ≤ 2 * n * Real.log R := by
  have Rp : 0 < R := by linarith
  have e : R⁻¹ ^ (2 * n) = Real.exp (-(2 * n * Real.log R)) := by
    rw [show -(2 * n * Real.log R) = (2 * n : ℕ) * (-Real.log R) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_neg, Real.exp_log Rp]
  rw [e]
  linarith [Real.add_one_le_exp (-(2 * n * Real.log R))]

/-- The shell area is at most `π (R^2 - 1) + 2π N log R + π T(N)` -/
lemma shell_le {R : ℝ} (R1 : 1 ≤ R) (N : ℕ) :
    volume.real ((psi 2 '' norm_Ioi R)ᶜ \ multibrot 2) ≤
      π * (R ^ 2 - 1) + 2 * π * N * Real.log R + π * areaTail N := by
  have hs := hasSum_shell (d := 2) R1
  have L0 : 0 ≤ Real.log R := Real.log_nonneg R1
  have bound : ∀ n, π * n * ‖bcoeff 2 n‖ ^ 2 * (1 - R⁻¹ ^ (2 * n)) ≤
      π * (2 * N * Real.log R * x n + tailTerm N n) := by
    intro n
    have xn := x_nonneg n
    have t0 : 0 ≤ R⁻¹ ^ (2 * n) := by
      have : 0 < R := by linarith
      positivity
    have e : π * n * ‖bcoeff 2 n‖ ^ 2 * (1 - R⁻¹ ^ (2 * n)) = π * (x n * (1 - R⁻¹ ^ (2 * n))) := by
      unfold x; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    unfold tailTerm
    split_ifs with nN
    · have : x n * (1 - R⁻¹ ^ (2 * n)) ≤ x n := by nlinarith
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * N) L0) xn]
    · have n_le : (n : ℝ) ≤ N := by exact_mod_cast not_lt.mp nN
      have h1 := one_sub_le R1 n
      have a : x n * (1 - R⁻¹ ^ (2 * n)) ≤ x n * (2 * n * Real.log R) := mul_le_mul_of_nonneg_left h1 xn
      have b : 2 * (n : ℝ) * Real.log R ≤ 2 * N * Real.log R :=
        mul_le_mul_of_nonneg_right (by linarith) L0
      have c := mul_le_mul_of_nonneg_left b xn
      linarith [mul_comm (x n) (2 * N * Real.log R)]
  have hg : HasSum (fun n ↦ π * (2 * N * Real.log R * x n + tailTerm N n))
      (π * (2 * N * Real.log R * ∑' n, x n + ∑' n, tailTerm N n)) :=
    ((summable_x.hasSum.mul_left _).add (summable_tailTerm N).hasSum).mul_left π
  have le := hasSum_le bound hs hg
  have xs := tsum_x_le
  rw [← areaTail_eq] at le
  nlinarith [mul_le_mul_of_nonneg_left xs (by positivity : (0 : ℝ) ≤ 2 * π * N * Real.log R)]

/-- Cusp parameters fill a disk inside the shell -/
lemma disk_subset {s : ℝ} (s0 : 0 < s) (s4 : s ≤ 1 / 4) {m : ℕ} (ms : (m + 1 : ℕ) * s ≤ 1) :
    closedBall (((1 / 4 + s ^ 2 : ℝ) : ℂ)) (s ^ 3 / 10000) ⊆
      (psi 2 '' norm_Ioi (Real.exp (4 / 2 ^ m)))ᶜ \ multibrot 2 := by
  intro c cm
  set h := c - ((1 / 4 + s ^ 2 : ℝ) : ℂ)
  have hs : ‖h‖ ≤ s ^ 3 / 10000 := by simpa [h, dist_eq_norm] using cm
  have ce : c = Cusp.param s h := by simp [Cusp.param, h]
  have R1 : 1 ≤ Real.exp (4 / 2 ^ m) := Real.one_le_exp (by positivity)
  refine mem_shell R1 (by rw [ce]; exact Cusp.param_notMem s0 s4 hs) ?_
  rw [ce, ← Real.exp_neg]
  refine lt_of_lt_of_le ?_ (Cusp.exp_le_potential s0 s4 hs ms)
  rw [Real.exp_lt_exp]
  have : (0 : ℝ) < 2 ^ m := by positivity
  rw [neg_div, neg_lt_neg_iff, div_lt_div_iff_of_pos_right this]
  norm_num

/-- `exp x - 1 ≤ 2 x` for `0 ≤ x ≤ 1/2` -/
lemma exp_sub_one_le {x : ℝ} (x0 : 0 ≤ x) (x2 : x ≤ 1 / 2) : Real.exp x - 1 ≤ 2 * x := by
  rcases x0.eq_or_lt with e | x0
  · simp [← e]
  have h := Real.exp_bound_div_one_sub_of_interval' x0 (by linarith)
  have : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

/-- The main inequality at scale `k`: `T(2^k) ≥ 1 / (10^8 (2k+1)^6) - 24 / 2^k` -/
lemma tail_ge_sub (k : ℕ) (k2 : 2 ≤ k) :
    1 / (10 ^ 8 * (2 * k + 1 : ℝ) ^ 6) - 24 / 2 ^ k ≤ areaTail (2 ^ k) := by
  set s : ℝ := 1 / (2 * k + 1)
  have kp : (0 : ℝ) < 2 * k + 1 := by positivity
  have s0 : 0 < s := by positivity
  have s4 : s ≤ 1 / 4 := by
    rw [div_le_div_iff₀ kp (by norm_num)]
    have : (2 : ℝ) ≤ k := by exact_mod_cast k2
    linarith
  have ms : ((2 * k + 1 : ℕ) : ℝ) * s ≤ 1 := by simp [s, field]
  set R := Real.exp (4 / 2 ^ (2 * k))
  have R1 : 1 ≤ R := Real.one_le_exp (by positivity)
  -- The disk has area π (s^3 / 10^4)^2 and lies in the shell
  have sub := disk_subset s0 s4 (m := 2 * k) (by simpa using ms)
  have vd : volume.real (closedBall (((1 / 4 + s ^ 2 : ℝ) : ℂ)) (s ^ 3 / 10000)) =
      (s ^ 3 / 10000) ^ 2 * π := by
    simp only [Measure.real, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ s ^ 3 / 10000), ENNReal.coe_toReal, NNReal.coe_real_pi]
  have fin : volume ((psi 2 '' norm_Ioi R)ᶜ \ multibrot 2) ≠ ⊤ :=
    measure_ne_top_of_subset sdiff_subset (volume_compl_psi_ne_top R1)
  have mono := measureReal_mono sub fin
  have sh := shell_le R1 (2 ^ k)
  rw [vd] at mono
  -- Bound the non-tail terms by 24 π / 2^k
  have p2 : (0 : ℝ) < 2 ^ k := by positivity
  have e4 : (2 : ℝ) ^ (2 * k) = 2 ^ k * 2 ^ k := by rw [two_mul, pow_add]
  have logR : Real.log R = 4 / 2 ^ (2 * k) := Real.log_exp _
  have t1 : R ^ 2 - 1 ≤ 16 / 2 ^ k := by
    have x2 : 8 / (2 : ℝ) ^ (2 * k) ≤ 1 / 2 := by
      rw [e4, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (4 : ℝ) ≤ 2 ^ k := by
        calc (4 : ℝ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) k2
      nlinarith
    have : R ^ 2 = Real.exp (8 / 2 ^ (2 * k)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    refine (exp_sub_one_le (by positivity) x2).trans ?_
    rw [e4]
    calc (2 : ℝ) * (8 / (2 ^ k * 2 ^ k)) = 16 / 2 ^ k / 2 ^ k := by field_simp; ring
      _ ≤ 16 / 2 ^ k := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
  have t2 : 2 * π * ((2 ^ k : ℕ) : ℝ) * Real.log R = π * (8 / 2 ^ k) := by
    rw [logR, e4]; push_cast; field_simp; ring
  have h1 : (s ^ 3 / 10000) ^ 2 * π ≤ (16 / 2 ^ k + 8 / 2 ^ k + areaTail (2 ^ k)) * π :=
    calc (s ^ 3 / 10000) ^ 2 * π
      _ ≤ volume.real ((psi 2 '' norm_Ioi R)ᶜ \ multibrot 2) := mono
      _ ≤ π * (R ^ 2 - 1) + 2 * π * ((2 ^ k : ℕ) : ℝ) * Real.log R + π * areaTail (2 ^ k) := sh
      _ = π * (R ^ 2 - 1) + π * (8 / 2 ^ k) + π * areaTail (2 ^ k) := by rw [t2]
      _ ≤ π * (16 / 2 ^ k) + π * (8 / 2 ^ k) + π * areaTail (2 ^ k) := by gcongr
      _ = (16 / 2 ^ k + 8 / 2 ^ k + areaTail (2 ^ k)) * π := by ring
  have h2 := le_of_mul_le_mul_right h1 Real.pi_pos
  have e : (s ^ 3 / 10000) ^ 2 = 1 / (10 ^ 8 * (2 * k + 1 : ℝ) ^ 6) := by
    simp only [s]; field_simp; ring
  rw [e] at h2
  have : (16 : ℝ) / 2 ^ k + 8 / 2 ^ k = 24 / 2 ^ k := by ring
  linarith

end AreaTail

open AreaTail in
/-- **The tail of the Mandelbrot area series decays slower than any power.**  For large `k`,
    `∑_{n > 2^k} n |b_n|^2 ≥ 1 / (2 · 10^8 (2k + 1)^6)`, where `ψ(w) = w + ∑ b_n w^{-n}` is the exterior
    map of the Mandelbrot set. -/
public theorem areaTail_pow_two_ge :
    ∀ᶠ k : ℕ in atTop, 1 / (2 * 10 ^ 8 * (2 * k + 1 : ℝ) ^ 6) ≤ areaTail (2 ^ k) := by
  -- 24 / 2^k is eventually below half the main term, since k^6 / 2^k → 0
  have lim := tendsto_pow_const_div_const_pow_of_one_lt 6 (by norm_num : (1 : ℝ) < 2)
  have ev := lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / (48 * 10 ^ 8 * 3 ^ 6)))
  filter_upwards [ev, eventually_ge_atTop 2] with k small k2
  have t := tail_ge_sub k k2
  have kp : (0 : ℝ) < 2 * k + 1 := by positivity
  have p2 : (0 : ℝ) < 2 ^ k := by positivity
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  -- (2k+1)^6 ≤ 3^6 k^6, so 24/2^k ≤ 1/(2·10^8 (2k+1)^6)
  have b1 : (2 * k + 1 : ℝ) ^ 6 ≤ 3 ^ 6 * (k : ℝ) ^ 6 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ kp.le (by linarith) 6
  have b2 : 24 / 2 ^ k ≤ 1 / (2 * 10 ^ 8 * (2 * k + 1 : ℝ) ^ 6) := by
    rw [div_lt_iff₀ p2] at small
    rw [div_le_div_iff₀ p2 (by positivity)]
    nlinarith
  have e : 1 / (10 ^ 8 * (2 * k + 1 : ℝ) ^ 6) = 2 * (1 / (2 * 10 ^ 8 * (2 * k + 1 : ℝ) ^ 6)) := by
    field_simp
  linarith

/-- The Mandelbrot area in terms of the coefficients `bcoeff 2 n` of `ψ(w) = w + ∑ b_n w^{-n}` -/
public theorem multibrot_volume_eq :
    volume.real (multibrot 2) = π * (1 - ∑' n : ℕ, (n : ℝ) * ‖bcoeff 2 n‖ ^ 2) := by
  have h := AreaTail.hasSum_x.tsum_eq
  simp only [AreaTail.x] at h
  rw [h]; field_simp; ring

open AreaTail in
/-- The tail decays slower than any power of the number of terms: for every `a > 0`, eventually
    `∑_{n > 2^k} n |b_n|^2 > (2^k)^{-a}` -/
public theorem areaTail_pow_two_gt_rpow {a : ℝ} (a0 : 0 < a) :
    ∀ᶠ k : ℕ in atTop, ((2 : ℝ) ^ k) ^ (-a) < areaTail (2 ^ k) := by
  set r : ℝ := (2 : ℝ) ^ (-a)
  have r0 : 0 < r := by positivity
  have r1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have lim := tendsto_pow_const_mul_const_pow_of_abs_lt_one 6 (by rw [abs_of_pos r0]; exact r1)
  have ev := lim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / (2 * 10 ^ 8 * 3 ^ 6)))
  filter_upwards [ev, areaTail_pow_two_ge, eventually_ge_atTop 1] with k small main k1
  have e : ((2 : ℝ) ^ k) ^ (-a) = r ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  rw [e]
  refine lt_of_lt_of_le ?_ main
  have kp : (0 : ℝ) < 2 * k + 1 := by positivity
  have k1' : (1 : ℝ) ≤ k := by exact_mod_cast k1
  have b1 : (2 * k + 1 : ℝ) ^ 6 ≤ 3 ^ 6 * (k : ℝ) ^ 6 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ kp.le (by linarith) 6
  rw [lt_div_iff₀ (by positivity)]
  have rk : 0 < r ^ k := by positivity
  nlinarith
