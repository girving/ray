import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Order.BoundedOrder
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence
import Ray.Analytic.Analytic
import Ray.Misc.Bounds
import Ray.Misc.Topology
import Ray.Tactic.Bound

/-!
## Convergent sequences of analytic functions

We show that uniformly convergence sequences of analytic functions have analytic limits.
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Complex (abs I)
open Filter (atTop)
open MeasureTheory.MeasureSpace (volume)
open Metric (ball closedBall sphere)
open scoped Real NNReal Topology
noncomputable section

theorem cauchy_on_cball_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOn ℂ f (closedBall z r)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f z r) z r := by
  have hd : DifferentiableOn ℂ f (closedBall z r) := by
    intro x H; exact AnalyticAt.differentiableWithinAt (h x H)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := cauchyPowerSeries f z r
  exact DifferentiableOn.hasFPowerSeriesOnBall hd rp

theorem analyticOn_cball_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOn ℂ f (closedBall z r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall f p z r :=
  ⟨cauchyPowerSeries f z r, cauchy_on_cball_radius rp h⟩

theorem analyticOn_small_cball {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (h : AnalyticOn ℂ f (ball z r))
    (s : ℝ≥0) (sr : s < r) : AnalyticOn ℂ f (closedBall z s) := by
  intro x hx
  rw [closedBall] at hx; simp at hx
  have hb : x ∈ ball z r := by
    rw [ball]; simp only [dist_lt_coe, Set.mem_setOf_eq]; exact lt_of_le_of_lt hx sr
  exact h x hb

theorem analyticOn_ball_radius {f : ℂ → ℂ} {z : ℂ} {r : ℝ≥0} (rp : r > 0)
    (h : AnalyticOn ℂ f (ball z r)) :
    ∃ p : FormalMultilinearSeries ℂ ℂ ℂ, HasFPowerSeriesOnBall f p z r := by
  have h0 := analyticOn_small_cball h (r / 2) (NNReal.half_lt_self <| rp.ne')
  rcases analyticOn_cball_radius (half_pos rp) h0 with ⟨p, ph⟩
  set R := FormalMultilinearSeries.radius p
  refine'
    ⟨p, {
        r_le := _
        r_pos := ENNReal.coe_pos.mpr rp
        hasSum := _ }⟩
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro t tp tr
    have ht := analyticOn_small_cball h t (ENNReal.coe_lt_coe.mp tr)
    rcases analyticOn_cball_radius tp ht with ⟨p', hp'⟩
    have pp : p = p' := HasFPowerSeriesAt.eq_formalMultilinearSeries ⟨↑(r / 2), ph⟩ ⟨t, hp'⟩
    rw [← pp] at hp'
    refine' hp'.r_le
  · intro y yr
    rw [EMetric.ball, Set.mem_setOf] at yr
    rcases exists_between yr with ⟨t, t0, t1⟩
    have t1' : t.toNNReal < r := by
      rw [← WithTop.coe_lt_coe]; exact lt_of_le_of_lt ENNReal.coe_toNNReal_le_self t1
    have ht := analyticOn_small_cball h t.toNNReal t1'
    have tp : 0 < ENNReal.toNNReal t :=
      ENNReal.toNNReal_pos (ne_of_gt <| pos_of_gt t0) (ne_top_of_lt t1)
    rcases analyticOn_cball_radius tp ht with ⟨p', hp'⟩
    have pp : p = p' :=
      HasFPowerSeriesAt.eq_formalMultilinearSeries ⟨↑(r / 2), ph⟩ ⟨t.toNNReal, hp'⟩
    rw [← pp] at hp'
    refine' hp'.hasSum _
    rw [EMetric.ball, Set.mem_setOf]
    calc edist y 0
      _ < t := t0
      _ = ↑t.toNNReal := (ENNReal.coe_toNNReal <| ne_top_of_lt t1).symm

theorem cauchy_bound {f : ℂ → ℂ} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} {w : ℂ} {n : ℕ} (rp : r > 0)
    (h : ∀ w ∈ closedBall c r, abs (f w) ≤ d) :
    abs (cauchyPowerSeries f c r n fun _ ↦ w) ≤ abs w ^ n * r⁻¹ ^ n * d := by
  set wr := abs w ^ n * r⁻¹ ^ n * d
  rw [cauchyPowerSeries_apply f c r n w, smul_eq_mul, Complex.abs.map_mul]
  generalize hg : (fun z ↦ (w / (z - c)) ^ n • (z - c)⁻¹ • f z) = g
  have gs : ∀ z ∈ sphere c r, ‖g z‖ ≤ wr * r⁻¹ := by
    intro z; simp only [mem_sphere_iff_norm, Complex.norm_eq_abs]; intro zr
    simp only [← hg, zr, div_pow, Algebra.id.smul_eq_mul, AbsoluteValue.map_mul, map_div₀,
      Complex.abs_pow, map_inv₀]
    have zb : z ∈ closedBall c r := by
      simp only [Metric.mem_closedBall, dist_le_coe, ← NNReal.coe_le_coe, coe_nndist,
        Complex.dist_eq, zr, le_refl]
    have zs := h z zb
    calc abs w ^ n / ↑r ^ n * (r⁻¹ * abs (f z))
      _ = abs w ^ n * r⁻¹ ^ n * (r⁻¹ * abs (f z)) := by
        rw [div_eq_mul_inv, ← inv_pow, NNReal.coe_pow, NNReal.coe_inv]
      _ ≤ abs w ^ n * r⁻¹ ^ n * (r⁻¹ * d) := by bound
      _ = abs w ^ n * r⁻¹ ^ n * d * r⁻¹ := by ring
      _ = wr * r⁻¹ := rfl
  have cn := circleIntegral.norm_integral_le_of_norm_le_const (NNReal.coe_nonneg r) gs
  rw [Complex.norm_eq_abs] at cn
  simp only [mul_inv_rev, Complex.inv_I, AbsoluteValue.map_neg, AbsoluteValue.map_mul,
    Complex.abs_I, map_inv₀, Complex.abs_ofReal, Complex.abs_two, one_mul, div_pow,
    Algebra.id.smul_eq_mul] at hg cn ⊢
  have p3 : |π| = π := abs_eq_self.mpr (by bound)
  calc |π|⁻¹ * 2⁻¹ * abs (circleIntegral g c ↑r)
    _ ≤ |π|⁻¹ * 2⁻¹ * (2 * π * r * (wr * r⁻¹)) := by bound
    _ = π * |π|⁻¹ * (r * r⁻¹) * wr := by ring
    _ = π * π⁻¹ * (r * r⁻¹) * wr := by rw [p3]
    _ = 1 * (r * r⁻¹) * wr := by rw [mul_inv_cancel Real.pi_ne_zero]
    _ = wr := by
      rw [NNReal.coe_inv, mul_inv_cancel (NNReal.coe_ne_zero.mpr rp.ne'), one_mul, one_mul]

theorem circleIntegral_sub {f g : ℂ → ℂ} {c : ℂ} {r : ℝ} (fi : CircleIntegrable f c r)
    (gi : CircleIntegrable g c r) :
    circleIntegral f c r - circleIntegral g c r = circleIntegral (f - g) c r := by
  rw [circleIntegral]
  generalize hf : (fun θ : ℝ ↦ deriv (circleMap c r) θ • f (circleMap c r θ)) = fc
  rw [circleIntegral]
  generalize hg : (fun θ : ℝ ↦ deriv (circleMap c r) θ • g (circleMap c r θ)) = gc
  rw [circleIntegral]
  generalize hfg : (fun θ : ℝ ↦ deriv (circleMap c r) θ • (f - g) (circleMap c r θ)) = fgc
  have hs : fc - gc = fgc := by
    rw [← hf, ← hg, ← hfg]; funext
    simp only [deriv_circleMap, Algebra.id.smul_eq_mul, Pi.sub_apply, mul_sub_left_distrib]
  rw [← hs]; clear hfg hs fgc; symm
  have fci := CircleIntegrable.out fi; rw [hf] at fci
  have gci := CircleIntegrable.out gi; rw [hg] at gci
  exact intervalIntegral.integral_sub fci gci

theorem circleMap_nz {c : ℂ} {r : ℝ≥0} {θ : ℝ} (rp : r > 0) : circleMap c r θ - c ≠ 0 := by
  simp only [circleMap_sub_center, Ne.def, circleMap_eq_center_iff, NNReal.coe_eq_zero]
  intro h; rw [h] at rp; simp only [gt_iff_lt, not_lt_zero'] at rp

theorem cauchy_is_circleIntegrable {f : ℂ → ℂ} {c : ℂ} {r : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (h : ContinuousOn f (closedBall c r)) :
    CircleIntegrable (fun z ↦ w ^ n / (z - c) ^ n * ((z - c)⁻¹ * f z)) c r := by
  refine ContinuousOn.intervalIntegrable ?_
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.mul continuousOn_const ?_
    apply Continuous.continuousOn
    refine Continuous.inv₀ ?_ fun x ↦ pow_ne_zero n (circleMap_nz rp)
    apply Continuous.pow; continuity
  · refine' ContinuousOn.mul _ _
    apply Continuous.continuousOn
    refine' Continuous.inv₀ (by continuity) fun x ↦ circleMap_nz rp
    refine' ContinuousOn.comp h (Continuous.continuousOn (by continuity)) _
    intro θ _; exact circleMap_mem_closedBall c (NNReal.coe_nonneg r) θ

theorem cauchy_sub {f g : ℂ → ℂ} {c : ℂ} {r : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (cf : ContinuousOn f (closedBall c r)) (cg : ContinuousOn g (closedBall c r)) :
    ((cauchyPowerSeries f c r n fun _ ↦ w) - cauchyPowerSeries g c r n fun _ ↦ w) =
      cauchyPowerSeries (f - g) c r n fun _ ↦ w := by
  rw [cauchyPowerSeries_apply f c r n w]
  rw [cauchyPowerSeries_apply g c r n w]
  rw [cauchyPowerSeries_apply (f - g) c r n w]
  set s : ℂ := (2 * π * I)⁻¹
  simp only [div_pow, Algebra.id.smul_eq_mul, Pi.sub_apply]
  have fi := cauchy_is_circleIntegrable n w rp cf
  have gi := cauchy_is_circleIntegrable n w rp cg
  have cia := circleIntegral_sub fi gi
  rw [← mul_sub_left_distrib, cia]
  clear cia fi gi cf cg rp
  have flip :
    ((fun z ↦ w ^ n / (z - c) ^ n * ((z - c)⁻¹ * f z)) - fun z ↦
        w ^ n / (z - c) ^ n * ((z - c)⁻¹ * g z)) =
      fun z ↦ w ^ n / (z - c) ^ n * ((z - c)⁻¹ * f z) - w ^ n / (z - c) ^ n * ((z - c)⁻¹ * g z) :=
    rfl
  simp only [flip, mul_sub_left_distrib]

theorem cauchy_dist {f g : ℂ → ℂ} {c : ℂ} {r : ℝ≥0} {d : ℝ≥0} (n : ℕ) (w : ℂ) (rp : r > 0)
    (cf : ContinuousOn f (closedBall c r)) (cg : ContinuousOn g (closedBall c r))
    (h : ∀ z, z ∈ closedBall c r → abs (f z - g z) ≤ d) :
    dist (cauchyPowerSeries f c r n fun _ ↦ w) (cauchyPowerSeries g c r n fun _ ↦ w) ≤
      abs w ^ n * r⁻¹ ^ n * d := by
  rw [Complex.dist_eq, cauchy_sub n w rp cf cg]
  refine' cauchy_bound rp _; intro z zr; simp at h zr; refine' h z zr

/-- Uniform limits of analytic functions are analytic -/
theorem uniform_analytic_lim {I : Type} [Lattice I] [Nonempty I] {f : I → ℂ → ℂ} {g : ℂ → ℂ}
    {s : Set ℂ} (o : IsOpen s) (h : ∀ n, AnalyticOn ℂ (f n) s)
    (u : TendstoUniformlyOn f g atTop s) : AnalyticOn ℂ g s := by
  intro c hc
  rcases open_has_cball o c hc with ⟨r, rp, cb⟩
  have hb : ∀ n, AnalyticOn ℂ (f n) (closedBall c r) := fun n ↦ (h n).mono cb
  set pr := fun n ↦ cauchyPowerSeries (f n) c r
  have hpf : ∀ n, HasFPowerSeriesOnBall (f n) (pr n) c r := by
    intro n
    have cs := cauchy_on_cball_radius rp (hb n)
    have pn : pr n = cauchyPowerSeries (f n) c r := rfl
    rw [← pn] at cs; exact cs
  have cfs : ∀ n, ContinuousOn (f n) s := fun n ↦ AnalyticOn.continuousOn (h n)
  have cf : ∀ n, ContinuousOn (f n) (closedBall c r) := fun n ↦ ContinuousOn.mono (cfs n) cb
  have cg : ContinuousOn g (closedBall c r) :=
    ContinuousOn.mono (TendstoUniformlyOn.continuousOn u (Filter.eventually_of_forall cfs)) cb
  clear h hb hc o cfs
  set p := cauchyPowerSeries g c r
  refine
    HasFPowerSeriesOnBall.analyticAt
      { r_le := le_radius_cauchyPowerSeries g c r
        r_pos := ENNReal.coe_pos.mpr rp
        hasSum := ?_ }
  intro y yb
  have yr := yb; simp at yr
  set a := abs y / r
  have a0 : a ≥ 0 := by bound
  have a1 : a < 1 := (div_lt_one (NNReal.coe_pos.mpr rp)).mpr yr
  have a1p : 1 - a > 0 := by bound
  rw [HasSum, Metric.tendsto_atTop]
  intro e ep
  generalize d4 : (1 - a) * (e / 4) = d
  have dp : d > 0 := by rw [← d4]; bound
  rcases Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp u d dp) with ⟨n, hn'⟩
  set hn := hn' n; simp at hn; clear hn' u
  have dfg : dist (f n (c + y)) (g (c + y)) ≤ d := by
    apply le_of_lt; rw [dist_comm]
    refine' hn (c + y) _
    apply cb
    simp; exact yr.le
  set hs := (hpf n).hasSum yb; rw [HasSum, Metric.tendsto_atTop] at hs
  rcases hs d dp with ⟨N, NM⟩; clear hs
  exists N; intro M NlM
  have dpf := (NM M NlM).le; clear NM NlM N yb
  have dppr : dist (M.sum fun k : ℕ ↦ p k fun _ ↦ y)
      (M.sum fun k : ℕ ↦ pr n k fun _ ↦ y) ≤ e / 4 := by
    trans M.sum fun k : ℕ ↦ dist (p k fun _ ↦ y) (pr n k fun _ ↦ y)
    apply dist_sum_sum_le M (fun k : ℕ ↦ p k fun _ ↦ y) fun k : ℕ ↦ pr n k fun _ ↦ y
    trans M.sum fun k ↦ a ^ k * d
    · apply Finset.sum_le_sum; intro k _
      have hak : a ^ k = abs y ^ k * r⁻¹ ^ k := by
        calc (abs y / r) ^ k
          _ = (abs y * r⁻¹) ^ k := by rw [div_eq_mul_inv, NNReal.coe_inv]
          _ = abs y ^ k * r⁻¹ ^ k := mul_pow _ _ _
      rw [hak]
      generalize hd' : d.toNNReal = d'
      have dd : (d' : ℝ) = d := by rw [← hd']; exact Real.coe_toNNReal d dp.le
      have hcb : ∀ z, z ∈ closedBall c r → abs (g z - f n z) ≤ d' := by
        intro z zb; exact _root_.trans (hn z (cb zb)).le (le_of_eq dd.symm)
      exact _root_.trans (cauchy_dist k y rp cg (cf n) hcb)
        (mul_le_mul_of_nonneg_left (le_of_eq dd) (by bound))
    · have pgb : (M.sum fun k ↦ a ^ k) ≤ (1 - a)⁻¹ := partial_geometric_bound M a0 a1
      calc
        (M.sum fun k ↦ a ^ k * d) = (M.sum fun k ↦ a ^ k) * d := by rw [← Finset.sum_mul]
        _ ≤ (1 - a)⁻¹ * d := by bound
        _ = (1 - a)⁻¹ * ((1 - a) * (e / 4)) := by rw [← d4]
        _ = (1 - a) * (1 - a)⁻¹ * (e / 4) := by ring
        _ = 1 * (e / 4) := by rw [mul_inv_cancel a1p.ne']
        _ = e / 4 := by ring
  generalize hMp : M.sum (fun k : ℕ ↦ p k fun _ ↦ y) = Mp; rw [hMp] at dppr
  generalize hMpr : M.sum (fun k ↦ pr n k fun _ ↦ y) = Mpr; rw [hMpr] at dpf dppr
  calc dist Mp (g (c + y))
    _ ≤ dist Mp (f n (c + y)) + dist (f n (c + y)) (g (c + y)) := dist_triangle _ _ _
    _ ≤ dist Mp Mpr + dist Mpr (f n (c + y)) + d := by bound
    _ ≤ e / 4 + d + d := by bound
    _ = e / 4 + 2 * (1 - a) * (e / 4) := by rw [← d4]; ring
    _ ≤ e / 4 + 2 * (1 - 0) * (e / 4) := by bound
    _ = 3 / 4 * e := by ring
    _ < 1 * e := (mul_lt_mul_of_pos_right (by norm_num) ep)
    _ = e := by simp
