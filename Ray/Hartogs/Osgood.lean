import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Field.InfiniteSum
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.Basic
import Ray.Analytic.Analytic
import Ray.Tactic.Bound
import Ray.Misc.Bounds
import Ray.Misc.Multilinear
import Ray.Misc.Topology

/-!
## Osgood's lemma for two variables

We show that continuous, separately analytic functions over ℂ are jointly analytic:

  https://en.wikipedia.org/wiki/Osgood's_lemma

The continuity assumption is unnecessary: see `Hartogs.lean` for the stronger version requiring only
separate analyticity.  We prove it for two variables only, as that's all we need; if more variables
if need, Hartogs' should be generalized, not Osgood's.

## Proof details

Osgood's lemma follows from the multidimensional Cauchy integral formula

  `f c = (2πi)^(-d) (prod_k ∫_(C k) d(z k)) (prod_k (z k - c k)⁻¹) f z`

The `n`th multidimensional coefficient (with `n : fin d → ℕ`) looks like

  `p n = (2πi)^(-d) (prod_k ∫_(C k) d(z k)) (prod_k (z k - c k)^(-1 - n k)) f z`

For a quick refresher on why the Cauchy power series works, for `c = 0`:

  f_n = (2πi)⁻¹ ∫_C dz z^(-1-n) * f z
  f w = (2πi)⁻¹ ∫_C dz (z - w)⁻¹ * f z
      = (2πi)⁻¹ ∫_C dz (z - z * (w/z))⁻¹ * f z
      = (2πi)⁻¹ ∫_C dz (1 - w/z)⁻¹ * z⁻¹ * f z
      = (2πi)⁻¹ ∫_C dz Σ_n (w/z)^n * z⁻¹ * f z
      = Σ_n w^n (2πi)⁻¹ ∫_C dz  z⁻¹^n * z⁻¹ * f z
-/

open Complex (abs exp I log)
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere isOpen_ball)
open intervalIntegral
open scoped Real NNReal ENNReal Topology MeasureTheory
noncomputable section

section osgood

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {f : ℂ × ℂ → E}
variable {s : Set (ℂ × ℂ)}
variable {c0 c1 w0 w1 : ℂ}
variable {r b : ℝ}

/-- A measureable, separately analytic function of 2 complex variables near `c`.
    We assume `f` is differentiable in an open neighborhood of the closedBall for simplicity. -/
structure Separate (f : ℂ × ℂ → E) (c0 c1 : ℂ) (r b : ℝ) (s : Set (ℂ × ℂ)) : Prop where
  rp : 0 < r
  so : IsOpen s
  rs : closedBall (c0, c1) r ⊆ s
  fc : ContinuousOn f s
  fa0 : ∀ {c0 c1}, (c0, c1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, c1)) c0
  fa1 : ∀ {c0 c1}, (c0, c1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (c0, z1)) c1
  bp : 0 ≤ b
  fb : ∀ {z0 z1}, z0 ∈ sphere c0 r → z1 ∈ sphere c1 r → ‖f (z0, z1)‖ ≤ b

-- Teach `bound` about the positivity fields of `Separate`
attribute [aesop safe forward (rule_sets [bound])] Separate.rp Separate.bp

theorem spheres_subset_closedBall {c0 c1 : ℂ} {r : ℝ} :
    sphere c0 r ×ˢ sphere c1 r ⊆ closedBall (c0, c1) r := by
  rw [←closedBall_prod_same, Set.subset_def]; intro z
  simp only [Set.mem_prod, mem_sphere_iff_norm, Complex.norm_eq_abs, Metric.mem_closedBall, and_imp]
  rw [Complex.dist_eq, Complex.dist_eq]
  intro a b; exact ⟨le_of_eq a, le_of_eq b⟩

theorem Separate.rs' (h : Separate f c0 c1 r b s) : sphere c0 r ×ˢ sphere c1 r ⊆ s :=
  le_trans spheres_subset_closedBall h.rs

theorem mem_open_closed {z c : ℂ} {r : ℝ} : z ∈ ball c r → z ∈ closedBall c r := by
  simp only [Metric.mem_ball, Metric.mem_closedBall]; exact le_of_lt

theorem mem_sphere_closed {z c : ℂ} {r : ℝ} : z ∈ sphere c r → z ∈ closedBall c r := by
  simp only [mem_sphere_iff_norm, Complex.norm_eq_abs, Metric.mem_closedBall]; exact le_of_eq

/-- Spheres don't contain their center -/
theorem center_not_in_sphere {c z : ℂ} {r : ℝ} (rp : r > 0) (zs : z ∈ sphere c r) : z - c ≠ 0 := by
  simp only [mem_sphere_iff_norm, Complex.norm_eq_abs] at zs
  rw [←Complex.abs.ne_zero_iff, zs]; exact rp.ne'

/-- `f` is continuous in `z0` -/
theorem Separate.fc0 (h : Separate f c0 c1 r b s) (w1m : w1 ∈ ball c1 r) :
    ContinuousOn (fun z0 ↦ f (z0, w1)) (closedBall c0 r) := by
  refine' ContinuousOn.comp h.fc _ _
  exact ContinuousOn.prod continuousOn_id continuousOn_const
  intro z0 z0m; apply h.rs
  rw [← closedBall_prod_same]; exact Set.mem_prod.mpr ⟨z0m, mem_open_closed w1m⟩

/-- `f` is continuous in `z1` -/
theorem Separate.fc1 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ closedBall c0 r) :
    ContinuousOn (fun z1 ↦ f (w0, z1)) (closedBall c1 r) := by
  refine' ContinuousOn.comp h.fc _ _
  exact ContinuousOn.prod continuousOn_const continuousOn_id
  intro z1 z1m; apply h.rs
  rw [← closedBall_prod_same]; exact Set.mem_prod.mpr ⟨w0m, z1m⟩

/-- `f` is differentiable in `z0` -/
theorem Separate.fd0 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ closedBall c0 r)
    (w1m : w1 ∈ closedBall c1 r) : DifferentiableAt ℂ (fun z0 ↦ f (z0, w1)) w0 :=
  haveI m : (w0, w1) ∈ s := by
    apply h.rs; rw [←closedBall_prod_same]; exact Set.mem_prod.mpr ⟨w0m, w1m⟩
  AnalyticAt.differentiableAt (h.fa0 m)

/-- `f` is differentiable in `z1` -/
theorem Separate.fd1 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ closedBall c0 r)
    (w1m : w1 ∈ closedBall c1 r) : DifferentiableAt ℂ (fun z1 ↦ f (w0, z1)) w1 :=
  haveI m : (w0, w1) ∈ s := by
    apply h.rs; rw [←closedBall_prod_same]; exact Set.mem_prod.mpr ⟨w0m, w1m⟩
  AnalyticAt.differentiableAt (h.fa1 m)

/-- Simplied 1D Cauchy integral formula, assuming differentiability everywhere in the interior -/
theorem cauchy1 {r : ℝ} {c w : ℂ} {f : ℂ → E} (wm : w ∈ ball c r)
    (fc : ContinuousOn f (closedBall c r)) (fd : ∀ z, z ∈ ball c r → DifferentiableAt ℂ f z) :
    (2*π*I : ℂ)⁻¹ • (∮ z in C(c, r), (z - w)⁻¹ • f z) = f w := by
  refine' Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty wm fc _
  intro z zm; apply fd z _; simp only [Metric.mem_ball, Set.diff_empty] at zm ⊢; assumption

/-- The 2D Cauchy integral formula -/
theorem cauchy2 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball c0 r) (w1m : w1 ∈ ball c1 r) :
    (2*π*I : ℂ)⁻¹ • (∮ z0 in C(c0, r), (z0 - w0)⁻¹ • (2*π*I : ℂ)⁻¹ •
      (∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0, z1))) =
      f (w0, w1) := by
  have h1 := fun z0 (z0m : z0 ∈ closedBall c0 r) ↦
    cauchy1 w1m (h.fc1 z0m) fun z1 z1m ↦ h.fd1 z0m (mem_open_closed z1m)
  have ic1 : ContinuousOn (fun z0 ↦ (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹ • f (z0, z1))
      (closedBall c0 r) :=
    (h.fc0 w1m).congr h1
  have id1 : DifferentiableOn ℂ (fun z0 ↦ (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - w1)⁻¹
      • f (z0, z1)) (ball c0 r) := by
    rw [differentiableOn_congr fun z zs ↦ h1 z (mem_open_closed zs)]
    intro z0 z0m; apply DifferentiableAt.differentiableWithinAt
    exact h.fd0 (mem_open_closed z0m) (mem_open_closed w1m)
  have h01 :=
    cauchy1 w0m ic1 fun z0 z0m ↦
      DifferentiableOn.differentiableAt id1 (IsOpen.mem_nhds isOpen_ball z0m)
  exact _root_.trans h01 (h1 w0 (mem_open_closed w0m))

/-- One 2D coefficient of the 2D Cauchy series -/
@[nolint unusedArguments]  -- Don't complain about the first argument
def Separate.series2Coeff (_ : Separate f c0 c1 r b s) (n0 n1 : ℕ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ z0 in C(c0, r), (z0 - c0)⁻¹ ^ n0 • (z0 - c0)⁻¹ •
    (2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1)

/-- `series2Coeff` summed over `n0` -/
@[nolint unusedArguments]  -- Don't complain about the first argument
def Separate.series2CoeffN0Sum (_ : Separate f c0 c1 r b s) (n1 : ℕ) (w0 : ℂ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ z0 : ℂ in C(c0, r), (z0 - (c0 + w0))⁻¹ •
    (2*π*I : ℂ)⁻¹ • ∮ z1 : ℂ in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1)

/-- The 1D Cauchy series converges as expected
   (rephrasing of `hasSum_cauchy_power_series_integral`) -/
theorem cauchy1_hasSum {f : ℂ → E} {c w : ℂ} {r : ℝ} (rp : r > 0) (fc : ContinuousOn f (sphere c r))
    (wm : w ∈ ball (0 : ℂ) r) :
    HasSum
      (fun n : ℕ ↦ w ^ n • (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z)
      ((2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), (z - (c + w))⁻¹ • f z) := by
  simp at wm
  have ci : CircleIntegrable f c r := ContinuousOn.circleIntegrable (by linarith) fc
  have h := hasSum_cauchyPowerSeries_integral ci wm
  simp_rw [cauchyPowerSeries_apply] at h
  generalize hs : (2*π*I : ℂ)⁻¹ = s; simp_rw [hs] at h
  generalize hg : (s • ∮ z : ℂ in C(c, r), (z - (c + w))⁻¹ • f z) = g; rw [hg] at h
  simp_rw [div_eq_mul_inv, mul_pow, ← smul_smul, circleIntegral.integral_smul, smul_comm s _] at h
  assumption

/-- Circle integrals are continuous if the function varies continuously -/
theorem ContinuousOn.circleIntegral {f : ℂ → ℂ → E} {s : Set ℂ} (rp : r > 0) (cs : IsCompact s)
    (fc : ContinuousOn (uncurry f) (s ×ˢ sphere c1 r)) :
    ContinuousOn (fun z0 ↦ ∮ z1 in C(c1, r), f z0 z1) s := by
  rcases fc.norm.bounded (IsCompact.prod cs (isCompact_sphere _ _)) with ⟨b, _, bh⟩
  intro z1 z1s
  have fb : ∀ᶠ x : ℂ in 𝓝[s] z1, ∀ᵐ t : ℝ, t ∈ Set.uIoc 0 (2 * π) →
      ‖deriv (circleMap c1 r) t • (fun z1 : ℂ ↦ f x z1) (circleMap c1 r t)‖ ≤ r * b := by
    apply eventually_nhdsWithin_of_forall; intro x xs
    apply MeasureTheory.ae_of_all _; intro t _; simp only [deriv_circleMap]
    rw [norm_smul, Complex.norm_eq_abs]
    simp only [map_mul, abs_circleMap_zero, Complex.abs_I, mul_one]
    have bx := bh (x, circleMap c1 r t) (Set.mk_mem_prod xs (circleMap_mem_sphere c1
      (by linarith) t))
    simp only [uncurry] at bx
    calc |r| * ‖f x (circleMap c1 r t)‖ ≤ |r| * b := by bound
      _ = r * b := by rw [abs_of_pos rp]
  refine' intervalIntegral.continuousWithinAt_of_dominated_interval _ fb (by simp) _
  · apply eventually_nhdsWithin_of_forall; intro x xs
    apply ContinuousOn.aestronglyMeasurable
    apply ContinuousOn.smul; simp
    exact ContinuousOn.mul (Continuous.continuousOn (continuous_circleMap _ _)) continuousOn_const
    have comp : (fun t ↦ f x (circleMap c1 r t)) = uncurry f ∘ fun t ↦ (x, circleMap c1 r t) := by
      apply funext; intro t; simp
    simp; rw [comp]; apply ContinuousOn.comp fc
    exact ContinuousOn.prod continuousOn_const (Continuous.continuousOn (continuous_circleMap _ _))
    intro t _; simp; exact ⟨xs, by linarith⟩
    exact measurableSet_uIoc
  · apply MeasureTheory.ae_of_all _; intro t _; simp
    apply ContinuousOn.smul continuousOn_const
    have comp : (fun x ↦ f x (circleMap c1 r t)) = uncurry f ∘ fun x ↦ (x, circleMap c1 r t) := by
      apply funext; intro t; simp
    rw [comp]; apply ContinuousOn.comp fc (ContinuousOn.prod continuousOn_id continuousOn_const)
    intro x xs; simp; exact ⟨xs, by linarith⟩
    exact z1s

/-- Inverses are continuous on the sphere -/
theorem ContinuousOn.inv_sphere {c : ℂ} {r : ℝ} (rp : r > 0) :
    ContinuousOn (fun z ↦ (z - c)⁻¹) (sphere c r) :=
  ContinuousOn.inv₀ (ContinuousOn.sub continuousOn_id continuousOn_const) fun _ zs ↦
    center_not_in_sphere rp zs

/-- Shifted inverses are continuous on the sphere -/
theorem ContinuousOn.inv_sphere_ball {c w : ℂ} {r : ℝ} (wr : w ∈ ball (0 : ℂ) r) :
    ContinuousOn (fun z ↦ (z - (c + w))⁻¹) (sphere c r) := by
  refine' ContinuousOn.inv₀ (ContinuousOn.sub continuousOn_id continuousOn_const) fun z zs ↦ _
  rw [←Complex.abs.ne_zero_iff]
  simp only [mem_ball_zero_iff, Complex.norm_eq_abs, mem_sphere_iff_norm] at zs wr
  apply ne_of_gt
  calc abs (z - (c + w))
    _ = abs (z - c + -w) := by ring_nf
    _ ≥ abs (z - c) - abs (-w) := by bound
    _ = r - abs (-w) := by rw [zs]
    _ = r - abs w := by rw [Complex.abs.map_neg]
    _ > r - r := (sub_lt_sub_left wr _)
    _ = 0 := by ring

/-- Cauchy series terms are continuous in the function -/
theorem ContinuousOn.cauchy1 {n1 : ℕ} (rp : r > 0)
    (fc : ContinuousOn f (sphere c0 r ×ˢ sphere c1 r)) :
    ContinuousOn (fun z0 ↦ ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1))
      (sphere c0 r) := by
  apply ContinuousOn.circleIntegral rp (isCompact_sphere _ _)
  apply ContinuousOn.smul; apply ContinuousOn.pow; apply ContinuousOn.inv₀
  apply Continuous.continuousOn
  exact Continuous.sub (Continuous.snd continuous_id) continuous_const
  intro x xp; exact center_not_in_sphere rp (Set.mem_prod.mp xp).right
  apply ContinuousOn.smul; apply ContinuousOn.inv₀
  apply Continuous.continuousOn
  exact Continuous.sub (Continuous.snd continuous_id) continuous_const
  intro x xp; exact center_not_in_sphere rp (Set.mem_prod.mp xp).right
  simp; exact fc

/-- Summing over `n0` in the 2D series does the right thing -/
theorem cauchy2_hasSum_n0 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r) (n1 : ℕ) :
    HasSum (fun n0 : ℕ ↦ w0 ^ n0 • h.series2Coeff n0 n1) (h.series2CoeffN0Sum n1 w0) :=
  haveI cc1 : ContinuousOn (fun z0 ↦
      (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1))
      (sphere c0 r) :=
    ContinuousOn.smul continuousOn_const (ContinuousOn.cauchy1 h.rp (ContinuousOn.mono h.fc h.rs'))
  cauchy1_hasSum h.rp cc1 w0m

/-- Sums commute with `circle_integral` under reasonable hypotheses -/
theorem sum_integral_commute {f : ℕ → ℂ → E} {g : ℂ → E} {c : ℂ} {r : ℝ} (b : ℕ → ℝ) (rp : r > 0)
    (fc : ∀ n, ContinuousOn (f n) (sphere c r)) (fb : ∀ n z, z ∈ sphere c r → ‖f n z‖ ≤ b n)
    (bs : Summable b) (h : ∀ z, z ∈ sphere c r → HasSum (fun n ↦ f n z) (g z)) :
    HasSum (fun n ↦ ∮ z in C(c, r), f n z) (∮ z in C(c, r), g z) := by
  rw [circleIntegral]; simp_rw [circleIntegral]; simp
  apply intervalIntegral.hasSum_integral_of_dominated_convergence fun n _ ↦ r * b n
  · intro n; apply ContinuousOn.aestronglyMeasurable; apply ContinuousOn.smul
    apply ContinuousOn.mul (Continuous.continuousOn (continuous_circleMap _ _)) continuousOn_const
    apply ContinuousOn.comp (fc n) (Continuous.continuousOn (continuous_circleMap _ _))
    intro t _; exact circleMap_mem_sphere _ (by linarith) _
    exact measurableSet_uIoc
  · intro n; apply MeasureTheory.ae_of_all; intro t _; rw [norm_smul, Complex.norm_eq_abs]; simp
    rw [abs_of_pos rp]
    refine' mul_le_mul_of_nonneg_left _ rp.le
    exact fb n (circleMap c r t) (circleMap_mem_sphere _ (by linarith) _)
  · apply MeasureTheory.ae_of_all; intro t _
    exact Summable.mul_left _ bs
  · simp only [_root_.intervalIntegrable_const]
  · apply MeasureTheory.ae_of_all; intro t _
    apply HasSum.const_smul
    exact h (circleMap c r t) (circleMap_mem_sphere _ (by linarith) _)

/-- The simple bound on circle_interval -/
theorem bounded_circleIntegral {f : ℂ → E} {c : ℂ} {r b : ℝ} (rp : r > 0)
    (fc : ContinuousOn f (sphere c r)) (fb : ∀ z, z ∈ sphere c r → ‖f z‖ ≤ b) :
    ‖∮ z in C(c, r), f z‖ ≤ 2 * π * r * b := by
  rw [circleIntegral]; simp only [deriv_circleMap]
  have nonneg_2π := Real.two_pi_pos.le
  have ib : ‖(∫ t in (0)..(2*π), (circleMap 0 r t * I) • f (circleMap c r t))‖ ≤
      (∫ t in (0)..(2*π), ‖(circleMap 0 r t * I) • f (circleMap c r t)‖) :=
    intervalIntegral.norm_integral_le_integral_norm nonneg_2π
  refine' le_trans ib _; clear ib
  simp_rw [norm_smul, Complex.norm_eq_abs]
  simp only [map_mul, abs_circleMap_zero, Complex.abs_I, mul_one, integral_const_mul]
  have mo : ∀ t, t ∈ Set.Icc 0 (2 * π) → ‖f (circleMap c r t)‖ ≤ b := fun t _ ↦
    fb (circleMap c r t) (circleMap_mem_sphere c (by linarith) t)
  have i0 : IntervalIntegrable (fun t ↦ ‖f (circleMap c r t)‖) Real.measureSpace.volume
      0 (2*π) := by
    apply ContinuousOn.intervalIntegrable
    have ca : ContinuousOn (norm : E → ℝ) Set.univ := Continuous.continuousOn continuous_norm
    refine' ContinuousOn.comp ca _ (Set.mapsTo_univ _ _)
    apply ContinuousOn.comp fc
    exact Continuous.continuousOn (continuous_circleMap _ _)
    intro t _; exact circleMap_mem_sphere _ (by linarith) _
  have i1 : IntervalIntegrable (fun _ ↦ b) Real.measureSpace.volume 0 (2 * π) :=
    intervalIntegrable_const
  have im := intervalIntegral.integral_mono_on nonneg_2π i0 i1 mo
  simp only [integral_const, sub_zero, smul_eq_mul] at im
  calc |r| * ∫ t in (0)..(2*π), ‖f (circleMap c r t)‖
    _ ≤ |r| * (2 * π * b) := by bound
    _ = r * (2 * π * b) := by rw [abs_of_pos rp]
    _ = 2 * π * r * b := by ring

/-- The 1D Cauchy integral without the constant has the expected bound -/
theorem cauchy1_bound {f : ℂ → E} {b r : ℝ} {c : ℂ} (rp : r > 0)
    (fc : ContinuousOn f (sphere c r)) (bh : ∀ z, z ∈ sphere c r → ‖f z‖ ≤ b) (n : ℕ) :
    ‖∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ 2 * π * b * r⁻¹ ^ n := by
  have sb : ∀ z, z ∈ sphere c r → ‖(z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ r⁻¹ ^ n * r⁻¹ * b := by
    intro z zs; have fb := bh z zs
    rw [norm_smul, norm_smul, Complex.norm_eq_abs, Complex.norm_eq_abs]
    simp only [inv_pow, map_inv₀, map_pow, ge_iff_le, Metric.mem_sphere, Complex.dist_eq] at zs ⊢
    rw [zs]; ring_nf; bound
  have isb := bounded_circleIntegral rp ?_ sb
  · calc ‖∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖
      _ ≤ 2 * π * r * (r⁻¹ ^ n * r⁻¹ * b) := isb
      _ = 2 * π * b * r⁻¹ ^ n * (r * r⁻¹) := by ring
      _ = 2 * π * b * r⁻¹ ^ n := by rw [mul_inv_cancel rp.ne']; simp
  · apply ContinuousOn.smul; apply ContinuousOn.pow; exact ContinuousOn.inv_sphere rp
    apply ContinuousOn.smul; exact ContinuousOn.inv_sphere rp; assumption

/-- The 1D Cauchy integral with the constant has the expected bound -/
theorem cauchy1_bound' {f : ℂ → E} {r : ℝ} {c : ℂ} (rp : r > 0) (b : ℝ)
    (fc : ContinuousOn f (sphere c r)) (bh : ∀ z, z ∈ sphere c r → ‖f z‖ ≤ b) (n : ℕ) :
    ‖(2*π*I : ℂ)⁻¹ • ∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖ ≤ b * r⁻¹ ^ n := by
  have a : abs (2*π*I : ℂ)⁻¹ = (2*π)⁻¹ := by
    simp only [mul_inv_rev, Complex.inv_I, neg_mul, map_neg_eq_map, map_mul, Complex.abs_I,
      map_inv₀, Complex.abs_ofReal, Complex.abs_two, one_mul, mul_eq_mul_right_iff, inv_inj,
      abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
    exact Real.pi_pos.le
  rw [norm_smul, Complex.norm_eq_abs, a]
  calc (2*π)⁻¹ * ‖∮ z in C(c, r), (z - c)⁻¹ ^ n • (z - c)⁻¹ • f z‖
    _ ≤ (2*π)⁻¹ * (2*π * b * r⁻¹ ^ n) := by bound [cauchy1_bound rp fc bh n]
    _ = (2*π)⁻¹ * (2*π) * b * r⁻¹ ^ n := by ring
    _ = b * r⁻¹ ^ n := by field_simp [Real.pi_pos.ne']

/-- Corollary of cauchy1_bound used in cauchy2_hasSum_n1n0 -/
theorem cauchy2_hasSum_n1n0_bound (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (n : ℕ) {z0 : ℂ} (z0s : z0 ∈ sphere c0 r) :
    ‖w1 ^ n • (2 * π * I : ℂ)⁻¹ • (z0 - (c0 + w0))⁻¹ •
      ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n • (z1 - c1)⁻¹ • f (z0, z1)‖ ≤
      (r - abs w0)⁻¹ * b * (abs w1 / r) ^ n := by
  have isb := cauchy1_bound h.rp
    (ContinuousOn.mono (h.fc1 (mem_sphere_closed z0s)) Metric.sphere_subset_closedBall)
    (fun z1 z1s ↦ h.fb z0s z1s) n
  simp only [mem_sphere_iff_norm, Complex.norm_eq_abs, Metric.mem_ball, dist_zero_right] at z0s w0m
  have zcw : abs (z0 - (c0 + w0)) ≥ r - abs w0 := by
    calc abs (z0 - (c0 + w0))
      _ = abs (z0 - c0 + -w0) := by ring_nf
      _ ≥ abs (z0 - c0) - abs (-w0) := by bound
      _ = r - abs w0 := by rw [z0s]; simp only [map_neg_eq_map]
  have zcw' : (abs (z0 - (c0 + w0)))⁻¹ ≤ (r - abs w0)⁻¹ := by bound
  have a : (abs (2 * π * I : ℂ))⁻¹ = (2 * π)⁻¹ := by
    simp only [map_mul, Complex.abs_two, Complex.abs_ofReal, Complex.abs_I, mul_one, mul_inv_rev,
      mul_eq_mul_right_iff, inv_inj, abs_eq_self, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
    bound
  rw [norm_smul, norm_smul, norm_smul, Complex.norm_eq_abs, Complex.norm_eq_abs,
    Complex.norm_eq_abs, Complex.abs.map_pow, map_inv₀, map_inv₀, a]
  calc abs w1 ^ n * ((2*π)⁻¹ * ((abs (z0 - (c0 + w0)))⁻¹ *
      ‖∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n • (z1 - c1)⁻¹ • f (z0, z1)‖))
    _ ≤ abs w1 ^ n * ((2 * π)⁻¹ * ((abs (z0 - (c0 + w0)))⁻¹ * (2 * π * b * r⁻¹ ^ n))) := by bound
    _ ≤ abs w1 ^ n * ((2 * π)⁻¹ * ((r - abs w0)⁻¹ * (2 * π * b * r⁻¹ ^ n))) := by bound
    _ = 2 * π * (2 * π)⁻¹ * (r - abs w0)⁻¹ * b * (abs w1 ^ n * r⁻¹ ^ n) := by ring
    _ = (r - abs w0)⁻¹ * b * (abs w1 / r) ^ n := by
      rw [mul_inv_cancel Real.two_pi_pos.ne', ← mul_pow, ← div_eq_mul_inv _ r, one_mul]

/-- The outer n1 sum in the 2D series does the right thing -/
theorem cauchy2_hasSum_n1n0 (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (w1m : w1 ∈ ball (0 : ℂ) r) :
    HasSum (fun n1 ↦ w1 ^ n1 • h.series2CoeffN0Sum n1 w0) (f (c0 + w0, c1 + w1)) := by
  have cw0m : c0 + w0 ∈ ball c0 r := by
    simpa only [Metric.mem_ball, dist_self_add_left, Complex.norm_eq_abs, Complex.dist_eq,
      sub_zero] using w0m
  have cw1m : c1 + w1 ∈ ball c1 r := by
    simpa only [Metric.mem_ball, dist_self_add_left, Complex.norm_eq_abs, dist_zero_right] using w1m
  simp_rw [Separate.series2CoeffN0Sum]
  rw [← cauchy2 h cw0m cw1m]
  generalize hs : (2 * ↑π * I)⁻¹ = s
  simp_rw [smul_comm _ s _]
  apply HasSum.const_smul
  simp_rw [← circleIntegral.integral_smul (w1 ^ _) _ _ _]
  apply sum_integral_commute (fun n ↦ (r - abs w0)⁻¹ * b * (abs w1 / r) ^ n) h.rp
  · intro n
    apply ContinuousOn.smul continuousOn_const
    apply ContinuousOn.smul continuousOn_const
    apply ContinuousOn.smul
    exact ContinuousOn.inv_sphere_ball w0m
    apply ContinuousOn.cauchy1 h.rp
    apply ContinuousOn.mono h.fc h.rs'
  · rw [← hs]; exact fun n z0 z0s ↦ cauchy2_hasSum_n1n0_bound h w0m n z0s
  · apply Summable.mul_left
    apply summable_geometric_of_abs_lt_one
    rw [abs_div, abs_of_pos h.rp]; simp at w1m ⊢; exact (div_lt_one h.rp).mpr w1m
  · intro z0 z0s
    simp_rw [smul_comm s _]; simp_rw [smul_comm (w1 ^ _) _]; apply HasSum.const_smul
    have fcs : ContinuousOn (fun z1 ↦ f (z0, z1)) (sphere c1 r) :=
      ContinuousOn.mono (h.fc1 (Metric.sphere_subset_closedBall z0s))
        Metric.sphere_subset_closedBall
    have hs1 := cauchy1_hasSum h.rp fcs w1m
    simp_rw [hs, smul_comm _ s] at hs1
    assumption

/-- 2D Cauchy series terms are geometrically bounded -/
theorem series2Coeff_bound (h : Separate f c0 c1 r b s) (n0 n1 : ℕ) :
    ‖h.series2Coeff n0 n1‖ ≤ b * r⁻¹ ^ (n0 + n1) := by
  have inner_c :
    ContinuousOn
      (fun z0 ↦ (2 * π * I : ℂ)⁻¹ • ∮ z1 in C(c1, r), (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0, z1))
      (sphere c0 r) :=
    ContinuousOn.smul continuousOn_const (ContinuousOn.cauchy1 h.rp (ContinuousOn.mono h.fc h.rs'))
  have inner_b : ∀ z0 _, ‖(2*π*I : ℂ)⁻¹ • ∮ z1 in C(c1, r),
      (z1 - c1)⁻¹ ^ n1 • (z1 - c1)⁻¹ • f (z0,z1)‖ ≤ b * r⁻¹ ^ n1 :=
    fun z0 z0s ↦ cauchy1_bound' h.rp b
      (ContinuousOn.mono (h.fc1 (mem_sphere_closed z0s)) Metric.sphere_subset_closedBall)
      (fun z1 ↦ h.fb z0s) n1
  have outer := cauchy1_bound' h.rp _ inner_c inner_b n0
  have e : b * r⁻¹ ^ n1 * r⁻¹ ^ n0 = b * r⁻¹ ^ (n0 + n1) := by
    rw [mul_assoc, ← pow_add, add_comm n0 _]
  rw [Separate.series2Coeff]; rw [e] at outer; exact outer

/-- The 2D Cauchy series -/
def series2 (h : Separate f c0 c1 r b s) : FormalMultilinearSeries ℂ (ℂ × ℂ) E := fun n ↦
  (Finset.range (n + 1)).sum fun n0 ↦ termCmmap ℂ n n0 (h.series2Coeff n0 (n - n0))

/-- `series2` is (roughly) geometrically bounded -/
theorem series2_norm (h : Separate f c0 c1 r b s) (n : ℕ) :
    ‖series2 h n‖ ≤ (n + 1) * b * r⁻¹ ^ n := by
  rw [series2]; simp only [ge_iff_le, inv_pow]
  have tb : ∀ n0, n0 ∈ Finset.range (n+1) →
      ‖termCmmap ℂ n n0 (h.series2Coeff n0 (n - n0))‖ ≤ b * r⁻¹ ^ n := by
    intro n0 n0n; simp at n0n
    apply le_trans (termCmmap_norm ℂ n n0 (h.series2Coeff n0 (n - n0)))
    have sb := series2Coeff_bound h n0 (n - n0)
    rw [← Nat.add_sub_assoc (Nat.le_of_lt_succ n0n) n0, Nat.add_sub_cancel_left] at sb
    assumption
  trans (Finset.range (n + 1)).sum fun n0 ↦ ‖termCmmap ℂ n n0 (h.series2Coeff n0 (n - n0))‖
  · bound
  · trans (Finset.range (n + 1)).sum fun _ ↦ b * r⁻¹ ^ n
    · bound
    · clear tb; rw [Finset.sum_const]
      simp only [Finset.card_range, inv_pow, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring_nf; rfl

/-- `series2` converges within radius r -/
theorem cauchy2_radius (h : Separate f c0 c1 r b s) : ENNReal.ofReal r ≤ (series2 h).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro t tr
  rw [←ENNReal.toReal_lt_toReal (@ENNReal.coe_ne_top t) (@ENNReal.ofReal_ne_top r)] at tr
  rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal h.rp.le] at tr
  apply FormalMultilinearSeries.le_radius_of_summable_nnnorm
  simp_rw [← norm_toNNReal, ← NNReal.summable_coe]; simp
  have lo : ∀ n : ℕ, 0 ≤ ‖series2 h n‖ * (t:ℝ)^n := by intro; bound
  have hi : ∀ n : ℕ, ‖series2 h n‖ * (t:ℝ)^n ≤ (n + 1) * b * (t / r) ^ n := by
    intro n; trans (↑n + 1) * b * r⁻¹ ^ n * (t:ℝ)^n
    · bound [series2_norm h n]
    · rw [mul_assoc ((↑n + 1) * b) _ _, ← mul_pow, inv_mul_eq_div]
  refine .of_nonneg_of_le lo hi ?_
  simp_rw [mul_comm _ b, mul_assoc b _ _]; apply Summable.mul_left b
  have trn : ‖↑t / r‖ < 1 := by simp; rw [abs_of_pos h.rp, div_lt_one h.rp]; assumption
  simp_rw [right_distrib _ _ _, one_mul]
  exact Summable.add (hasSum_coe_mul_geometric_of_norm_lt_one trn).summable
    (hasSum_geometric_of_norm_lt_one trn).summable

/-- The 2D series converges to `f` -/
theorem cauchy2_hasSum_2d (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (w1m : w1 ∈ ball (0 : ℂ) r) :
    HasSum (fun n : ℕ × ℕ ↦ w0 ^ n.snd • w1 ^ n.fst • h.series2Coeff n.snd n.fst)
      (f (c0 + w0, c1 + w1)) := by
  generalize ha : f (c0 + w0, c1 + w1) = a
  generalize hf : (fun n : ℕ × ℕ ↦ w0 ^ n.snd • w1 ^ n.fst • h.series2Coeff n.snd n.fst) = f
  generalize hg : (fun n1 : ℕ ↦ w1 ^ n1 • h.series2CoeffN0Sum n1 w0) = g
  generalize ha' : ∑' n, f n = a'
  have gs : HasSum g a := by rw [← hg, ← ha]; exact cauchy2_hasSum_n1n0 h w0m w1m
  have fs : ∀ n1 : ℕ, HasSum (fun n0 ↦ f ⟨n1, n0⟩) (g n1) := by
    intro n1; rw [← hf, ← hg]; simp only
    simp_rw [smul_comm (w0 ^ _) _]; apply HasSum.const_smul; exact cauchy2_hasSum_n0 h w0m n1
  have fb : ∀ n : ℕ × ℕ, ‖f n‖ ≤ b * (abs w0 / r) ^ n.snd * (abs w1 / r) ^ n.fst := by
    intro n; rw [← hf]; simp
    rw [norm_smul, norm_smul, mul_assoc]
    rw [Complex.norm_eq_abs, Complex.norm_eq_abs, ← mul_assoc]; simp
    trans abs w0 ^ n.snd * abs w1 ^ n.fst * (b * r⁻¹ ^ (n.snd + n.fst))
    · bound [series2Coeff_bound h n.snd n.fst]
    · rw [pow_add, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]; ring_nf; rfl
  have sf : Summable f := by
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_eq_abs] at w0m w1m
    refine .of_norm_bounded _ ?_ fb
    simp_rw [mul_assoc]; apply Summable.mul_left; simp_rw [mul_comm ((abs w0 / r) ^ _) _]
    apply Summable.mul_of_nonneg
    · exact summable_geometric_of_lt_one (by bound) ((div_lt_one h.rp).mpr w1m)
    · exact summable_geometric_of_lt_one (by bound) ((div_lt_one h.rp).mpr w0m)
    · intro n; simp only [Pi.zero_apply, div_pow]; bound
    · intro n; simp only [Pi.zero_apply, div_pow]; bound
  have fs' : HasSum f a' := by rw [← ha']; exact sf.hasSum
  have gs' := HasSum.prod_fiberwise fs' fs; simp at gs'
  rwa [HasSum.unique gs gs']

/-- We convert the 2D sum to a 1D outer sum with an inner finite antidiagonal -/
theorem HasSum.antidiagonal_of_2d {f : ℕ × ℕ → E} {a : E} (h : HasSum f a) :
    HasSum (fun n ↦ (Finset.range (n + 1)).sum fun n1 ↦ f (n1, n - n1)) a := by
  generalize hg : (fun n ↦ (Finset.range (n + 1)).sum fun n1 ↦ f (n1, n - n1)) = g
  rw [←Finset.sigmaAntidiagonalEquivProd.hasSum_iff] at h
  have fg : ∀ n, HasSum (fun d : Finset.antidiagonal n ↦
      (f ∘ Finset.sigmaAntidiagonalEquivProd) ⟨n, d⟩) (g n) := by
    intro n; simp only [Function.comp_apply, Finset.sigmaAntidiagonalEquivProd_apply]
    have fs := hasSum_fintype fun d : ↥(Finset.antidiagonal n) ↦ f ↑d
    -- simp at fs,
    have e : (Finset.univ.sum fun d : ↥(Finset.antidiagonal n) ↦ f ↑d) = g n := by
      rw [Finset.sum_coe_sort, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← hg]
    rwa [← e]
  exact HasSum.sigma h fg

/-- `series2` converges to `f` -/
theorem cauchy2_hasSum (h : Separate f c0 c1 r b s) (w0m : w0 ∈ ball (0 : ℂ) r)
    (w1m : w1 ∈ ball (0 : ℂ) r) :
    HasSum (fun n ↦ series2 h n fun _ : Fin n ↦ (w0, w1)) (f (c0 + w0, c1 + w1)) := by
  have sum := (cauchy2_hasSum_2d h w0m w1m).antidiagonal_of_2d; simp only [ge_iff_le] at sum
  generalize ha : f (c0 + w0, c1 + w1) = a; rw [ha] at sum; clear ha
  have e : (fun n ↦
      (Finset.range (n + 1)).sum fun n1 ↦ w0 ^ (n - n1) • w1 ^ n1 • h.series2Coeff (n - n1) n1) =
      fun n ↦ series2 h n fun _ : Fin n ↦ (w0, w1) := by
    clear sum; funext n
    rw [series2]; simp only [ge_iff_le, ContinuousMultilinearMap.sum_apply]
    simp_rw [termCmmap_apply]
    nth_rw 1 [← Finset.sum_range_reflect]; simp
    apply Finset.sum_congr rfl
    intro n0 n0n'; simp only [Finset.mem_range] at n0n'
    have n0n := Nat.le_of_lt_succ n0n'
    rw [Nat.sub_sub_self n0n, min_eq_left n0n]
  rwa [←e]

/-- Osgood's lemma on a `closedBall`: `f` is jointly analytic -/
theorem osgood_h (h : Separate f c0 c1 r b s) :
    HasFPowerSeriesOnBall f (series2 h) (c0, c1) (ENNReal.ofReal r) :=
  { r_le := cauchy2_radius h
    r_pos := by simp; exact h.rp
    hasSum := by
      simp only [Metric.emetric_ball, Metric.mem_ball, dist_zero_right, Prod.forall]
      intro w0 w1 wr; rw [Prod.norm_def] at wr
      simp only [Complex.norm_eq_abs, ge_iff_le, max_lt_iff] at wr
      have w0m : w0 ∈ ball (0 : ℂ) r := by simp; exact wr.left
      have w1m : w1 ∈ ball (0 : ℂ) r := by simp; exact wr.right
      exact cauchy2_hasSum h w0m w1m }

end osgood

/-- Osgood's lemma: if `f` is separately analytic on an open set,
    it is jointly analytic on that set -/
theorem osgood {E : Type} {f : ℂ × ℂ → E} {s : Set (ℂ × ℂ)} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (o : IsOpen s) (fc : ContinuousOn f s)
    (fa0 : ∀ z0 z1 : ℂ, (z0, z1) ∈ s → AnalyticAt ℂ (fun z0 ↦ f (z0, z1)) z0)
    (fa1 : ∀ z0 z1 : ℂ, (z0, z1) ∈ s → AnalyticAt ℂ (fun z1 ↦ f (z0, z1)) z1) :
    AnalyticOn ℂ f s := by
  intro c cs
  rcases Metric.isOpen_iff.mp o c cs with ⟨r, rp, rs⟩
  have rs : closedBall c (r / 2) ⊆ s := le_trans (Metric.closedBall_subset_ball (by linarith)) rs
  rcases (ContinuousOn.mono fc rs).norm.bounded (isCompact_closedBall _ _) with ⟨b, bp, bh⟩
  have h : Separate f c.fst c.snd (r / 2) b s :=
    { rp := by linarith
      so := o
      rs := rs
      fc := fc
      fa0 := fa0 _ _
      fa1 := fa1 _ _
      bp := bp
      fb := fun {z0 z1} z0m z1m ↦ bh (z0, z1)
        (spheres_subset_closedBall (Set.mk_mem_prod z0m z1m)) }
  have a := (osgood_h h).analyticAt
  simpa only [Prod.mk.eta] using a

/-- Osgood's lemma at a point: if `f` is separately analytic near a point,
    it is jointly analytic there -/
theorem osgood_at' {E : Type} {f : ℂ × ℂ → E} {c : ℂ × ℂ} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (h : ∀ᶠ x : ℂ × ℂ in 𝓝 c, ContinuousAt f x ∧
      AnalyticAt ℂ (fun z ↦ f (z, x.2)) x.1 ∧ AnalyticAt ℂ (fun z ↦ f (x.1, z)) x.2) :
    AnalyticAt ℂ f c := by
  rcases eventually_nhds_iff.mp h with ⟨s, h, o, cs⟩
  exact osgood o (fun _ m ↦ (h _ m).1.continuousWithinAt) (fun _ _ m ↦ (h _ m).2.1)
    (fun _ _ m ↦ (h _ m).2.2) c cs

/-- Osgood's lemma at a point: if `f` is separately analytic near a point,
    it is jointly analytic there -/
theorem osgood_at {E : Type} {f : ℂ × ℂ → E} {c : ℂ × ℂ} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (fc : ∀ᶠ x in 𝓝 c, ContinuousAt f x)
    (fa0 : ∀ᶠ x : ℂ × ℂ in 𝓝 c, AnalyticAt ℂ (fun z ↦ f (z, x.2)) x.1)
    (fa1 : ∀ᶠ x : ℂ × ℂ in 𝓝 c, AnalyticAt ℂ (fun z ↦ f (x.1, z)) x.2) : AnalyticAt ℂ f c :=
  osgood_at' (fc.and (fa0.and fa1))
