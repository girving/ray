import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Ray.Analytic.Holomorphic
import Ray.Koebe.WindArea
import Ray.Manifold.GlobalInverse
import Ray.Misc.Annuli
import Ray.Misc.Cobounded
import Ray.Misc.Deriv
import Ray.Misc.Linear
import Ray.Misc.Subexp

/-!
## Grönwall's area theorem

Let `g : ℂ → ℂ` be analytic and injective for `1 < ‖z‖`, with `g z = z + b 1 / z + b 2 / z^2 + ...`.
Then the complement of the image of the `r < ‖z‖` annulus has area

  `π * (r ^ 2 - ∑ n ≥ 1, n * |b n| ^ 2 / r ^ (2 * n))`

Letting `r → 1`, nonnegativity of the area gives

  `∑ n ≥ 1, n * |b n| ^ 2 ≤ 1`

This is the key step in the proof of the Koebe quarter theorem, following
https://en.wikipedia.org/wiki/Koebe_quarter_theorem.

To avoid dealing with power series at infinity, we state the theorem in terms of `f z = z * g z⁻¹`,
which is analytic for `‖z‖ < 1` with `f 0 = 1`, `deriv f 0 = 0`.

Since Mathlib is missing the general formula for area within a curve, we prove that complement
image is star-shaped for sufficiently large `r`, then use the machinery in `WindArea.lean`.
-/

open Bornology (cobounded)
open Classical
open Complex (abs arg exp I)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped ComplexConjugate ContDiff Topology NNReal Real
noncomputable section

variable {α β ι : Type}
variable {f : ℂ → ℂ}

/-!
### Preliminaries
-/

/-- Properties of `f` as discussed above -/
structure Gronwall (f : ℂ → ℂ) : Prop where
  fa : AnalyticOnNhd ℂ f (ball 0 1)
  f0 : f 0 = 1
  df0 : HasDerivAt f 0 0
  inj' : InjOn (fun w ↦ w * f w⁻¹) {w : ℂ | 1 < ‖w‖}

namespace Gronwall

def g (_ : Gronwall f) (w : ℂ) : ℂ := w * f w⁻¹

/-- `g` is analytic for `1 < ‖z‖` -/
lemma ga (i : Gronwall f) {z : ℂ} (z1 : 1 < ‖z‖) : AnalyticAt ℂ i.g z := by
  refine analyticAt_id.mul ((i.fa _ (by simp; bound)).comp (analyticAt_inv ?_))
  rw [← norm_pos_iff]; linarith

/-- `g` is analytic for `1 < ‖z‖` -/
lemma ga' (i : Gronwall f) : AnalyticOnNhd ℂ i.g (norm_Ioi 1) := fun _ z1 ↦ i.ga z1

/-- `g` is injective on `norm_Ioi 1` -/
lemma inj (i : Gronwall f) : InjOn i.g (norm_Ioi 1) := i.inj'

/-- Power series coefficients of `f` -/
def coeff (_ : Gronwall f) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / n.factorial

/-- The power series of `f` over the whole unit ball -/
lemma hasFPowerSeriesOnBall (i : Gronwall f) :
    HasFPowerSeriesOnBall f (.ofScalars ℂ i.coeff) 0 1 := by
  have a0 := (i.fa 0 (by simp)).hasFPowerSeriesAt
  obtain ⟨p,a1⟩ := (analyticOnNhd_ball_iff_hasFPowerSeriesOnBall (by norm_num)).mp
    (Metric.emetric_ball (α := ℂ) ▸ i.fa)
  have pe := a0.eq_formalMultilinearSeries a1.hasFPowerSeriesAt
  unfold coeff
  simp only [a0.eq_formalMultilinearSeries a1.hasFPowerSeriesAt] at a0 ⊢
  simpa using a1

/-- `coeff` decays geometrically as fast as we need to do our power series sums -/
lemma norm_coeff_le (i : Gronwall f) {r : ℝ} (r0 : 0 < r) (r1 : r < 1) :
    ∃ a ∈ Set.Ioo 0 1, ∃ C : ℝ, 0 < C ∧ ∀ n, ‖i.coeff n‖ ≤ C * (a / r) ^ n := by
  have le := i.hasFPowerSeriesOnBall.r_le
  set r' : ℝ≥0 := ⟨r, r0.le⟩
  have r'1 : r' < 1 := by rw [← NNReal.mk_one]; simp only [r', ← NNReal.coe_lt_coe]; simp [r1]
  have r'r : r' < (FormalMultilinearSeries.ofScalars ℂ i.coeff).radius :=
    lt_of_lt_of_le (by simp only [ENNReal.coe_lt_one_iff, r'1]) le
  obtain ⟨a,am,C,C0,le⟩ :=
    (FormalMultilinearSeries.ofScalars ℂ i.coeff).norm_mul_pow_le_mul_pow_of_lt_radius r'r
  refine ⟨a, am, C, C0, fun n ↦ ?_⟩
  specialize le n
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by bound)]
  simpa [r'] using le

-- `coeff` decays geometrically, large `r` version
def norm_prop (i : Gronwall f) (r : ℝ) : Prop :=
  ∃ ac : ℝ × ℝ, ac.1 ∈ Set.Ioo 0 1 ∧ 0 < ac.2 ∧ ∀ n, ‖i.coeff n‖ ≤ ac.2 * (ac.1 * r) ^ n
lemma eventually_norm_prop (i : Gronwall f) : ∀ᶠ r in atTop, i.norm_prop r := by
  filter_upwards [Filter.eventually_gt_atTop 1] with r r1
  obtain ⟨a,am,C,C0,le⟩ := i.norm_coeff_le (r := r⁻¹) (by bound) (by bound)
  exact ⟨⟨a, C⟩, am, C0, fun n ↦ div_inv_eq_mul a r ▸ le n⟩
def a (i : Gronwall f) (r : ℝ) : ℝ := if p : i.norm_prop r then (choose p).1 else 1
def C (i : Gronwall f) (r : ℝ) : ℝ := if p : i.norm_prop r then (choose p).2 else 1
lemma ac_prop (i : Gronwall f) : ∀ᶠ r in atTop, i.a r ∈ Ioo 0 1 ∧ 0 < i.C r ∧
    ∀ n, ‖i.coeff n‖ ≤ i.C r * (i.a r * r) ^ n := by
  filter_upwards [i.eventually_norm_prop] with r p
  simp only [a, p, ↓reduceDIte, C]
  exact Classical.choose_spec p

/-- Eventually `f` is large near 0 -/
lemma f_large_near_one (i : Gronwall f) (b : ℝ) (b1 : b < 1) : ∀ᶠ z in 𝓝 0, b < ‖f z‖ := by
  apply continuousAt_const.eventually_lt
  · exact (i.fa _ (by simp)).continuousAt.norm
  · simpa only [i.f0, norm_one]

/-- `(f z - 1) / z^2` -/
def h (_ : Gronwall f) : ℂ → ℂ :=
  dslope (dslope f 0) 0

/-- `h` is analytic -/
lemma ha (i : Gronwall f) : AnalyticOnNhd ℂ i.h (ball 0 1) := by
  have n : ball (0 : ℂ) 1 ∈ 𝓝 0 := Metric.ball_mem_nhds 0 (by bound)
  simp only [h, Complex.analyticOnNhd_iff_differentiableOn isOpen_ball,
    Complex.differentiableOn_dslope n]
  exact i.fa.differentiableOn

/-- `f z = 1 + z^2 * h z` -/
lemma f_eq (i : Gronwall f) (z : ℂ) : f z = 1 + z^2 * i.h z := by
  by_cases z0 : z = 0
  · simp [z0, i.f0]
  · simp only [h, dslope_of_ne _ z0, slope, sub_zero, i.f0, vsub_eq_sub, smul_eq_mul, dslope_same,
      i.df0.deriv, ← mul_assoc]
    field_simp [z0]
    ring

/-!
### Injectivity of `z ↦ snap (g z)` on large circles

We derive injectivity via

  `snap (g z) = snap (g w)`
  `snap (z * f z⁻¹) = snap (w * f w⁻¹)`
  `z / w = snap (f w⁻¹ / f z⁻¹)`

and use flatness of `ff (w,z) = snap (f w / f z)` near `0` to deduce `z = w`.
-/

/-- `f⁻¹` is flat at `0` -/
lemma f_inv_flat (i : Gronwall f) : HasDerivAt (fun z ↦ (f z)⁻¹) 0 0 := by
  have e : 0 = -0 / f 0 ^ 2 := by simp
  nth_rw 1 [e]
  exact i.df0.inv (by simp [i.f0])

/-- `f x` is eventually nonzero near 0 -/
lemma f0' (i : Gronwall f) : ∀ᶠ z in 𝓝 0, f z ≠ 0 := by
  apply ContinuousAt.eventually_ne
  · exact (i.fa _ (by simp)).continuousAt
  · simp only [i.f0, ne_eq, one_ne_zero, not_false_eq_true]

/-- `snap (f w / f z)` is useful in proving injectivity of `g` -/
def ff (_ : Gronwall f) (p : ℂ × ℂ) : ℂ := (snap (f p.2 / f p.1)).val

@[simp] lemma ff_self (i : Gronwall f) (z : ℂ) : i.ff (z,z) = 1 := by
  by_cases n : f z = 0
  all_goals simp [ff, n]

lemma analyticAt_ff (i : Gronwall f) : AnalyticAt ℝ i.ff 0 := by
  apply AnalyticAt.snap
  · refine AnalyticAt.div ?_ ?_ ?_
    · exact ((i.fa _ (by simp)).comp analyticAt_snd).restrictScalars
    · exact ((i.fa _ (by simp)).comp analyticAt_fst).restrictScalars
    · simp [i.f0]
  · simp [i.f0]

-- Cache this since inferring it is timing out
instance Gromwall.fderiv_smul_zero_class : SMulZeroClass ℂ (ℂ × ℂ →L[ℂ] ℂ) := by infer_instance

/-- `f w / f z` is flat at `0` -/
lemma ff_flat (i : Gronwall f) : HasFDerivAt i.ff (0 : ℂ × ℂ →L[ℝ] ℂ) (0 : ℂ × ℂ) := by
  unfold ff
  refine hasFDeriv_zero_of_comp_right (f := fun z ↦ (snap z).val) (y := 1)
    (analyticAt_snap (by simp)).differentiableAt ?_ (by simp [i.f0])
  simp only [div_eq_inv_mul]
  have e : (0 : ℂ × ℂ →L[ℝ] ℂ) = (f (0 : ℂ × ℂ).1)⁻¹ • ((0 : ℂ →L[ℝ] ℂ).comp
      (ContinuousLinearMap.snd ℝ ℂ ℂ)) + (f (0 : ℂ × ℂ).2) • ((0 : ℂ →L[ℝ] ℂ).comp
      (ContinuousLinearMap.fst ℝ ℂ ℂ)) := by
    simp only [Prod.fst_zero, i.f0, inv_one, ContinuousLinearMap.zero_comp, one_smul, Prod.snd_zero,
      add_zero]
  rw [e]
  have df := i.df0.hasFDerivAt.restrictScalars ℝ
  have dfi := i.f_inv_flat.hasFDerivAt.restrictScalars ℝ
  simp only [ContinuousLinearMap.smulRight_zero, ContinuousLinearMap.restrictScalars_zero] at df dfi
  refine HasFDerivAt.mul (c := fun p : ℂ × ℂ ↦ (f p.1)⁻¹) (d := fun p : ℂ × ℂ ↦ f p.2)
    (𝕜 := ℝ) (E := ℂ × ℂ) (𝔸' := ℂ)
    ?_ ?_
  · exact dfi.comp_of_eq _ hasFDerivAt_fst (by simp)
  · exact df.comp_of_eq _ hasFDerivAt_snd (by simp)

/-- `f w / f z` is arbitrarily Lipschitz near `0` -/
lemma ff_lipschitz (i : Gronwall f) {L : ℝ≥0} (L0 : 0 < L) :
    ∀ᶠ r in 𝓝[>] 0, LipschitzOnWith L i.ff (closedBall 0 r) := by
  have df : ∀ᶠ p in 𝓝 0, DifferentiableAt ℝ i.ff p := by
    filter_upwards [i.analyticAt_ff.eventually_analyticAt]
    intro p a
    exact a.differentiableAt
  have dL : ∀ᶠ p in 𝓝 0, ‖fderiv ℝ i.ff p‖₊ ≤ L := by
    refine .mono ?_ (fun _ ↦ le_of_lt)
    apply ContinuousAt.eventually_lt
    · apply ContinuousAt.nnnorm
      exact ((i.analyticAt_ff.contDiffAt (n := ω)).fderiv_right (m := ω) (by simp)).continuousAt
    · exact continuousAt_const
    · simpa only [i.ff_flat.fderiv, nnnorm_zero]
  simp only [← eventually_nhdsGT_zero_closedBall_iff_nhds] at df dL
  filter_upwards [df, dL] with r df dL
  exact Convex.lipschitzOnWith_of_nnnorm_fderiv_le df dL (convex_closedBall _ _)

/-- `g` is nonzero for large `r` -/
lemma g0 (i : Gronwall f) : ∀ᶠ r in atTop, ∀ z ∈ sphere 0 r, i.g z ≠ 0 := by
  rw [eventually_atTop_iff_nhdsGT_zero]
  filter_upwards [eventually_nhdsGT_zero_sphere_of_nhds i.f0', eventually_mem_nhdsWithin]
    with r f0 r0 z zr
  simp only [mem_sphere_iff_norm, sub_zero, mem_Ioi] at zr r0
  have z0 : z ≠ 0 := by rw [ne_eq, ← norm_eq_zero, zr]; apply ne_of_gt; bound
  simp only [g, ne_eq, mul_eq_zero, z0, false_or]
  apply f0
  simp only [mem_sphere_iff_norm, sub_zero, norm_inv, zr, inv_inv]

/-- `z ↦ snap (i.g z)` is injective for large `r` -/
lemma g_inj (i : Gronwall f) : ∀ᶠ r in atTop, InjOn (fun z ↦ snap (i.g z)) (sphere 0 r) := by
  rw [eventually_atTop_iff_nhdsGT_zero]
  have f0 := eventually_nhdsGT_zero_sphere_of_nhds i.f0'
  filter_upwards [i.ff_lipschitz (L := 1) (by norm_num), eventually_mem_nhdsWithin, f0,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (b := 1) (by norm_num))]
    with r L r0 f0 r1 z zr w wr e
  simp only [mem_sphere_iff_norm, sub_zero, mem_Ioi] at zr wr r0 f0
  have ri0 : 0 < r⁻¹ := by bound
  have z0 : z ≠ 0 := by rw [ne_eq, ← norm_eq_zero]; linarith
  have w0 : w ≠ 0 := by rw [ne_eq, ← norm_eq_zero]; linarith
  have fz0 : f z⁻¹ ≠ 0 := by apply f0; simp only [norm_inv, zr, inv_inv]
  have fw0 : f w⁻¹ ≠ 0 := by apply f0; simp only [norm_inv, wr, inv_inv]
  simp only [g, ne_eq, z0, not_false_eq_true, fz0, snap_mul, w0, fw0] at e
  have wz : (snap (w / z)).val = z⁻¹ / w⁻¹ := by
    simp only [ne_eq, w0, not_false_eq_true, z0, snap_div, Circle.coe_div, coe_snap, wr,
      Complex.ofReal_inv, div_inv_eq_mul, zr]
    field_simp [r0.ne']
    ring
  rw [mul_comm, ← div_eq_div_iff_mul_eq_mul, ← snap_div fz0 fw0, ← snap_div w0 z0, Circle.ext_iff,
    wz] at e
  generalize ha : z⁻¹ = a at e fz0
  generalize hb : w⁻¹ = b at e fw0
  have ar : ‖a‖ = r := by simp only [← ha, norm_inv, zr, inv_inv]
  have br : ‖b‖ = r := by simp only [← hb, norm_inv, wr, inv_inv]
  suffices a = b by rwa [← inv_inj, ha, hb]
  clear z w zr wr z0 w0 wz ha hb
  have b0 : b ≠ 0 := by rw [ne_eq, ← norm_eq_zero]; linarith
  rw [(by rfl : (snap (f a / f b)).val = i.ff (b,a))] at e
  -- The rest follows from
  --   `‖i.ff (b,a) - 1‖ ≤ ‖b - a‖`
  --   `‖a / b - 1‖ = ‖a - b‖ / ‖b‖ = ‖a - b‖ / r > ‖a - b‖`
  have le : ‖a - b‖ / r ≤ ‖b - a‖ := by
    calc ‖a - b‖ / r
      _ = ‖a / b - 1‖ := by simp only [br, norm_div, div_sub_one b0]
      _ = ‖i.ff (b,a) - i.ff (a,a)‖ := by rw [e, ff_self]
      _ ≤ 1 * ‖(b,a) - (a,a)‖ := by apply L.norm_sub_le; all_goals simp [ar, br]
      _ = ‖b - a‖ := by simp
  contrapose le
  simp only [norm_sub_rev b, not_le]
  rw [lt_div_iff₀ r0]
  exact mul_lt_of_lt_one_right (norm_sub_pos_iff.mpr le) r1

/-!
### Topology of the inner and outer regions
-/

/-- The region outside a `g` cycle -/
def outer (i : Gronwall f) (r : ℝ) : Set ℂ := i.g '' norm_Ioi r

/-- The complement region inside a `g` cycle -/
def disk (i : Gronwall f) (r : ℝ) : Set ℂ := (i.outer r)ᶜ

/-- The outer region is preconnected -/
lemma isPreconnected_outer (i : Gronwall f) : ∀ᶠ r in atTop, IsPreconnected (i.outer r) := by
  filter_upwards [Filter.eventually_gt_atTop 1] with r r1
  apply isPreconnected_norm_Ioi.image
  intro z m
  exact (i.ga (lt_trans r1 m)).continuousAt.continuousWithinAt

/-- `g` is an open map -/
lemma g_open (i : Gronwall f) : ∀ s ⊆ norm_Ioi 1, IsOpen s → IsOpen (i.g '' s) := by
  rcases i.ga'.is_constant_or_isOpen isPreconnected_norm_Ioi with c | o
  · obtain ⟨w,e⟩ := c
    have e : i.g 2 = i.g 3 := by rw [e, e]; all_goals simp [norm_Ioi]
    rw [i.inj.eq_iff] at e
    · norm_num at e
    · simp [norm_Ioi]
    · simp [norm_Ioi]
  · exact o

/-- The outer region is open -/
lemma isOpen_outer (i : Gronwall f) {r : ℝ} (r1 : 1 < r) : IsOpen (i.outer r) := by
  refine i.g_open _ ?_ isOpen_norm_Ioi
  intro z m
  simp only [norm_Ioi, mem_setOf_eq] at m ⊢
  linarith

-- DO NOT SUBMIT: Do I need this?
/-- Be lazy and use a global inverse hammer to make the following easier -/
lemma exists_inv (i : Gronwall f) : ∃ gi : ℂ → ℂ,
    AnalyticOnNhd ℂ gi (i.g '' norm_Ioi 1) ∧ ∀ z, z ∈ norm_Ioi 1 → gi (i.g z) = z :=
  global_complex_inverse_fun_open'' i.ga' i.inj isOpen_norm_Ioi
def gi (i : Gronwall f) : ℂ → ℂ := choose i.exists_inv
lemma gia (i : Gronwall f) : AnalyticOnNhd ℂ i.gi (i.g '' norm_Ioi 1) :=
  (choose_spec i.exists_inv).1
lemma gi_g (i : Gronwall f) {z : ℂ} (m : z ∈ norm_Ioi 1) : i.gi (i.g z) = z :=
  (choose_spec i.exists_inv).2 z m

-- DO NOT SUBMIT: Do I need this?
/-- `g` and `gi` as a partial homeomorph -/
def gg (i : Gronwall f) : PartialHomeomorph ℂ ℂ where
  toFun := i.g
  invFun := i.gi
  source := norm_Ioi 1
  target := i.g '' norm_Ioi 1
  map_source' := by aesop
  map_target' := by intro x ⟨y,m,e⟩; simp only [← e, i.gi_g m, m]
  left_inv' := by intro x m; simp only [i.gi_g m]
  right_inv' := by intro x ⟨y,m,e⟩; simp only [← e, i.gi_g m]
  open_source := isOpen_norm_Ioi
  open_target := i.g_open _ (by rfl) isOpen_norm_Ioi
  continuousOn_toFun := i.ga'.continuousOn
  continuousOn_invFun := i.gia.continuousOn

/-- `g` tends to infinity at infinity -/
lemma g_tendsto (i : Gronwall f) : Tendsto i.g (cobounded ℂ) (cobounded ℂ) := by
  unfold g
  have f0 := (i.fa 0 (by simp)).continuousAt
  simp only [ContinuousAt, i.f0, Metric.tendsto_nhds_nhds] at f0
  obtain ⟨s,s0,sh⟩ := f0 (1/2) (by simp)
  simp only [dist_zero_right, Complex.dist_eq, one_div] at sh
  simp only [tendsto_cobounded, Complex.norm_mul, hasBasis_cobounded_norm_lt.eventually_iff,
    mem_setOf_eq, true_and]
  intro r
  use max (2 * r) s⁻¹
  intro z lt
  simp only [sup_lt_iff] at lt
  have zs := inv_lt_of_inv_lt₀ (by bound) lt.2
  specialize @sh z⁻¹ (by simpa)
  have f2 : 2⁻¹ ≤ ‖f z⁻¹‖ := by
    calc ‖f z⁻¹‖
      _ = ‖1 + (f z⁻¹ - 1)‖ := by ring_nf
      _ ≥ ‖(1 : ℂ)‖ - ‖f z⁻¹ - 1‖ := by bound
      _ ≥ ‖(1 : ℂ)‖ - 2⁻¹ := by bound
      _ = 2⁻¹ := by norm_num
  rw [(by ring_nf : r = 2 * r * 2⁻¹)]
  exact mul_lt_mul lt.1 f2 (by norm_num) (norm_nonneg _)

/-- The outer region has the expected closure.
This proof is atrocious, but I'm tired of it and thus giving up on elegance. -/
lemma closure_outer (i : Gronwall f) : ∀ᶠ r in atTop, closure (i.outer r) = i.g '' norm_Ici r := by
  filter_upwards [Filter.eventually_gt_atTop 1] with r r1
  apply subset_antisymm
  · intro w m
    simp only [outer, mem_closure_iff_frequently, mem_image, norm_Ioi, norm_Ici, mem_setOf_eq,
      Filter.frequently_iff_seq_forall, Classical.skolem] at m ⊢
    obtain ⟨s,st,z,m⟩ := m
    rcases tendsto_cobounded_or_mapClusterPt z atTop with t | ⟨a,c⟩
    · have zt := i.g_tendsto.comp t
      replace e : ∀ n, i.g (z n) = s n := fun n ↦ (m n).2
      contrapose e
      simp only [Function.comp_def, not_forall] at zt ⊢
      have large := zt.eventually (eventually_cobounded_le_norm (1 + 2 * ‖w‖))
      have small := st.eventually (eventually_norm_sub_lt (x₀ := w) (ε := 1 + ‖w‖) (by positivity))
      obtain ⟨n,le,lt⟩ := (large.and small).exists
      use n
      contrapose lt
      simp only [Decidable.not_not, not_lt] at lt le ⊢
      simp only [lt] at le
      calc ‖s n - w‖
        _ ≥ ‖s n‖ - ‖w‖ := by bound
        _ ≥ 1 + 2 * ‖w‖ - ‖w‖ := by bound
        _ = 1 + ‖w‖ := by ring
    · use a
      simp only [Metric.nhds_basis_ball.mapClusterPt_iff_frequently] at c
      have ra : r ≤ ‖a‖ := by
        refine le_of_forall_pos_lt_add fun e e0 ↦ ?_
        obtain ⟨n,za⟩ := (c e e0).exists
        calc ‖a‖ + e
          _ = ‖z n - (z n - a)‖ + e := by ring_nf
          _ ≥ ‖z n‖ - ‖z n - a‖ + e := by bound
          _ > ‖z n‖ - e + e := by bound
          _ = ‖z n‖ := by ring
          _ ≥ r := by bound [(m n).1]
      refine ⟨ra, ?_⟩
      refine eq_of_forall_dist_le fun e e0 ↦ ?_
      obtain ⟨d,d0,dg⟩ := Metric.continuousAt_iff.mp ((i.ga (z := a) (by order)).continuousAt) (e/2)
        (by bound)
      obtain ⟨n,sw,za⟩ := ((Metric.tendsto_nhds.mp st (e/2) (by bound)).and_frequently
        (c d d0)).exists
      specialize @dg (z n) (by simpa using za)
      calc dist (i.g a) w
        _ ≤ dist (i.g a) (i.g (z n)) + dist (i.g (z n)) w := by bound
        _ = dist (i.g (z n)) (i.g a) + dist (s n) w := by rw [dist_comm, (m _).2]
        _ ≤ e/2 + e/2 := by bound
        _ = e := by ring
  · rw [← closure_norm_Ioi]
    refine ContinuousOn.image_closure (i.ga'.continuousOn.mono ?_)
    simp only [closure_norm_Ioi, r1, norm_Ici_subset_norm_Ioi]

/-- The outer region has the expected frontier -/
lemma frontier_outer (i : Gronwall f) : ∀ᶠ r in atTop,
    frontier (i.outer r) = i.g '' sphere 0 r := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.closure_outer] with r r1 close
  rw [frontier, (i.isOpen_outer r1).interior_eq, close, outer,
    ← (i.inj.mono (norm_Ici_subset_norm_Ioi r1)).image_diff_subset norm_Ioi_subset_norm_Ici,
    norm_Ici_diff_norm_Ioi]

/-!
### Area within large radii

We show that `g` satisfies the `WindDiff` conditions for large `r`, then use `WindDiff.volume_eq`.
-/

/-- `g` as a circle map -/
def gc (i : Gronwall f) (r : ℝ) : Circle → ℂˣ := fun z ↦
  Units.mk1 (i.g (r * z.val))

/-- `gc` eventually winds -/
lemma wind (i : Gronwall f) : ∀ᶠ r in atTop, WindDiff (i.gc r) := by
  filter_upwards [i.g_inj, i.g0, Filter.eventually_gt_atTop 1] with r inj g0 r1
  have r0 : 0 < r := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    refine (Units.continuousAt_mk1 ?_).comp ?_
    · apply g0; simp [r0.le]
    · exact (i.ga (by simp [abs_of_pos r0, r1])).continuousAt.comp (by fun_prop)
  · intro x y e
    simp only [gc, Units.snap_mk1] at e
    simpa only [mul_eq_mul_left_iff, SetLike.coe_eq_coe, Complex.ofReal_eq_zero, r0.ne',
      or_false] using (inj.eq_iff (by simp [r0.le]) (by simp [r0.le])).mp e
  · have e : ∀ t, (i.gc r (Circle.exp t)).val = i.g (circleMap 0 r t) := by
      intro t
      rw [gc, Units.val_mk1]
      · simp [circleMap]
      · apply g0; simp [r0.le]
    intro t
    refine DifferentiableAt.congr_of_eventuallyEq ?_ (.of_forall e)
    apply ((i.ga ?_).differentiableAt.restrictScalars _).comp
    · apply differentiable_circleMap
    · simp [abs_of_pos r0, r1]

lemma gc_exp (i : Gronwall f) : ∀ᶠ r in atTop, ∀ t,
    (i.gc r (Circle.exp t)).val = i.g (circleMap 0 r t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.g0, i.wind] with r r1 g0 w t
  rw [gc, Units.val_mk1]
  · simp [circleMap]
  · apply g0; simp; linarith

/-- `w.fe` is (real) analytic -/
lemma analyticAt_fe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ (w : WindDiff (i.gc r)), ∀ t,
    AnalyticAt ℝ w.fe t := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.g0, i.gc_exp] with r r1 g0 gc_exp w t
  have r0 : 0 < r := by linarith
  unfold WindDiff.fe
  simp only [gc_exp]
  refine (i.ga ?_).restrictScalars.comp ?_
  · simp [abs_of_pos r0, r1]
  · apply analyticOnNhd_circleMap; trivial

/-- Eventually, the two notions of spheres coincide -/
lemma sphere_eq (i : Gronwall f) : ∀ᶠ r in atTop,
    i.g '' sphere 0 r = range (fun z ↦ (i.gc r z).val) := by
  filter_upwards [i.g0, Filter.eventually_gt_atTop 0] with r g0 r0
  ext w
  simp only [mem_image, mem_sphere_iff_norm, sub_zero, mem_range, gc]
  constructor
  · intro ⟨z,zr,e⟩
    have z0 : z ≠ 0 := by rw [ne_eq, ← norm_eq_zero]; linarith
    refine ⟨snap z, ?_⟩
    rw [Units.val_mk1]
    · simp [coe_snap, z0, zr, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr r0.ne'), e]
    · apply g0; simp [r0.le]
  · intro ⟨z,e⟩
    refine ⟨r * z.val, by simp [r0.le], ?_⟩
    rwa [Units.val_mk1] at e
    apply g0; simp [r0.le]

/-- Our two notions of outside (based on `g` and star-shaped extrapolation) match -/
lemma outer_eq_outer (i : Gronwall f) :
    ∀ᶠ r in atTop, ∀ w : Wind (i.gc r), i.outer r = w.outer := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.isPreconnected_outer, i.frontier_outer,
    i.sphere_eq] with r r1 c0 fo se w
  refine c0.eq_of_frontier_eq w.isPreconnected_outer (i.isOpen_outer r1) w.isOpen_outer ?_ ?_
  · simp only [fo, w.frontier_outer, w.sphere_eq, se]
  · obtain ⟨z,zo,zr⟩ := ((i.g_tendsto.eventually w.large_mem_outer).and
      (eventually_cobounded_lt_norm r)).exists
    exact ⟨i.g z, ⟨z, zr, rfl⟩, zo⟩

/-- Power series for `w.fe` -/
lemma hasSum_fe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    HasSum (fun n : ℕ ↦ i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)) (w.fe t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.gc_exp] with r r1 gc_exp w t
  have r0 : 0 < r := by linarith
  have ri0 : 0 < r⁻¹ := by bound
  have ri1 : r⁻¹ < 1 := by bound
  have sum : ∀ t, HasSum (fun n ↦ i.coeff n * circleMap 0 r⁻¹ t ^ n) (f (circleMap 0 r⁻¹ t)) := by
    intro t
    have sum := i.hasFPowerSeriesOnBall.hasSum (y := circleMap 0 r⁻¹ t)
      (by simp [← ofReal_norm, abs_of_pos ri0, ri1])
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm, zero_add, mul_pow, smul_eq_mul,
      ← mul_assoc, zero_add, Complex.ofReal_inv] using sum
  have pow : ∀ n : ℕ, circleMap 0 r t * circleMap 0 r⁻¹ (-t) ^ n =
      circleMap 0 r t ^ (1 - n : ℤ) := by
    intro n
    rw [zpow_sub₀, zpow_one, zpow_natCast, ← circleMap_zero_inv, inv_pow, div_eq_mul_inv]
    simp [r0.ne']
  rw [WindDiff.fe, gc_exp, g, circleMap_zero_inv]
  replace sum := (sum (-t)).mul_left (circleMap 0 r t)
  simp only [← mul_assoc, mul_comm _ (i.coeff _)] at sum
  simp only [mul_assoc, pow] at sum
  exact sum

-- Power series bound lemmas
def uf (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ := i.C r * r * i.a r ^ n
def udf (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ := i.C r * r * (n + 1) * i.a r ^ n
lemma summable_uf (i : Gronwall f) : ∀ᶠ r in atTop, Summable (i.uf r) := by
  filter_upwards [i.ac_prop] with r ⟨⟨a0,a1⟩,C0,_⟩
  exact summable_subexp_mul_pow a0 a1
lemma summable_udf (i : Gronwall f) : ∀ᶠ r in atTop, Summable (i.udf r) := by
  filter_upwards [i.summable_uf, i.ac_prop] with r suf ⟨⟨a0,a1⟩,C0,_⟩
  exact summable_subexp_mul_pow a0 a1
lemma le_uf (i : Gronwall f) : ∀ᶠ r in atTop, ∀ n t,
    ‖i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)‖ ≤ i.uf r n := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.ac_prop] with r r1 ⟨⟨a0,a1⟩,C0,cle⟩ n t
  have r0 : 0 < r := by linarith
  simp only [Complex.norm_mul, norm_zpow, norm_circleMap_zero, abs_of_pos r0, zpow_sub₀ r0.ne',
    zpow_one, zpow_natCast, uf]
  calc ‖i.coeff n‖ * (r / r ^ n)
    _ ≤ i.C r * (i.a r * r) ^ n * (r / r ^ n) := by bound [cle n]
    _ = i.C r * r * i.a r ^ n * (r ^ n * (r ^ n)⁻¹) := by rw [← inv_pow]; ring
    _ ≤ i.C r * r * i.a r ^ n := by rw [mul_inv_cancel₀ (by positivity), mul_one]
lemma le_udf (i : Gronwall f) : ∀ᶠ r in atTop, ∀ (n : ℕ) t,
    ‖(1 - n : ℤ) * I * i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)‖ ≤ i.udf r n := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.ac_prop] with r r1 ⟨⟨a0,a1⟩,C0,cle⟩ n t
  have r0 : 0 < r := by linarith
  have nb : ‖(1 - n : ℂ)‖ ≤ n + 1 := by induction' n with n; all_goals simp; try linarith
  simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, zpow_natCast, Complex.norm_mul, mul_one,
    norm_circleMap_zero, abs_of_pos r0, Complex.norm_I, udf, norm_zpow, zpow_sub₀ r0.ne', zpow_one]
  calc ‖(1 - n : ℂ)‖ * ‖i.coeff n‖ * (r / r ^ n)
    _ ≤ (n + 1) * (i.C r * (i.a r * r) ^ n) * (r / r ^ n) := by bound [cle n]
    _ = i.C r * r * (n + 1) * i.a r ^ n * (r ^ n * (r ^ n)⁻¹) := by rw [← inv_pow]; ring
    _ ≤ i.C r * r * (n + 1) * i.a r ^ n := by rw [mul_inv_cancel₀ (by positivity), mul_one]

/-- Power series for the derivative `w.dfe` -/
lemma hasSum_dfe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    HasSum (fun n : ℕ ↦ (1 - n : ℤ) * I * i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)) (w.dfe t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.hasSum_fe, i.summable_uf, i.summable_udf, i.le_uf,
    i.le_udf] with r r1 sum suf sudf le_uf le_udf w t
  simp only [WindDiff.dfe]
  have c0 : ∀ {t}, circleMap 0 r t ≠ 0 := fun {t} ↦ circleMap_ne_center (by positivity)
  set f := fun (n : ℕ) t ↦ i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)
  set f' := fun (n : ℕ) t ↦ i.coeff n * ((1 - n : ℤ) * circleMap 0 r t ^ (1 - n - 1 : ℤ) *
    (circleMap 0 r t * I))
  have df : ∀ n t, HasDerivAt (f n) (f' n t) t := by
    intro n t
    simp only [f, f']
    apply HasDerivAt.const_mul
    exact (hasDerivAt_zpow (1 - n) (circleMap 0 r t) (.inl c0)).comp t (hasDerivAt_circleMap 0 r t)
  have hf : ∀ n t, f n t = i.coeff n * circleMap 0 r t ^ (1 - n : ℤ) := by intro n t; rfl
  have hf' : ∀ n t, f' n t = (1 - n : ℤ) * I * i.coeff n * circleMap 0 r t ^ (1 - n : ℤ) := by
    intro n t
    simp only [f', ← mul_assoc _ _ I, mul_assoc _ (_ ^ (_ : ℤ)) (circleMap _ _ _),
      ← zpow_add_one₀ c0]
    ring_nf
  have e : w.fe = fun t ↦ ∑' n, f n t := by ext t; exact (sum w t).tsum_eq.symm
  rw [e]
  simp only [← hf']
  have fu : ∀ n t, ‖f n t‖ ≤ i.uf r n := by intro n t; simp only [hf]; apply le_uf
  have f'v : ∀ n t, ‖f' n t‖ ≤ i.udf r n := by intro n t; simp only [hf']; apply le_udf
  rw [deriv_tsum_apply sudf (y₀ := t)]
  · simp only [(df _ _).deriv]
    exact (sudf.of_norm_bounded (fun n ↦ f'v n t)).hasSum
  · intro n t
    exact (df n t).differentiableAt
  · intro n t
    simp only [(df _ _).deriv, f'v]
  · exact suf.of_norm_bounded (fun n ↦ fu n t)

/-- `inner ℝ (w.fe t * I) (w.dfe t)` is eventually nonnegative -/
lemma inner_nonneg (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    0 ≤ inner ℝ (w.fe t * I) (w.dfe t) := by
  -- `deriv f 0 = 0`, and thus `‖deriv f z / f z‖ < 1` is small near `0`
  have dfc : ContinuousAt (fun z ↦ deriv f z / f z) 0 := by
    have a0 := i.fa 0 (by simp)
    have d0 := a0.deriv.div a0 (by simp [i.f0])
    exact d0.continuousAt
  obtain ⟨s,s0,dfs⟩ := Metric.continuousAt_iff.mp dfc 1 (by simp)
  simp only [dist_zero_right, i.df0.deriv, zero_div] at dfs
  -- Now choose sufficiently large `r`
  filter_upwards [Filter.eventually_gt_atTop (max 1 s⁻¹), i.g0, i.gc_exp] with r r1s g0 gc_exp w t
  simp only [sup_lt_iff] at r1s
  have r0 : 0 < r := by linarith
  have ri1 : r⁻¹ < 1 := by bound
  have rs : r⁻¹ < s := (inv_lt_comm₀ s0 r0).mp r1s.2
  simp only [WindDiff.fe, WindDiff.dfe]
  unfold WindDiff.fe
  -- Various derivatives
  set z := fun t ↦ circleMap 0 r t
  have hz : ∀ t, circleMap 0 r t = z t := by intro; rfl
  have circ : ∀ t, (r : ℂ) * Circle.exp t = z t := by intro; simp [circleMap, ← hz]
  have z0 : ∀ {t}, z t ≠ 0 := by intro t; simp [z, r0.ne']
  have fdz : ∀ t, DifferentiableAt ℂ f (z t)⁻¹ := by
    intro t; exact (i.fa (z t)⁻¹ (by simp [z, abs_of_pos r0, ri1])).differentiableAt
  have g0c : ∀ {t}, i.g (z t) ≠ 0 := by intro t; apply g0; simp [z, r0.le]
  simp only [gc_exp, hz]
  have dz : ∀ t, HasDerivAt z (z t * I) t := by
    intro t; simp only [← hz]; apply hasDerivAt_circleMap
  have dzi : ∀ t, HasDerivAt (fun t ↦ (z t)⁻¹) ((-(z t * I)) / (z t) ^ 2) t :=
    fun t ↦ (dz t).inv_tower z0
  simp only [pow_two, neg_div, mul_div_mul_comm, div_self z0, one_mul] at dzi
  have dg : HasDerivAt (fun t ↦ i.g (z t))
      (z t * I * f (z t)⁻¹ + z t * (deriv f (z t)⁻¹ * -(I / z t))) t :=
    (dz t).mul ((fdz t).hasDerivAt.comp t (dzi t))
  simp only [dg.deriv]
  -- Now a bunch of poorly organised algebra
  simp only [g, Complex.inner, add_mul, map_mul, Complex.conj_I]
  generalize hw : z t = w
  generalize hf : f w⁻¹ = fw
  generalize hd : deriv f w⁻¹ = dfw
  have nw : ‖w‖ = r := by simp [← hw, z, r0.le]
  have f0 : 0 < ‖fw‖ := by simp [g, ← hf, ← hw] at g0c ⊢; exact g0c.2
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  have e : w * fw * (starRingEnd ℂ) w * (starRingEnd ℂ) fw = ‖w‖^2 * ‖fw‖^2 := by
    simp only [mul_comm _ (conj w), ← mul_assoc, Complex.conj_mul']
    simp only [mul_assoc, Complex.mul_conj']
  simp only [e, Complex.mul_conj']
  simp only [mul_assoc, ← mul_sub, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.sub_re,
    Complex.ofReal_re]
  apply mul_nonneg (by positivity)
  rw [sub_nonneg]
  refine le_trans (Complex.re_le_norm _) ?_
  simp only [Complex.norm_mul, RCLike.norm_conj, norm_inv, nw, pow_two]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← div_eq_mul_inv, div_le_iff₀ r0, mul_comm _ r, ← div_le_iff₀ f0]
  specialize @dfs w⁻¹ (by simp [nw, rs])
  simp only [hd, hf, Complex.norm_div] at dfs
  linarith

/-- Terms for our 2D sum -/
def term (i : Gronwall f) (r : ℝ) (n m : ℕ) (t : ℝ) : ℂ :=
  (1 - n) * I * i.coeff n * conj (i.coeff m) * r ^ 2 / r ^ (n + m) * exp ((m - n) * t * I)

/-- `i.term` is continuous -/
@[fun_prop] lemma continuous_term (i : Gronwall f) (r : ℝ) (n m : ℕ) :
    Continuous (i.term r n m) := by
  unfold term
  fun_prop

-- Bounds on `i.term`
def ut (i : Gronwall f) (r : ℝ) (p : ℕ × ℕ) : ℝ := i.C r ^ 2 * (p.1 + 1) * r ^ 2 * i.a r ^ (p.1 + p.2)
lemma le_ut (i : Gronwall f) : ∀ᶠ r in atTop, ∀ n m t, ‖i.term r n m t‖ ≤ i.ut r (n,m) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.ac_prop] with r r1 ⟨⟨a0,a1⟩,C0,cle⟩ n m t
  simp only [term, ut]
  generalize i.a r = a at a0 a1 cle
  have r0 : 0 < r := by linarith
  have rn0 : ∀ {n}, r ^ n ≠ 0 := by intro n; positivity
  have nb : ‖(1 - n : ℂ)‖ ≤ n + 1 := by induction' n with n; all_goals simp; try linarith
  simp only [norm_mul, Complex.norm_div, Complex.norm_I, mul_one, RCLike.norm_conj, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos r0, Complex.norm_exp, Complex.mul_re,
    Complex.sub_re, Complex.natCast_re, Complex.ofReal_re, Complex.sub_im, Complex.natCast_im,
    sub_self, Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul,
    add_zero, Complex.I_im, Real.exp_zero]
  calc ‖(1 - n : ℂ)‖ * ‖i.coeff n‖ * ‖i.coeff m‖ * r ^ 2 / r ^ (n + m)
    _ ≤ (n + 1) * (i.C r * (a * r) ^ n) * (i.C r * (a * r) ^ m) * r ^ 2 / r ^ (n + m) := by bound
    _ = i.C r ^ 2 * (n + 1) * r ^ 2 * a ^ (n + m) * (r ^ (n + m) / r ^ (n + m)) := by ring
    _ = i.C r ^ 2 * (n + 1) * r ^ 2 * a ^ (n + m) := by simp only [div_self rn0, mul_one]
lemma summable_ut (i : Gronwall f) : ∀ᶠ r in atTop, Summable (i.ut r) := by
  filter_upwards [i.ac_prop] with r ⟨⟨a0,a1⟩,C0,cle⟩
  unfold ut
  generalize i.a r = a at a0 a1 cle
  simp only [← mul_assoc, mul_comm _ (r ^ 2)]
  simp only [mul_assoc _ (_ + _)]
  apply Summable.mul_left
  simp only [pow_add, ← mul_assoc]
  apply Summable.mul_of_nonneg (f := fun n : ℕ ↦ (n + 1) * a ^ n) (g := fun m ↦ a ^ m)
  · exact summable_subexp_mul_pow a0 a1
  · exact summable_geometric_of_lt_one a0.le a1
  · intro n; simp only [Pi.zero_apply]; bound
  · intro n; simp only [Pi.zero_apply]; bound

/-- Power series for `w.dfe t * conj (w.fe t)` -/
lemma hasSum_inner (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t : ℝ,
    HasSum (fun ((n : ℕ), (m : ℕ)) ↦ i.term r n m t) (w.dfe t * conj (w.fe t)) := by
  filter_upwards [i.hasSum_fe, i.hasSum_dfe, i.summable_uf, i.summable_udf, i.le_uf, i.le_udf,
    Filter.eventually_gt_atTop 1] with r sfe sdfe suf sudf le_uf le_udf r1 w t
  have c0 : ∀ {t}, circleMap 0 r t ≠ 0 := fun {t} ↦ circleMap_ne_center (by positivity)
  have snf := suf.of_nonneg_of_le (by bound) (fun n ↦ le_uf n t)
  have sndf := sudf.of_nonneg_of_le (by bound) (fun n ↦ le_udf n t)
  simp only [← Complex.norm_conj (_ * _)] at snf
  have sp := (summable_mul_of_summable_norm sndf snf).hasSum
  simp only [← tsum_mul_tsum_of_summable_norm sndf snf,
    (Complex.hasSum_conj'.mpr (sfe w t)).tsum_eq, (sdfe w t).tsum_eq] at sp
  apply sp.congr_fun
  intro ⟨n,m⟩
  simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast, zpow_sub₀ c0, zpow_one, zpow_natCast,
    map_mul, map_div₀, Complex.conj_circleMap, map_zero, map_pow, term]
  simp only [pow_add, div_eq_mul_inv, mul_inv_rev, sub_mul (m : ℂ), sub_mul (m * t : ℂ),
    Complex.exp_sub, circleMap, zero_add, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_neg,
    neg_mul, Complex.exp_neg, inv_pow, inv_inv, inv_mul_cancel₀ (Complex.exp_ne_zero _),
    mul_comm _ (exp (t * I)), mul_comm _ (exp (t * I))⁻¹, ← mul_assoc, pow_two, one_mul]
  ring

/-- Our integrals commute with our sum -/
lemma sum_integral_comm (i : Gronwall f) : ∀ᶠ r in atTop,
    HasSum (fun (p : ℕ × ℕ) ↦ ∫ t in -π..π, i.term r p.1 p.2 t)
      (∫ t in -π..π, ∑' (p : ℕ × ℕ), i.term r p.1 p.2 t) := by
  filter_upwards [i.le_ut, i.summable_ut, i.hasSum_inner, i.wind]
    with r le_ut summable_ut hasSum_inner w
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (bound := fun p t ↦ i.ut r p)
  · intro n; apply Continuous.aestronglyMeasurable; fun_prop
  · simp [le_ut]
  · simp [summable_ut]
  · apply intervalIntegrable_const; simp
  · simp [(hasSum_inner w _).summable.hasSum]

/-- Diagonal term integrals -/
def term_diag (i : Gronwall f) (r : ℝ) (n : ℕ) : ℂ :=
  2 * π * (1 - n) * I * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)

/-- Only the diagonal `i.term` integrals survive -/
lemma integral_term_diag (i : Gronwall f) (r : ℝ) (n m : ℕ) :
    ∫ t in -π..π, i.term r n m t = if n = m then i.term_diag r n else 0 := by
  have ce : (m - n : ℂ) = (m - n : ℤ) := by simp
  simp only [term, term_diag, div_eq_mul_inv, intervalIntegral.integral_const_mul,
    integral_exp_mul_I, ce, sub_eq_zero, Nat.cast_inj]
  by_cases nm : n = m
  · simp only [← nm, ↓reduceIte, ← Complex.conj_mul', ← two_mul, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  · simp [nm, Ne.symm nm]

@[simp] lemma tsum_diag {f : ι → ℂ} {d : (n m : ι) → Decidable (n = m)} :
   ∑' (p : ι × ι), @ite _ (p.1 = p.2) (d p.1 p.2) (f p.1) 0 = ∑' n, f n := by
  apply tsum_eq_tsum_of_ne_zero_bij (i := fun n ↦ (n.val, n.val))
  · intro ⟨n,_⟩ ⟨m,_⟩
    simp
  · intro ⟨n,m⟩ s
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at s
    simp [← s.1, s.2]
  · simp

/-- Our final series terms -/
def gronwall_term (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ :=
    π * (1 - n) * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)

/-- We also need the `ℂ` version -/
def gronwall_c (i : Gronwall f) (r : ℝ) (n : ℕ) : ℂ :=
    π * (1 - n) * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)

/-- `i.gronwall_c` is summable -/
def ug (i : Gronwall f) (r : ℝ) (n : ℕ) : ℝ :=
  π * ‖(1 - n : ℂ)‖ * r ^ 2 * i.C r ^ 2 * i.a r ^ (2 * n)
lemma le_ug (i : Gronwall f) : ∀ᶠ r in atTop, ∀ n, ‖i.gronwall_c r n‖ ≤ i.ug r n := by
  filter_upwards [i.ac_prop, Filter.eventually_gt_atTop 1] with r ⟨⟨a0,a1⟩,C0,cle⟩ r1 n
  have r0 : 0 < r := by linarith
  simp only [gronwall_c, ug]
  simp only [Complex.norm_div, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, norm_pow, sq_abs, abs_of_pos r0]
  calc π * ‖(1 - n : ℂ)‖ * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)
    _ ≤ π * ‖(1 - n : ℂ)‖ * (i.C r * (i.a r * r) ^ n) ^ 2 * r ^ 2 / r ^ (2 * n) := by bound
    _ = π * ‖(1 - n : ℂ)‖ * r ^ 2 * i.C r ^ 2 * i.a r ^ (2 * n) * (r / r) ^ (2 * n) := by ring
    _ ≤ π * ‖(1 - n : ℂ)‖ * r ^ 2 * i.C r ^ 2 * i.a r ^ (2 * n) := by simp [div_self r0.ne']
lemma summable_ug (i : Gronwall f) : ∀ᶠ r in atTop, Summable (i.ug r) := by
  filter_upwards [i.ac_prop] with r ⟨⟨a0,a1⟩,C0,cle⟩
  unfold ug
  simp only [pow_mul]
  exact summable_subexp_mul_pow (by bound) (pow_lt_one₀ (by bound) a1 (by norm_num))
lemma summable_gronwall_c (i : Gronwall f) : ∀ᶠ r in atTop, Summable (i.gronwall_c r) := by
  filter_upwards [i.summable_ug, i.le_ug] with r summable_ug le_ug
  exact summable_ug.of_norm_bounded le_ug

lemma volume_eq (i : Gronwall f) : ∀ᶠ r in atTop,
    HasSum (fun n ↦ i.gronwall_term r n) (volume.real (i.disk r)) := by
  filter_upwards [i.wind, i.outer_eq_outer, i.inner_nonneg, i.analyticAt_fe, i.hasSum_inner,
    i.sum_integral_comm, i.summable_gronwall_c]
    with r w oe i0 fa is sum_integral_comm summable_gronwall_c
  have ed : i.disk r = w.wind.disk := by simp only [disk, ← w.wind.compl_outer, oe w.wind]
  simp only [ed, w.volume_eq, abs_of_nonneg (i0 w _)]
  simp only [Complex.inner, ← Complex.reCLM_apply]
  have ii : IntervalIntegrable (fun t ↦ w.dfe t * (starRingEnd ℂ) (w.fe t * I)) volume (-π) π := by
    apply Continuous.intervalIntegrable
    simp only [WindDiff.dfe]
    have fc1 : ContDiff ℝ 1 w.fe := by
      rw [contDiff_iff_contDiffAt]
      exact fun t ↦ (fa w t).contDiffAt.of_le le_top
    have dc := fc1.continuous_deriv_one
    have fc := fc1.continuous
    continuity
  have er : ∀ n : ℕ, i.gronwall_term r n =
      Complex.reCLM (π * (1 - ↑n) * ‖i.coeff n‖ ^ 2 * r ^ 2 / r ^ (2 * n)) := by
    intro n; simp only [Complex.reCLM_apply, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
      ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_natCast, ← Complex.ofReal_div,
      Complex.ofReal_re, gronwall_term]
  rw [Complex.reCLM.intervalIntegral_comp_comm ii, Complex.reCLM_apply, ← Complex.re_ofReal_mul]
  simp only [er, ← Complex.reCLM_apply]
  apply Complex.reCLM.hasSum
  simp only [Complex.ofReal_inv, Complex.ofReal_ofNat, map_mul, Complex.conj_I, mul_neg,
    intervalIntegral.integral_neg, ← mul_assoc, intervalIntegral.integral_mul_const]
  simp only [mul_comm _ I, ← mul_assoc, ← div_eq_mul_inv, ← neg_mul, ← neg_div]
  simp only [←(is w _).tsum_eq, ← sum_integral_comm.tsum_eq, i.integral_term_diag, tsum_diag]
  rw [← tsum_mul_left]
  simp only [term_diag, mul_comm _ I, ← mul_assoc, div_eq_mul_inv, mul_neg, Complex.I_mul_I,
    neg_neg, one_mul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)]
  exact summable_gronwall_c.hasSum

end Gronwall

/-- Grönwall's area theorem, standalone version -/
theorem gronwall_area {f : ℂ → ℂ} (fa : AnalyticOn ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) (df : HasDerivAt f 1 0) :
    ball (f 0) (1/4) ⊆ f '' (ball 0 1) :=
  sorry
