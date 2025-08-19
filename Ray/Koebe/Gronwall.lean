import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Ray.Analytic.Holomorphic
import Ray.Koebe.WindArea
import Ray.Manifold.GlobalInverse
import Ray.Misc.Annuli
import Ray.Misc.Cobounded

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
open Complex (abs arg)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped ContDiff Topology NNReal Real
noncomputable section

variable {α : Type}
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

-- DO NOT SUBMIT: Move elsewhere
@[simp] lemma _root_.ContinuousLinearMap.smulRight_zero {M₁ : Type} [TopologicalSpace M₁]
    [AddCommMonoid M₁] {M₂ : Type} [TopologicalSpace M₂] [AddCommMonoid M₂] {R : Type} {S : Type}
    [Semiring R] [Semiring S] [Module R M₁] [Module R M₂] [Module R S] [Module S M₂]
    [IsScalarTower R S M₂] [TopologicalSpace S] [ContinuousSMul S M₂] (c : M₁ →L[R] S)
    : (c.smulRight (0 : M₂) : M₁ →L[R] M₂) = 0 := by
  ext
  simp only [ContinuousLinearMap.smulRight_apply, smul_zero, ContinuousLinearMap.zero_apply]

-- DO NOT SUBMIT: Move elsewhere
lemma _root_.HasFDerivAt.comp_of_eq {𝕜 : Type} [NontriviallyNormedField 𝕜] {E : Type}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : E → F} {f' : E →L[𝕜] F} (x : E)
    {g : F → G} {g' : F →L[𝕜] G} {y : F} (hg : HasFDerivAt g g' y) (hf : HasFDerivAt f f' x)
    (e : f x = y) : HasFDerivAt (g ∘ f) (g'.comp f') x := by
  rw [← e] at hg
  exact hg.comp x hf

-- DO NOT SUBMIT: Move elsewhere
lemma _root_.hasFDeriv_zero_of_comp_right {𝕜 E F G : Type} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : F → G} {g : E → F} {y : F} {x : E}
    (df : DifferentiableAt 𝕜 f y) (dg : HasFDerivAt g (0 : E →L[𝕜] F) x) (e : g x = y) :
    HasFDerivAt (fun x ↦ f (g x)) (0 : E →L[𝕜] G) x := by
  convert df.hasFDerivAt.comp_of_eq _ dg e
  simp only [ContinuousLinearMap.comp_zero]

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

-- DO NOT SUBMIT: Move elsewhere
lemma eventually_nhdsGT_zero_ball_iff_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop} :
    (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ ball c r, p x) ↔ ∀ᶠ x in 𝓝 c, p x := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff, Metric.nhds_basis_ball.eventually_iff]
  constructor
  · intro ⟨r,r0,h⟩
    exact ⟨r/2, by bound, fun x m ↦ @h (r/2) (by simpa) _ m⟩
  · intro ⟨r,r0,h⟩
    refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
    simp only [Metric.mem_ball, mem_Ioo] at m sr ⊢
    linarith

-- DO NOT SUBMIT: Move elsewhere
lemma eventually_nhdsGT_zero_closedBall_iff_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop} :
    (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ closedBall c r, p x) ↔ ∀ᶠ x in 𝓝 c, p x := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff, Metric.nhds_basis_closedBall.eventually_iff]
  constructor
  · intro ⟨r,r0,h⟩
    exact ⟨r/2, by bound, fun x m ↦ @h (r/2) (by simpa) _ m⟩
  · intro ⟨r,r0,h⟩
    refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
    simp only [Metric.mem_closedBall, mem_Ioo] at m sr ⊢
    linarith

-- DO NOT SUBMIT: Move elsewhere
lemma eventually_nhdsGT_zero_sphere_of_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop}
    (h : ∀ᶠ x in 𝓝 c, p x) : (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ sphere c r, p x) := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff,
    Metric.nhds_basis_closedBall.eventually_iff] at h ⊢
  obtain ⟨r,r0,h⟩ := h
  refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
  simp only [Metric.mem_sphere, mem_Ioo, Metric.mem_closedBall] at m sr ⊢
  rw [← m] at sr
  exact sr.2.le

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

-- DO NOT SUBMIT: Move elsewhere
lemma eventually_atTop_iff_nhdsGT_zero {p : ℝ → Prop} :
    (∀ᶠ r in atTop, p r) ↔ ∀ᶠ r in 𝓝[>] 0, p r⁻¹ := by
  simp only [Filter.eventually_atTop, (nhdsGT_basis (0 : ℝ)).eventually_iff]
  constructor
  · intro ⟨r,h⟩
    refine ⟨(max 1 r)⁻¹, by bound, fun s m ↦ h _ ?_⟩
    rw [mem_Ioo, lt_inv_comm₀, max_lt_iff] at m
    all_goals bound
  · intro ⟨r,r0,h⟩
    refine ⟨2 * r⁻¹, fun s m ↦ ?_⟩
    refine inv_inv s ▸ @h s⁻¹ ?_
    simp only [mem_Ioo, inv_pos]
    have s0 : 0 < s := lt_of_lt_of_le (by bound) m
    refine ⟨s0, ?_⟩
    rw [inv_lt_comm₀ s0 r0]
    exact lt_of_lt_of_le (lt_mul_of_one_lt_left (by bound) (by norm_num)) m

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

-- DO NOT SUBMIT: Move elsewhere
/-- Pull an `∃` out of an `∃ᶠ` via Skolemization -/
lemma frequently_skolem {X Y : Type} [TopologicalSpace X] [n : Nonempty Y] {p : X → Y → Prop}
    (f : Filter X) : (∃ᶠ x in f, ∃ y, p x y) ↔ ∃ s : X → Y, ∃ᶠ x in f, p x (s x) := by
  constructor
  · intro h
    set s : X → Y := fun x ↦ if q : ∃ y, p x y then Classical.choose q else Classical.choice n
    use s
    refine h.mp (.of_forall fun x e ↦ ?_)
    simp only [e, ↓reduceDIte, choose_spec, s]
  · intro ⟨s,h⟩
    refine h.mp (.of_forall fun x e ↦ ?_)
    use s x

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

-- DO NOT SUBMIT: inner ℝ (w.fe t * Complex.I) (w.dfe t)
lemma hasSum_fe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    HasSum (fun n : ℕ ↦ i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)) (w.fe t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.g0] with r r1 g0 w t
  have r0 : 0 < r := by linarith
  have ri0 : 0 < r⁻¹ := by bound
  have ri1 : r⁻¹ < 1 := by bound
  have circ : ∀ t, (r : ℂ) * Circle.exp t = circleMap 0 r t := by intro; simp [circleMap]
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
  rw [WindDiff.fe, gc, Units.val_mk1 (g0 _ (by simp [r0.le])), g, circ, circleMap_zero_inv]
  replace sum := (sum (-t)).mul_left (circleMap 0 r t)
  simp only [← mul_assoc, mul_comm _ (i.coeff _)] at sum
  simp only [mul_assoc, pow] at sum
  exact sum

lemma hasSum_dfe (i : Gronwall f) : ∀ᶠ r in atTop, ∀ w : WindDiff (i.gc r), ∀ t,
    HasSum (fun n : ℕ ↦ i.coeff n * circleMap 0 r t ^ (1 - n : ℤ)) (w.dfe t) := by
  filter_upwards [Filter.eventually_gt_atTop 1, i.hasSum_fe] with r r1 sum w t
  simp only [WindDiff.dfe]
  sorry

lemma volume_eq (i : Gronwall f) : ∀ᶠ r in atTop,
    HasSum (fun n ↦ (n - 1) * ‖i.coeff n‖ ^ 2 / r ^ (2 * n - 2)) (volume.real (i.disk r)) := by
  filter_upwards [i.wind, i.outer_eq_outer] with r w oe
  have ed : i.disk r = w.wind.disk := by simp only [disk, ← w.wind.compl_outer, oe w.wind]
  simp only [ed, w.volume_eq]
  sorry

#exit

end Gronwall

/-- Grönwall's area theorem -/
theorem gronwall_area {f : ℂ → ℂ} (fa : AnalyticOn ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) (df : HasDerivAt f 1 0) :
    ball (f 0) (1/4) ⊆ f '' (ball 0 1) :=
  sorry
