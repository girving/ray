import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Ray.Analytic.Holomorphic
import Ray.Koebe.WindArea
import Ray.Misc.Annuli
import Ray.Misc.AtInf

/-!
## Koebe quarter theorem

If `f : ball 0 1 → ℂ` is analytic and injective, with `f' 0 = 1`, then its image contains a disk
of radius `1/4` centered at `f 0`.

The proof follows Wikipedia: https://en.wikipedia.org/wiki/Koebe_quarter_theorem

DO NOT SUBMIT: Rename to Gromwall.lean for the Gromwall's area theorem part.
-/

open Classical
open Complex (abs arg)
open Metric (ball closedBall isOpen_ball sphere)
open Set
open Filter (atTop Tendsto)
open MeasureTheory (volume)
open scoped ContDiff Topology NNReal
noncomputable section

/-!
## Grönwall's area theorem

The traditional statement involves a function `g w = w + b1/w + b2/w^2 + ...` analytic and
injective for `1 < abs w`.  In order to avoid infinity, we state the theorem in terms of
`f z = z * g z⁻¹`, which is analytic for `abs z < 1` with `f 0 = 1`, `deriv f 0 = 0`.  Let

  `f z = ∑ n, a n * z^n`
  `g w = w * f w⁻¹`
  `g_Ioi r = g '' {w | r < abs w}`

Then the theorem is

  `volume (g_Ioi 1)ᶜ = π * ∑ n, (1 - n) * abs (a n) ^ 2`

Mathlib lacks the general Stokes theorem, but we can work instead with `g_Ioi r0 \ g_Ioi r1` for
`r0 → 1`, `r1 → ∞` and use `fubini_annulus`.  To do this, we show that `g_Ioi r` approximates
`{z | r < abs z}` for large `r`, whence

  `volume (g_Ioi 1)ᶜ = lim_{r0 → 1, r1 → ∞} volume (closedBall 0 r1) - volume (g_Ioi r0 \ g_Ioi r1)`

Hmm, actually it's subtle that `g_Ioi r1` approximates `closedBall 0 r1`.  But do we really need that?
Let's do the integral to see.

  `dg z = deriv g z = f z⁻¹ - z * df z⁻¹ / z^2`
  `  = f z⁻¹ - z⁻¹ * df z⁻¹ = ∑ n, (1 - n) * a n * z^(-n)`
  `S = g_Ioi r0 \ g_Ioi r1 = {z | r0 < abs z ≤ r1}`
  `volume (g '' S) = ∫ z in g '' S, 1 ∂z`
  `  = ∫ z in S, |dg z|^2 ∂z` by `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`
  `  = ∫ z in S, conj (dg z) * dg z ∂z`
  `  = ∫ r in Ioc r0 r1, r * ∫ t in Ioc 0 (2*π), ∑ n0 n1, (1-n0) * (1-n1) * conj (a n0) * (a n1) *`
  `     r^(-n0-n1) * exp (I * (n1-n0) * t) ∂t ∂r` by `fubini_annulus`
  `  = ∫ r in Ioc r0 r1, ∑ n, 2*π * (1-n)^2 * (abs (a n))^2 * r^(1-2*n) ∂r`
  `  = 2*π * ∑ n, (1-n)^2 * (abs (a n))^2 * ∫ r in Ioc r0 r1, r^(1-2*n) ∂r`
  `  = 2*π * ∑ n, (1-n)^2 * (abs (a n))^2 * (2-2*n)⁻¹ * (r1^(2-2*n) - r0^(2-2*n))` since `a 1 = 0`
  `  = π * ∑ n, (1-n) * (abs (a n))^2 * (r1^(2-2*n) - r0^(2-2*n))`

To finish our estimate, we need an `o(1)`-accurate estimate for `(g_Ioi r1)ᶜ` for large `r1`.  The
above gives us an `O((abs (a 2))^2 * r0^2)`-accurate estimate.  Can we get the rest of the way by
rescaling?  Consider the case `f z = 1 + a * z^2`, `g w = w + a/w`.  When is this injective?

  `z + a/z = w + a/w`
  `zzw + aw = zww + az`
  `z(zw - a) = w(zw - a)`
  `(z - w)(zw - a) = 0`

So we get duplicate values exact at `z = a/w`, which means we're injective down to `r = sqrt a`.

Let's try do `g w = w + a/w` a different way.  The image for large `r` is

  `I = g '' {w | r < abs w} = {z | ∃ w, z = w + a/w ∧ r < abs w}`
  `  = {z | ∃ w, w^2 - zw + a = 0 ∧ r < abs w}`
  `  = {z | ∃ w, w = (z ± sqrt(z^2 - 4a))/2a ∧ r < abs w}`

Ah, but that's useless since `g w = w + a/w` is not injective enough.

Ooh, I know.  Let's try to prove that `(g_Ioi r)ᶜ` is star-shaped for large `r`.  If there is a
collision, we get

  `t ∈ Icc 0 1`
  `abs z0 = abs z1 = 1`
  `t * g (r * z0) = g (r * z1)`
  `arg (g (r * z0)) = arg (g (r * z1))`
  `arg z0 + arg (1 + r^-2 * z0^-2 * h (r⁻¹ * z0⁻¹))`
  ` = arg z1 + arg (1 + r^-2 * z1^-2 * h (r⁻¹ * z1⁻¹))`
  `arg z0 + O(r^-2) = arg z1 + O(r^arg (1 + r^-2 * z1^-2 * h (r⁻¹ * z1⁻¹))`

Yeah, it looks star-shaped.  Let's prove it.

DO NOT SUBMIT: Refactor the above
-/

/-- Properties of `f` as discussed above -/
structure Gronwall (f : ℂ → ℂ) : Prop where
  fa : AnalyticOnNhd ℂ f (ball 0 1)
  f0 : f 0 = 1
  df0 : HasDerivAt f 0 0
  inj' : InjOn (fun w ↦ w * f w⁻¹) {w : ℂ | 1 < ‖w‖}

variable {f : ℂ → ℂ}

namespace Gronwall

def g (_ : Gronwall f) (w : ℂ) : ℂ := w * f w⁻¹

/-- The region outside a `g` cycle -/
def g_Ioi (i : Gronwall f) (r : ℝ) : Set ℂ := i.g '' norm_Ioi r

/-- `g` is injective on `norm_Ioi 1` -/
lemma inj (i : Gronwall f) : InjOn i.g (norm_Ioi 1) := i.inj'

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

#exit

-- DO NOT SUBMIT: Put in a new sectio
/-- `g` as a circle map -/
def gc (i : Gronwall f) (r : ℝ) : Circle → ℂˣ := fun z ↦
  Units.mk1 (i.g (r * z.val))

/-- `g_Ioi r` is roughly `outside r` -/
lemma gr_subset {i : Gronwall f} {e : ℝ} (e0 : 0 < e) :
    ∀ᶠ r in atTop, i.g_Ioi r ⊆ outside (r - e/r) := by
  have hc : ContinuousOn i.h (closedBall 0 (1/2)) :=
    i.ha.continuousOn.mono (Metric.closedBall_subset_ball (by bound))
  rcases hc.norm.bounded (isCompact_closedBall _ _) with ⟨b,bp,hb⟩
  refine eventually_of_forall (fun r ↦ ?_)
  intro u ⟨w,wr,wu⟩
  simp? [outside, ←wu, g, i.f_eq] at wr ⊢


-- (r - e/r)^2 = r^2 - 2*e + e^2/r^2

/-- `g_Ioi r` is roughly `outside r` -/
lemma subset_gr {i : Gronwall f} {e : ℝ} (e0 : 0 < e) :
    ∀ᶠ r in atTop, outside (r + e/r) ⊆ i.g_Ioi r := by
  sorry

/-- `volume (g_Ioi r0)ᶜ` as a limit -/
lemma tendsto_volume_compl_gr {i : Gronwall f} {r0 : ℝ} (r01 : 1 < r0) :
    Tendsto (fun r1 ↦ volume (closedBall (0:ℂ) r1) - volume (i.g_Ioi r0 \ i.g_Ioi r1))
      atTop (𝓝 (volume (i.g_Ioi r0)ᶜ)) :=
  sorry

/-- `volume (g_Ioi 1)ᶜ` as a limit -/
lemma tendsto_volume_compl_gr_one {i : Gronwall f} :
    Tendsto (fun r0 ↦ volume (i.g_Ioi r0)ᶜ) atTop (𝓝 (volume (i.g_Ioi 1)ᶜ)) := by
  sorry

end Gronwall

/-- Grönwall's area theorem -/
theorem gronwall_area {f : ℂ → ℂ} (fa : AnalyticOn ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) (df : HasDerivAt f 1 0) :
    ball (f 0) (1/4) ⊆ f '' (ball 0 1) :=
  sorry

/-!
## Koebe quarter theorem
-/

/-- The Koebe quarter theorem -/
theorem koebe_quarter {f : ℂ → ℂ} (fa : AnalyticOn ℂ f (ball 0 1))
    (inj : InjOn f (ball 0 1)) (df : HasDerivAt f 1 0) :
    ball (f 0) (1/4) ⊆ f '' (ball 0 1) :=
  sorry
