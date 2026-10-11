module
public import Ray.Dynamics.FatouNear
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic.Bound
import Ray.Analytic.Uniform

/-!
## The inverse branch of a near-translation near `∞`

In a petal coordinate the near-translation estimate `G w = w + 1 + β / w + O(‖w‖^(-1-δ))` holds on a neighbourhood
`R < ‖w‖` of `∞`, not just on a right half-plane.  There `G` has an analytic inverse branch: `G w = z` is the
fixed-point equation `w = z - 1 - ε w` with `ε w = G w - w - 1`, and since `‖ε‖ ≤ 1/4` and (by a Cauchy estimate)
`‖ε'‖ ≤ 1/16` far out, the map `w ↦ z - 1 - ε w` contracts the disk `‖w - (z - 1)‖ ≤ 1/4`.  Its iterates converge
geometrically and uniformly in `z`, so the inverse is analytic.

We prove:
1. `NearTranslationOut.toNearTranslation`: the restriction to the right half-plane is a `NearTranslation`.
2. `inv_analytic`, `apply_inv`, `inv_apply`: `G⁻¹` is analytic on `4R < ‖z‖`, `G (G⁻¹ z) = z`, and `G⁻¹ (G w) = w` for
   `5R < ‖w‖`.
3. `inv_approx`: `G⁻¹ z = z - 1 - β / z + O(‖z‖^(-1-δ))`.

4. `reflInv_nearTranslation`: the reflection `w ↦ -G⁻¹ (-w)` is a near-translation by `+1` with `-β`.
5. `fatouRepel_analytic`, `fatouRepel_eqn`, `fatouRepel_injOn`: its Fatou coordinate gives the repelling Fatou
   coordinate `Φ_rep z = -Φ̃ (-z)` of `G` on a left half-plane: analytic, `Φ_rep (G z) = Φ_rep z + 1`, and injective
   on a smaller left half-plane.
-/

open Set
open scoped Real

/-- The outside of the disk of radius `R` -/
@[expose] public def outside (R : ℝ) : Set ℂ := {w | R < ‖w‖}

/-- `G` is the translation by `1` up to `β / w` and an error `A / ‖w‖^(1 + δ)` on the neighbourhood `R < ‖w‖` of `∞` -/
public structure NearTranslationOut (G : ℂ → ℂ) (β : ℂ) (R A δ : ℝ) : Prop where
  four_le : 4 ≤ R
  large : 4 * (‖β‖ + A) ≤ R
  A0 : 0 ≤ A
  δ0 : 0 < δ
  δ1 : δ ≤ 1
  ga : AnalyticOnNhd ℂ G (outside R)
  approx : ∀ w ∈ outside R, ‖G w - (w + 1 + β / w)‖ ≤ A / ‖w‖ ^ (1 + δ)

/-- The fixed-point iteration for `G⁻¹ z`: `x 0 = z - 1`, `x (n + 1) = z - 1 - ε (x n)` -/
@[expose] public noncomputable def invSeq (G : ℂ → ℂ) (z : ℂ) : ℕ → ℂ
  | 0 => z - 1
  | n + 1 => z - 1 - (G (invSeq G z n) - invSeq G z n - 1)

/-- The inverse branch `G⁻¹ z = lim x n` -/
@[expose] public noncomputable def nearInv (G : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - 1) + ∑' n, (invSeq G z (n + 1) - invSeq G z n)

namespace NearTranslationOut

variable {G : ℂ → ℂ} {β : ℂ} {R A δ : ℝ}

public lemma isOpen_outside (R : ℝ) : IsOpen (outside R) := isOpen_lt continuous_const continuous_norm

lemma rightHalf_subset : rightHalf R ⊆ outside R := fun w m ↦ lt_of_lt_of_le m (Complex.re_le_norm w)

/-- The restriction to the right half-plane is a near-translation there -/
public lemma toNearTranslation (h : NearTranslationOut G β R A δ) : NearTranslation G β R A δ :=
  ⟨h.four_le, h.large, h.A0, h.δ0, h.δ1, h.ga.mono rightHalf_subset,
    fun w m ↦ h.approx w (rightHalf_subset m)⟩

lemma norm_pos (h : NearTranslationOut G β R A δ) {w : ℂ} (m : w ∈ outside R) : 0 < ‖w‖ := by
  have : R < ‖w‖ := m; linarith [h.four_le]

/-- `‖ε w‖ ≤ (‖β‖ + A) / ‖w‖` -/
lemma eps_le (h : NearTranslationOut G β R A δ) {w : ℂ} (m : w ∈ outside R) :
    ‖G w - w - 1‖ ≤ (‖β‖ + A) / ‖w‖ := by
  have n0 := h.norm_pos m
  have n1 : 1 ≤ ‖w‖ := by have : R < ‖w‖ := m; linarith [h.four_le]
  have e1 : ‖G w - w - 1‖ ≤ ‖G w - (w + 1 + β / w)‖ + ‖β / w‖ := by
    calc ‖G w - w - 1‖ = ‖(G w - (w + 1 + β / w)) + β / w‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have e2 : A / ‖w‖ ^ (1 + δ) ≤ A / ‖w‖ := by
    refine div_le_div_of_nonneg_left h.A0 n0 ?_
    simpa using Real.rpow_le_rpow_of_exponent_le n1 (by linarith [h.δ0] : (1 : ℝ) ≤ 1 + δ)
  rw [norm_div] at e1
  have e3 := h.approx w m
  rw [add_div]
  linarith

/-- `‖ε w‖ ≤ 1/4` -/
lemma eps_le_quarter (h : NearTranslationOut G β R A δ) {w : ℂ} (m : w ∈ outside R) : ‖G w - w - 1‖ ≤ 1 / 4 := by
  refine le_trans (h.eps_le m) ?_
  have : R < ‖w‖ := m
  rw [div_le_iff₀ (h.norm_pos m)]
  linarith [h.large]

lemma eps_analytic (h : NearTranslationOut G β R A δ) : AnalyticOnNhd ℂ (fun w ↦ G w - w - 1) (outside R) :=
  fun w m ↦ ((h.ga w m).sub analyticAt_id).sub analyticAt_const

/-- A Cauchy estimate: `‖ε' w‖ ≤ 1/16` where `2R < ‖w‖` -/
lemma deriv_eps_le (h : NearTranslationOut G β R A δ) {w : ℂ} (m : 2 * R < ‖w‖) :
    ‖deriv (fun w ↦ G w - w - 1) w‖ ≤ 1 / 16 := by
  have R4 := h.four_le
  have n0 : 0 < ‖w‖ := by linarith
  have ball_sub : Metric.closedBall w (‖w‖ / 2) ⊆ outside R := by
    intro y yb
    have := norm_sub_norm_le w y
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at yb
    show R < ‖y‖; linarith
  have d := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith) (C := 2 * (‖β‖ + A) / ‖w‖)
    (((h.eps_analytic).differentiableOn).diffContOnCl_ball ball_sub) fun y ys ↦ by
      have yb := ball_sub (Metric.sphere_subset_closedBall ys)
      refine le_trans (h.eps_le yb) ?_
      have : ‖w‖ / 2 ≤ ‖y‖ := by
        have := norm_sub_norm_le w y
        rw [mem_sphere_iff_norm, norm_sub_rev] at ys
        linarith
      have ba : 0 ≤ ‖β‖ + A := by have := h.A0; positivity
      calc (‖β‖ + A) / ‖y‖ ≤ (‖β‖ + A) / (‖w‖ / 2) := div_le_div_of_nonneg_left ba (by linarith) this
        _ = 2 * (‖β‖ + A) / ‖w‖ := by field_simp
  refine le_trans d ?_
  rw [div_div, div_le_iff₀ (by positivity)]
  have l := h.large
  nlinarith

/-!
### The fixed-point iteration
-/

/-- The region `4R < ‖z‖` where we invert -/
lemma iter_far (h : NearTranslationOut G β R A δ) {z w : ℂ} (zR : 4 * R < ‖z‖) (wz : ‖w - (z - 1)‖ ≤ 1 / 4) :
    2 * R < ‖w‖ := by
  have := norm_sub_norm_le z w
  have e : ‖z - w‖ ≤ 5 / 4 := by
    calc ‖z - w‖ = ‖(1 : ℂ) - (w - (z - 1))‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖w - (z - 1)‖ := norm_sub_le _ _
      _ ≤ 5 / 4 := by rw [norm_one]; linarith
  linarith [h.four_le]

/-- The contraction: `‖ε w₁ - ε w₂‖ ≤ ‖w₁ - w₂‖ / 16` on the disk `‖w - (z - 1)‖ ≤ 1/4` -/
lemma eps_lipschitz (h : NearTranslationOut G β R A δ) {z w₁ w₂ : ℂ} (zR : 4 * R < ‖z‖)
    (m₁ : ‖w₁ - (z - 1)‖ ≤ 1 / 4) (m₂ : ‖w₂ - (z - 1)‖ ≤ 1 / 4) :
    ‖(G w₁ - w₁ - 1) - (G w₂ - w₂ - 1)‖ ≤ 1 / 16 * ‖w₁ - w₂‖ := by
  set D := Metric.closedBall (z - 1) (1 / 4)
  have far : ∀ w ∈ D, 2 * R < ‖w‖ := fun w m ↦ h.iter_far zR (by simpa [D, dist_eq_norm] using m)
  have out : ∀ w ∈ D, w ∈ outside R := fun w m ↦ by
    have := far w m; show R < ‖w‖; linarith [h.four_le]
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w m ↦ (h.eps_analytic w (out w m)).differentiableAt) (fun w m ↦ h.deriv_eps_le (far w m))
    (convex_closedBall _ _) (by simpa [D, dist_eq_norm] using m₂) (by simpa [D, dist_eq_norm] using m₁)

/-- The iterates stay in the disk `‖x n - (z - 1)‖ ≤ 1/4` -/
lemma invSeq_mem (h : NearTranslationOut G β R A δ) {z : ℂ} (zR : 4 * R < ‖z‖) (n : ℕ) :
    ‖invSeq G z n - (z - 1)‖ ≤ 1 / 4 := by
  induction n with
  | zero => simp [invSeq]
  | succ n ih =>
    have o : invSeq G z n ∈ outside R := by
      have := h.iter_far zR ih; show R < ‖_‖; linarith [h.four_le]
    simp only [invSeq, sub_sub_cancel_left, norm_neg]
    exact h.eps_le_quarter o

/-- The steps shrink geometrically: `‖x (n + 1) - x n‖ ≤ (1/4) (1/16)^n` -/
lemma invSeq_step (h : NearTranslationOut G β R A δ) {z : ℂ} (zR : 4 * R < ‖z‖) (n : ℕ) :
    ‖invSeq G z (n + 1) - invSeq G z n‖ ≤ 1 / 4 * (1 / 16) ^ n := by
  induction n with
  | zero =>
    have o : z - 1 ∈ outside R := by
      have := h.iter_far zR (w := z - 1) (by simp); show R < ‖z - 1‖; linarith [h.four_le]
    have e : invSeq G z 1 - invSeq G z 0 = -(G (z - 1) - (z - 1) - 1) := by simp only [invSeq]; ring
    rw [e, norm_neg]
    simpa using h.eps_le_quarter o
  | succ n ih =>
    have e : invSeq G z (n + 2) - invSeq G z (n + 1) =
        -((G (invSeq G z (n + 1)) - invSeq G z (n + 1) - 1) - (G (invSeq G z n) - invSeq G z n - 1)) := by
      simp only [invSeq]; ring
    rw [e, norm_neg]
    refine le_trans (h.eps_lipschitz zR (h.invSeq_mem zR _) (h.invSeq_mem zR _)) ?_
    rw [pow_succ]
    nlinarith [norm_nonneg (invSeq G z (n + 1) - invSeq G z n)]

lemma summable_geom : Summable fun n : ℕ ↦ (1 / 4 : ℝ) * (1 / 16) ^ n :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The iterates converge uniformly on `4R < ‖z‖` -/
lemma tendstoUniformlyOn_inv (h : NearTranslationOut G β R A δ) :
    TendstoUniformlyOn (fun N z ↦ invSeq G z N) (nearInv G) Filter.atTop (outside (4 * R)) := by
  have u := tendstoUniformlyOn_tsum_nat summable_geom (s := outside (4 * R))
    (f := fun n z ↦ invSeq G z (n + 1) - invSeq G z n) (fun n z m ↦ h.invSeq_step m n)
  rw [Metric.tendstoUniformlyOn_iff] at u ⊢
  intro ε ε0
  filter_upwards [u ε ε0] with N hN z m
  have tele : invSeq G z N = (z - 1) + ∑ n ∈ Finset.range N, (invSeq G z (n + 1) - invSeq G z n) := by
    rw [Finset.sum_range_sub (fun n ↦ invSeq G z n)]; simp [invSeq]
  rw [tele, nearInv, dist_add_left]
  exact hN z m

/-- The iterates are analytic in `z` -/
lemma invSeq_analytic (h : NearTranslationOut G β R A δ) (n : ℕ) :
    AnalyticOnNhd ℂ (fun z ↦ invSeq G z n) (outside (4 * R)) := by
  induction n with
  | zero => exact fun z _ ↦ analyticAt_id.sub analyticAt_const
  | succ n ih =>
    intro z m
    have o : invSeq G z n ∈ outside R := by
      have := h.iter_far m (h.invSeq_mem m n); show R < ‖_‖; linarith [h.four_le]
    have hc : AnalyticAt ℂ (fun z ↦ G (invSeq G z n)) z :=
      AnalyticAt.comp (g := G) (f := fun z ↦ invSeq G z n) (x := z) (h.ga _ o) (ih z m)
    simp only [invSeq]
    exact (analyticAt_id.sub analyticAt_const).sub ((hc.sub (ih z m)).sub analyticAt_const)

/-- The inverse branch is analytic on `4R < ‖z‖` -/
public theorem inv_analytic (h : NearTranslationOut G β R A δ) : AnalyticOnNhd ℂ (nearInv G) (outside (4 * R)) :=
  uniform_analytic_lim (isOpen_outside _) h.invSeq_analytic h.tendstoUniformlyOn_inv

/-- `G⁻¹ z` lies in the disk `‖w - (z - 1)‖ ≤ 1/4` -/
lemma inv_mem (h : NearTranslationOut G β R A δ) {z : ℂ} (zR : z ∈ outside (4 * R)) :
    ‖nearInv G z - (z - 1)‖ ≤ 1 / 4 := by
  have t := h.tendstoUniformlyOn_inv.tendsto_at zR
  have c : IsClosed (Metric.closedBall (z - 1) (1 / 4 : ℝ)) := Metric.isClosed_closedBall
  have := c.mem_of_tendsto t (Filter.Eventually.of_forall fun n ↦ by
    simpa [dist_eq_norm] using h.invSeq_mem zR n)
  simpa [dist_eq_norm] using this

/-- `G⁻¹ z` is a fixed point: `G⁻¹ z = z - 1 - ε (G⁻¹ z)` -/
lemma inv_fixed (h : NearTranslationOut G β R A δ) {z : ℂ} (zR : z ∈ outside (4 * R)) :
    nearInv G z = z - 1 - (G (nearInv G z) - nearInv G z - 1) := by
  have t := h.tendstoUniformlyOn_inv.tendsto_at zR
  have o : nearInv G z ∈ outside R := by
    have := h.iter_far zR (h.inv_mem zR); show R < ‖_‖; linarith [h.four_le]
  have ec := (h.eps_analytic _ o).continuousAt
  have t1 : Filter.Tendsto (fun n ↦ invSeq G z (n + 1)) Filter.atTop (nhds (nearInv G z)) :=
    t.comp (Filter.tendsto_add_atTop_nat 1)
  have t2 : Filter.Tendsto (fun n ↦ invSeq G z (n + 1)) Filter.atTop
      (nhds (z - 1 - (G (nearInv G z) - nearInv G z - 1))) := by
    simp only [invSeq]
    exact (ec.tendsto.comp t).const_sub _
  exact tendsto_nhds_unique t1 t2

/-- `G (G⁻¹ z) = z` -/
public theorem apply_inv (h : NearTranslationOut G β R A δ) {z : ℂ} (zR : z ∈ outside (4 * R)) :
    G (nearInv G z) = z := by
  have e := h.inv_fixed zR
  linear_combination e

/-- Uniqueness: a fixed point in the disk is `G⁻¹ z` -/
lemma eq_inv (h : NearTranslationOut G β R A δ) {z w : ℂ} (zR : z ∈ outside (4 * R))
    (wz : ‖w - (z - 1)‖ ≤ 1 / 4) (fix : w = z - 1 - (G w - w - 1)) : w = nearInv G z := by
  have e := h.inv_fixed zR
  have l := h.eps_lipschitz zR wz (h.inv_mem zR)
  have d : w - nearInv G z = -((G w - w - 1) - (G (nearInv G z) - nearInv G z - 1)) := by
    calc w - nearInv G z = (z - 1 - (G w - w - 1)) - (z - 1 - (G (nearInv G z) - nearInv G z - 1)) := by
          rw [← fix, ← e]
      _ = _ := by ring
  have : ‖w - nearInv G z‖ ≤ 1 / 16 * ‖w - nearInv G z‖ := by
    calc ‖w - nearInv G z‖ = ‖(G w - w - 1) - (G (nearInv G z) - nearInv G z - 1)‖ := by rw [d, norm_neg]
      _ ≤ _ := l
  have : ‖w - nearInv G z‖ = 0 := by linarith [norm_nonneg (w - nearInv G z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- `G⁻¹ (G w) = w` where `5R < ‖w‖` -/
public theorem inv_apply (h : NearTranslationOut G β R A δ) {w : ℂ} (wR : w ∈ outside (5 * R)) :
    nearInv G (G w) = w := by
  have R4 := h.four_le
  have o : w ∈ outside R := by have : 5 * R < ‖w‖ := wR; show R < ‖w‖; linarith
  have q := h.eps_le_quarter o
  have zR : G w ∈ outside (4 * R) := by
    have : ‖w‖ ≤ ‖G w‖ + 5 / 4 := by
      calc ‖w‖ = ‖G w - (1 + (G w - w - 1))‖ := by ring_nf
        _ ≤ ‖G w‖ + ‖1 + (G w - w - 1)‖ := norm_sub_le _ _
        _ ≤ ‖G w‖ + (1 + 1 / 4) := by
          gcongr; exact le_trans (norm_add_le _ _) (by rw [norm_one]; linarith)
        _ = ‖G w‖ + 5 / 4 := by norm_num
    have : 5 * R < ‖w‖ := wR
    show 4 * R < ‖G w‖; linarith
  refine (h.eq_inv zR ?_ ?_).symm
  · have : w - (G w - 1) = -(G w - w - 1) := by ring
    rw [this, norm_neg]; exact q
  · ring

/-- The inverse is a near-translation by `-1`: `‖G⁻¹ z - (z - 1 - β / z)‖ ≤ (4A + 3‖β‖) / ‖z‖^(1 + δ)` -/
public theorem inv_approx (h : NearTranslationOut G β R A δ) {z : ℂ} (zR : z ∈ outside (4 * R)) :
    ‖nearInv G z - (z - 1 - β / z)‖ ≤ (4 * A + 3 * ‖β‖) / ‖z‖ ^ (1 + δ) := by
  have R4 := h.four_le
  set w := nearInv G z with hw
  have zn : 4 * R < ‖z‖ := zR
  have wm := h.inv_mem zR
  have zw : ‖z - w‖ ≤ 5 / 4 := by
    calc ‖z - w‖ = ‖(1 : ℂ) - (w - (z - 1))‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖w - (z - 1)‖ := norm_sub_le _ _
      _ ≤ 5 / 4 := by rw [norm_one]; linarith
  have wz2 : ‖z‖ / 2 ≤ ‖w‖ := by have := norm_sub_norm_le z w; linarith
  have z0 : 0 < ‖z‖ := by linarith
  have w0 : 0 < ‖w‖ := by linarith
  have o : w ∈ outside R := by show R < ‖w‖; linarith
  have e := h.inv_fixed zR
  have key : w - (z - 1 - β / z) = -(G w - (w + 1 + β / w)) - (β / w - β / z) := by
    rw [← hw] at e
    calc w - (z - 1 - β / z) = (z - 1 - (G w - w - 1)) - (z - 1 - β / z) := by rw [← e]
      _ = _ := by ring
  rw [key]
  -- the two pieces
  have P0 : 0 < ‖z‖ ^ (1 + δ) := Real.rpow_pos_of_pos z0 _
  have t1 : ‖G w - (w + 1 + β / w)‖ ≤ 4 * A / ‖z‖ ^ (1 + δ) := by
    refine le_trans (h.approx w o) ?_
    have m1 : ‖z‖ ^ (1 + δ) / 4 ≤ ‖w‖ ^ (1 + δ) := by
      have a : (‖z‖ / 2) ^ (1 + δ) ≤ ‖w‖ ^ (1 + δ) := Real.rpow_le_rpow (by positivity) wz2 (by linarith [h.δ0])
      have b : (‖z‖ / 2) ^ (1 + δ) = ‖z‖ ^ (1 + δ) / 2 ^ (1 + δ) := Real.div_rpow z0.le (by norm_num) _
      have c : (2 : ℝ) ^ (1 + δ) ≤ 4 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith [h.δ1] : 1 + δ ≤ 2)
        norm_num at this ⊢; linarith
      rw [b] at a
      refine le_trans ?_ a
      exact div_le_div_of_nonneg_left P0.le (by positivity) c
    calc A / ‖w‖ ^ (1 + δ) ≤ A / (‖z‖ ^ (1 + δ) / 4) :=
          div_le_div_of_nonneg_left h.A0 (by positivity) m1
      _ = 4 * A / ‖z‖ ^ (1 + δ) := by field_simp
  have t2 : ‖β / w - β / z‖ ≤ 3 * ‖β‖ / ‖z‖ ^ (1 + δ) := by
    have e2 : β / w - β / z = β * (z - w) / (w * z) := by
      field_simp [norm_pos_iff.mp w0, norm_pos_iff.mp z0]
    rw [e2, norm_div, norm_mul, norm_mul]
    have zsq : ‖z‖ ^ (1 + δ) ≤ ‖z‖ ^ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ ‖z‖) (by linarith [h.δ1] : 1 + δ ≤ (2 : ℝ))
    calc ‖β‖ * ‖z - w‖ / (‖w‖ * ‖z‖) ≤ ‖β‖ * (5 / 4) / (‖z‖ / 2 * ‖z‖) := by gcongr
      _ = 5 / 2 * ‖β‖ / ‖z‖ ^ 2 := by field_simp; ring
      _ ≤ 3 * ‖β‖ / ‖z‖ ^ 2 := by gcongr; norm_num
      _ ≤ 3 * ‖β‖ / ‖z‖ ^ (1 + δ) := by gcongr
  calc ‖-(G w - (w + 1 + β / w)) - (β / w - β / z)‖ ≤ ‖G w - (w + 1 + β / w)‖ + ‖β / w - β / z‖ := by
        refine le_trans (norm_sub_le _ _) ?_; rw [norm_neg]
    _ ≤ 4 * A / ‖z‖ ^ (1 + δ) + 3 * ‖β‖ / ‖z‖ ^ (1 + δ) := add_le_add t1 t2
    _ = (4 * A + 3 * ‖β‖) / ‖z‖ ^ (1 + δ) := by ring

/-!
### The repelling Fatou coordinate
-/

/-- The constants of the reflected inverse `w ↦ -G⁻¹ (-w)` -/
@[expose] public noncomputable def repA (β : ℂ) (A : ℝ) : ℝ := 4 * A + 3 * ‖β‖
@[expose] public noncomputable def repR (β : ℂ) (R A : ℝ) : ℝ := 5 * R + 4 * (‖β‖ + repA β A)

/-- The reflected inverse, a near-translation by `+1` -/
@[expose] public noncomputable def reflInv (G : ℂ → ℂ) (w : ℂ) : ℂ := -nearInv G (-w)

lemma refl_out (h : NearTranslationOut G β R A δ) {w : ℂ} (m : w ∈ rightHalf (repR β R A)) :
    -w ∈ outside (5 * R) := by
  have : 0 ≤ repA β A := by unfold repA; have := h.A0; positivity
  have : repR β R A < ‖w‖ := lt_of_lt_of_le m (Complex.re_le_norm w)
  have : 5 * R ≤ repR β R A := by unfold repR; have := h.A0; nlinarith [norm_nonneg β]
  show 5 * R < ‖-w‖; rw [norm_neg]; linarith

lemma refl_out4 (h : NearTranslationOut G β R A δ) {w : ℂ} (m : w ∈ rightHalf (repR β R A)) :
    -w ∈ outside (4 * R) := by
  have a := h.refl_out m
  have b := h.four_le
  have c : 5 * R < ‖-w‖ := a
  show 4 * R < ‖-w‖; linarith

/-- `w ↦ -G⁻¹ (-w)` is a near-translation by `+1`, with `-β` -/
public theorem reflInv_nearTranslation (h : NearTranslationOut G β R A δ) :
    NearTranslation (reflInv G) (-β) (repR β R A) (repA β A) δ := by
  have A0 := h.A0
  have rA : 0 ≤ repA β A := by unfold repA; positivity
  refine ⟨?_, ?_, rA, h.δ0, h.δ1, ?_, ?_⟩
  · unfold repR; have := h.four_le; nlinarith [norm_nonneg β]
  · unfold repR; rw [norm_neg]; have := h.four_le; linarith
  · intro w m
    have hn : AnalyticAt ℂ (fun w : ℂ ↦ -w) w := analyticAt_id.neg
    exact ((h.inv_analytic _ (h.refl_out4 m)).comp (f := fun w ↦ -w) hn).neg
  · intro w m
    have e : reflInv G w - (w + 1 + -β / w) = -(nearInv G (-w) - (-w - 1 - β / -w)) := by
      simp only [reflInv]; ring
    rw [e, norm_neg]
    simpa [repA, norm_neg] using h.inv_approx (h.refl_out4 m)

/-- The left half-plane `re z < -R` -/
@[expose] public def leftHalf (R : ℝ) : Set ℂ := {z | z.re < -R}

/-- The repelling Fatou coordinate `Φ_rep z = -Φ̃ (-z)`, with `Φ̃` the Fatou coordinate of `w ↦ -G⁻¹ (-w)` -/
@[expose] public noncomputable def fatouRepel (G : ℂ → ℂ) (β z : ℂ) : ℂ :=
  -NearTranslation.fatou (reflInv G) (-β) (-z)

lemma neg_mem_rightHalf {z : ℂ} {a : ℝ} (m : z ∈ leftHalf a) : -z ∈ rightHalf a := by
  simp only [leftHalf, rightHalf, mem_ofPred_eq, Complex.neg_re] at m ⊢; linarith

/-- The repelling Fatou coordinate is analytic on the left half-plane -/
public theorem fatouRepel_analytic (h : NearTranslationOut G β R A δ) :
    AnalyticOnNhd ℂ (fatouRepel G β) (leftHalf (repR β R A)) := fun z m ↦ by
  have hn : AnalyticAt ℂ (fun w : ℂ ↦ -w) z := analyticAt_id.neg
  exact ((h.reflInv_nearTranslation.fatou_analytic _ (neg_mem_rightHalf m)).comp (f := fun w ↦ -w) hn).neg

/-- The repelling Fatou coordinate conjugates `G` to the translation by `1` where `z` and `G z` lie in the left
half-plane -/
public theorem fatouRepel_eqn (h : NearTranslationOut G β R A δ) {z : ℂ} (m : z ∈ leftHalf (repR β R A))
    (gm : G z ∈ leftHalf (repR β R A)) : fatouRepel G β (G z) = fatouRepel G β z + 1 := by
  have e := h.reflInv_nearTranslation.fatou_eqn (neg_mem_rightHalf gm)
  have inv : reflInv G (-G z) = -z := by
    simp only [reflInv, neg_neg]
    have zo : z ∈ outside (5 * R) := by simpa using h.refl_out (neg_mem_rightHalf m)
    rw [h.inv_apply zo]
  rw [inv] at e
  simp only [fatouRepel]
  rw [e]; ring

/-- The repelling Fatou coordinate is injective on a smaller left half-plane -/
public theorem fatouRepel_injOn (h : NearTranslationOut G β R A δ) :
    ∃ R' ≥ repR β R A, InjOn (fatouRepel G β) (leftHalf R') := by
  obtain ⟨R', le, inj⟩ := h.reflInv_nearTranslation.fatou_injOn
  refine ⟨R', le, fun x xm y ym e ↦ ?_⟩
  simp only [fatouRepel] at e
  exact neg_inj.mp (inj (neg_mem_rightHalf xm) (neg_mem_rightHalf ym) (neg_inj.mp e))

end NearTranslationOut
