module
public import Ray.Dynamics.FatouNear
public import Ray.Dynamics.FatouRepel
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Bound
import Ray.Manifold.GlobalInverse

/-!
## The Fatou parametrisation of a near-translation

The Fatou coordinate `Φ` of a near-translation `G` (`FatouNear.lean`) is injective on a right half-plane `H`.  Its
image `Φ H` is open, invariant under `ζ ↦ ζ + 1`, and every point enters it after enough steps: for each `ζ` there is an
`n` with `ζ + n ∈ Φ H`.  (`Φ H` is not a half-plane in general: `Φ w ≈ w - β log w` bends it logarithmically.)  The
inverse `Ψ : Φ H → H` is analytic.

For a repelling near-translation (`NearTranslationOut`), reflecting gives the repelling parametrisation
`repel_param`: an open `V` closed under `ζ ↦ ζ - 1` that every point reaches after enough steps left, and an analytic
`Ψ` on `V` with values far out in a left half-plane and `G (Ψ (ζ - 1)) = Ψ ζ`.

Surjectivity is a contraction argument: `Φ = id + f` with `f` `1/2`-Lipschitz, so `z = t - f z` has a fixed point in
the disk around `t` of radius `2 ‖f t‖ + 1`, which lies in `H` once `re t` beats `‖f t‖ = O(log ‖t‖)`.
-/

open Asymptotics Filter
open Complex (log)
open Set
open scoped NNReal Topology

namespace NearTranslation

variable {G : ℂ → ℂ} {β : ℂ} {R A δ : ℝ}

/-- Shrinking the half-plane preserves near-translations -/
public lemma mono (h : NearTranslation G β R A δ) {R' : ℝ} (RR : R ≤ R') : NearTranslation G β R' A δ where
  four_le := le_trans h.four_le RR
  large := le_trans h.large RR
  A0 := h.A0
  δ0 := h.δ0
  δ1 := h.δ1
  ga := fun w m ↦ h.ga w (lt_of_le_of_lt RR m)
  approx := fun w m ↦ h.approx w (lt_of_le_of_lt RR m)

/-- Banach's fixed point theorem on a closed disk, for a `1/2`-contraction -/
lemma exists_fixed {T : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (maps : MapsTo T (Metric.closedBall c ρ) (Metric.closedBall c ρ))
    (lip : ∀ x ∈ Metric.closedBall c ρ, ∀ y ∈ Metric.closedBall c ρ, ‖T x - T y‖ ≤ 1 / 2 * ‖x - y‖)
    (ρ0 : 0 ≤ ρ) : ∃ z ∈ Metric.closedBall c ρ, T z = z := by
  have cs : ContractingWith (1 / 2 : ℝ≥0) (maps.restrict T _ _) := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; norm_num, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    have := lip x x.2 y y.2
    simpa using this
  obtain ⟨z, zm, fz, -⟩ := cs.exists_fixedPoint' (Metric.isClosed_closedBall.isComplete) maps
    (Metric.mem_closedBall_self ρ0) (edist_ne_top _ _)
  exact ⟨z, zm, fz⟩

/-- Every point enters the image of the Fatou coordinate after enough steps -/
lemma exists_shift_mem (h : NearTranslation G β R A δ) {a : ℝ} (Ra : R ≤ a) (Sa : tailBound β A δ a ≤ 1 / 4)
    (lip : ∀ x ∈ rightHalf (2 * a), ∀ y ∈ rightHalf (2 * a),
      ‖(fatou G β x - x) - (fatou G β y - y)‖ ≤ 1 / 2 * ‖x - y‖) (ζ : ℂ) :
    ∃ n : ℕ, ζ + n ∈ fatou G β '' rightHalf (2 * a) := by
  have a4 : 4 ≤ a := le_trans h.four_le Ra
  set f := fun z ↦ fatou G β z - z with hf
  set p : ℝ := 2 * a + 1
  set K : ℝ := ‖ζ - p‖ / 2 + 1 / 4
  -- `2 ‖β‖ log x ≤ x / 2` eventually
  have lg : ∀ᶠ x : ℝ in atTop, 2 * ‖β‖ * Real.log x ≤ x / 2 := by
    have := Real.isLittleO_log_id_atTop.bound (c := 1 / (4 * ‖β‖ + 1)) (by positivity)
    filter_upwards [this, eventually_ge_atTop 1] with x hx x1
    simp only [Real.norm_eq_abs, id] at hx
    rw [abs_of_nonneg (Real.log_nonneg x1), abs_of_nonneg (by linarith)] at hx
    have : 2 * ‖β‖ * Real.log x ≤ 2 * ‖β‖ * (1 / (4 * ‖β‖ + 1) * x) := by gcongr
    refine le_trans this ?_
    rw [div_eq_mul_inv]
    have b0 := norm_nonneg β
    field_simp
    nlinarith
  have tn : Tendsto (fun n : ℕ ↦ p + n) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  obtain ⟨n, hn, big⟩ := ((tn.eventually lg).and (eventually_ge_atTop
    (⌈2 * (|p| + ‖ζ‖ + 2 * K + 2 * a + 4)⌉₊))).exists
  have nb : 2 * (|p| + ‖ζ‖ + 2 * K + 2 * a + 4) ≤ n := Nat.le_of_ceil_le big
  set t := ζ + n
  set x : ℂ := ((p + n : ℝ) : ℂ)
  have xr : x.re = p + n := by simp [x]
  have tr : 2 * a + 2 * K + 2 * ‖β‖ * Real.log (p + n) + 2 < t.re := by
    have := Complex.abs_re_le_norm ζ
    rw [abs_le] at this
    have pa : |p| = p := abs_of_pos (by positivity)
    simp only [t, Complex.add_re, Complex.natCast_re]
    nlinarith
  have xH : x ∈ rightHalf (2 * a) := by
    show 2 * a < x.re; rw [xr]; have := Nat.cast_nonneg (α := ℝ) n; simp only [p]; linarith
  -- `‖f x‖ ≤ ‖β‖ log x + 1/4` on the real axis
  have fx : ‖f x‖ ≤ ‖β‖ * Real.log (p + n) + 1 / 4 := by
    have xm : x ∈ rightHalf R := by show R < x.re; have := xH; simp only [rightHalf, mem_ofPred_eq] at this; linarith
    have e := h.fatou_sub_approx_le xm Ra (by rw [xr]; have := Nat.cast_nonneg (α := ℝ) n; simp only [p]; linarith)
    have px : 0 < p + n := by positivity
    have lx : log x = (Real.log (p + n) : ℂ) := by simp only [x]; exact (Complex.ofReal_log px.le).symm
    have l0 : 0 ≤ Real.log (p + n) := Real.log_nonneg (by simp only [p]; have := Nat.cast_nonneg (α := ℝ) n; linarith)
    calc ‖f x‖ = ‖(fatou G β x - approxFatou β x) - β * log x‖ := by simp only [hf, approxFatou]; ring_nf
      _ ≤ ‖fatou G β x - approxFatou β x‖ + ‖β * log x‖ := norm_sub_le _ _
      _ ≤ 1 / 4 + ‖β‖ * Real.log (p + n) := by
          rw [norm_mul, lx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg l0]; linarith
      _ = _ := by ring
  have tH : t ∈ rightHalf (2 * a) := by
    show 2 * a < t.re; have := mul_nonneg (norm_nonneg β) (Real.log_nonneg (show (1 : ℝ) ≤ p + n by
      simp only [p]; have := Nat.cast_nonneg (α := ℝ) n; linarith)); unfold K at tr; nlinarith [norm_nonneg (ζ - p)]
  have ft : ‖f t‖ ≤ K + ‖β‖ * Real.log (p + n) := by
    have l := lip t tH x xH
    have tx : t - x = ζ - p := by simp only [t, x]; push_cast; ring
    rw [tx] at l
    calc ‖f t‖ ≤ ‖f x‖ + ‖f t - f x‖ := by
          have := norm_add_le (f x) (f t - f x); simp only [add_sub_cancel] at this; exact this
      _ ≤ _ := by unfold K; simp only [hf] at l ⊢; linarith
  -- the contraction `z ↦ t - f z` on the disk of radius `ρ = 2 ‖f t‖ + 1` around `t`
  set ρ := 2 * ‖f t‖ + 1
  have bH : Metric.closedBall t ρ ⊆ rightHalf (2 * a) := by
    intro z zb
    have := le_trans (Complex.abs_re_le_norm (z - t)) (by simpa [dist_eq_norm] using zb)
    rw [abs_le, Complex.sub_re] at this
    show 2 * a < z.re
    simp only [ρ] at this
    linarith
  obtain ⟨z, zb, fz⟩ := exists_fixed (T := fun z ↦ t - f z) (c := t) (ρ := ρ)
    (fun z zb ↦ by
      simp only [Metric.mem_closedBall, dist_eq_norm] at zb ⊢
      have l := lip z (bH (by simpa [dist_eq_norm] using zb)) t tH
      calc ‖t - f z - t‖ = ‖f z‖ := by rw [sub_sub_cancel_left, norm_neg]
        _ ≤ ‖f t‖ + ‖f z - f t‖ := by
            have := norm_add_le (f t) (f z - f t); simp only [add_sub_cancel] at this; exact this
        _ ≤ ‖f t‖ + 1 / 2 * ‖z - t‖ := by simp only [hf] at l ⊢; linarith
        _ ≤ ρ := by simp only [ρ]; nlinarith [norm_nonneg (f t)])
    (fun x xb y yb ↦ by
      have l := lip x (bH xb) y (bH yb)
      rw [show t - f x - (t - f y) = -(f x - f y) by ring, norm_neg]
      simpa only [hf] using l)
    (by positivity)
  refine ⟨n, z, bH zb, ?_⟩
  have e : fatou G β z = z + f z := by simp [hf]
  have ht : t = ζ + n := rfl
  linear_combination e - fz + ht

/-- The Fatou parametrisation: on a half-plane `H` where `Φ` is injective, `Φ H` is open, every point enters it after
enough steps, and `Φ⁻¹ : Φ H → H` is analytic -/
public theorem fatou_param (h : NearTranslation G β R A δ) :
    ∃ R' ≥ R, ∃ Ψ : ℂ → ℂ, InjOn (fatou G β) (rightHalf R') ∧ IsOpen (fatou G β '' rightHalf R') ∧
      (∀ ζ : ℂ, ∃ n : ℕ, ζ + n ∈ fatou G β '' rightHalf R') ∧
      AnalyticOnNhd ℂ Ψ (fatou G β '' rightHalf R') ∧ (∀ w ∈ rightHalf R', Ψ (fatou G β w) = w) := by
  obtain ⟨a, Ra, Sa, -, lip⟩ := h.exists_lip
  have a4 : 4 ≤ a := le_trans h.four_le Ra
  set H := rightHalf (2 * a)
  have HR : H ⊆ rightHalf R := fun w m ↦ by
    simp only [H, rightHalf, mem_ofPred_eq] at m ⊢; linarith
  have inj : InjOn (fatou G β) H := fun x xm y ym e ↦ by
    have mv := lip x xm y ym
    rw [show fatou G β x - x - (fatou G β y - y) = y - x by rw [e]; ring, norm_sub_rev] at mv
    have : ‖x - y‖ = 0 := by linarith [norm_nonneg (x - y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have fa : AnalyticOnNhd ℂ (fatou G β) H := fun w m ↦ h.fatou_analytic w (HR m)
  obtain ⟨Ψ, Ψa, Ψf⟩ := global_complex_inverse_fun_open'' fa inj (isOpen_rightHalf _)
  refine ⟨2 * a, by linarith, Ψ, inj, ?_, h.exists_shift_mem Ra Sa lip, Ψa, Ψf⟩
  -- open mapping: `Φ` is not constant, being injective
  rcases fa.is_constant_or_isOpen (convex_halfSpace_re_gt (2 * a)).isPreconnected with ⟨c, hc⟩ | o
  · exfalso
    have m1 : ((2 * a + 1 : ℝ) : ℂ) ∈ H := by show 2 * a < _; simp
    have m2 : ((2 * a + 2 : ℝ) : ℂ) ∈ H := by show 2 * a < _; simp
    have := inj m1 m2 (by rw [hc _ m1, hc _ m2])
    simp only [Complex.ofReal_inj] at this; linarith
  · exact o H subset_rfl (isOpen_rightHalf _)

end NearTranslation

namespace NearTranslationOut

variable {G : ℂ → ℂ} {β : ℂ} {R A δ : ℝ}

/-- The repelling Fatou parametrisation, with values in any given left half-plane -/
public theorem repel_param (h : NearTranslationOut G β R A δ) (R₁ : ℝ) :
    ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧ (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧
      AnalyticOnNhd ℂ Ψ V ∧ (∀ ζ ∈ V, Ψ ζ ∈ leftHalf R₁) ∧ (∀ ζ ∈ V, G (Ψ (ζ - 1)) = Ψ ζ) := by
  set R₂ := max R₁ (repR β R A)
  have hF := h.reflInv_nearTranslation.mono (le_max_right R₁ (repR β R A))
  obtain ⟨R', RR, Ψ, -, Wo, reach, Ψa, Ψf⟩ := hF.fatou_param
  set F := reflInv G
  set W := NearTranslation.fatou F (-β) '' rightHalf R'
  have sub : ∀ {w}, w ∈ rightHalf R' → w ∈ rightHalf R₂ := fun {w} m ↦ by
    simp only [rightHalf, mem_ofPred_eq] at m ⊢; linarith
  have hF' := hF.mono RR
  have ΨW : ∀ ζ ∈ W, Ψ ζ ∈ rightHalf R' ∧ NearTranslation.fatou F (-β) (Ψ ζ) = ζ := by
    rintro _ ⟨w, wm, rfl⟩; rw [Ψf w wm]; exact ⟨wm, rfl⟩
  have Wr : ∀ ζ ∈ W, ζ + 1 ∈ W := by
    rintro _ ⟨w, wm, rfl⟩; exact ⟨F w, hF'.mapsTo wm, hF.fatou_eqn (sub wm)⟩
  refine ⟨(fun ζ ↦ -ζ) ⁻¹' W, fun ζ ↦ -Ψ (-ζ), Wo.preimage continuous_neg, fun ζ m ↦ ?_, fun ζ ↦ ?_,
    fun ζ m ↦ ?_, fun ζ m ↦ ?_, fun ζ m ↦ ?_⟩
  · have := Wr _ m; simp only [mem_preimage] at this ⊢; rwa [neg_sub, sub_eq_neg_add]
  · obtain ⟨n, m⟩ := reach (-ζ); exact ⟨n, by simp only [mem_preimage, neg_sub]; rwa [sub_eq_neg_add]⟩
  · exact ((Ψa _ m).comp (f := fun ζ : ℂ ↦ -ζ) analyticAt_id.neg).neg
  · have := (ΨW _ m).1
    simp only [leftHalf, rightHalf, mem_ofPred_eq, Complex.neg_re] at this ⊢
    have := le_max_left R₁ (repR β R A); linarith
  · -- `Ψ (-(ζ - 1)) = F (Ψ (-ζ))`, and `-F w = G⁻¹ (-w)`
    obtain ⟨wm, fw⟩ := ΨW _ m
    set w := Ψ (-ζ)
    have e1 : Ψ (-(ζ - 1)) = F w := by
      rw [← Ψf (F w) (hF'.mapsTo wm), hF.fatou_eqn (sub wm), fw]; ring_nf
    simp only [e1, F, reflInv, neg_neg]
    refine h.apply_inv ?_
    simp only [leftHalf, rightHalf, mem_ofPred_eq, Complex.neg_re] at wm ⊢
    have : 4 * R ≤ repR β R A := by
      unfold repR repA; have := h.A0; have := h.four_le; nlinarith [norm_nonneg β]
    have := le_max_right R₁ (repR β R A); linarith

end NearTranslationOut
