module
public import Ray.Schwarz.Defs
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Schwarz
import Ray.Analytic.Analytic
import Ray.Misc.Bound
import Ray.Schwarz.Mobius

/-!
## Schwarz-Pick theorem

The Schwarz-Pick theorem provides the tightest bounds on finite differences and derivatives of
an anlytic function on the unit disk:

  https://en.wikipedia.org/wiki/Schwarz_lemma#Schwarz%E2%80%93Pick_theorem

For downstream convenience, we prove slightly stronger versions that require mapping into the closed
disk, rather than open disk. This is essentially the same by the open mapping theorem, but demands
only nonstrict inequalities from downstream users.
-/

open Filter (Tendsto)
open Metric (ball closedBall isOpen_ball)
open Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section

variable {w z c0 c1 : ℂ} {f : ℂ → ℂ} {r r0 r1 : ℝ}

/-!
### Slightly stronger version of Schwarz for convenience, only requiring mapping to the closed disk
-/

/-- An analytic function from open to closed balls maps to the open ball, or is constant -/
lemma MapsTo.mapsTo_ball (fa : ContDiffOn ℂ ω f (ball c0 r0))
    (fm : MapsTo f (ball c0 r0) (closedBall c1 r1)) :
    (∃ w, ∀ z ∈ ball c0 r0, f z = w) ∨ MapsTo f (ball c0 r0) (ball c1 r1) := by
  by_cases r0p : r0 ≤ 0
  · simp [Metric.ball_eq_empty.mpr r0p]
  simp only [not_le] at r0p
  have r1p : 0 ≤ r1 := by contrapose fm; simp [Metric.closedBall_eq_empty.mpr (not_le.mp fm), r0p]
  by_cases r1z : r1 = 0
  · simp only [MapsTo, Metric.mem_ball, dist_eq_norm, r1z, Metric.closedBall_zero,
      mem_singleton_iff, Metric.ball_zero, mem_empty_iff_false, imp_false, not_lt] at fm ⊢
    exact .inl ⟨c1, fun z zr ↦ fm zr⟩
  replace r1p : 0 < r1 := (Ne.symm r1z).lt_of_le r1p
  rcases (fa.analyticOnNhd isOpen_ball).is_constant_or_isOpen (g := f) (U := ball c0 r0)
    (convex_ball _ _).isPreconnected with c | o
  · exact .inl c
  · right
    simp only [mapsTo_iff_image_subset] at fm ⊢
    simpa only [interior_closedBall _ r1p.ne'] using
      interior_maximal fm (o (ball c0 r0) (by rfl) isOpen_ball)

/-- Slightly stronger version of Schwarz, requiring mapping to the closed disk only -/
lemma ContDiffOn.norm_le_norm_of_mapsTo_closedBall (fa : ContDiffOn ℂ ω f (ball 0 r))
    (fm : MapsTo f (ball 0 r) (closedBall 0 r)) (f0 : f 0 = 0) (zr : ‖z‖ < r) : ‖f z‖ ≤ ‖z‖ := by
  have r0 : 0 < r := lt_of_le_of_lt (by bound) zr
  rcases MapsTo.mapsTo_ball fa fm with ⟨w,c⟩ | m
  · have w0 := f0 ▸ c 0 (by simp [r0])
    rw [c _ (by simp [zr]), ← w0, norm_zero]
    bound
  · exact Complex.norm_le_norm_of_mapsTo_ball (fa.differentiableOn (by decide)) fm f0 zr

/-!
### Unit ball versions
-/

/-- Finite difference version of Schwarz-Pick for the unit disk -/
public lemma ContDiffOn.dist_le_mul_mobius_of_mapsTo_unit_ball (fa : ContDiffOn ℂ ω f (ball 0 1))
    (fi : MapsTo f (ball 0 1) (closedBall 0 1)) (z1 : ‖z‖ < 1) (w1 : ‖w‖ < 1) :
    ‖f z - f w‖ ≤ ‖1 - conj (f z) * f w‖ * ‖mobius z w‖ := by
  rcases MapsTo.mapsTo_ball fa fi with ⟨a,c⟩ | fi
  · rw [c _ (by simpa), c _ (by simpa), sub_self, norm_zero]
    bound
  have fz1 : ‖f z‖ < 1 := by simpa using fi (x := z) (by simpa)
  have fw1 : ‖f w‖ < 1 := by simpa using fi (x := w) (by simpa)
  set g := mobius (f z) ∘ f ∘ mobius z
  have gm' := fi.comp (mapsTo_mobius z1)
  have gm : MapsTo g (ball 0 1) (ball 0 1) := (mapsTo_mobius fz1).comp gm'
  have gm_closed : MapsTo g (ball 0 1) (closedBall 0 1) :=
    gm.mono_right Metric.ball_subset_closedBall
  have ga : ContDiffOn ℂ ω g (ball 0 1) :=
    (contDiffOn_mobius fz1).comp (fa.comp (contDiffOn_mobius z1) (mapsTo_mobius z1)) gm'
  have g0 : g 0 = 0 := by simp only [g, Function.comp_apply, mobius_zero, mobius_self]
  set u := mobius z w
  have u1 : ‖u‖ < 1 := norm_mobius_lt_one z1 w1
  simpa only [g, Function.comp_apply, mobius_def (f z), u, mobius_mobius z1 w1, norm_div,
    div_le_iff₀ (norm_mobius_denom_pos fz1 fw1), mul_comm ‖mobius _ _‖] using
    Complex.norm_le_norm_of_mapsTo_ball (ga.differentiableOn (by decide)) gm_closed g0 u1

/-- Derivative version of Schwarz-Pick for the unit disk -/
public lemma ContDiffOn.norm_deriv_le_div_of_mapsTo_unit_ball (fa : ContDiffOn ℂ ω f (ball 0 1))
    (fi : MapsTo f (ball 0 1) (closedBall 0 1)) (z1 : ‖z‖ < 1) :
    ‖deriv f z‖ ≤ (1 - ‖f z‖ ^ 2) / (1 - ‖z‖ ^ 2) := by
  rcases MapsTo.mapsTo_ball fa fi with ⟨a,c⟩ | fi'
  · rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ a), deriv_const, norm_zero]
    · have fz1 : ‖f z‖ ≤ 1 := by simpa using fi (x := z) (by simpa)
      bound
    · have z1' : z ∈ ball 0 1 := by simpa using z1
      filter_upwards [isOpen_ball.eventually_mem z1'] with w w1
      exact c w w1
  have zm : z ∈ ball 0 1 := by simpa using z1
  have fz1 : ‖f z‖ < 1 := by simpa using fi' (x := z) (by simpa)
  have df := (fa.differentiableOn (by decide)).differentiableAt (x := z) (isOpen_ball.mem_nhds zm)
  have s : ∀ᶠ w in 𝓝[≠] z, ‖slope f z w‖ - ‖1 - conj (f z) * f w‖ / ‖1 - conj z * w‖ ≤ 0 := by
    simp only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff]
    filter_upwards [isOpen_ball.eventually_mem zm] with w w1 wz
    simp only [Metric.mem_ball, dist_zero_right] at w1
    have s := ContDiffOn.dist_le_mul_mobius_of_mapsTo_unit_ball fa fi z1 w1
    simp only [mobius_def, Complex.norm_div, ← mul_div_assoc, mul_div_right_comm] at s
    rw [← div_le_iff₀ (norm_pos_iff.mpr (by grind))] at s
    simpa [slope, ← div_eq_inv_mul, norm_sub_rev (f w), norm_sub_rev w]
  have dc : ContinuousAt (fun w ↦ ‖1 - conj (f z) * f w‖ / ‖1 - conj z * w‖) z :=
    ContinuousAt.div
      (by simpa using (ContinuousAt.norm <| continuousAt_const.sub <| df.continuousAt.const_mul
        (conj (f z))))
      (by fun_prop) (norm_mobius_denom_pos z1 z1).ne'
  have t1 := (continuous_norm.tendsto _).comp df.hasDerivAt.tendsto_slope
  have t2 := dc.tendsto
  have e : ∀ x : ℝ, (1 - x : ℂ) = (1 - x : ℝ) := by simp
  have n : ∀ {z : ℂ}, ‖z‖ < 1 → |1 - ‖z‖ ^ 2| = (1 - ‖z‖ ^ 2) := by
    intro z z1
    rw [abs_of_nonneg]
    bound
  simp only [Function.comp_def, Complex.conj_mul', ← Complex.ofReal_pow, e, Complex.norm_real,
    Real.norm_eq_abs, n z1, n fz1] at t1 t2
  rw [← sub_nonpos]
  exact le_of_tendsto (t1.sub (t2.mono_left nhdsWithin_le_nhds)) s

/-!
### Variable radii versions

We leave the centres at zero since otherwise the statements get very messy.
-/

/-- Holomorphicity and boundedness of the scaled function -/
lemma scaled_prop (fa : ContDiffOn ℂ ω f (ball 0 r0))
    (fi : MapsTo f (ball 0 r0) (closedBall 0 r1)) (r0p : 0 < r0) :
    let g := fun z ↦ r1⁻¹ * (f (r0 * z))
    ContDiffOn ℂ ω g (ball 0 1) ∧ MapsTo g (ball 0 1) (closedBall 0 1) := by
  have r1p : 0 ≤ r1 := by contrapose fi; simp [Metric.closedBall_eq_empty.mpr (not_le.mp fi), r0p]
  have r0z : (r0 : ℂ) ≠ 0 := by simp [r0p.ne']
  constructor
  · intro z z1
    simp only [Metric.mem_ball, dist_zero_right] at z1
    refine contDiffWithinAt_const.mul ?_
    refine (fa _ (by simp [abs_of_pos r0p]; bound)).comp _ (by fun_prop) ?_
    intro w w1
    simp [abs_of_pos r0p] at w1 ⊢
    bound
  · intro z z1
    simp only [Metric.mem_ball, dist_zero_right] at z1
    by_cases r1z : r1 = 0
    · simp [r1z]
    replace r1p : 0 < r1 := (Ne.symm r1z).lt_of_le r1p
    simp [← div_eq_inv_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r1p, div_le_iff₀ r1p,
      one_mul] at z1 ⊢
    simpa using fi (x := r0 * z) (by simp [abs_of_pos r0p]; bound)

/-- Finite difference version of Schwarz-Pick for disks of any radii -/
public lemma Complex.dist_le_mul_mobius_of_mapsTo_ball (fa : ContDiffOn ℂ ω f (ball 0 r0))
    (fi : MapsTo f (ball 0 r0) (closedBall 0 r1)) (zr : ‖z‖ < r0) (wr : ‖w‖ < r0) :
    ‖f z - f w‖ ≤ r0 / r1 * ‖r1 ^ 2 - conj (f z) * f w‖ * ‖z - w‖ / ‖r0 ^ 2 - conj z * w‖ := by
  have r0p : 0 < r0 := lt_of_le_of_lt (by bound) zr
  have r1p : 0 ≤ r1 := by contrapose fi; simp [Metric.closedBall_eq_empty.mpr (not_le.mp fi), r0p]
  by_cases r1z : r1 = 0
  · simp only [MapsTo, Metric.mem_ball, dist_zero_right, r1z, Metric.closedBall_zero,
      mem_singleton_iff] at fi
    simp [r1z, fi zr, fi wr]
  replace r1p : 0 < r1 := (Ne.symm r1z).lt_of_le r1p
  have r0z : (r0 : ℂ) ≠ 0 := by simp [r0p.ne']
  obtain ⟨ga, gm⟩ := scaled_prop fa fi r0p
  have s := ContDiffOn.dist_le_mul_mobius_of_mapsTo_unit_ball ga gm (z := r0⁻¹ * z) (w := r0⁻¹ * w)
    (by simpa [abs_of_pos r0p, ← div_eq_inv_mul, div_lt_iff₀ r0p])
    (by simpa [abs_of_pos r0p, ← div_eq_inv_mul, div_lt_iff₀ r0p])
  simp only [mobius_denom_inv_mul r1p.ne', mobius_denom_inv_mul r0p.ne', norm_mul, mobius_def] at s
  simp only [← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ r0z, one_mul, ← mul_sub, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r1p, norm_pow, norm_div,
    abs_of_pos r0p, ← div_eq_inv_mul _ r1, div_le_iff₀ r1p] at s
  exact le_trans s (le_of_eq (by field_simp [r0p.ne', r1p.ne']))

/-- Derivative version of Schwarz-Pick for disks of any radii -/
public lemma Complex.norm_deriv_le_mul_div_of_mapsTo_ball (fa : ContDiffOn ℂ ω f (ball 0 r0))
    (fi : MapsTo f (ball 0 r0) (closedBall 0 r1)) (zr : ‖z‖ < r0) :
    ‖deriv f z‖ ≤ r0 / r1 * (r1 ^ 2 - ‖f z‖ ^ 2) / (r0 ^ 2 - ‖z‖ ^ 2) := by
  have r0p : 0 < r0 := lt_of_le_of_lt (by bound) zr
  have r1p : 0 ≤ r1 := by contrapose fi; simp [Metric.closedBall_eq_empty.mpr (not_le.mp fi), r0p]
  by_cases r1z : r1 = 0
  · simp only [MapsTo, Metric.mem_ball, dist_zero_right, r1z, Metric.closedBall_zero,
      mem_singleton_iff] at fi
    rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ 0), deriv_const, norm_zero, fi zr]
    · bound
    · have zr' : z ∈ ball 0 r0 := by simpa using zr
      filter_upwards [isOpen_ball.eventually_mem zr'] with w wr
      exact fi (x := w) (by simpa using wr)
  replace r1p : 0 < r1 := (Ne.symm r1z).lt_of_le r1p
  have r0z : (r0 : ℂ) ≠ 0 := by simp [r0p.ne']
  obtain ⟨ga, gm⟩ := scaled_prop fa fi r0p
  have s := ContDiffOn.norm_deriv_le_div_of_mapsTo_unit_ball ga gm (z := r0⁻¹ * z)
    (by simpa [abs_of_pos r0p, ← div_eq_inv_mul, div_lt_iff₀ r0p])
  have e : ∀ {a b : ℝ}, 0 < a → 1 - (a ^ 2)⁻¹ * b = (a ^ 2)⁻¹ * (a ^ 2 - b) := by intros; field_simp
  simp only [ofReal_inv, deriv_const_mul_field', deriv_comp_mul_left,
    ← mul_assoc, mul_inv_cancel₀ r0z, one_mul, smul_eq_mul, Complex.norm_mul, norm_inv, norm_real,
    Real.norm_eq_abs, abs_of_pos r1p, abs_of_pos r0p, mul_pow, inv_pow, e r1p, e r0p] at s
  rw [mul_comm _ ‖deriv _ _‖, ← le_div_iff₀ (by positivity)] at s
  exact le_trans s (le_of_eq (by field_simp [r0p.ne', r1p.ne']))
