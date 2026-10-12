module
public import Ray.Dynamics.Parabolic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Bound

/-!
## The ends of the horn map

For `ζ` with large imaginary part, the repelling parametrisation lands in the basin of the adjacent attracting petal,
and the horn map is `H ζ = ζ - π i β + o(1)`.

The reason is that the attracting and repelling petal charts are the same branch on the upper half of the petal
plane: there both Fatou coordinates are defined, `Φ_att w ≈ w - β log w` and `Φ_rep w ≈ w - β log (-w)`, and
`log w - log (-w) = π i`.

1. `PetalGerm.upper`: far out in the upper half-plane the attracting chart is a near-translation chart and still
   semiconjugates (branch consistency through the rotated branch `c' exp (-log (-i w) / k)`).
-/

open Classical
open Complex (exp log slitPlane arg I)
open Filter
open Set
open scoped Real Topology

variable {g : ℂ → ℂ} {k : ℕ} {a b : ℂ}

/-- On the upper half-plane the principal branch is a rotated branch -/
lemma root_rotate {c v : ℂ} (vi : 0 < v.im) :
    petalRoot k c v = petalRoot k (c * exp (-(π / 2 * I) / k)) (-I * v) := by
  have v0 : v ≠ 0 := fun e ↦ by simp [e] at vi
  have hl : log (-I * v) = log (-I) + log v := by
    refine (Complex.log_mul_eq_add_log_iff (by simp) v0).mpr ?_
    rw [Complex.arg_neg_I]
    have a0 : 0 ≤ arg v := Complex.arg_nonneg_iff.mpr vi.le
    have a1 := Complex.arg_le_pi v
    constructor <;> linarith [Real.pi_pos]
  simp only [petalRoot, hl, Complex.log_neg_I, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Far out in the upper half-plane, the attracting chart of a germ in normal form is a near-translation chart with
step within `1/4` of `1`, and it semiconjugates -/
public lemma PetalGerm.upper (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = -1 / (k * a)) :
    ∃ R A : ℝ, 4 ≤ R ∧ 0 ≤ A ∧ 4 * (‖petalResidue k a b‖ + A) ≤ R ∧ ∀ w : ℂ, R < w.im →
      AnalyticAt ℂ (fun w ↦ petalCoord k a (g (petalRoot k c w))) w ∧
      ‖petalCoord k a (g (petalRoot k c w)) - (w + 1 + petalResidue k a b / w)‖ ≤
        A / ‖w‖ ^ (1 + (k : ℝ)⁻¹) ∧
      ‖petalCoord k a (g (petalRoot k c w)) - (w + 1)‖ ≤ 1 / 4 ∧
      g (petalRoot k c w) = petalRoot k c (petalCoord k a (g (petalRoot k c w))) := by
  have k0 := h.k0
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  have a0 := h.a0
  have c0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow k0.ne'] at hc
    exact div_ne_zero (by norm_num) (mul_ne_zero kc a0) hc.symm
  obtain ⟨R₀, A, A0, ht⟩ := h.transfer
  set β := petalResidue k a b
  set R := max R₀ (max 4 (4 * (‖β‖ + A)))
  have R4 : 4 ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
  have Rl : 4 * (‖β‖ + A) ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨R, A, R4, A0, Rl, fun w wi ↦ ?_⟩
  have wn : R < ‖w‖ := lt_of_lt_of_le wi (le_trans (le_abs_self _) (Complex.abs_im_le_norm w))
  have w0 : w ≠ 0 := fun e ↦ by simp [e] at wn; linarith
  have zk : (petalRoot k c w) ^ k = -1 / (k * a * w) := by
    rw [PetalGerm.root_pow w0 k0, hc]; field_simp
  obtain ⟨ga, g0, ⟨u, gu, ku⟩, -, est⟩ :=
    ht w _ (lt_of_le_of_lt (le_max_left _ _) wn) zk
  set G' := petalCoord k a (g (petalRoot k c w))
  have sm : w ∈ slitPlane := by rw [Complex.mem_slitPlane_iff]; right; exact (ne_of_gt (by linarith))
  -- the step is within `1/4` of `1`
  have n1 : 1 ≤ ‖w‖ := by linarith
  have dv : ‖G' - (w + 1)‖ ≤ 1 / 4 := by
    have r1 : ‖w‖ ≤ ‖w‖ ^ (1 + (k : ℝ)⁻¹) := by
      have : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
      simpa using Real.rpow_le_rpow_of_exponent_le n1 (by linarith : (1 : ℝ) ≤ 1 + (k : ℝ)⁻¹)
    have e2 : A / ‖w‖ ^ (1 + (k : ℝ)⁻¹) ≤ A / ‖w‖ := div_le_div_of_nonneg_left A0 (by positivity) r1
    calc ‖G' - (w + 1)‖ = ‖(G' - (w + 1 + β / w)) + β / w‖ := by ring_nf
      _ ≤ ‖G' - (w + 1 + β / w)‖ + ‖β / w‖ := norm_add_le _ _
      _ ≤ A / ‖w‖ + ‖β‖ / ‖w‖ := by rw [norm_div]; linarith
      _ = (‖β‖ + A) / ‖w‖ := by ring
      _ ≤ 1 / 4 := by rw [div_le_iff₀ (by linarith)]; linarith
  have pa : AnalyticAt ℂ (petalCoord k a) (g (petalRoot k c w)) := PetalGerm.analyticAt_petalCoord g0 kc a0
  refine ⟨pa.comp (f := fun w ↦ g (petalRoot k c w))
    (ga.comp (f := fun w ↦ petalRoot k c w) (PetalGerm.analyticAt_root sm)), est, dv, ?_⟩
  -- branch consistency in the rotated chart `s = -i w`
  have Gi : 0 < G'.im := by
    have := le_trans (Complex.abs_im_le_norm _) dv
    rw [abs_le] at this
    simp only [Complex.sub_im, Complex.add_im, Complex.one_im] at this
    linarith
  have G0 : G' ≠ 0 := fun e ↦ by simp [e] at Gi
  obtain ⟨u', hs, un'⟩ := PetalGerm.step_ratio (w := w) (w' := G') (by linarith) (PetalGerm.step_le dv)
  set c' := c * exp (-(π / 2 * I) / k)
  have c'0 : c' ≠ 0 := mul_ne_zero c0 (Complex.exp_ne_zero _)
  have sr : 0 < (-I * w).re := by simp; linarith
  have hs' : -I * G' = (-I * w) * (1 + u') := by rw [hs]; ring
  rw [gu, root_rotate (k := k) (c := c) (by linarith : 0 < w.im), root_rotate (k := k) (c := c) Gi]
  refine PetalGerm.branch k0 c'0 sr hs' un' ku ?_
  rw [← root_rotate (by linarith : 0 < w.im), ← root_rotate Gi, ← gu, PetalGerm.root_pow G0 k0, hc]
  have gk : g (petalRoot k c w) ^ k ≠ 0 := pow_ne_zero _ g0
  simp only [G', petalCoord]
  field_simp
