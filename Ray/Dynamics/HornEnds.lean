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

/-!
### Orbits in the upper half-plane
-/

/-- `log` is additive along a short step that stays in the upper half-plane -/
lemma log_mul_upper {x y : ℂ} (xi : 0 < x.im) (yr : 0 < y.re) (xyi : 0 < (x * y).im) :
    log (x * y) = log x + log y := by
  set x' := -I * x
  have hx : x = I * x' := by simp only [x']; ring_nf; rw [Complex.I_sq]; ring
  have x'r : 0 < x'.re := by simp [x', xi]
  set v := x' * y
  have hv : x * y = I * v := by rw [hx]; ring
  have vr : 0 < v.re := by rw [hv] at xyi; simpa using xyi
  have ne : ∀ {z : ℂ}, 0 < z.re → z ≠ 0 := fun r e ↦ by simp [e] at r
  have ar : ∀ {z : ℂ}, 0 < z.re → -(π / 2) < arg z ∧ arg z < π / 2 := fun r ↦ by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl r); rwa [abs_lt] at this
  have lI : ∀ {z : ℂ}, 0 < z.re → log (I * z) = log I + log z := fun r ↦ by
    refine (Complex.log_mul_eq_add_log_iff Complex.I_ne_zero (ne r)).mpr ?_
    rw [Complex.arg_I]; have := ar r; constructor <;> linarith [Real.pi_pos]
  have l3 : log v = log x' + log y := by
    refine (Complex.log_mul_eq_add_log_iff (ne x'r) (ne yr)).mpr ?_
    have := ar x'r; have := ar yr; constructor <;> linarith [Real.pi_pos]
  rw [hv, lI vr, l3, hx, lI x'r]; ring

section Upper

variable {G : ℂ → ℂ} {β : ℂ} {R A δ : ℝ}

/-- Orbits starting high enough march right and stay in the upper region -/
lemma up_orbit (up : ∀ w : ℂ, R < w.im → ‖G w - (w + 1)‖ ≤ 1 / 4) {n : ℕ} {w : ℂ}
    (wi : R + n / 4 < w.im) : ∀ j ≤ n, w.im - j / 4 ≤ (G^[j] w).im ∧ w.re + 3 / 4 * j ≤ (G^[j] w).re := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro jn
    obtain ⟨i1, r1⟩ := ih (by omega)
    have jn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast jn
    have vi : R < (G^[j] w).im := by linarith
    have d := le_trans (Complex.abs_re_le_norm _) (up _ vi)
    have d' := le_trans (Complex.abs_im_le_norm _) (up _ vi)
    rw [abs_le] at d d'
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.one_im] at d d'
    rw [Function.iterate_succ_apply']
    push_cast
    constructor <;> linarith

/-- The approximate coordinate changes by `n` along `n` steps, up to `n K / (im w - n/4)^(1+δ)` -/
lemma up_sum (R4 : 4 ≤ R) (A0 : 0 ≤ A) (δ0 : 0 < δ) (δ1 : δ ≤ 1)
    (up : ∀ w : ℂ, R < w.im → ‖G w - (w + 1 + β / w)‖ ≤ A / ‖w‖ ^ (1 + δ) ∧ ‖G w - (w + 1)‖ ≤ 1 / 4)
    {n : ℕ} {w : ℂ} (wi : R + n / 4 < w.im) :
    ‖approxFatou β (G^[n] w) - n - approxFatou β w‖ ≤
      n * ((A + ‖β‖ * (‖β‖ + A + 2)) / (w.im - n / 4) ^ (1 + δ)) := by
  have orb := up_orbit (fun w m ↦ (up w m).2) wi
  set K := A + ‖β‖ * (‖β‖ + A + 2)
  have K0 : 0 ≤ K := by positivity
  have Y0 : 0 < w.im - n / 4 := by linarith
  have step : ∀ j < n, ‖approxFatou β (G^[j + 1] w) - approxFatou β (G^[j] w) - 1‖ ≤
      K / (w.im - n / 4) ^ (1 + δ) := by
    intro j jn
    set v := G^[j] w
    obtain ⟨i1, -⟩ := orb j jn.le
    obtain ⟨i2, -⟩ := orb (j + 1) jn
    have jn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast jn
    have vi : R < v.im := by linarith
    have vn : v.im ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm v)
    have v0 : v ≠ 0 := fun e ↦ by rw [e] at vi; simp at vi; linarith
    obtain ⟨ap, dv⟩ := up v vi
    rw [Function.iterate_succ_apply']
    have hlog : log (G v) = log v + log (1 + (G v - v) / v) := by
      obtain ⟨u', hs, un'⟩ := PetalGerm.step_ratio (w := v) (w' := G v) (by linarith)
        (PetalGerm.step_le dv)
      have hu : (G v - v) / v = u' := by rw [hs]; field_simp; ring
      have ur : 0 < (1 + u').re := by
        have := Complex.abs_re_le_norm u'
        simp only [Complex.add_re, Complex.one_re]
        rw [abs_le] at this; linarith
      have Gi : 0 < (v * (1 + u')).im := by
        rw [← hs]; rw [Function.iterate_succ_apply'] at i2; push_cast at i2; linarith
      rw [hu, hs]
      exact log_mul_upper (by linarith) ur Gi
    refine le_trans (NearTranslation.approxFatou_step_of A0 δ0 δ1 (by linarith) ap dv hlog) ?_
    refine div_le_div_of_nonneg_left K0 (Real.rpow_pos_of_pos Y0 _) ?_
    refine Real.rpow_le_rpow Y0.le ?_ (by linarith)
    have : (j : ℝ) ≤ n := by linarith
    linarith
  -- telescope
  have tele : ∀ m ≤ n, ‖approxFatou β (G^[m] w) - m - approxFatou β w‖ ≤
      m * (K / (w.im - n / 4) ^ (1 + δ)) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro mn
      have e : approxFatou β (G^[m + 1] w) - ((m + 1 : ℕ) : ℂ) - approxFatou β w =
          (approxFatou β (G^[m] w) - m - approxFatou β w) +
          (approxFatou β (G^[m + 1] w) - approxFatou β (G^[m] w) - 1) := by push_cast; ring
      rw [e]
      refine le_trans (norm_add_le _ _) ?_
      have := ih (by omega)
      have := step m (by omega)
      push_cast
      linarith
  exact tele n le_rfl

end Upper

/-!
### Helpers
-/

lemma log_sub_log_neg {w : ℂ} (wi : 0 < w.im) : log w - log (-w) = π * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos wi]

/-- On the upper half-plane, the repelling branch at `c` is the attracting branch at `c exp (π i / k)` -/
lemma root_neg_upper {c w : ℂ} (wi : 0 < w.im) :
    petalRoot k c (-w) = petalRoot k (c * exp (π * I / k)) w := by
  have e : log (-w) = log w - π * I := by linear_combination -(log_sub_log_neg wi)
  simp only [petalRoot, e, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

lemma norm_log_le {z : ℂ} (z1 : 1 ≤ ‖z‖) : ‖log z‖ ≤ Real.log (‖z‖ + 1) + 4 := by
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg z1)]
  have := Complex.abs_arg_le_pi z
  have := Real.log_le_log (by linarith) (by linarith : ‖z‖ ≤ ‖z‖ + 1)
  linarith [Real.pi_le_four]

/-- `c₀ + c₁ log (y + 1) ≤ η y` eventually -/
lemma log_small (c₀ c₁ : ℝ) {η : ℝ} (η0 : 0 < η) :
    ∀ᶠ y : ℝ in atTop, c₀ + c₁ * Real.log (y + 1) ≤ η * y := by
  have b := Real.isLittleO_log_id_atTop.bound (c := η / (2 * (|c₁| + 1))) (by positivity)
  have t : Tendsto (fun y : ℝ ↦ y + 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  filter_upwards [t.eventually b, eventually_ge_atTop ((2 * |c₀| + η) / η), eventually_ge_atTop 0]
    with y hb hy y0
  simp only [Real.norm_eq_abs, id] at hb
  have l0 : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
  rw [abs_of_nonneg l0, abs_of_nonneg (show (0 : ℝ) ≤ y + 1 by linarith)] at hb
  have c1 : c₁ * Real.log (y + 1) ≤ |c₁| * Real.log (y + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) l0
  have c2 : |c₁| * Real.log (y + 1) ≤ η / 2 * (y + 1) := by
    calc |c₁| * Real.log (y + 1) ≤ |c₁| * (η / (2 * (|c₁| + 1)) * (y + 1)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ η / 2 * (y + 1) := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [abs_nonneg c₁]
  rw [div_le_iff₀ η0] at hy
  have := le_abs_self c₀
  nlinarith

/-- If `‖w - ζ‖ ≤ B (log (‖w‖ + 1) + 4) + S`, then `‖w‖ ≤ 2 ‖ζ‖ + 2 (1 + 4 B² + 4 B + S)` -/
lemma norm_le_of_log {w ζ : ℂ} {B S : ℝ} (B0 : 0 ≤ B) (hw : ‖w - ζ‖ ≤ B * (Real.log (‖w‖ + 1) + 4) + S) :
    ‖w‖ ≤ 2 * ‖ζ‖ + 2 * (1 + 4 * B ^ 2 + 4 * B + S) := by
  set t := ‖w‖ + 1
  have t1 : 1 ≤ t := by simp only [t]; linarith [norm_nonneg w]
  have l := Real.log_le_rpow_div (x := t) (by linarith) (by norm_num : (0 : ℝ) < 1 / 2)
  have sq : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have s0 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have amgm : B * Real.log t ≤ t / 4 + 4 * B ^ 2 := by
    have : B * Real.log t ≤ B * (t ^ (1 / 2 : ℝ) / (1 / 2)) := mul_le_mul_of_nonneg_left l B0
    nlinarith [sq_nonneg (t ^ (1 / 2 : ℝ) / 2 - 2 * B)]
  have tri : ‖w‖ ≤ ‖ζ‖ + ‖w - ζ‖ := by
    have := norm_add_le ζ (w - ζ); simp only [add_sub_cancel] at this; linarith
  have S0 : -S ≤ B * (Real.log t + 4) := by
    have := le_trans (norm_nonneg _) hw
    linarith
  simp only [t] at amgm
  nlinarith [norm_nonneg ζ]

/-- The arithmetic behind the step-sum bound: `N K / Y^p < ε / 3` -/
lemma e2_bound {N K Y y Q ε p : ℝ} (N0 : 0 ≤ N) (K0 : 0 ≤ K) (y2 : 2 ≤ y) (Yb : y / 2 ≤ Y) (NQ : N ≤ 2 * Q)
    (Qη : Q ≤ ε / (24 * (K + 1)) * y) (ε0 : 0 < ε) (p1 : 1 ≤ p) : N * (K / Y ^ p) < ε / 3 := by
  have Y1 : 1 ≤ Y := by linarith
  have Yp : Y ≤ Y ^ p := by simpa using Real.rpow_le_rpow_of_exponent_le Y1 p1
  have b1 : K / Y ^ p ≤ K / (y / 2) := div_le_div_of_nonneg_left K0 (by linarith) (by linarith)
  have b2 : N * (K / Y ^ p) ≤ N * (K / (y / 2)) := mul_le_mul_of_nonneg_left b1 N0
  refine lt_of_le_of_lt b2 ?_
  have y0 : 0 < y := by linarith
  have e : N * (K / (y / 2)) = 2 * N * K / y := by field_simp
  rw [e, div_lt_iff₀ y0]
  have h1 : N ≤ 2 * (ε / (24 * (K + 1)) * y) := by linarith
  have h2 : 2 * N * K ≤ 4 * (ε / (24 * (K + 1)) * y) * K := by nlinarith
  have h3 : 4 * (ε / (24 * (K + 1)) * y) * K = ε * y * (K / (6 * (K + 1))) := by field_simp; ring
  have h4 : K / (6 * (K + 1)) < 1 / 3 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have h5 : ε * y * (K / (6 * (K + 1))) < ε * y * (1 / 3) := mul_lt_mul_of_pos_left h4 (by positivity)
  linarith

/-!
### The upper end, for a germ in normal form
-/

/-- Local attracting and repelling objects for adjacent petals, built together, and the upper end of their horn
map: for `ζ` high enough, a translate `ζ - m` lies in the parametrisation's domain, its orbit lands in the attracting
petal after `N` steps without leaving a small ball, and `Φ (g^[N] (Ψ (ζ - m))) - N = (ζ - m) - π i β + o(1)`. -/
lemma PetalGerm.local_horn (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = 1 / (k * a)) {δ₀ : ℝ} (δ0 : 0 < δ₀) :
    ∃ P : Set ℂ, ∃ Φ : ℂ → ℂ, ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ,
      (IsOpen P ∧ P.Nonempty ∧ P ⊆ Metric.ball 0 δ₀ ∧ MapsTo g P P ∧ AnalyticOnNhd ℂ Φ P ∧
        ∀ z ∈ P, Φ (g z) = Φ z + 1) ∧
      (IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧ (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧ AnalyticOnNhd ℂ Ψ V ∧
        (∀ ζ ∈ V, Ψ ζ ∈ Metric.ball 0 δ₀) ∧ ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) ∧
      ∀ ε > 0, ∃ T : ℝ, ∀ ζ : ℂ, T < ζ.im → ∃ m : ℤ, ∃ N : ℕ, ζ - m ∈ V ∧
        (∀ j ≤ N, g^[j] (Ψ (ζ - m)) ∈ Metric.ball 0 δ₀) ∧ g^[N] (Ψ (ζ - m)) ∈ P ∧
        ‖Φ (g^[N] (Ψ (ζ - m))) - N - (ζ - m) + π * I * petalResidue k a b‖ < ε := by
  have k0 := h.k0
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  have a0 := h.a0
  set β := petalResidue k a b
  set c' := c * exp (π * I / k)
  have hc' : c' ^ k = -1 / (k * a) := by
    simp only [c', mul_pow, ← Complex.exp_nat_mul, hc]
    rw [mul_div_cancel₀ _ kc, Complex.exp_pi_mul_I]; ring
  -- the three charts
  obtain ⟨Ra, Aa, nta, semia⟩ := h.attracting hc'
  obtain ⟨Ru, Au, Ru4, Au0, -, up⟩ := h.upper hc'
  obtain ⟨Rr, Ar, ntr, semir⟩ := h.repelling hc
  set Ga := fun w ↦ petalCoord k a (g (petalRoot k c' w))
  set Gr := fun w ↦ petalCoord k a (g (petalRoot k c (-w)))
  set RF := NearTranslationOut.repR β Rr Ar
  set R₁ := max (max Ra Ru) (max RF (‖c'‖ ^ k / δ₀ ^ k))
  have hRa : Ra ≤ R₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRu : Ru ≤ R₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hRF : RF ≤ R₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRδ : ‖c'‖ ^ k / δ₀ ^ k ≤ R₁ := le_trans (le_max_right _ _) (le_max_right _ _)
  have Rr4 := ntr.four_le
  have hRr : Rr ≤ RF := by
    simp only [RF, NearTranslationOut.repR, NearTranslationOut.repA]; have := ntr.A0
    nlinarith [norm_nonneg β]
  have hc0 : ‖c‖ ^ k / δ₀ ^ k ≤ R₁ := by
    have : ‖c'‖ = ‖c‖ := by
      simp only [c', norm_mul, Complex.norm_exp]
      have : (π * I / (k : ℂ)).re = 0 := by simp [Complex.div_re]
      rw [this, Real.exp_zero, mul_one]
    rwa [this] at hRδ
  obtain ⟨V, Ψw, Vo, Vl, reach, Ψa, Ψm, Ψe, Ψfat, Cv, hCv⟩ := ntr.repel_param R₁
  obtain ⟨Po, Pne, Pb, PM, Φa, Φe⟩ := h.attr_objects hc' nta semia hRa hRδ δ0
  obtain ⟨Ψa', Ψb', Ψe'⟩ := h.rep_objects semir (by linarith) (le_trans hRr hRF) hc0 δ0 Vl Ψa Ψm Ψe
  refine ⟨_, _, V, _, ⟨Po, Pne, Pb, PM, Φa, Φe⟩, ⟨Vo, Vl, reach, Ψa', Ψb', Ψe'⟩, ?_⟩
  intro ε ε0
  -- thresholds for the two Fatou approximations
  have ntF := ntr.reflInv_nearTranslation
  set F := NearTranslationOut.reflInv Gr
  obtain ⟨M₁, hM₁⟩ := nta.exists_norm_bound (by positivity : 0 < ε / 3)
  obtain ⟨M₃, hM₃⟩ := ntF.exists_norm_bound (by positivity : 0 < ε / 3)
  set S₀ := NearTranslation.tailBound (-β) (NearTranslationOut.repA β Ar) (k : ℝ)⁻¹ RF
  have hS₀ : ∀ v ∈ rightHalf RF,
      ‖NearTranslation.fatou F (-β) v - approxFatou (-β) v‖ ≤ S₀ := fun v m ↦
    ntF.fatou_sub_approx_le m le_rfl m.le
  have S0 : 0 ≤ S₀ := by
    have m : ((RF + 1 : ℝ) : ℂ) ∈ rightHalf RF := by show RF < _; simp
    exact le_trans (norm_nonneg _) (hS₀ _ m)
  set B := ‖β‖
  have B0 : 0 ≤ B := norm_nonneg _
  set K := Au + ‖β‖ * (‖β‖ + Au + 2)
  have K0 : 0 ≤ K := by positivity
  set D := 2 * (1 + 4 * B ^ 2 + 4 * B + S₀)
  have D0 : 0 ≤ D := by positivity
  -- all the logarithmic quantities are at most `Q y = q₀ + q₁ log (y + 1)`
  set q₀ := |Cv| + 2 * B * Real.log 3 + 1 + 1 + B * (Real.log (D + 7) + 4) + S₀ + R₁ + 1
  set η := ε / (24 * (K + 1))
  have η0 : 0 < η := by positivity
  set Mx := max (max Ru R₁) (max M₁ M₃)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (((log_small q₀ (3 * B) η0).and
    (log_small q₀ (3 * B) (by norm_num : (0 : ℝ) < 1 / 64))).and (eventually_ge_atTop (4 * (Mx + 2))))
  refine ⟨max T 1, fun ζ hζ ↦ ?_⟩
  set y := ζ.im
  obtain ⟨⟨Qη, Q64⟩, ybig⟩ := hT y (le_trans (le_max_left _ _) hζ.le)
  have y1 : 1 ≤ y := le_trans (le_max_right _ _) hζ.le
  have l0 : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
  have l3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have lD : 0 ≤ Real.log (D + 7) := Real.log_nonneg (by linarith)
  have hR1 := le_max_left Ru R₁
  have hR2 := le_max_right Ru R₁
  have hM1 := le_max_left M₁ M₃
  have hM2 := le_max_right M₁ M₃
  have hMx1 := le_max_left (max Ru R₁) (max M₁ M₃)
  have hMx2 := le_max_right (max Ru R₁) (max M₁ M₃)
  have R₁4 : 4 ≤ R₁ := le_trans Ru4 hRu
  set X := |Cv| + 2 * B * (Real.log 3 + Real.log (y + 1)) + 1
  set L := B * (Real.log (D + 7) + Real.log (y + 1) + 4) + S₀
  set Q := q₀ + 3 * B * Real.log (y + 1)
  have hQ : Q = X + 1 + L + R₁ + 1 := by simp only [Q, X, L, q₀]; ring
  have X0 : 0 ≤ X := by positivity
  have L0 : 0 ≤ L := by positivity
  -- the shift into the window `-X - 1 < re < -X`
  set m : ℤ := ⌈ζ.re + X⌉
  set ζ' := ζ - (m : ℂ)
  have mr1 : ζ.re + X ≤ m := Int.le_ceil _
  have mr2 : (m : ℝ) < ζ.re + X + 1 := Int.ceil_lt_add_one _
  have ζr : ζ'.re = ζ.re - m := by simp [ζ']
  have ζi : ζ'.im = y := by simp [ζ', y]
  have ζn : ‖ζ'‖ ≤ 3 * y := by
    have h1 := Complex.norm_le_abs_re_add_abs_im ζ'
    have h2 : |ζ'.re| ≤ X + 1 := abs_le.mpr ⟨by rw [ζr]; linarith, by rw [ζr]; linarith⟩
    rw [ζi, abs_of_pos (by linarith : (0 : ℝ) < y)] at h1
    linarith
  have ζV : ζ' ∈ V := by
    refine hCv ζ' ?_
    have lg : Real.log (‖ζ'‖ + 1) ≤ Real.log 3 + Real.log (y + 1) := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) (by linarith)
    have : 2 * B * Real.log (‖ζ'‖ + 1) ≤ 2 * B * (Real.log 3 + Real.log (y + 1)) :=
      mul_le_mul_of_nonneg_left lg (by positivity)
    have := le_abs_self Cv
    rw [ζr]
    simp only [X] at mr1 ⊢
    linarith
  -- locate `w = Ψ_w ζ'`: within `L` of `ζ'`
  set w := Ψw ζ'
  have wm : w.re < -R₁ := Ψm ζ' ζV
  have fat := Ψfat ζ' ζV
  have nwm : -w ∈ rightHalf RF := by show RF < (-w).re; simp only [Complex.neg_re]; linarith
  set e₃ := NearTranslation.fatou F (-β) (-w) - approxFatou (-β) (-w)
  have e3S : ‖e₃‖ ≤ S₀ := hS₀ _ nwm
  have hζw : ζ' = w - β * log (-w) - e₃ := by
    rw [fat]; simp only [e₃, approxFatou]; ring
  have wn4 : 4 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w; rw [abs_le] at this; linarith
  have dwz : ‖w - ζ'‖ ≤ B * (Real.log (‖w‖ + 1) + 4) + S₀ := by
    have e : w - ζ' = β * log (-w) + e₃ := by rw [hζw]; ring
    have nl := norm_log_le (z := -w) (by rw [norm_neg]; linarith)
    rw [norm_neg] at nl
    rw [e]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left nl B0
    linarith
  have wN : ‖w‖ ≤ 2 * ‖ζ'‖ + D := norm_le_of_log B0 dwz
  have Lb : ‖w - ζ'‖ ≤ L := by
    have lg : Real.log (‖w‖ + 1) ≤ Real.log (D + 7) + Real.log (y + 1) := by
      rw [← Real.log_mul (by linarith) (by linarith)]
      exact Real.log_le_log (by linarith [norm_nonneg w]) (by nlinarith)
    have := mul_le_mul_of_nonneg_left lg B0
    simp only [L]
    linarith
  have wi : y - L ≤ w.im := by
    have := le_trans (Complex.abs_im_le_norm (w - ζ')) Lb
    rw [abs_le, Complex.sub_im, ζi] at this; linarith
  have wr : -X - 1 - L ≤ w.re := by
    have := le_trans (Complex.abs_re_le_norm (w - ζ')) Lb
    rw [abs_le, Complex.sub_re, ζr] at this; linarith
  -- the orbit of `w` under the attracting chart
  set N := ⌈4 / 3 * Q⌉₊
  have Nge : 4 / 3 * Q ≤ N := Nat.le_ceil _
  have Nle : (N : ℝ) < 4 / 3 * Q + 1 := Nat.ceil_lt_add_one (by rw [hQ]; positivity)
  have Qy : Q ≤ y / 64 := by linarith
  have Yb : y / 2 ≤ w.im - N / 4 := by rw [hQ] at Qy; linarith
  have Yb' : 4 * (Mx + 2) ≤ y := ybig
  have hw_orb : Ru + N / 4 < w.im := by linarith
  have orb := up_orbit (G := Ga) (fun v hv ↦ (up v hv).2.2.1) hw_orb
  have imj : ∀ j ≤ N, R₁ < (Ga^[j] w).im := fun j jN ↦ by
    have := (orb j jN).1
    have : (j : ℝ) ≤ N := by exact_mod_cast jN
    linarith
  have semi_orb : ∀ j ≤ N, g^[j] (petalRoot k c' w) = petalRoot k c' (Ga^[j] w) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro jN
      rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply']
      exact (up _ (lt_of_le_of_lt hRu (imj j (by omega)))).2.2.2
  have wi0 : 0 < w.im := by linarith
  have Ψζ : petalRoot k c (-Ψw ζ') = petalRoot k c' w := root_neg_upper wi0
  set vN := Ga^[N] w
  have vNr : R₁ < vN.re := by
    have := (orb N le_rfl).2
    rw [hQ] at Nge
    linarith
  have vNi := (orb N le_rfl).1
  have vNn : y / 2 ≤ ‖vN‖ := le_trans (by linarith) (le_trans (le_abs_self _) (Complex.abs_im_le_norm vN))
  have v0 : vN ≠ 0 := fun e ↦ by rw [e] at vNr; simp at vNr; linarith
  refine ⟨m, N, ζV, fun j jN ↦ ?_, ?_, ?_⟩
  · rw [Ψζ, semi_orb j jN]
    have ij := imj j jN
    have vj : Ga^[j] w ≠ 0 := fun e ↦ by rw [e] at ij; simp at ij; linarith
    simp only [Metric.mem_ball, dist_zero_right]
    exact norm_root_lt k0 δ0 vj (lt_of_le_of_lt hRδ (lt_of_lt_of_le ij
      (le_trans (le_abs_self _) (Complex.abs_im_le_norm _))))
  · rw [Ψζ, semi_orb N le_rfl]
    exact mem_image_of_mem _ vNr
  · rw [Ψζ, semi_orb N le_rfl, coord_root k0 a0 hc' v0]
    -- the three errors
    set e₁ := NearTranslation.fatou Ga β vN - approxFatou β vN
    set e₂ := approxFatou β vN - N - approxFatou β w
    have he1 : ‖e₁‖ < ε / 3 := hM₁ vN (show Ra < vN.re by linarith) (by linarith)
    have he3 : ‖e₃‖ < ε / 3 := hM₃ (-w) nwm (by
      rw [norm_neg]; exact le_trans (by linarith) (le_trans (le_abs_self _) (Complex.abs_im_le_norm w)))
    have he2 : ‖e₂‖ < ε / 3 := by
      have s := up_sum (G := Ga) (β := β) Ru4 Au0 (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast k0))
        (fun v hv ↦ ⟨(up v hv).2.1, (up v hv).2.2.1⟩) hw_orb
      refine lt_of_le_of_lt s (e2_bound (Nat.cast_nonneg _) K0 (by linarith) Yb ?_ Qη ε0 ?_)
      · rw [hQ] at Nle ⊢; linarith
      · have : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
        linarith
    have key : NearTranslation.fatou Ga β vN - N - ζ' + π * I * β = e₁ + e₂ + e₃ := by
      have ll := log_sub_log_neg wi0
      simp only [e₁, e₂, approxFatou]
      rw [hζw]
      linear_combination -β * ll
    have hζ' : ζ - (m : ℂ) = ζ' := rfl
    rw [hζ', key]
    exact lt_of_le_of_lt norm_add₃_le (by linarith only [he1, he2, he3])

/-!
### The upper end of the horn map
-/

/-- Integer translations of a `1`-periodic domain and a map commuting with `ζ ↦ ζ + 1` -/
lemma horn_int {D : Set ℂ} {H : ℂ → ℂ} (Dp : ∀ ζ, ζ ∈ D ↔ ζ + 1 ∈ D) (He : ∀ ζ ∈ D, H (ζ + 1) = H ζ + 1)
    {ζ : ℂ} (mem : ζ ∈ D) (m : ℤ) : ζ + m ∈ D ∧ H (ζ + m) = H ζ + m := by
  induction m using Int.induction_on with
  | zero => simpa using mem
  | succ n ih =>
    obtain ⟨m1, e1⟩ := ih
    have e : ζ + ((n + 1 : ℤ) : ℂ) = (ζ + (n : ℤ)) + 1 := by push_cast; ring
    rw [e]
    refine ⟨(Dp _).mp m1, ?_⟩
    rw [He _ m1, e1]; push_cast; ring
  | pred n ih =>
    obtain ⟨m1, e1⟩ := ih
    have e : ζ + ((-(n : ℤ) : ℤ) : ℂ) = (ζ + ((-(n : ℤ) - 1 : ℤ) : ℂ)) + 1 := by push_cast; ring
    rw [e] at m1 e1
    have m2 := (Dp _).mpr m1
    refine ⟨m2, ?_⟩
    rw [He _ m2] at e1
    push_cast at e1 ⊢
    linear_combination e1

/-- The upper end of the horn map.  Let `g` be entire with `g z = z + a z^(k+1) + O(z^(k+2))`, `a ≠ 0`.  For a
repelling direction (a `k`-th root `c` of `1 / (k a)`) and the adjacent attracting direction `c exp (π i / k)`, there
are an attracting petal `P` with Fatou coordinate `Φ` and a repelling parametrisation `Ψ` such that the horn map
`H = Φ ∘ Ψ` is defined on an upper half-plane and `H ζ = ζ - π i β + o(1)` as `im ζ → ∞`.  Here `β` is the iterative
residue of the petal normal form `φ ∘ g ∘ h = z + a z^(k+1) + b z^(2k+1) + O(z^(2k+2))`. -/
public theorem horn_upper (ga : ∀ z, AnalyticAt ℂ g z) (g0 : g 0 = 0) (k0 : 0 < k) (a0 : a ≠ 0)
    (approx : (fun z ↦ g z - (z + a * z ^ (k + 1))) =O[𝓝 0] fun z ↦ z ^ (k + 2)) {c : ℂ}
    (hc : c ^ k = 1 / (k * a)) :
    ∃ P : Set ℂ, ∃ Φ : ℂ → ℂ, ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, ∃ h φ : ℂ → ℂ, ∃ b : ℂ,
      (AnalyticAt ℂ h 0 ∧ AnalyticAt ℂ φ 0 ∧ h 0 = 0 ∧ (∀ᶠ z in 𝓝 0, φ (h z) = z) ∧
        (∀ᶠ z in 𝓝 0, h (φ z) = z) ∧ PetalGerm (φ ∘ g ∘ h) k a b) ∧
      (IsOpen P ∧ P.Nonempty ∧ MapsTo g P P ∧ AnalyticOnNhd ℂ Φ P ∧ ∀ z ∈ P, Φ (g z) = Φ z + 1) ∧
      (IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧ (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧ AnalyticOnNhd ℂ Ψ V ∧
        ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) ∧
      (∃ T : ℝ, ∀ ζ : ℂ, T < ζ.im → ζ ∈ hornDomain g Ψ P V) ∧
      Tendsto (fun ζ ↦ hornMap g Φ Ψ P V ζ - ζ) (comap Complex.im atTop)
        (𝓝 (-(π * I * petalResidue k a b))) := by
  obtain ⟨h, φ, b, ha, φa, h0, -, l, r, pg⟩ := PetalGerm.normalize k0 a0 (ga 0) g0 approx
  obtain ⟨δ, δ0, inj, hδ⟩ := conj_setup (ga 0) g0 ha φa h0 l r one_pos
  obtain ⟨P', Φ', V, Ψ', ⟨Po, Pne, Pb, PM, Φa, Φe⟩, ⟨Vo, Vl, reach, Ψa, Ψb, Ψe⟩, ends⟩ := pg.local_horn hc δ0
  obtain ⟨Po', gP, Φa', Φe'⟩ := transport_attr δ0 inj (fun z m ↦ ⟨(hδ z m).1, (hδ z m).2.1,
    (hδ z m).2.2.1, (hδ z m).2.2.2.1⟩) Po Pb PM Φa Φe
  obtain ⟨Ψa', Ψe'⟩ := transport_rep (fun z m ↦ ⟨(hδ z m).2.1, (hδ z m).2.2.2.1⟩) Vl Ψa Ψb Ψe
  set P := h '' P'
  set Φ := Φ' ∘ φ
  set Ψ := h ∘ Ψ'
  set g' := φ ∘ g ∘ h
  obtain ⟨-, Dp, -, He⟩ := horn_map ga Po' gP Φa' Φe' Vo Vl reach Ψa' Ψe'
  -- orbits that stay small and land in `P'` transport
  have land : ∀ ζ' ∈ V, ∀ N : ℕ, (∀ j ≤ N, g'^[j] (Ψ' ζ') ∈ Metric.ball 0 δ) → g'^[N] (Ψ' ζ') ∈ P' →
      ζ' ∈ hornDomain g Ψ P V ∧ hornMap g Φ Ψ P V ζ' = Φ' (g'^[N] (Ψ' ζ')) - N := by
    intro ζ' m N small land
    have orb : ∀ j ≤ N, g^[j] (Ψ ζ') = h (g'^[j] (Ψ' ζ')) := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro jN
        rw [Function.iterate_succ_apply', ih (by omega), Function.iterate_succ_apply',
          (hδ _ (small j (by omega))).2.2.2.1]
        rfl
    have pe := paramExt_eq Vl Ψe' m
    have gN : g^[N] (Ψ ζ') ∈ P := by rw [orb N le_rfl]; exact mem_image_of_mem h land
    refine ⟨by simp only [hornDomain, mem_preimage, pe]; exact ⟨N, gN⟩, ?_⟩
    simp only [hornMap, pe]
    rw [basinExt_eq_of gP Φe' gN, orb N le_rfl]
    simp only [Φ, Function.comp_apply, (hδ _ (small N le_rfl)).1]
  have shift : ∀ ζ : ℂ, ∀ (m : ℤ), ζ - m ∈ hornDomain g Ψ P V →
      ζ ∈ hornDomain g Ψ P V ∧ hornMap g Φ Ψ P V ζ - ζ = hornMap g Φ Ψ P V (ζ - m) - (ζ - m) := by
    intro ζ m mem
    obtain ⟨m1, e1⟩ := horn_int Dp He mem m
    simp only [sub_add_cancel] at m1 e1
    exact ⟨m1, by rw [e1]; ring⟩
  refine ⟨P, Φ, V, Ψ, h, φ, b, ⟨ha, φa, h0, l, r, pg⟩, ⟨Po', Pne.image _, gP, Φa', Φe'⟩,
    ⟨Vo, Vl, reach, Ψa', Ψe'⟩, ?_, ?_⟩
  · obtain ⟨T, hT⟩ := ends 1 one_pos
    refine ⟨T, fun ζ hζ ↦ ?_⟩
    obtain ⟨m, N, mV, small, land', -⟩ := hT ζ hζ
    exact (shift ζ m (land _ mV N small land').1).1
  · rw [Metric.tendsto_nhds]
    intro ε ε0
    obtain ⟨T, hT⟩ := ends ε ε0
    rw [Filter.eventually_comap]
    filter_upwards [eventually_gt_atTop T] with y hy ζ hζ
    obtain ⟨m, N, mV, small, land', est⟩ := hT ζ (by rw [hζ]; exact hy)
    obtain ⟨dm, e⟩ := land _ mV N small land'
    rw [dist_eq_norm, (shift ζ m dm).2, e]
    simpa [sub_neg_eq_add] using est
