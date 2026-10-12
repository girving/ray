module
public import Ray.Dynamics.FatouExtend
public import Ray.Dynamics.FatouParam
public import Ray.Dynamics.PetalNormal
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Bound

/-!
## Fatou coordinates and parametrisations of a parabolic fixed point

Let `g` be entire with `g z = z + a z^(k+1) + O(z^(k+2))`, `a ≠ 0`.  For each attracting direction (a `k`-th root
`c` of `-1 / (k a)`) we build a petal `P` near `0` with `g P ⊆ P` and an attracting Fatou coordinate `Φ`, analytic on
the basin `{z | ∃ n, g^[n] z ∈ P}` with `Φ (g z) = Φ z + 1`.  For each repelling direction (a `k`-th root of
`1 / (k a)`) we build an entire repelling parametrisation `Ψ` with `g (Ψ ζ) = Ψ (ζ + 1)`.  Their composition
`H = Φ ∘ Ψ` is the horn map: analytic where defined, and `H (ζ + 1) = H ζ + 1`.

The steps:
1. For a germ in petal normal form, `PetalGerm.attracting`/`repelling` give near-translations in the petal
   coordinate; the Fatou coordinate (`FatouNear`) and the repelling parametrisation (`FatouParam`) there pull back to
   the `z`-plane through the petal branch `ψ`.
2. `PetalGerm.normalize` conjugates `g` to normal form by local inverses `h`, `φ`: `Φ ∘ φ` and `h ∘ Ψ` are the local
   objects for `g`.
3. `basinExt` and `paramExt` (`FatouExtend`) extend them using the dynamics of the entire map `g`.
-/

open Classical
open Complex (exp log slitPlane)
open Filter
open Set
open scoped Topology

variable {g : ℂ → ℂ} {k : ℕ} {a b : ℂ}

/-!
### Generic facts
-/

/-- An injective analytic map on a preconnected open set is an open map there -/
public lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U S : Set ℂ} (fa : AnalyticOnNhd ℂ f U) (Uc : IsPreconnected U)
    (inj : InjOn f U) {x y : ℂ} (xU : x ∈ U) (yU : y ∈ U) (xy : x ≠ y) (SU : S ⊆ U) (So : IsOpen S) :
    IsOpen (f '' S) := by
  rcases fa.is_constant_or_isOpen Uc with ⟨w, hw⟩ | o
  · exact absurd (inj xU yU (by rw [hw x xU, hw y yU])) xy
  · exact o S SU So

/-!
### Petal branches
-/

public lemma root_ne_zero {c s : ℂ} (c0 : c ≠ 0) : petalRoot k c s ≠ 0 :=
  mul_ne_zero c0 (Complex.exp_ne_zero _)

public lemma coord_root {c w : ℂ} (k0 : 0 < k) (a0 : a ≠ 0) (hc : c ^ k = -1 / (k * a)) (w0 : w ≠ 0) :
    petalCoord k a (petalRoot k c w) = w := by
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  simp only [petalCoord]
  rw [PetalGerm.root_pow w0 k0, hc]
  field_simp

public lemma norm_root_lt {c s : ℂ} {ε : ℝ} (k0 : 0 < k) (ε0 : 0 < ε) (s0 : s ≠ 0) (big : ‖c‖ ^ k / ε ^ k < ‖s‖) :
    ‖petalRoot k c s‖ < ε := by
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) ε0.le k0.ne').mp ?_
  rw [← norm_pow, PetalGerm.root_pow s0 k0, norm_div, norm_pow, div_lt_iff₀ (norm_pos_iff.mpr s0)]
  rw [div_lt_iff₀ (by positivity)] at big
  linarith

public lemma c_ne_zero {c : ℂ} {t : ℂ} (k0 : 0 < k) (t0 : t ≠ 0) (hc : c ^ k = t) : c ≠ 0 := by
  rintro rfl; rw [zero_pow k0.ne'] at hc; exact t0 hc.symm

/-- If `F ∘ G = s • id` near `x` with `s ≠ 0` (both analytic), then `F' (G x) ≠ 0` and `G' x ≠ 0` -/
public lemma deriv_ne_zero_of_comp {F G : ℂ → ℂ} {x s : ℂ} (s0 : s ≠ 0) (Fa : AnalyticAt ℂ F (G x))
    (Ga : AnalyticAt ℂ G x) (e : ∀ᶠ y in 𝓝 x, F (G y) = s * y) : deriv F (G x) ≠ 0 ∧ deriv G x ≠ 0 := by
  have e' : (F ∘ G) =ᶠ[𝓝 x] fun y ↦ s * y := e
  have d := e'.deriv_eq
  rw [deriv_comp _ Fa.differentiableAt Ga.differentiableAt] at d
  have : deriv (fun y : ℂ ↦ s * y) x = s := by simp
  rw [this] at d
  constructor <;> intro z <;> simp [z, s0.symm] at d

/-!
### Local objects for a germ in normal form
-/

/-- The explicit attracting petal `ψ (re w > R₁)` and Fatou coordinate `Φ_G ∘ w`, given the petal near-translation -/
public lemma PetalGerm.attr_objects (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = -1 / (k * a)) {R A : ℝ}
    (nt : NearTranslation (fun w ↦ petalCoord k a (g (petalRoot k c w))) (petalResidue k a b) R A (k : ℝ)⁻¹)
    (semi : ∀ w ∈ rightHalf R, g (petalRoot k c w) = petalRoot k c (petalCoord k a (g (petalRoot k c w))))
    {R₁ ε : ℝ} (RR : R ≤ R₁) (Rε : ‖c‖ ^ k / ε ^ k ≤ R₁) (ε0 : 0 < ε)
    (Rd : ∀ w ∈ rightHalf R₁,
      deriv (NearTranslation.fatou (fun w ↦ petalCoord k a (g (petalRoot k c w))) (petalResidue k a b)) w ≠ 0) :
    let P := (fun w ↦ petalRoot k c w) '' rightHalf R₁
    let Φ := fun z ↦ NearTranslation.fatou (fun w ↦ petalCoord k a (g (petalRoot k c w))) (petalResidue k a b)
      (petalCoord k a z)
    IsOpen P ∧ P.Nonempty ∧ P ⊆ Metric.ball 0 ε ∧ MapsTo g P P ∧ AnalyticOnNhd ℂ Φ P ∧
      (∀ z ∈ P, Φ (g z) = Φ z + 1) ∧ ∀ z ∈ P, deriv Φ z ≠ 0 := by
  intro P Φ
  have k0 := h.k0
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  have c0 : c ≠ 0 := c_ne_zero k0 (div_ne_zero (by norm_num) (mul_ne_zero kc h.a0)) hc
  have nt1 := nt.mono RR
  set β := petalResidue k a b
  set G := fun w ↦ petalCoord k a (g (petalRoot k c w))
  have R4 := nt1.four_le
  have facts : ∀ w ∈ rightHalf R₁, w ≠ 0 ∧ w ∈ slitPlane ∧ w ∈ rightHalf R ∧ R₁ < ‖w‖ := fun w m ↦ by
    have wr : R₁ < w.re := m
    have wn := lt_of_lt_of_le wr (Complex.re_le_norm w)
    refine ⟨fun e ↦ by rw [e] at wr; simp at wr; linarith, ?_, ?_, wn⟩
    · rw [Complex.mem_slitPlane_iff]; left; linarith
    · show R < w.re; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- open: the branch is injective, with left inverse the petal coordinate
    have m1 : ((R₁ + 1 : ℝ) : ℂ) ∈ rightHalf R₁ := by show R₁ < _; simp
    have m2 : ((R₁ + 2 : ℝ) : ℂ) ∈ rightHalf R₁ := by show R₁ < _; simp
    refine isOpen_image_of_injOn (fun w m ↦ PetalGerm.analyticAt_root (facts w m).2.1)
      (convex_halfSpace_re_gt R₁).isPreconnected (fun x xm y ym e ↦ ?_) m1 m2
      (by rw [Ne, Complex.ofReal_inj]; linarith) subset_rfl (NearTranslation.isOpen_rightHalf R₁)
    have e' := congrArg (petalCoord k a) e
    rwa [coord_root k0 h.a0 hc (facts x xm).1, coord_root k0 h.a0 hc (facts y ym).1] at e'
  · exact ⟨_, mem_image_of_mem _ (show ((R₁ + 1 : ℝ) : ℂ) ∈ rightHalf R₁ by show R₁ < _; simp)⟩
  · rintro _ ⟨w, m, rfl⟩
    simp only [Metric.mem_ball, dist_zero_right]
    exact norm_root_lt k0 ε0 (facts w m).1 (lt_of_le_of_lt Rε (facts w m).2.2.2)
  · rintro _ ⟨w, m, rfl⟩
    exact ⟨G w, nt1.mapsTo m, (semi w (facts w m).2.2.1).symm⟩
  · rintro _ ⟨w, m, rfl⟩
    have e := coord_root k0 h.a0 hc (facts w m).1
    have fa := nt.fatou_analytic _ (facts w m).2.2.1
    rw [← e] at fa
    exact fa.comp (PetalGerm.analyticAt_petalCoord (root_ne_zero c0) kc h.a0)
  · rintro _ ⟨w, m, rfl⟩
    simp only [Φ]
    rw [coord_root k0 h.a0 hc (facts w m).1]
    exact nt.fatou_eqn (facts w m).2.2.1
  · rintro _ ⟨w, m, rfl⟩
    -- `w ∘ ψ = id` near `w`, so `w' ≠ 0` at `ψ w`
    have ψa := PetalGerm.analyticAt_root (k := k) (c := c) (facts w m).2.1
    have pa := PetalGerm.analyticAt_petalCoord (k := k) (a := a) (root_ne_zero (k := k) (s := w) c0) kc h.a0
    have ev : ∀ᶠ y in 𝓝 w, petalCoord k a (petalRoot k c y) = 1 * y := by
      filter_upwards [(NearTranslation.isOpen_rightHalf R₁).mem_nhds m] with y ym
      rw [one_mul]; exact coord_root k0 h.a0 hc (facts y ym).1
    have pd := (deriv_ne_zero_of_comp one_ne_zero pa ψa ev).1
    have fa := nt.fatou_analytic _ (facts w m).2.2.1
    rw [← coord_root k0 h.a0 hc (facts w m).1] at fa
    have hd := fa.differentiableAt.hasDerivAt.comp _ pa.differentiableAt.hasDerivAt
    simp only [Φ]
    rw [show (fun z ↦ NearTranslation.fatou (fun w ↦ petalCoord k a (g (petalRoot k c w)))
      (petalResidue k a b) (petalCoord k a z)) = NearTranslation.fatou (fun w ↦ petalCoord k a
      (g (petalRoot k c w))) (petalResidue k a b) ∘ petalCoord k a from rfl, hd.deriv]
    refine mul_ne_zero ?_ pd
    rw [coord_root k0 h.a0 hc (facts w m).1]
    exact Rd w m

/-- The attracting petal contains a sector around its direction near `0`: `c r (1 + e)` is in `ψ (re w > R₁)` for
`0 < r < ε` and `‖e‖ ≤ 1 / (4k)` -/
public lemma petal_sector (c : ℂ) (k0 : 0 < k) (R₁ : ℝ) :
    ∃ ε > 0, ∀ (r : ℝ) (e : ℂ), 0 < r → r < ε → ‖e‖ ≤ 1 / (4 * k) →
      c * r * (1 + e) ∈ (fun w ↦ petalRoot k c w) '' rightHalf R₁ := by
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  have k1 : (1 : ℝ) ≤ k := by exact_mod_cast k0
  set M := 2 * |R₁| + 2
  have M0 : 0 < M := by positivity
  refine ⟨1 / (2 * M), by positivity, fun r e r0 rε en ↦ ?_⟩
  have en2 : ‖e‖ ≤ 1 / 2 := le_trans en (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith)
  set u : ℂ := r * (1 + e)
  have e1 : 1 + e ≠ 0 := by
    intro h; have : e = -1 := by linear_combination h
    rw [this] at en2; norm_num at en2
  have u0 : u ≠ 0 := mul_ne_zero (by exact_mod_cast r0.ne') e1
  -- `Complex.arg u = Complex.arg (1 + e) = im (log (1 + e))` is small
  have la := Complex.norm_log_one_add_half_le_self en2
  have argu : |Complex.arg u| ≤ 3 / (8 * k) := by
    rw [show u = (r : ℂ) * (1 + e) from rfl, Complex.arg_real_mul _ r0, ← Complex.log_im]
    refine le_trans (Complex.abs_im_le_norm _) (le_trans la ?_)
    rw [show (3 : ℝ) / (8 * k) = 3 / 2 * (1 / (4 * k)) by field_simp; ring]
    gcongr
  have karg : |(k : ℝ) * Complex.arg u| ≤ 3 / 8 := by
    rw [abs_mul, Nat.abs_cast]
    calc (k : ℝ) * |Complex.arg u| ≤ k * (3 / (8 * k)) := by gcongr
      _ = 3 / 8 := by field_simp
  set w := exp (-(k * log u))
  have wim : (-(k * log u)).im = -(k * Complex.arg u) := by
    simp [Complex.log_im]
  have lw : log w = -(k * log u) := by
    rw [abs_le] at karg
    refine Complex.log_exp ?_ ?_ <;> rw [wim] <;> linarith [Real.two_le_pi]
  have ψw : petalRoot k c w = c * r * (1 + e) := by
    simp only [petalRoot, lw, neg_neg, mul_div_cancel_left₀ _ kc, Complex.exp_log u0, u]; ring
  refine ⟨w, ?_, ψw⟩
  -- `re w > R₁`: `‖w‖ = ‖u‖^(-k)` is large and `Complex.arg w = -k Complex.arg u` is small
  have nu : ‖u‖ < 1 / M := by
    have : ‖1 + e‖ ≤ 3 / 2 := by
      have := norm_add_le (1 : ℂ) e; rw [norm_one] at this; linarith
    calc ‖u‖ = r * ‖1 + e‖ := by simp [u, abs_of_pos r0]
      _ ≤ r * (3 / 2) := by gcongr
      _ < 1 / M := by
          rw [lt_div_iff₀ (by positivity)] at rε
          rw [lt_div_iff₀ M0]; nlinarith
  have nu1 : ‖u‖ ≤ 1 := le_trans nu.le (by rw [div_le_one M0]; linarith [abs_nonneg R₁])
  have nu0 : 0 < ‖u‖ := norm_pos_iff.mpr u0
  have nw : ‖w‖ = (‖u‖ ^ k)⁻¹ := by
    simp only [w, Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.log_re]
    rw [Real.exp_neg, ← Real.log_pow, Real.exp_log (by positivity)]
  have nwM : M < ‖w‖ := by
    rw [nw, lt_inv_comm₀ M0 (by positivity)]
    calc ‖u‖ ^ k ≤ ‖u‖ := pow_le_of_le_one nu0.le nu1 k0.ne'
      _ < 1 / M := nu
      _ = M⁻¹ := one_div M
  have w0 : w ≠ 0 := Complex.exp_ne_zero _
  have aw : Complex.arg w = -(k * Complex.arg u) := by rw [← Complex.log_im, lw, wim]
  have cw : 1 / 2 ≤ Real.cos (Complex.arg w) := by
    have := Real.one_sub_sq_div_two_le_cos (x := Complex.arg w)
    rw [aw, neg_sq] at this
    have : ((k : ℝ) * Complex.arg u) ^ 2 ≤ (3 / 8) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) karg 2
    rw [aw]; linarith
  have rw' : w.re = ‖w‖ * Real.cos (Complex.arg w) := by
    rw [Complex.cos_arg w0]; field_simp
  show R₁ < w.re
  rw [rw']
  have := le_abs_self R₁
  nlinarith [norm_nonneg w]

/-- Petals of distinct directions are disjoint -/
public lemma petal_disjoint {c₁ c₂ : ℂ} (k0 : 0 < k) (a0 : a ≠ 0) (h₁ : c₁ ^ k = -1 / (k * a))
    (h₂ : c₂ ^ k = -1 / (k * a)) (ne : c₁ ≠ c₂) {R₁ R₂ : ℝ} (R0 : 0 ≤ R₁) (R0' : 0 ≤ R₂) :
    Disjoint ((fun w ↦ petalRoot k c₁ w) '' rightHalf R₁) ((fun w ↦ petalRoot k c₂ w) '' rightHalf R₂) := by
  rw [Set.disjoint_left]
  rintro _ ⟨w, wm, rfl⟩ ⟨w', wm', e⟩
  have w0 : w ≠ 0 := fun h ↦ by have : R₁ < w.re := wm; rw [h] at this; simp at this; linarith
  have w0' : w' ≠ 0 := fun h ↦ by have : R₂ < w'.re := wm'; rw [h] at this; simp at this; linarith
  have ww : w' = w := by
    have := congrArg (petalCoord k a) e
    simp only at this
    rwa [coord_root k0 a0 h₂ w0', coord_root k0 a0 h₁ w0] at this
  subst ww
  simp only [petalRoot] at e
  exact ne (mul_right_cancel₀ (Complex.exp_ne_zero _) e).symm

/-- An attracting petal near `0` with its Fatou coordinate, for a germ in normal form -/
lemma PetalGerm.local_attracting (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = -1 / (k * a)) {ε : ℝ}
    (ε0 : 0 < ε) : ∃ P : Set ℂ, ∃ Φ : ℂ → ℂ, IsOpen P ∧ P.Nonempty ∧ P ⊆ Metric.ball 0 ε ∧ MapsTo g P P ∧
      AnalyticOnNhd ℂ Φ P ∧ ∀ z ∈ P, Φ (g z) = Φ z + 1 := by
  obtain ⟨R, A, nt, semi⟩ := h.attracting hc
  obtain ⟨a', Ra', -, -, -, hd⟩ := nt.exists_lip_deriv
  set R₁ := max (max R (‖c‖ ^ k / ε ^ k)) (2 * a')
  obtain ⟨Po, Pne, Pb, PM, Φa, Φe, -⟩ := h.attr_objects hc nt semi (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _)) ε0 (fun w (m : R₁ < w.re) ↦ hd w
      (show 2 * a' < w.re from lt_of_le_of_lt (le_max_right _ _) m))
  exact ⟨_, _, Po, Pne, Pb, PM, Φa, Φe⟩

/-- The explicit repelling parametrisation `ψ ∘ (-Ψ_w)`, given a parametrisation `Ψ_w` in the petal plane -/
public lemma PetalGerm.rep_objects (h : PetalGerm g k a b) {c : ℂ} {R : ℝ}
    (semi : ∀ w ∈ leftHalf R,
      g (petalRoot k c (-w)) = petalRoot k c (-petalCoord k a (g (petalRoot k c (-w)))))
    (R4 : 0 ≤ R) {R₁ ε : ℝ} (RR : R ≤ R₁) (Rε : ‖c‖ ^ k / ε ^ k ≤ R₁) (ε0 : 0 < ε) {V : Set ℂ} {Ψw : ℂ → ℂ}
    (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (Ψa : AnalyticOnNhd ℂ Ψw V) (Ψm : ∀ ζ ∈ V, Ψw ζ ∈ leftHalf R₁)
    (Ψe : ∀ ζ ∈ V, petalCoord k a (g (petalRoot k c (-Ψw (ζ - 1)))) = Ψw ζ)
    (hc : c ^ k = 1 / (k * a)) (Ψd : ∀ ζ ∈ V, deriv Ψw ζ ≠ 0) :
    let Ψ := fun ζ ↦ petalRoot k c (-Ψw ζ)
    AnalyticOnNhd ℂ Ψ V ∧ (∀ ζ ∈ V, Ψ ζ ∈ Metric.ball 0 ε) ∧ (∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) ∧
      ∀ ζ ∈ V, deriv Ψ ζ ≠ 0 := by
  intro Ψ
  have k0 := h.k0
  have facts : ∀ ζ ∈ V, -Ψw ζ ≠ 0 ∧ -Ψw ζ ∈ slitPlane ∧ Ψw ζ ∈ leftHalf R ∧
      ‖c‖ ^ k / ε ^ k < ‖-Ψw ζ‖ := fun ζ m ↦ by
    have r : (Ψw ζ).re < -R₁ := Ψm ζ m
    have nr : -(Ψw ζ).re ≤ ‖-Ψw ζ‖ := by rw [← Complex.neg_re]; exact Complex.re_le_norm _
    refine ⟨fun e ↦ by rw [neg_eq_zero] at e; rw [e] at r; simp at r; linarith, ?_, ?_, by linarith⟩
    · rw [Complex.mem_slitPlane_iff, Complex.neg_re]; left; linarith
    · show (Ψw ζ).re < -R; linarith
  refine ⟨fun ζ m ↦ ?_, fun ζ m ↦ ?_, fun ζ m ↦ ?_, fun ζ m ↦ ?_⟩
  · exact (PetalGerm.analyticAt_root (facts ζ m).2.1).comp (f := fun ζ ↦ -Ψw ζ) (Ψa ζ m).neg
  · simp only [Metric.mem_ball, dist_zero_right]
    exact norm_root_lt k0 ε0 (facts ζ m).1 (facts ζ m).2.2.2
  · have m' := Vl ζ m
    simp only [Ψ]
    rw [semi _ (facts _ m').2.2.1]
    congr 2
    exact Ψe ζ m
  · -- `w ∘ ψ = -id` near `-Ψ_w ζ`
    have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
    have c0 : c ≠ 0 := c_ne_zero k0 (div_ne_zero one_ne_zero (mul_ne_zero kc h.a0)) hc
    set s₀ := -Ψw ζ
    have sm : s₀ ∈ slitPlane := (facts ζ m).2.1
    have ψa := PetalGerm.analyticAt_root (k := k) (c := c) sm
    have pa := PetalGerm.analyticAt_petalCoord (k := k) (a := a) (root_ne_zero (k := k) (s := s₀) c0) kc h.a0
    have ev : ∀ᶠ y in 𝓝 s₀, petalCoord k a (petalRoot k c y) = -1 * y := by
      filter_upwards [Complex.isOpen_slitPlane.mem_nhds sm] with y ym
      have y0 : y ≠ 0 := Complex.slitPlane_ne_zero ym
      simp only [petalCoord]
      rw [PetalGerm.root_pow y0 k0, hc]; field_simp; rw [div_self h.a0]
    have rd := (deriv_ne_zero_of_comp (by norm_num) pa ψa ev).2
    have hd := ψa.differentiableAt.hasDerivAt.comp ζ (Ψa ζ m).differentiableAt.hasDerivAt.neg
    rw [show Ψ = (fun w ↦ petalRoot k c w) ∘ (-Ψw) from rfl, hd.deriv]
    exact mul_ne_zero rd (neg_ne_zero.mpr (Ψd ζ m))

/-- A repelling parametrisation near `0`, for a germ in normal form -/
lemma PetalGerm.local_repelling (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = 1 / (k * a)) {ε : ℝ}
    (ε0 : 0 < ε) : ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧
      (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧ AnalyticOnNhd ℂ Ψ V ∧ (∀ ζ ∈ V, Ψ ζ ∈ Metric.ball 0 ε) ∧
      (∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) := by
  obtain ⟨R, A, nt, semi⟩ := h.repelling hc
  obtain ⟨V, Ψw, Vo, Vl, reach, Ψa, Ψm, Ψe, -, -, Ψd⟩ := nt.repel_param (max R (‖c‖ ^ k / ε ^ k))
  obtain ⟨Ψa', Ψb', Ψe', -⟩ := h.rep_objects semi (by linarith [nt.four_le]) (le_max_left _ _)
    (le_max_right _ _) ε0 Vl Ψa Ψm Ψe hc Ψd
  exact ⟨V, _, Vo, Vl, reach, Ψa', Ψb', Ψe'⟩

/-!
### Transport through the normalising conjugacy
-/

/-- Small balls on which the normalising conjugacy behaves: `φ ∘ h = id`, `h` maps into a given ball, and
`g ∘ h = h ∘ (φ ∘ g ∘ h)` -/
public lemma conj_setup {h φ : ℂ → ℂ} (ga : AnalyticAt ℂ g 0) (g0 : g 0 = 0) (ha : AnalyticAt ℂ h 0)
    (φa : AnalyticAt ℂ φ 0) (h0 : h 0 = 0) (l : ∀ᶠ z in 𝓝 0, φ (h z) = z) (r : ∀ᶠ z in 𝓝 0, h (φ z) = z)
    {ε : ℝ} (ε0 : 0 < ε) : ∃ δ > 0, InjOn h (Metric.ball 0 δ) ∧ ∀ z ∈ Metric.ball (0 : ℂ) δ,
      φ (h z) = z ∧ AnalyticAt ℂ h z ∧ AnalyticAt ℂ φ (h z) ∧ g (h z) = h (φ (g (h z))) ∧
      h z ∈ Metric.ball 0 ε := by
  obtain ⟨ε', ε'0, hε'⟩ := Metric.eventually_nhds_iff.mp (r.and φa.eventually_analyticAt)
  have th : Tendsto h (𝓝 0) (𝓝 0) := by
    have := ha.continuousAt.tendsto; rwa [h0] at this
  have tgh : Tendsto (fun z ↦ g (h z)) (𝓝 0) (𝓝 0) := by
    have := (ga.continuousAt.comp_of_eq ha.continuousAt h0).tendsto
    simpa [Function.comp_def, h0, g0] using this
  have b : ∀ {ρ : ℝ}, 0 < ρ → ∀ᶠ y in 𝓝 (0 : ℂ), dist y 0 < ρ := fun ρ0 ↦ Metric.ball_mem_nhds 0 ρ0
  obtain ⟨δ, δ0, hδ⟩ := Metric.eventually_nhds_iff.mp (l.and (ha.eventually_analyticAt.and
    ((th.eventually (b ε'0)).and ((tgh.eventually (b ε'0)).and (th.eventually (b ε0))))))
  refine ⟨δ, δ0, fun x xm y ym e ↦ ?_, fun z zm ↦ ?_⟩
  · rw [← (hδ xm).1, ← (hδ ym).1, e]
  · obtain ⟨e1, a1, b1, b2, b3⟩ := hδ zm
    exact ⟨e1, a1, (hε' b1).2, ((hε' b2).1).symm, b3⟩

public lemma continuous_of_entire (ga : ∀ z, AnalyticAt ℂ g z) : Continuous g :=
  continuous_iff_continuousAt.mpr fun z ↦ (ga z).continuousAt

/-!
### Attracting Fatou coordinates and repelling parametrisations
-/

/-- Transporting attracting objects through the normalising conjugacy -/
public lemma transport_attr {h φ Φ' : ℂ → ℂ} {P' : Set ℂ} {δ : ℝ} (δ0 : 0 < δ) (inj : InjOn h (Metric.ball 0 δ))
    (hδ : ∀ z ∈ Metric.ball (0 : ℂ) δ, φ (h z) = z ∧ AnalyticAt ℂ h z ∧ AnalyticAt ℂ φ (h z) ∧
      g (h z) = h (φ (g (h z))))
    (Po : IsOpen P') (Pb : P' ⊆ Metric.ball 0 δ) (PM : MapsTo (φ ∘ g ∘ h) P' P')
    (Φa : AnalyticOnNhd ℂ Φ' P') (Φe : ∀ z ∈ P', Φ' ((φ ∘ g ∘ h) z) = Φ' z + 1) :
    IsOpen (h '' P') ∧ MapsTo g (h '' P') (h '' P') ∧ AnalyticOnNhd ℂ (Φ' ∘ φ) (h '' P') ∧
      ∀ y ∈ h '' P', (Φ' ∘ φ) (g y) = (Φ' ∘ φ) y + 1 := by
  have sub : ∀ {z}, z ∈ P' → z ∈ Metric.ball (0 : ℂ) δ := fun m ↦ Pb m
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine isOpen_image_of_injOn (fun z m ↦ (hδ z m).2.1) (convex_ball _ _).isPreconnected inj
      (Metric.mem_ball_self δ0) (x := 0) (y := ((δ / 2 : ℝ) : ℂ)) (by simp; linarith [abs_of_pos δ0])
      (by rw [Ne, eq_comm, Complex.ofReal_eq_zero]; linarith) (fun z m ↦ Pb m) Po
  · rintro _ ⟨z, m, rfl⟩
    exact ⟨_, PM m, ((hδ z (sub m)).2.2.2).symm⟩
  · rintro _ ⟨z, m, rfl⟩
    have fa := Φa z m
    rw [← (hδ z (sub m)).1] at fa
    exact fa.comp (hδ z (sub m)).2.2.1
  · rintro _ ⟨z, m, rfl⟩
    simp only [Function.comp_apply, (hδ z (sub m)).1]
    exact Φe z m

/-- Transporting a repelling parametrisation through the normalising conjugacy -/
public lemma transport_rep {h φ Ψ' : ℂ → ℂ} {V : Set ℂ} {δ : ℝ}
    (hδ : ∀ z ∈ Metric.ball (0 : ℂ) δ, AnalyticAt ℂ h z ∧ g (h z) = h (φ (g (h z))))
    (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (Ψa : AnalyticOnNhd ℂ Ψ' V) (Ψb : ∀ ζ ∈ V, Ψ' ζ ∈ Metric.ball 0 δ)
    (Ψe : ∀ ζ ∈ V, (φ ∘ g ∘ h) (Ψ' (ζ - 1)) = Ψ' ζ) :
    AnalyticOnNhd ℂ (h ∘ Ψ') V ∧ ∀ ζ ∈ V, g ((h ∘ Ψ') (ζ - 1)) = (h ∘ Ψ') ζ := by
  refine ⟨fun ζ m ↦ (hδ _ (Ψb ζ m)).1.comp (Ψa ζ m), fun ζ m ↦ ?_⟩
  simp only [Function.comp_apply]
  rw [(hδ _ (Ψb _ (Vl ζ m))).2]
  exact congrArg h (Ψe ζ m)

/-- Attracting petals and Fatou coordinates of a parabolic fixed point.  For each `k`-th root `c` of `-1 / (k a)`
there is a petal `P` in any given ball around `0`, with `g P ⊆ P` and an analytic `Φ` with `Φ ∘ g = Φ + 1` on `P`;
`Φ` extends along orbits to the basin of `P`. -/
public theorem parabolic_attracting (ga : ∀ z, AnalyticAt ℂ g z) (g0 : g 0 = 0) (k0 : 0 < k) (a0 : a ≠ 0)
    (approx : (fun z ↦ g z - (z + a * z ^ (k + 1))) =O[𝓝 0] fun z ↦ z ^ (k + 2)) {c : ℂ}
    (hc : c ^ k = -1 / (k * a)) {ε : ℝ} (ε0 : 0 < ε) :
    ∃ P : Set ℂ, ∃ Φ : ℂ → ℂ, IsOpen P ∧ P.Nonempty ∧ P ⊆ Metric.ball 0 ε ∧ MapsTo g P P ∧
      AnalyticOnNhd ℂ Φ P ∧ (∀ z ∈ P, Φ (g z) = Φ z + 1) ∧
      IsOpen (basin g P) ∧ MapsTo g (basin g P) (basin g P) ∧
      AnalyticOnNhd ℂ (basinExt g Φ P) (basin g P) ∧
      ∀ z ∈ basin g P, basinExt g Φ P (g z) = basinExt g Φ P z + 1 := by
  obtain ⟨h, φ, b, ha, φa, h0, -, l, r, -, pg⟩ := PetalGerm.normalize k0 a0 (ga 0) g0 approx
  obtain ⟨δ, δ0, inj, hδ⟩ := conj_setup (ga 0) g0 ha φa h0 l r ε0
  obtain ⟨P', Φ', Po, Pne, Pb, PM, Φa, Φe⟩ := pg.local_attracting hc δ0
  obtain ⟨Po', gP, Φa', Φe'⟩ := transport_attr δ0 inj (fun z m ↦ ⟨(hδ z m).1, (hδ z m).2.1, (hδ z m).2.2.1,
    (hδ z m).2.2.2.1⟩) Po Pb PM Φa Φe
  refine ⟨h '' P', Φ' ∘ φ, Po', Pne.image _, ?_, gP, Φa', Φe', isOpen_basin (continuous_of_entire ga) Po',
    mapsTo_basin gP, basinExt_analytic ga Po' gP Φe' Φa', fun z m ↦ basinExt_eqn gP Φe' m⟩
  rintro _ ⟨z, m, rfl⟩
  exact (hδ z (Pb m)).2.2.2.2

/-- Repelling parametrisations of a parabolic fixed point.  For each `k`-th root `c` of `1 / (k a)` there is an open
`V`, closed under `ζ ↦ ζ - 1` and reached from every point, and an analytic `Ψ` on `V` with values in any given ball
around `0` and `g (Ψ (ζ - 1)) = Ψ ζ`; `Ψ` extends to an entire map with `Ψ (ζ + 1) = g (Ψ ζ)`. -/
public theorem parabolic_repelling (ga : ∀ z, AnalyticAt ℂ g z) (g0 : g 0 = 0) (k0 : 0 < k) (a0 : a ≠ 0)
    (approx : (fun z ↦ g z - (z + a * z ^ (k + 1))) =O[𝓝 0] fun z ↦ z ^ (k + 2)) {c : ℂ}
    (hc : c ^ k = 1 / (k * a)) {ε : ℝ} (ε0 : 0 < ε) :
    ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧ (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧
      AnalyticOnNhd ℂ Ψ V ∧ (∀ ζ ∈ V, Ψ ζ ∈ Metric.ball 0 ε) ∧ (∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) ∧
      (∀ ζ, AnalyticAt ℂ (paramExt g Ψ V) ζ) ∧ (∀ ζ, paramExt g Ψ V (ζ + 1) = g (paramExt g Ψ V ζ)) ∧
      ∀ ζ ∈ V, paramExt g Ψ V ζ = Ψ ζ := by
  obtain ⟨h, φ, b, ha, φa, h0, -, l, r, -, pg⟩ := PetalGerm.normalize k0 a0 (ga 0) g0 approx
  obtain ⟨δ, δ0, -, hδ⟩ := conj_setup (ga 0) g0 ha φa h0 l r ε0
  obtain ⟨V, Ψ', Vo, Vl, reach, Ψa, Ψb, Ψe⟩ := pg.local_repelling hc δ0
  obtain ⟨Ψa', Ψe'⟩ := transport_rep (fun z m ↦ ⟨(hδ z m).2.1, (hδ z m).2.2.2.1⟩) Vl Ψa Ψb Ψe
  exact ⟨V, h ∘ Ψ', Vo, Vl, reach, Ψa', fun ζ m ↦ (hδ _ (Ψb ζ m)).2.2.2.2, Ψe',
    paramExt_analytic ga Vo Vl Ψe' reach Ψa', paramExt_eqn Vl Ψe' reach, fun ζ m ↦ paramExt_eq Vl Ψe' m⟩

/-!
### The horn map
-/

/-- The horn map `H = Φ ∘ Ψ` of an attracting Fatou coordinate and a repelling parametrisation -/
@[expose] public noncomputable def hornMap (g Φ Ψ : ℂ → ℂ) (P V : Set ℂ) (ζ : ℂ) : ℂ :=
  basinExt g Φ P (paramExt g Ψ V ζ)

/-- The domain of the horn map: parameters whose image lies in the basin -/
@[expose] public def hornDomain (g Ψ : ℂ → ℂ) (P V : Set ℂ) : Set ℂ :=
  paramExt g Ψ V ⁻¹' basin g P

/-- The horn map is analytic on its open domain, which is invariant under `ζ ↦ ζ ± 1`, and it commutes with
`ζ ↦ ζ + 1` -/
public theorem horn_map {Φ Ψ : ℂ → ℂ} {P V : Set ℂ} (ga : ∀ z, AnalyticAt ℂ g z) (Po : IsOpen P)
    (gP : MapsTo g P P) (Φa : AnalyticOnNhd ℂ Φ P) (Φe : ∀ z ∈ P, Φ (g z) = Φ z + 1) (Vo : IsOpen V)
    (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (reach : ∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) (Ψa : AnalyticOnNhd ℂ Ψ V)
    (Ψe : ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) :
    IsOpen (hornDomain g Ψ P V) ∧ (∀ ζ, ζ ∈ hornDomain g Ψ P V ↔ ζ + 1 ∈ hornDomain g Ψ P V) ∧
      AnalyticOnNhd ℂ (hornMap g Φ Ψ P V) (hornDomain g Ψ P V) ∧
      ∀ ζ ∈ hornDomain g Ψ P V, hornMap g Φ Ψ P V (ζ + 1) = hornMap g Φ Ψ P V ζ + 1 := by
  have pa := paramExt_analytic ga Vo Vl Ψe reach Ψa
  have pe := paramExt_eqn Vl Ψe reach
  refine ⟨(isOpen_basin (continuous_of_entire ga) Po).preimage
    (continuous_iff_continuousAt.mpr fun ζ ↦ (pa ζ).continuousAt), fun ζ ↦ ?_, fun ζ m ↦ ?_, fun ζ m ↦ ?_⟩
  · simp only [hornDomain, mem_preimage, pe]
    constructor
    · exact fun m ↦ mapsTo_basin gP m
    · rintro ⟨n, m⟩
      exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩
  · exact (basinExt_analytic ga Po gP Φe Φa _ m).comp (pa ζ)
  · simp only [hornMap, pe]
    exact basinExt_eqn gP Φe m

/-!
### Critical values of the horn map
-/

lemma hasDerivAt_iterate (ga : ∀ z, AnalyticAt ℂ g z) (m : ℕ) (y : ℂ) :
    HasDerivAt g^[m] (∏ j ∈ Finset.range m, deriv g (g^[j] y)) y := by
  induction m with
  | zero => simpa using hasDerivAt_id y
  | succ m ih =>
    rw [Function.iterate_succ', Finset.prod_range_succ, mul_comm]
    exact (ga _).differentiableAt.hasDerivAt.comp y ih

/-- The critical values of the horn map lie in `Φ (critical values of g) + ℤ`: if `H' ζ = 0` then some critical
point `c₀` of `g` has `H ζ = Φ (g c₀) + j`, `j ∈ ℤ`.  (A critical point of `H` comes from a critical point of `g` met
either by the orbit of `Ψ ζ` before it reaches the petal, or by `Ψ`'s backward orbit.) -/
public theorem horn_crit_values {Φ Ψ : ℂ → ℂ} {P V : Set ℂ} (ga : ∀ z, AnalyticAt ℂ g z) (Po : IsOpen P)
    (gP : MapsTo g P P) (Φa : AnalyticOnNhd ℂ Φ P) (Φe : ∀ z ∈ P, Φ (g z) = Φ z + 1) (Vo : IsOpen V)
    (Vl : ∀ ζ ∈ V, ζ - 1 ∈ V) (reach : ∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) (Ψa : AnalyticOnNhd ℂ Ψ V)
    (Ψe : ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) (Φd : ∀ z ∈ P, deriv Φ z ≠ 0) (Ψd : ∀ ζ ∈ V, deriv Ψ ζ ≠ 0)
    {ζ : ℂ} (mD : ζ ∈ hornDomain g Ψ P V) (crit : deriv (hornMap g Φ Ψ P V) ζ = 0) :
    ∃ c₀ : ℂ, deriv g c₀ = 0 ∧ g c₀ ∈ basin g P ∧ ∃ j : ℤ, hornMap g Φ Ψ P V ζ = basinExt g Φ P (g c₀) + j := by
  obtain ⟨N, hN⟩ := reach ζ
  set y := Ψ (ζ - N)
  have pe : paramExt g Ψ V ζ = g^[N] y := paramExt_eq_of Vl Ψe hN
  obtain ⟨n, hn⟩ := mD
  rw [pe, ← Function.iterate_add_apply] at hn
  -- near `ζ`, `H ξ = Φ (g^[n + N] (Ψ (ξ - N))) - n`
  have sa : AnalyticAt ℂ (fun ξ : ℂ ↦ ξ - N) ζ := analyticAt_id.sub analyticAt_const
  have ev1 : ∀ᶠ ξ : ℂ in 𝓝 ζ, ξ - (N : ℂ) ∈ V := sa.continuousAt.preimage_mem_nhds (Vo.mem_nhds hN)
  have qa : AnalyticAt ℂ (fun ξ ↦ g^[n + N] (Ψ (ξ - N))) ζ :=
    (iterate_analyticAt ga _ _).comp ((Ψa _ hN).comp (f := fun ξ : ℂ ↦ ξ - N) sa)
  have ev2 : ∀ᶠ ξ in 𝓝 ζ, g^[n + N] (Ψ (ξ - N)) ∈ P := qa.continuousAt.preimage_mem_nhds (Po.mem_nhds hn)
  have eq : hornMap g Φ Ψ P V =ᶠ[𝓝 ζ] fun ξ ↦ Φ (g^[n + N] (Ψ (ξ - N))) - n := by
    filter_upwards [ev1, ev2] with ξ m1 m2
    simp only [hornMap, paramExt_eq_of Vl Ψe m1]
    have m2' : g^[n] (g^[N] (Ψ (ξ - N))) ∈ P := by rwa [← Function.iterate_add_apply]
    rw [basinExt_eq_of gP Φe m2', ← Function.iterate_add_apply]
  -- the chain rule
  have d : HasDerivAt (fun ξ ↦ Φ (g^[n + N] (Ψ (ξ - N))) - n)
      (deriv Φ (g^[n + N] y) * ((∏ j ∈ Finset.range (n + N), deriv g (g^[j] y)) * (deriv Ψ (ζ - N) * 1))) ζ := by
    have dΨ : HasDerivAt (fun ξ : ℂ ↦ Ψ (ξ - N)) (deriv Ψ (ζ - N) * 1) ζ :=
      (Ψa _ hN).differentiableAt.hasDerivAt.comp ζ ((hasDerivAt_id ζ).sub_const _)
    have dg := (hasDerivAt_iterate ga (n + N) y).comp ζ dΨ
    exact ((Φa _ hn).differentiableAt.hasDerivAt.comp ζ dg).sub_const _
  rw [eq.deriv_eq, d.deriv] at crit
  simp only [mul_one, mul_eq_zero, Φd _ hn, Ψd _ hN, false_or, or_false] at crit
  obtain ⟨j, jm, hj⟩ := Finset.prod_eq_zero_iff.mp crit
  have jn : j < n + N := Finset.mem_range.mp jm
  refine ⟨g^[j] y, hj, ⟨n + N - (j + 1), ?_⟩, ⟨(N : ℤ) - (j + 1), ?_⟩⟩
  · rw [← Function.iterate_succ_apply' g j y, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    exact hn
  · have m2 : g^[n + N - (j + 1)] (g (g^[j] y)) ∈ P := by
      rw [← Function.iterate_succ_apply' g j y, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
      exact hn
    rw [eq.self_of_nhds, basinExt_eq_of gP Φe m2, ← Function.iterate_succ_apply' g j y,
      ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    push_cast [Nat.cast_sub (by omega : j + 1 ≤ n + N)]
    ring

/-- Nonvanishing derivatives survive the normalising conjugacy -/
public lemma transport_deriv {h φ Φ' Ψ' : ℂ → ℂ} {P' V : Set ℂ} {δ : ℝ}
    (hδ : ∀ z ∈ Metric.ball (0 : ℂ) δ, φ (h z) = z ∧ AnalyticAt ℂ h z ∧ AnalyticAt ℂ φ (h z))
    (Pb : P' ⊆ Metric.ball 0 δ) (Φa : AnalyticOnNhd ℂ Φ' P') (Φd : ∀ z ∈ P', deriv Φ' z ≠ 0)
    (Ψb : ∀ ζ ∈ V, Ψ' ζ ∈ Metric.ball 0 δ) (Ψa : AnalyticOnNhd ℂ Ψ' V) (Ψd : ∀ ζ ∈ V, deriv Ψ' ζ ≠ 0) :
    (∀ y ∈ h '' P', deriv (Φ' ∘ φ) y ≠ 0) ∧ ∀ ζ ∈ V, deriv (h ∘ Ψ') ζ ≠ 0 := by
  have dd : ∀ z ∈ Metric.ball (0 : ℂ) δ, deriv φ (h z) ≠ 0 ∧ deriv h z ≠ 0 := fun z m ↦
    deriv_ne_zero_of_comp one_ne_zero (hδ z m).2.2 (hδ z m).2.1 (by
      filter_upwards [Metric.isOpen_ball.mem_nhds m] with y ym; rw [one_mul]; exact (hδ y ym).1)
  refine ⟨?_, fun ζ m ↦ ?_⟩
  · rintro _ ⟨z, m, rfl⟩
    have fa := Φa z m
    rw [← (hδ z (Pb m)).1] at fa
    rw [deriv_comp _ fa.differentiableAt (hδ z (Pb m)).2.2.differentiableAt, (hδ z (Pb m)).1]
    exact mul_ne_zero (Φd z m) (dd z (Pb m)).1
  · rw [deriv_comp _ (hδ _ (Ψb ζ m)).2.1.differentiableAt (Ψa ζ m).differentiableAt]
    exact mul_ne_zero (dd _ (Ψb ζ m)).2 (Ψd ζ m)
