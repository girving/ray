module
public import Ray.Dynamics.FatouExtend
public import Ray.Dynamics.FatouParam
public import Ray.Dynamics.PetalNormal
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.OpenMapping
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
lemma isOpen_image_of_injOn {f : ℂ → ℂ} {U S : Set ℂ} (fa : AnalyticOnNhd ℂ f U) (Uc : IsPreconnected U)
    (inj : InjOn f U) {x y : ℂ} (xU : x ∈ U) (yU : y ∈ U) (xy : x ≠ y) (SU : S ⊆ U) (So : IsOpen S) :
    IsOpen (f '' S) := by
  rcases fa.is_constant_or_isOpen Uc with ⟨w, hw⟩ | o
  · exact absurd (inj xU yU (by rw [hw x xU, hw y yU])) xy
  · exact o S SU So

/-!
### Petal branches
-/

lemma root_ne_zero {c s : ℂ} (c0 : c ≠ 0) : petalRoot k c s ≠ 0 :=
  mul_ne_zero c0 (Complex.exp_ne_zero _)

lemma coord_root {c w : ℂ} (k0 : 0 < k) (a0 : a ≠ 0) (hc : c ^ k = -1 / (k * a)) (w0 : w ≠ 0) :
    petalCoord k a (petalRoot k c w) = w := by
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  simp only [petalCoord]
  rw [PetalGerm.root_pow w0 k0, hc]
  field_simp

lemma norm_root_lt {c s : ℂ} {ε : ℝ} (k0 : 0 < k) (ε0 : 0 < ε) (s0 : s ≠ 0) (big : ‖c‖ ^ k / ε ^ k < ‖s‖) :
    ‖petalRoot k c s‖ < ε := by
  refine (pow_lt_pow_iff_left₀ (norm_nonneg _) ε0.le k0.ne').mp ?_
  rw [← norm_pow, PetalGerm.root_pow s0 k0, norm_div, norm_pow, div_lt_iff₀ (norm_pos_iff.mpr s0)]
  rw [div_lt_iff₀ (by positivity)] at big
  linarith

lemma c_ne_zero {c : ℂ} {t : ℂ} (k0 : 0 < k) (t0 : t ≠ 0) (hc : c ^ k = t) : c ≠ 0 := by
  rintro rfl; rw [zero_pow k0.ne'] at hc; exact t0 hc.symm

/-!
### Local objects for a germ in normal form
-/

/-- An attracting petal near `0` with its Fatou coordinate, for a germ in normal form -/
lemma PetalGerm.local_attracting (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = -1 / (k * a)) {ε : ℝ}
    (ε0 : 0 < ε) : ∃ P : Set ℂ, ∃ Φ : ℂ → ℂ, IsOpen P ∧ P.Nonempty ∧ P ⊆ Metric.ball 0 ε ∧ MapsTo g P P ∧
      AnalyticOnNhd ℂ Φ P ∧ ∀ z ∈ P, Φ (g z) = Φ z + 1 := by
  have k0 := h.k0
  have kc : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k0.ne'
  have c0 : c ≠ 0 := c_ne_zero k0 (div_ne_zero (by norm_num) (mul_ne_zero kc h.a0)) hc
  obtain ⟨R, A, nt, semi⟩ := h.attracting hc
  set R₁ := max R (‖c‖ ^ k / ε ^ k)
  have nt1 := nt.mono (le_max_left R (‖c‖ ^ k / ε ^ k))
  set β := petalResidue k a b
  set G := fun w ↦ petalCoord k a (g (petalRoot k c w))
  have R4 := nt1.four_le
  have facts : ∀ w ∈ rightHalf R₁, w ≠ 0 ∧ w ∈ slitPlane ∧ w ∈ rightHalf R ∧ R₁ < ‖w‖ := fun w m ↦ by
    have wr : R₁ < w.re := m
    have wn := lt_of_lt_of_le wr (Complex.re_le_norm w)
    refine ⟨fun e ↦ by rw [e] at wr; simp at wr; linarith, ?_, ?_, wn⟩
    · rw [Complex.mem_slitPlane_iff]; left; linarith
    · show R < w.re; have := le_max_left R (‖c‖ ^ k / ε ^ k); linarith
  refine ⟨(fun w ↦ petalRoot k c w) '' rightHalf R₁, fun z ↦ NearTranslation.fatou G β (petalCoord k a z),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    exact norm_root_lt k0 ε0 (facts w m).1 (lt_of_le_of_lt (le_max_right _ _) (facts w m).2.2.2)
  · rintro _ ⟨w, m, rfl⟩
    exact ⟨G w, nt1.mapsTo m, (semi w (facts w m).2.2.1).symm⟩
  · rintro _ ⟨w, m, rfl⟩
    have e := coord_root k0 h.a0 hc (facts w m).1
    have fa := nt.fatou_analytic _ (facts w m).2.2.1
    rw [← e] at fa
    exact fa.comp (PetalGerm.analyticAt_petalCoord (root_ne_zero c0) kc h.a0)
  · rintro _ ⟨w, m, rfl⟩
    simp only
    rw [coord_root k0 h.a0 hc (facts w m).1]
    exact nt.fatou_eqn (facts w m).2.2.1

/-- A repelling parametrisation near `0`, for a germ in normal form -/
lemma PetalGerm.local_repelling (h : PetalGerm g k a b) {c : ℂ} (hc : c ^ k = 1 / (k * a)) {ε : ℝ}
    (ε0 : 0 < ε) : ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧
      (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧ AnalyticOnNhd ℂ Ψ V ∧ (∀ ζ ∈ V, Ψ ζ ∈ Metric.ball 0 ε) ∧
      (∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) := by
  have k0 := h.k0
  obtain ⟨R, A, nt, semi⟩ := h.repelling hc
  obtain ⟨V, Ψw, Vo, Vl, reach, Ψa, Ψm, Ψe⟩ := nt.repel_param (max R (‖c‖ ^ k / ε ^ k))
  have R4 := nt.four_le
  have facts : ∀ ζ ∈ V, -Ψw ζ ≠ 0 ∧ -Ψw ζ ∈ slitPlane ∧ Ψw ζ ∈ leftHalf R ∧
      ‖c‖ ^ k / ε ^ k < ‖-Ψw ζ‖ := fun ζ m ↦ by
    have r : (Ψw ζ).re < -max R (‖c‖ ^ k / ε ^ k) := Ψm ζ m
    have m1 := le_max_left R (‖c‖ ^ k / ε ^ k)
    have m2 := le_max_right R (‖c‖ ^ k / ε ^ k)
    have nr : -(Ψw ζ).re ≤ ‖-Ψw ζ‖ := by rw [← Complex.neg_re]; exact Complex.re_le_norm _
    refine ⟨fun e ↦ by rw [neg_eq_zero] at e; rw [e] at r; simp at r; linarith, ?_, ?_, by linarith⟩
    · rw [Complex.mem_slitPlane_iff, Complex.neg_re]; left; linarith
    · show (Ψw ζ).re < -R; linarith
  refine ⟨V, fun ζ ↦ petalRoot k c (-Ψw ζ), Vo, Vl, reach, fun ζ m ↦ ?_, fun ζ m ↦ ?_, fun ζ m ↦ ?_⟩
  · exact (PetalGerm.analyticAt_root (facts ζ m).2.1).comp (f := fun ζ ↦ -Ψw ζ) (Ψa ζ m).neg
  · simp only [Metric.mem_ball, dist_zero_right]
    exact norm_root_lt k0 ε0 (facts ζ m).1 (facts ζ m).2.2.2
  · have m' := Vl ζ m
    simp only
    rw [semi _ (facts _ m').2.2.1]
    congr 2
    exact Ψe ζ m

/-!
### Transport through the normalising conjugacy
-/

/-- Small balls on which the normalising conjugacy behaves: `φ ∘ h = id`, `h` maps into a given ball, and
`g ∘ h = h ∘ (φ ∘ g ∘ h)` -/
lemma conj_setup {h φ : ℂ → ℂ} (ga : AnalyticAt ℂ g 0) (g0 : g 0 = 0) (ha : AnalyticAt ℂ h 0)
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

lemma continuous_of_entire (ga : ∀ z, AnalyticAt ℂ g z) : Continuous g :=
  continuous_iff_continuousAt.mpr fun z ↦ (ga z).continuousAt

/-!
### Attracting Fatou coordinates and repelling parametrisations
-/

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
  obtain ⟨h, φ, b, ha, φa, h0, -, l, r, pg⟩ := PetalGerm.normalize k0 a0 (ga 0) g0 approx
  obtain ⟨δ, δ0, inj, hδ⟩ := conj_setup (ga 0) g0 ha φa h0 l r ε0
  obtain ⟨P', Φ', Po, Pne, Pb, PM, Φa, Φe⟩ := pg.local_attracting hc δ0
  have sub : ∀ {z}, z ∈ P' → z ∈ Metric.ball (0 : ℂ) δ := fun m ↦ Pb m
  have Po' : IsOpen (h '' P') := by
    refine isOpen_image_of_injOn (fun z m ↦ (hδ z m).2.1) (convex_ball _ _).isPreconnected inj
      (Metric.mem_ball_self δ0) (x := 0) (y := ((δ / 2 : ℝ) : ℂ)) (by simp; linarith [abs_of_pos δ0])
      (by rw [Ne, eq_comm, Complex.ofReal_eq_zero]; linarith) (fun z m ↦ Pb m) Po
  have gP : MapsTo g (h '' P') (h '' P') := by
    rintro _ ⟨z, m, rfl⟩
    exact ⟨_, PM m, ((hδ z (sub m)).2.2.2.1).symm⟩
  have Φa' : AnalyticOnNhd ℂ (Φ' ∘ φ) (h '' P') := by
    rintro _ ⟨z, m, rfl⟩
    have fa := Φa z m
    rw [← (hδ z (sub m)).1] at fa
    exact fa.comp (hδ z (sub m)).2.2.1
  have Φe' : ∀ y ∈ h '' P', (Φ' ∘ φ) (g y) = (Φ' ∘ φ) y + 1 := by
    rintro _ ⟨z, m, rfl⟩
    simp only [Function.comp_apply, (hδ z (sub m)).1]
    exact Φe z m
  refine ⟨h '' P', Φ' ∘ φ, Po', Pne.image _, ?_, gP, Φa', Φe', isOpen_basin (continuous_of_entire ga) Po',
    mapsTo_basin gP, basinExt_analytic ga Po' gP Φe' Φa', fun z m ↦ basinExt_eqn gP Φe' m⟩
  rintro _ ⟨z, m, rfl⟩
  exact (hδ z (sub m)).2.2.2.2

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
  obtain ⟨h, φ, b, ha, φa, h0, -, l, r, pg⟩ := PetalGerm.normalize k0 a0 (ga 0) g0 approx
  obtain ⟨δ, δ0, -, hδ⟩ := conj_setup (ga 0) g0 ha φa h0 l r ε0
  obtain ⟨V, Ψ', Vo, Vl, reach, Ψa, Ψb, Ψe⟩ := pg.local_repelling hc δ0
  have Ψa' : AnalyticOnNhd ℂ (h ∘ Ψ') V := fun ζ m ↦ (hδ _ (Ψb ζ m)).2.1.comp (Ψa ζ m)
  have Ψe' : ∀ ζ ∈ V, g ((h ∘ Ψ') (ζ - 1)) = (h ∘ Ψ') ζ := fun ζ m ↦ by
    simp only [Function.comp_apply]
    rw [(hδ _ (Ψb _ (Vl ζ m))).2.2.2.1]
    exact congrArg h (Ψe ζ m)
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
