module
public import Ray.Dynamics.HornEnds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic.Bound

/-!
## Parabolic points of multiplier `-1`

Let `f z = -z + O(z²)` with `g = f ∘ f = z + a z³ + O(z⁴)`, `a ≠ 0`: the parabolic point of `z² - 3/4` (in
`w = z + 1/2`, `f w = -w + w²`).  `g` has two attracting and two repelling petals, swapped by `f`.

In the coordinate `h` normalising `g` (`PetalGerm.normalize`), `f̃ = φ ∘ f ∘ h` is odd to third order:
`f̃ z = -z - (a/2) z³ + O(z⁴)`.  Indeed, writing `f̃ = -z + α z² + β z³ + ...`, the `z⁴` coefficient of `f̃ ∘ f̃` is
`α (α² + β) = -(a/2) α`, and the normal form has no `z⁴` term.  (Without this, `f` acts on the petal coordinate as
`w ↦ w + √w + ...`.)  So in the petal coordinate `f` is `w ↦ w + 1/2 + O(w^(-1/2))`, swapping the two petals.

1. `flip_odd`: the expansion of `f̃`.
2. `flip_chart`: in the petal coordinate `f` is `w ↦ w + 1/2 + O(‖z‖)` and swaps the branches at `c`, `-c`.
3. `NearTranslation.fatou_conj`: a map intertwining two near-translations (same `β`) that moves by `t + o(1)` shifts
   their Fatou coordinates by exactly `t` (the difference is invariant along orbits and vanishes far out).
4. `PetalGerm.flip_attr`: `Φ_{-c} (f z) = Φ_c z + 1/2` on the attracting petals.
5. `parabolic_flip`: for entire `f`, the horn maps of `g = f ∘ f` with both ends, and `f` swapping the two attracting
   basins with a half step; so `f ∘ Ψ` has horn maps `H± + 1/2` into the swapped petals.
-/

open Asymptotics Filter
open Complex (exp log slitPlane arg I)
open Set
open scoped Real Topology

/-- Taylor coefficients one at a time -/
lemma coeff_step {F : ℂ → ℂ} {n : ℕ} (Fa : AnalyticAt ℂ F 0) (o : F =O[𝓝 0] fun z ↦ z ^ n) :
    ∃ c, (fun z ↦ F z - c * z ^ n) =O[𝓝 0] fun z ↦ z ^ (n + 1) := by
  obtain ⟨q, qa, hq⟩ := exists_pow_mul_of_isBigO Fa o
  refine ⟨q 0, ?_⟩
  have qd : (fun z ↦ q z - q 0) =O[𝓝 0] fun z ↦ z := by
    simpa using qa.differentiableAt.hasDerivAt.isBigO_sub
  refine ((isBigO_refl (fun z : ℂ ↦ z ^ n) _).mul qd).congr' ?_ (Eventually.of_forall fun z ↦ by ring)
  filter_upwards [hq] with z e
  rw [e]; ring

/-- A monomial that is `O(z^(n+1))` vanishes -/
lemma coeff_zero {c : ℂ} {n : ℕ} (o : (fun z ↦ c * z ^ n) =O[𝓝 0] fun z ↦ z ^ (n + 1)) : c = 0 := by
  obtain ⟨C, hC⟩ := o.bound
  have t : Tendsto (fun t : ℝ ↦ ((t : ℂ))) (𝓝[>] 0) (𝓝 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖c‖ ≤ C * t := by
    filter_upwards [t.eventually hC, self_mem_nhdsWithin] with t ht (t0 : 0 < t)
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos t0] at ht
    have tp : 0 < t ^ n := pow_pos t0 n
    rw [pow_succ] at ht
    nlinarith
  have lim : Tendsto (fun t : ℝ ↦ C * t) (𝓝[>] 0) (𝓝 0) := by
    have c : Continuous (fun t : ℝ ↦ C * t) := by fun_prop
    have := (c.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have := ge_of_tendsto lim ev
  exact norm_le_zero_iff.mp this

variable {f : ℂ → ℂ}

/-- An analytic `f̃` with `f̃ 0 = 0`, `f̃' 0 = -1` is `-z + α z² + β z³ + γ z⁴ + O(z⁵)` -/
lemma flip_expand (fa : AnalyticAt ℂ f 0) (f0 : f 0 = 0) (fd : deriv f 0 = -1) :
    ∃ α β γ : ℂ, (fun z ↦ f z - (-z + α * z ^ 2 + β * z ^ 3 + γ * z ^ 4)) =O[𝓝 0] fun z ↦ z ^ 5 := by
  set F := fun z ↦ f z + z
  have Fa : AnalyticAt ℂ F 0 := fa.add analyticAt_id
  have F0 : F 0 = 0 := by simp [F, f0]
  have Fd : deriv F 0 = 0 := by
    have := (fa.differentiableAt.hasDerivAt.add (hasDerivAt_id (0 : ℂ))).deriv
    simp only [fd] at this
    rw [show F = f + id from rfl, this]; ring
  -- `F = O(z²)` by the second-order Taylor bound
  obtain ⟨C, r, -, r0, tay⟩ := taylor2 Fa
  have F2 : F =O[𝓝 0] fun z ↦ z ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) r0] with z zm
    have := tay z 0 (by simpa using zm) (by simpa using r0)
    simpa [F0, Fd, norm_pow] using this
  have poly : ∀ c₁ c₂ c₃ : ℂ, AnalyticAt ℂ (fun z ↦ F z - (c₁ * z ^ 2 + c₂ * z ^ 3 + c₃ * z ^ 4)) 0 :=
    fun _ _ _ ↦ Fa.sub (by fun_prop)
  obtain ⟨α, hα⟩ := coeff_step Fa F2
  obtain ⟨β, hβ⟩ := coeff_step ((poly α 0 0).congr (by filter_upwards with z; simp)) hα
  have hβ' : (fun z ↦ F z - (α * z ^ 2 + β * z ^ 3)) =O[𝓝 0] fun z ↦ z ^ 4 :=
    hβ.congr_left fun z ↦ by ring
  obtain ⟨γ, hγ⟩ := coeff_step ((poly α β 0).congr (by filter_upwards with z; simp)) hβ'
  exact ⟨α, β, γ, hγ.congr_left fun z ↦ by simp only [F]; ring⟩

/-- The quartic truncation `-z + α z² + β z³ + γ z⁴` -/
noncomputable def quart (α β γ z : ℂ) : ℂ := -z + α * z ^ 2 + β * z ^ 3 + γ * z ^ 4

/-- `quart ∘ quart` to fifth order -/
lemma quart_quart (α β γ z : ℂ) : quart α β γ (quart α β γ z) =
    z - 2 * (β + α ^ 2) * z ^ 3 + α * (α ^ 2 + β) * z ^ 4 + z ^ 5 * (z^11*γ^5 + 4*z^10*β*γ^4 + 4*z^9*α*γ^4 +
      6*z^9*β^2*γ^3 + 12*z^8*α*β*γ^3 + 4*z^8*β^3*γ^2 - 4*z^8*γ^4 + 6*z^7*α^2*γ^3 + 12*z^7*α*β^2*γ^2 +
      z^7*β^4*γ - 11*z^7*β*γ^3 + 12*z^6*α^2*β*γ^2 + 4*z^6*α*β^3*γ - 12*z^6*α*γ^3 - 9*z^6*β^2*γ^2 +
      4*z^5*α^3*γ^2 + 6*z^5*α^2*β^2*γ - 21*z^5*α*β*γ^2 - z^5*β^3*γ + 6*z^5*γ^3 + 4*z^4*α^3*β*γ -
      12*z^4*α^2*γ^2 - 6*z^4*α*β^2*γ + z^4*β^4 + 9*z^4*β*γ^2 + z^3*α^4*γ - 9*z^3*α^2*β*γ + 3*z^3*α*β^3 +
      13*z^3*α*γ^2 - 4*z^2*α^3*γ + 3*z^2*α^2*β^2 + 8*z^2*α*β*γ - 3*z^2*β^3 - 4*z^2*γ^2 + z*α^3*β +
      8*z*α^2*γ - 5*z*α*β^2 - z*β*γ - α^2*β - 6*α*γ + 3*β^2) := by
  simp only [quart]; ring

/-- `f ∘ f` to fifth order, from `f` to fifth order -/
lemma flip_square {α β γ : ℂ} (fa : AnalyticAt ℂ f 0) (f0 : f 0 = 0)
    (hf : (fun z ↦ f z - quart α β γ z) =O[𝓝 0] fun z ↦ z ^ 5) :
    (fun z ↦ f (f z) - (z - 2 * (β + α ^ 2) * z ^ 3 + α * (α ^ 2 + β) * z ^ 4)) =O[𝓝 0]
      fun z ↦ z ^ 5 := by
  have t : Tendsto f (𝓝 0) (𝓝 0) := by have := fa.continuousAt.tendsto; rwa [f0] at this
  have qO : (fun z ↦ quart α β γ z) =O[𝓝 0] fun z ↦ z := by
    have c : (fun z ↦ quart α β γ z) = fun z ↦ z * (-1 + α * z + β * z ^ 2 + γ * z ^ 3) := by
      funext z; simp only [quart]; ring
    rw [c]
    refine ((isBigO_refl (fun z : ℂ ↦ z) _).mul (Continuous.tendsto (by fun_prop) 0 |>.isBigO_one ℂ)).congr_right
      fun z ↦ by simp
  have uO : f =O[𝓝 0] fun z ↦ z :=
    ((hf.trans ((pow_isBigO_pow (m := 1) (n := 5) (by norm_num)).congr_right fun z ↦ pow_one z)).add
      qO).congr_left fun z ↦ by ring
  -- `f (f z) - quart (f z) = O((f z)^5) = O(z^5)`
  have e1 := (hf.comp_tendsto t).trans (uO.pow 5)
  -- `quart (f z) - quart (quart z) = (f z - quart z) · Q`, `Q` bounded
  set Q := fun u v : ℂ ↦ -1 + α * (u + v) + β * (u ^ 2 + u * v + v ^ 2) + γ * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)
  have Qe : ∀ u v, quart α β γ u - quart α β γ v = (u - v) * Q u v := fun u v ↦ by simp only [quart, Q]; ring
  have Qb : (fun z ↦ Q (f z) (quart α β γ z)) =O[𝓝 0] fun _ ↦ (1 : ℂ) := by
    have tq : Tendsto (fun z ↦ quart α β γ z) (𝓝 0) (𝓝 0) := by
      have c : Continuous (fun z ↦ quart α β γ z) := by simp only [quart]; fun_prop
      simpa [quart] using c.tendsto 0
    have cQ : Continuous (fun p : ℂ × ℂ ↦ Q p.1 p.2) := by simp only [Q]; fun_prop
    exact ((cQ.tendsto (0, 0)).comp (t.prodMk_nhds tq)).isBigO_one ℂ
  have e2 : (fun z ↦ quart α β γ (f z) - quart α β γ (quart α β γ z)) =O[𝓝 0] fun z ↦ z ^ 5 :=
    ((hf.mul Qb).congr_right fun z ↦ by simp).congr_left fun z ↦ (Qe _ _).symm
  -- the polynomial remainder
  have e3 : (fun z ↦ quart α β γ (quart α β γ z) - (z - 2 * (β + α ^ 2) * z ^ 3 +
      α * (α ^ 2 + β) * z ^ 4)) =O[𝓝 0] fun z ↦ z ^ 5 := by
    have c : Continuous (fun z : ℂ ↦ z^11*γ^5 + 4*z^10*β*γ^4 + 4*z^9*α*γ^4 +
      6*z^9*β^2*γ^3 + 12*z^8*α*β*γ^3 + 4*z^8*β^3*γ^2 - 4*z^8*γ^4 + 6*z^7*α^2*γ^3 + 12*z^7*α*β^2*γ^2 +
      z^7*β^4*γ - 11*z^7*β*γ^3 + 12*z^6*α^2*β*γ^2 + 4*z^6*α*β^3*γ - 12*z^6*α*γ^3 - 9*z^6*β^2*γ^2 +
      4*z^5*α^3*γ^2 + 6*z^5*α^2*β^2*γ - 21*z^5*α*β*γ^2 - z^5*β^3*γ + 6*z^5*γ^3 + 4*z^4*α^3*β*γ -
      12*z^4*α^2*γ^2 - 6*z^4*α*β^2*γ + z^4*β^4 + 9*z^4*β*γ^2 + z^3*α^4*γ - 9*z^3*α^2*β*γ + 3*z^3*α*β^3 +
      13*z^3*α*γ^2 - 4*z^2*α^3*γ + 3*z^2*α^2*β^2 + 8*z^2*α*β*γ - 3*z^2*β^3 - 4*z^2*γ^2 + z*α^3*β +
      8*z*α^2*γ - 5*z*α*β^2 - z*β*γ - α^2*β - 6*α*γ + 3*β^2) := by fun_prop
    refine ((isBigO_refl (fun z : ℂ ↦ z ^ 5) _).mul ((c.tendsto 0).isBigO_one ℂ)).congr' ?_ ?_
    · exact Eventually.of_forall fun z ↦ by beta_reduce; rw [quart_quart]; ring
    · exact Eventually.of_forall fun z ↦ by simp
  refine ((e1.add e2).add e3).congr_left fun z ↦ ?_
  simp only [Function.comp_apply]
  ring

/-- Two coefficients that are `O(z⁵)` together vanish -/
lemma coeff_zero₂ {c₃ c₄ : ℂ} (o : (fun z ↦ c₃ * z ^ 3 + c₄ * z ^ 4) =O[𝓝 0] fun z ↦ z ^ 5) :
    c₃ = 0 ∧ c₄ = 0 := by
  have h3 : c₃ = 0 := by
    refine coeff_zero (n := 3) ?_
    refine ((o.trans (pow_isBigO_pow (by norm_num))).sub
      ((isBigO_refl (fun z : ℂ ↦ z ^ 4) _).const_mul_left c₄)).congr_left fun z ↦ by ring
  subst h3
  exact ⟨rfl, coeff_zero (n := 4) (o.congr_left fun z ↦ by ring)⟩

/-- In the normalising coordinate of `f ∘ f`, `f` is odd to third order: `f z = -z - (a/2) z³ + O(z⁴)` -/
public lemma flip_odd {g : ℂ → ℂ} {a b : ℂ} (fa : AnalyticAt ℂ f 0) (f0 : f 0 = 0) (fd : deriv f 0 = -1)
    (pg : PetalGerm g 2 a b) (fg : ∀ᶠ z in 𝓝 0, g z = f (f z)) :
    (fun z ↦ f z - (-z - a / 2 * z ^ 3)) =O[𝓝 0] fun z ↦ z ^ 4 := by
  obtain ⟨α, β, γ, hf⟩ := flip_expand fa f0 fd
  have hf' : (fun z ↦ f z - quart α β γ z) =O[𝓝 0] fun z ↦ z ^ 5 := hf.congr_left fun z ↦ by simp [quart]
  have sq := flip_square fa f0 hf'
  -- `f ∘ f = z + a z³ + O(z⁵)` from the normal form
  have gO : (fun z ↦ f (f z) - (z + a * z ^ 3)) =O[𝓝 0] fun z ↦ z ^ 5 := by
    have ap := pg.approx
    norm_num at ap
    refine ((ap.trans (pow_isBigO_pow (by norm_num))).add
      ((isBigO_refl (fun z : ℂ ↦ z ^ 5) _).const_mul_left b)).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [fg] with z e
    rw [← e]; ring
  have co := coeff_zero₂ (c₃ := -2 * (β + α ^ 2) - a) (c₄ := α * (α ^ 2 + β))
    ((gO.sub sq).congr_left fun z ↦ by ring)
  obtain ⟨c3, c4⟩ := co
  have aβ : α ^ 2 + β = -a / 2 := by linear_combination -c3 / 2
  have α0 : α = 0 := by
    rw [aβ] at c4
    rcases mul_eq_zero.mp c4 with h | h
    · exact h
    · exfalso; exact pg.a0 (by linear_combination -2 * h)
  have β' : β = -a / 2 := by rw [α0] at aβ; simpa using aβ
  refine ((hf.trans (pow_isBigO_pow (by norm_num))).add
    ((isBigO_refl (fun z : ℂ ↦ z ^ 4) _).const_mul_left γ)).congr_left fun z ↦ ?_
  rw [α0, β']; ring

/-- In the petal coordinate `f` is a half step that swaps branches.  For `z = c exp (-log s / 2)` near `0` (any `c`,
`re s > 0`), with `w = petalCoord z` and `w' = petalCoord (f z)`: `‖w' - w - 1/2‖ ≤ C ‖z‖`, and `f z` is the branch at
`-c` of `s w' / w`. -/
public lemma flip_chart {a : ℂ} (a0 : a ≠ 0) (fa : AnalyticAt ℂ f 0)
    (hf : (fun z ↦ f z - (-z - a / 2 * z ^ 3)) =O[𝓝 0] fun z ↦ z ^ 4) :
    ∃ C ε : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ c s : ℂ, c ≠ 0 → 0 < s.re → ‖petalRoot 2 c s‖ < ε →
      f (petalRoot 2 c s) ≠ 0 ∧ AnalyticAt ℂ f (petalRoot 2 c s) ∧
      ‖petalCoord 2 a (f (petalRoot 2 c s)) - (petalCoord 2 a (petalRoot 2 c s) + 1 / 2)‖ ≤
        C * ‖petalRoot 2 c s‖ ∧
      f (petalRoot 2 c s) = petalRoot 2 (-c) (s * (petalCoord 2 a (f (petalRoot 2 c s)) /
        petalCoord 2 a (petalRoot 2 c s))) := by
  -- `f z = -z (1 + u z)` with `u z = (a/2) z² + O(z³)`
  set e := fun z ↦ f z - (-z - a / 2 * z ^ 3)
  set u := fun z : ℂ ↦ a / 2 * z ^ 2 - e z / z
  have fu : ∀ z, z ≠ 0 → f z = -z * (1 + u z) := fun z z0 ↦ by simp only [u, e]; field_simp; ring
  have eO : (fun z ↦ e z / z) =O[𝓝 0] fun z ↦ z ^ 3 := by
    obtain ⟨C, hC⟩ := hf.bound
    refine IsBigO.of_bound C ?_
    filter_upwards [hC] with z hz
    by_cases z0 : z = 0
    · simp [z0]
    · rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr z0)]
      calc ‖e z‖ ≤ C * ‖z ^ 4‖ := hz
        _ = C * ‖z ^ 3‖ * ‖z‖ := by rw [pow_succ z 3, norm_mul]; ring
  have uO : u =O[𝓝 0] fun z ↦ z ^ 2 :=
    (((isBigO_refl (fun z : ℂ ↦ z ^ 2) _).const_mul_left (a / 2)).sub
      (eO.trans (pow_isBigO_pow (by norm_num)))).congr_left fun z ↦ rfl
  have ut : Tendsto u (𝓝 0) (𝓝 0) := uO.trans_tendsto (by simpa using (continuous_pow 2).tendsto (0 : ℂ))
  -- the bracket `B = (1 + u)^(-2) - 1 + a z² = O(z³)`
  have BO : (fun z ↦ ((1 + u z) ^ 2)⁻¹ - 1 + a * z ^ 2) =O[𝓝 0] fun z ↦ z ^ 3 := by
    have e1 := ((one_add_pow_inv_expand 2).comp_tendsto ut).trans
      ((uO.pow 3).trans ((pow_isBigO_pow (by norm_num : 3 ≤ 2 * 3)).congr_left fun z ↦ by rw [pow_mul]))
    have e2 : (fun z ↦ u z ^ 2) =O[𝓝 0] fun z ↦ z ^ 3 :=
      (uO.pow 2).trans ((pow_isBigO_pow (by norm_num : 3 ≤ 2 * 2)).congr_left fun z ↦ by rw [pow_mul])
    refine ((e1.add (e2.const_mul_left 3)).add (eO.const_mul_left 2)).congr_left fun z ↦ ?_
    simp only [Function.comp_apply, u]; push_cast; ring
  obtain ⟨C₁, C₁0, hC₁⟩ := BO.exists_pos
  have ev : ∀ᶠ z in 𝓝 (0 : ℂ), ‖((1 + u z) ^ 2)⁻¹ - 1 + a * z ^ 2‖ ≤ C₁ * ‖z‖ ^ 3 ∧ ‖u z‖ < 1 / 4 ∧
      AnalyticAt ℂ f z := by
    have t := ut.norm; rw [norm_zero] at t
    filter_upwards [hC₁.bound, t.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
      fa.eventually_analyticAt] with z h1 h2 h3
    exact ⟨by simpa [norm_pow] using h1, h2, h3⟩
  obtain ⟨ε₀, ε₀0, hε₀⟩ := Metric.eventually_nhds_iff.mp ev
  have a0' : 0 < ‖a‖ := norm_pos_iff.mpr a0
  set C := C₁ / (2 * ‖a‖)
  set ε := min ε₀ (min (3 / (4 * (C + 1))) (1 / (4 * (‖a‖ + 1))))
  have ε0 : 0 < ε := by positivity
  refine ⟨C, ε, ε0, by positivity, fun c s c0 sr zε ↦ ?_⟩
  set z := petalRoot 2 c s
  have z0 : z ≠ 0 := root_ne_zero c0
  have nz : 0 < ‖z‖ := norm_pos_iff.mpr z0
  obtain ⟨hB, hu, ha⟩ := hε₀ (show dist z 0 < ε₀ by simpa using lt_of_lt_of_le zε (min_le_left _ _))
  have u1 : 1 + u z ≠ 0 := by
    intro h; have : u z = -1 := by linear_combination h
    rw [this] at hu; norm_num at hu
  have fz := fu z z0
  have f0 : f z ≠ 0 := by rw [fz]; exact mul_ne_zero (neg_ne_zero.mpr z0) u1
  set w := petalCoord 2 a z
  set w' := petalCoord 2 a (f z)
  have hw : w = -1 / (2 * a * z ^ 2) := by simp [w, petalCoord]
  have w0 : w ≠ 0 := by rw [hw]; exact div_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero two_ne_zero a0)
    (pow_ne_zero _ z0))
  have hw' : w' = w * ((1 + u z) ^ 2)⁻¹ := by
    simp only [w', w, petalCoord, fz]; push_cast; field_simp
  have key : w' - (w + 1 / 2) = w * (((1 + u z) ^ 2)⁻¹ - 1 + a * z ^ 2) := by
    rw [hw', hw]; field_simp; ring
  have nw : ‖w‖ = 1 / (2 * ‖a‖ * ‖z‖ ^ 2) := by rw [hw]; simp [norm_pow]
  have est : ‖w' - (w + 1 / 2)‖ ≤ C * ‖z‖ := by
    rw [key, norm_mul, nw]
    calc 1 / (2 * ‖a‖ * ‖z‖ ^ 2) * ‖((1 + u z) ^ 2)⁻¹ - 1 + a * z ^ 2‖
        ≤ 1 / (2 * ‖a‖ * ‖z‖ ^ 2) * (C₁ * ‖z‖ ^ 3) := by gcongr
      _ = C * ‖z‖ := by simp only [C]; field_simp
  refine ⟨f0, ha, est, ?_⟩
  -- branch consistency through `PetalGerm.branch`
  have zs : ‖z‖ < 3 / (4 * (C + 1)) := lt_of_lt_of_le zε (le_trans (min_le_right _ _) (min_le_left _ _))
  have za : ‖z‖ < 1 / (4 * (‖a‖ + 1)) := lt_of_lt_of_le zε (le_trans (min_le_right _ _) (min_le_right _ _))
  have Cz : C * ‖z‖ ≤ 3 / 4 := by
    have C0 : 0 ≤ C := by positivity
    rw [lt_div_iff₀ (by positivity)] at zs; nlinarith
  have w4 : 4 ≤ ‖w‖ := by
    rw [nw, le_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at za
    have : ‖z‖ ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖z‖]
  have dw : ‖w' - w‖ ≤ 5 / 4 := by
    calc ‖w' - w‖ = ‖(w' - (w + 1 / 2)) + 1 / 2‖ := by ring_nf
      _ ≤ ‖w' - (w + 1 / 2)‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 5 / 4 := by norm_num; linarith
  set u' := w' / w - 1
  have un' : ‖u'‖ ≤ 5 / 16 := by
    have : u' = (w' - w) / w := by simp only [u']; field_simp
    rw [this, norm_div, div_le_iff₀ (by linarith)]; nlinarith
  have hs : s * (w' / w) = s * (1 + u') := by simp only [u']; ring
  have rneg : petalRoot 2 (-c) s = -z := by simp only [petalRoot, z]; ring
  have s0 : s ≠ 0 := fun e ↦ by simp [e] at sr
  have w'0 : w' ≠ 0 := by rw [hw']; exact mul_ne_zero w0 (inv_ne_zero (pow_ne_zero _ u1))
  have s'0 : s * (w' / w) ≠ 0 := mul_ne_zero s0 (div_ne_zero w'0 w0)
  have br := PetalGerm.branch (k := 2) (c := -c) (s := s) (s' := s * (w' / w)) (u := u z) (u' := u')
    (by norm_num) (neg_ne_zero.mpr c0) sr hs un' (by push_cast; linarith) ?_
  · rw [fz, ← br, rneg]
  · -- both sides square to `-1 / (2 a w')`
    rw [PetalGerm.root_pow s'0 (by norm_num), rneg]
    have zs2 : z ^ 2 = c ^ 2 / s := PetalGerm.root_pow s0 (by norm_num)
    have z2w : z ^ 2 * w = -1 / (2 * a) := by rw [hw]; field_simp
    have fw' : (-z * (1 + u z)) ^ 2 = -1 / (2 * a * w') := by
      rw [← fz]; simp only [w', petalCoord]; push_cast; field_simp
    rw [fw', neg_sq]
    have c2 : c ^ 2 = z ^ 2 * s := by rw [zs2]; field_simp
    rw [c2, show z ^ 2 * s / (s * (w' / w)) = z ^ 2 * w / w' by field_simp, z2w]
    field_simp

/-- Uniqueness of Fatou coordinates under a semiconjugacy: if `F` maps the half-plane `re > R'` into `re > R`,
intertwines `G₁` with `G₂` there, and `F v = v + t + o(1)`, then `Φ₂ ∘ F = Φ₁ + t`.  The difference is invariant along
`G₁`-orbits and vanishes far out. -/
public lemma NearTranslation.fatou_conj {G₁ G₂ F : ℂ → ℂ} {β t : ℂ} {R A δ R₂ A₂ δ₂ R' : ℝ}
    (h₁ : NearTranslation G₁ β R A δ) (h₂ : NearTranslation G₂ β R₂ A₂ δ₂) (RR : R ≤ R')
    (Fm : ∀ v ∈ rightHalf R', F v ∈ rightHalf R₂) (Fc : ∀ v ∈ rightHalf R', F (G₁ v) = G₂ (F v))
    (Ft : ∀ η > 0, ∃ X, ∀ v ∈ rightHalf R', X ≤ v.re → ‖F v - (v + t)‖ < η) :
    ∀ v ∈ rightHalf R', NearTranslation.fatou G₂ β (F v) = NearTranslation.fatou G₁ β v + t := by
  intro v vm
  have h₁' := h₁.mono RR
  set D := fun w ↦ NearTranslation.fatou G₂ β (F w) - NearTranslation.fatou G₁ β w - t
  have sub : ∀ {w}, w ∈ rightHalf R' → w ∈ rightHalf R := fun {w} m ↦ by
    simp only [rightHalf, mem_ofPred_eq] at m ⊢; linarith
  -- invariance
  have inv : ∀ w ∈ rightHalf R', D (G₁ w) = D w := fun w m ↦ by
    simp only [D]
    rw [Fc w m, h₂.fatou_eqn (Fm w m), h₁.fatou_eqn (sub m)]; ring
  have invn : ∀ n : ℕ, D (G₁^[n] v) = D v := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', inv _ ((h₁'.mapsTo.iterate n) vm), ih]
  -- `D` is small far out
  suffices small : ∀ ε > 0, ‖D v‖ < ε by
    have : ‖D v‖ = 0 := le_antisymm (le_of_forall_pos_lt_add fun ε ε0 ↦ by simpa using small ε ε0)
      (norm_nonneg _)
    have := norm_eq_zero.mp this
    simp only [D] at this
    linear_combination this
  intro ε ε0
  obtain ⟨M₁, hM₁⟩ := h₂.exists_norm_bound (by positivity : 0 < ε / 3)
  obtain ⟨M₂, hM₂⟩ := h₁.exists_norm_bound (by positivity : 0 < ε / 3)
  set η := min (1 / 2) (ε / 6)
  have η0 : 0 < η := by positivity
  obtain ⟨X, hX⟩ := Ft η η0
  set B := ‖β‖
  set Y := max (max X (M₁ + ‖t‖ + 1)) (max M₂ (max (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1)))
  -- an iterate far enough right
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Y ≤ (G₁^[n] v).re := by
    obtain ⟨n, hn⟩ := exists_nat_ge (2 * (Y - v.re))
    refine ⟨n, le_trans ?_ (h₁'.re_iter vm n)⟩
    linarith
  set w := G₁^[n] v
  have wm : w ∈ rightHalf R' := (h₁'.mapsTo.iterate n) vm
  have wn : Y ≤ ‖w‖ := le_trans hn (Complex.re_le_norm w)
  have Y1 := le_max_left (max X (M₁ + ‖t‖ + 1)) (max M₂ (max (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1)))
  have Y2 := le_max_right (max X (M₁ + ‖t‖ + 1)) (max M₂ (max (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1)))
  have X1 := le_max_left X (M₁ + ‖t‖ + 1)
  have X2 := le_max_right X (M₁ + ‖t‖ + 1)
  have Z1 := le_max_left M₂ (max (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1))
  have Z2 := le_max_right M₂ (max (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1))
  have Z3 := le_max_left (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1)
  have Z4 := le_max_right (2 * (‖t‖ + 1)) (9 * B * (‖t‖ + 1) / ε + 1)
  have Fw := hX w wm (by linarith)
  have η1 : η ≤ 1 / 2 := min_le_left _ _
  have η2 : η ≤ ε / 6 := min_le_right _ _
  -- the three pieces
  have dFw : ‖F w - w‖ ≤ ‖t‖ + 1 := by
    calc ‖F w - w‖ = ‖(F w - (w + t)) + t‖ := by ring_nf
      _ ≤ ‖F w - (w + t)‖ + ‖t‖ := norm_add_le _ _
      _ ≤ ‖t‖ + 1 := by linarith
  have nFw : M₁ ≤ ‖F w‖ := by
    have h1 : ‖w‖ ≤ ‖F w‖ + ‖F w - w‖ := by
      have := norm_add_le (F w) (w - F w); rw [add_sub_cancel] at this; rw [norm_sub_rev] at this
      linarith
    linarith
  have e1 := hM₁ (F w) (Fm w wm) nFw
  have e2 := hM₂ w (sub wm) (by linarith)
  set r := (F w - w) / w
  have w0 : w ≠ 0 := fun e ↦ by rw [e] at wn; simp at wn; linarith [norm_nonneg t]
  have nw0 : 0 < ‖w‖ := norm_pos_iff.mpr w0
  have rn : ‖r‖ ≤ (‖t‖ + 1) / ‖w‖ := by simp only [r]; rw [norm_div]; gcongr
  have rn2 : ‖r‖ ≤ 1 / 2 := le_trans rn (by rw [div_le_iff₀ nw0]; linarith)
  have hl : log (F w) = log w + log (1 + r) := by
    have e : F w = w * (1 + r) := by simp only [r]; field_simp; ring
    have wr : 0 < w.re := by have : R' < w.re := wm; linarith [h₁'.four_le]
    have rr : 0 < (1 + r).re := by
      have := Complex.abs_re_le_norm r; simp only [Complex.add_re, Complex.one_re]
      rw [abs_le] at this; linarith
    rw [e]
    refine (Complex.log_mul_eq_add_log_iff w0 (fun z ↦ by simp [z] at rr)).mpr ?_
    have a1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl wr)
    have a2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl rr)
    rw [abs_lt] at a1 a2
    constructor <;> linarith
  have lr : ‖log (1 + r)‖ ≤ 3 / 2 * ‖r‖ := Complex.norm_log_one_add_half_le_self rn2
  have e3 : ‖approxFatou β (F w) - approxFatou β w - t‖ < ε / 3 := by
    have e : approxFatou β (F w) - approxFatou β w - t = (F w - (w + t)) - β * log (1 + r) := by
      simp only [approxFatou, hl]; ring
    rw [e]
    have b1 : B * ‖r‖ ≤ B * (‖t‖ + 1) / ‖w‖ := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left rn (norm_nonneg _)
    have b2 : B * (‖t‖ + 1) / ‖w‖ ≤ ε / 9 := by
      rw [div_le_iff₀ nw0]
      have : 9 * B * (‖t‖ + 1) / ε ≤ ‖w‖ := by linarith
      rw [div_le_iff₀ ε0] at this; linarith
    calc ‖(F w - (w + t)) - β * log (1 + r)‖ ≤ ‖F w - (w + t)‖ + ‖β * log (1 + r)‖ := norm_sub_le _ _
      _ < η + B * (3 / 2 * ‖r‖) := by
          rw [norm_mul]; exact add_lt_add_of_lt_of_le Fw (mul_le_mul_of_nonneg_left lr (norm_nonneg _))
      _ ≤ ε / 3 := by nlinarith
  rw [← invn n]
  have e : D w = (NearTranslation.fatou G₂ β (F w) - approxFatou β (F w)) -
      (NearTranslation.fatou G₁ β w - approxFatou β w) + (approxFatou β (F w) - approxFatou β w - t) := by
    simp only [D]; ring
  rw [e]
  calc _ ≤ ‖NearTranslation.fatou G₂ β (F w) - approxFatou β (F w)‖ +
        ‖NearTranslation.fatou G₁ β w - approxFatou β w‖ + ‖approxFatou β (F w) - approxFatou β w - t‖ := by
        refine le_trans (norm_add_le _ _) ?_
        gcongr
        exact norm_sub_le _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- `f` commutes with `g = f ∘ f` near `0` -/
lemma flip_commute {g : ℂ → ℂ} (fa : AnalyticAt ℂ f 0) (f0 : f 0 = 0) (fg : ∀ᶠ z in 𝓝 0, g z = f (f z)) :
    ∃ ε > 0, ∀ z : ℂ, ‖z‖ < ε → f (g z) = g (f z) := by
  have t : Tendsto f (𝓝 0) (𝓝 0) := by have := fa.continuousAt.tendsto; rwa [f0] at this
  obtain ⟨ε, ε0, hε⟩ := Metric.eventually_nhds_iff.mp (fg.and (t.eventually fg))
  exact ⟨ε, ε0, fun z zε ↦ by
    obtain ⟨e1, e2⟩ := hε (show dist z 0 < ε by simpa using zε); rw [e1, e2]⟩

/-- `f` carries the attracting petal at `c` to the one at `-c`, and is a half step in their Fatou coordinates:
`Φ_{-c} (f z) = Φ_c z + 1/2` -/
public lemma PetalGerm.flip_attr {g : ℂ → ℂ} {a b : ℂ} (pg : PetalGerm g 2 a b) (fa : AnalyticAt ℂ f 0)
    (f0 : f 0 = 0) (fd : deriv f 0 = -1) (fg : ∀ᶠ z in 𝓝 0, g z = f (f z)) {c : ℂ}
    (hc : c ^ 2 = -1 / (2 * a)) :
    ∃ R₀ : ℝ, ∀ R₁ ≥ R₀,
      MapsTo f ((fun w ↦ petalRoot 2 c w) '' rightHalf R₁) ((fun w ↦ petalRoot 2 (-c) w) '' rightHalf R₁) ∧
      ∀ z ∈ (fun w ↦ petalRoot 2 c w) '' rightHalf R₁,
        NearTranslation.fatou (fun w ↦ petalCoord 2 a (g (petalRoot 2 (-c) w))) (petalResidue 2 a b)
          (petalCoord 2 a (f z)) =
        NearTranslation.fatou (fun w ↦ petalCoord 2 a (g (petalRoot 2 c w))) (petalResidue 2 a b)
          (petalCoord 2 a z) + 1 / 2 := by
  have a0 := pg.a0
  have hf := flip_odd fa f0 fd pg fg
  obtain ⟨C, ε, ε0, C0, hch⟩ := flip_chart a0 fa hf
  obtain ⟨ε₂, ε₂0, comm⟩ := flip_commute fa f0 fg
  have hc2 : c ^ 2 = -1 / ((2 : ℕ) * a) := by push_cast; exact hc
  have hc2' : (-c) ^ 2 = -1 / ((2 : ℕ) * a) := by rw [neg_sq]; exact hc2
  have c0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow two_ne_zero] at hc
    exact div_ne_zero (by norm_num) (mul_ne_zero two_ne_zero a0) hc.symm
  obtain ⟨Rp, Ap, ntp, semip⟩ := pg.attracting hc2
  obtain ⟨Rm, Am, ntm, semim⟩ := pg.attracting hc2'
  set ε' := min (min ε ε₂) (1 / (2 * C + 2))
  have ε'0 : 0 < ε' := by positivity
  refine ⟨max (max Rp Rm) (‖c‖ ^ 2 / ε' ^ 2), fun R₁ R₁0 ↦ ?_⟩
  have hRp : Rp ≤ R₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) R₁0
  have hRm : Rm ≤ R₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) R₁0
  have hRε : ‖c‖ ^ 2 / ε' ^ 2 ≤ R₁ := le_trans (le_max_right _ _) R₁0
  have R4 : 4 ≤ R₁ := le_trans ntp.four_le hRp
  set F := fun w ↦ petalCoord 2 a (f (petalRoot 2 c w))
  -- the chart facts on `re w > R₁`
  have facts : ∀ w ∈ rightHalf R₁, ‖petalRoot 2 c w‖ < ε' ∧ f (petalRoot 2 c w) = petalRoot 2 (-c) (F w) ∧
      ‖F w - (w + 1 / 2)‖ ≤ C * ‖petalRoot 2 c w‖ ∧ F w ∈ rightHalf R₁ := by
    intro w m
    have wr : R₁ < w.re := m
    have wn : R₁ < ‖w‖ := lt_of_lt_of_le wr (Complex.re_le_norm w)
    have w0 : w ≠ 0 := fun e ↦ by rw [e] at wr; simp at wr; linarith
    have zε : ‖petalRoot 2 c w‖ < ε' := norm_root_lt (by norm_num) ε'0 w0 (lt_of_le_of_lt hRε wn)
    have zε1 : ‖petalRoot 2 c w‖ < ε := lt_of_lt_of_le zε (le_trans (min_le_left _ _) (min_le_left _ _))
    obtain ⟨-, -, est, br⟩ := hch c w c0 (by linarith) zε1
    have cr := coord_root (k := 2) (by norm_num) a0 hc2 w0
    rw [cr, mul_div_cancel₀ _ w0] at br
    rw [cr] at est
    refine ⟨zε, br, est, ?_⟩
    have Cz : C * ‖petalRoot 2 c w‖ ≤ 1 / 2 := by
      have := lt_of_lt_of_le zε (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at this; nlinarith [norm_nonneg (petalRoot 2 c w)]
    have := le_trans (Complex.abs_re_le_norm _) est
    rw [abs_le] at this
    simp only [Complex.sub_re, Complex.add_re] at this
    show R₁ < (F w).re
    norm_num at this
    linarith
  refine ⟨?_, ?_⟩
  · rintro _ ⟨w, m, rfl⟩
    exact ⟨F w, (facts w m).2.2.2, (facts w m).2.1.symm⟩
  · rintro _ ⟨w, m, rfl⟩
    have w0 : w ≠ 0 := fun e ↦ by have : R₁ < w.re := m; rw [e] at this; simp at this; linarith
    rw [coord_root (k := 2) (by norm_num) a0 hc2 w0]
    show NearTranslation.fatou _ _ (F w) = _
    refine ntp.fatou_conj (F := F) (t := 1 / 2) ntm hRp (fun v vm ↦ ?_) (fun v vm ↦ ?_) (fun η η0 ↦ ?_) w m
    · have := (facts v vm).2.2.2
      simp only [rightHalf, mem_ofPred_eq] at this ⊢; linarith
    · -- `F ∘ G_c = G_{-c} ∘ F`
      obtain ⟨zε, br, -, Fm⟩ := facts v vm
      have zε2 : ‖petalRoot 2 c v‖ < ε₂ := lt_of_lt_of_le zε (le_trans (min_le_left _ _) (min_le_right _ _))
      have F0 : F v ≠ 0 := fun e ↦ by
        have : R₁ < (F v).re := Fm; rw [e] at this; simp at this; linarith
      have cr := coord_root (k := 2) (by norm_num) a0 hc2' F0
      simp only [F]
      rw [← semip v (lt_of_le_of_lt hRp vm), comm _ zε2, br]
      simp only [F] at cr
      rw [cr]
    · refine ⟨‖c‖ ^ 2 / (η / (C + 1)) ^ 2 + R₁ + 1, fun v vm Xv ↦ ?_⟩
      obtain ⟨-, -, est, -⟩ := facts v vm
      have vr : R₁ < v.re := vm
      have v0 : v ≠ 0 := fun e ↦ by rw [e] at vr; simp at vr; linarith
      have zη : ‖petalRoot 2 c v‖ < η / (C + 1) := norm_root_lt (by norm_num) (by positivity) v0
        (by have := Complex.re_le_norm v; have : 0 ≤ ‖c‖ ^ 2 / (η / (C + 1)) ^ 2 := by positivity
            linarith)
      calc ‖F v - (v + 1 / 2)‖ ≤ C * ‖petalRoot 2 c v‖ := est
        _ ≤ C * (η / (C + 1)) := by gcongr
        _ < η := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

/-!
### Multiplier `-1`: the global statement
-/

lemma exp_half_neg : exp (-(π * I) / (2 : ℕ)) = -exp (π * I / (2 : ℕ)) := by
  have e : exp (π * I / (2 : ℕ)) = I := by
    rw [show π * I / ((2 : ℕ) : ℂ) = (π / 2 : ℝ) * I by push_cast; ring, Complex.exp_mul_I]
    simp
  have e' : exp (-(π * I) / (2 : ℕ)) = -I := by
    rw [show -(π * I) / ((2 : ℕ) : ℂ) = (-(π / 2) : ℝ) * I by push_cast; ring, Complex.exp_mul_I]
    simp
  rw [e, e']

lemma iterate_commute {f g : ℂ → ℂ} (c : ∀ z, f (g z) = g (f z)) (n : ℕ) (z : ℂ) :
    g^[n] (f z) = f (g^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', c]

/-- Parabolic points of multiplier `-1`.  Let `f` be entire with `f 0 = 0`, `f' 0 = -1` and
`f (f z) = z + a z³ + O(z⁴)`, `a ≠ 0`, and let `c` be a repelling direction of `g = f ∘ f` (`c² = 1 / (2a)`), with
repelling parametrisation `Ψ`.  The two adjacent attracting petals `Pu`, `Pl` (directions `± i c`) have Fatou
coordinates `Φu`, `Φl`; the horn maps `Hu = Φu ∘ Ψ`, `Hl = Φl ∘ Ψ` live on an upper and a lower half-plane, with
`Hu ζ = ζ - π i β + o(1)` and `Hl ζ = ζ + π i β + o(1)` (as in `horn_ends`).  In addition `f` swaps the two attracting
basins with a half step, `Φl (f z) = Φu z + 1/2` and `Φu (f z) = Φl z + 1/2`; so `f ∘ Ψ` (a parametrisation of the
opposite repelling petal) has horn maps `Hu + 1/2` and `Hl + 1/2` into the swapped petals. -/
public theorem parabolic_flip (fa : ∀ z, AnalyticAt ℂ f z) (f0 : f 0 = 0) (fd : deriv f 0 = -1) {a : ℂ}
    (a0 : a ≠ 0) (approx : (fun z ↦ f (f z) - (z + a * z ^ 3)) =O[𝓝 0] fun z ↦ z ^ 4) {c : ℂ}
    (hc : c ^ 2 = 1 / (2 * a)) :
    ∃ Pu : Set ℂ, ∃ Φu : ℂ → ℂ, ∃ Pl : Set ℂ, ∃ Φl : ℂ → ℂ, ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, ∃ b : ℂ,
      let g := fun z ↦ f (f z)
      (∃ h φ : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 0 ∧ deriv h 0 = 1 ∧ PetalGerm (φ ∘ g ∘ h) 2 a b ∧
        ∀ᶠ z in 𝓝 0, h ((φ ∘ g ∘ h) z) = g (h z)) ∧
      (∃ ε > 0, ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε →
        ‖z / (c * exp (π * I / (2 : ℕ)) * (‖z‖ / ‖c * exp (π * I / (2 : ℕ))‖ : ℝ)) - 1‖ ≤ 1 / 16 → z ∈ Pu) ∧
      Disjoint (basin g Pu) (basin g Pl) ∧
      (IsOpen Pu ∧ Pu.Nonempty ∧ MapsTo g Pu Pu ∧ AnalyticOnNhd ℂ Φu Pu ∧ ∀ z ∈ Pu, Φu (g z) = Φu z + 1) ∧
      (IsOpen Pl ∧ Pl.Nonempty ∧ MapsTo g Pl Pl ∧ AnalyticOnNhd ℂ Φl Pl ∧ ∀ z ∈ Pl, Φl (g z) = Φl z + 1) ∧
      (IsOpen V ∧ (∀ ζ ∈ V, ζ - 1 ∈ V) ∧ (∀ ζ : ℂ, ∃ n : ℕ, ζ - n ∈ V) ∧ AnalyticOnNhd ℂ Ψ V ∧
        ∀ ζ ∈ V, g (Ψ (ζ - 1)) = Ψ ζ) ∧
      (∃ T : ℝ, ∀ ζ : ℂ, T < ζ.im → ζ ∈ hornDomain g Ψ Pu V) ∧
      Tendsto (fun ζ ↦ hornMap g Φu Ψ Pu V ζ - ζ) (comap Complex.im atTop)
        (𝓝 (-(π * I * petalResidue 2 a b))) ∧
      (∃ T : ℝ, ∀ ζ : ℂ, ζ.im < T → ζ ∈ hornDomain g Ψ Pl V) ∧
      Tendsto (fun ζ ↦ hornMap g Φl Ψ Pl V ζ - ζ) (comap Complex.im atBot)
        (𝓝 (π * I * petalResidue 2 a b)) ∧
      (fun ζ ↦ hornMap g Φu Ψ Pu V ζ - ζ + π * I * petalResidue 2 a b) =O[comap Complex.im atTop]
        (fun ζ ↦ Real.exp (-2 * π * ζ.im)) ∧
      (fun ζ ↦ hornMap g Φl Ψ Pl V ζ - ζ - π * I * petalResidue 2 a b) =O[comap Complex.im atBot]
        (fun ζ ↦ Real.exp (2 * π * ζ.im)) ∧
      (∀ ζ ∈ hornDomain g Ψ Pu V, deriv (hornMap g Φu Ψ Pu V) ζ = 0 → ∃ c₀ : ℂ, deriv g c₀ = 0 ∧
        g c₀ ∈ basin g Pu ∧ ∃ j : ℤ, hornMap g Φu Ψ Pu V ζ = basinExt g Φu Pu (g c₀) + j) ∧
      (∀ ζ ∈ hornDomain g Ψ Pl V, deriv (hornMap g Φl Ψ Pl V) ζ = 0 → ∃ c₀ : ℂ, deriv g c₀ = 0 ∧
        g c₀ ∈ basin g Pl ∧ ∃ j : ℤ, hornMap g Φl Ψ Pl V ζ = basinExt g Φl Pl (g c₀) + j) ∧
      (MapsTo f (basin g Pu) (basin g Pl) ∧ ∀ z ∈ basin g Pu, basinExt g Φl Pl (f z) = basinExt g Φu Pu z + 1 / 2) ∧
      (MapsTo f (basin g Pl) (basin g Pu) ∧ ∀ z ∈ basin g Pl, basinExt g Φu Pu (f z) = basinExt g Φl Pl z + 1 / 2) ∧
      (∀ ζ ∈ hornDomain g Ψ Pu V, f (paramExt g Ψ V ζ) ∈ basin g Pl ∧
        basinExt g Φl Pl (f (paramExt g Ψ V ζ)) = hornMap g Φu Ψ Pu V ζ + 1 / 2) ∧
      ∀ ζ ∈ hornDomain g Ψ Pl V, f (paramExt g Ψ V ζ) ∈ basin g Pu ∧
        basinExt g Φu Pu (f (paramExt g Ψ V ζ)) = hornMap g Φl Ψ Pl V ζ + 1 / 2 := by
  set g := fun z ↦ f (f z) with hg
  have ga : ∀ z, AnalyticAt ℂ g z := fun z ↦ (fa (f z)).comp (fa z)
  have g0 : g 0 = 0 := by simp [g, f0]
  have gapprox : (fun z ↦ g z - (z + a * z ^ (2 + 1))) =O[𝓝 0] fun z ↦ z ^ (2 + 2) := by
    have e : (fun z ↦ g z - (z + a * z ^ (2 + 1))) = fun z ↦ f (f z) - (z + a * z ^ 3) := by
      funext z; norm_num [g]
    rw [e]; simpa using approx
  have hc2 : c ^ 2 = 1 / (((2 : ℕ) : ℂ) * a) := by push_cast; exact hc
  obtain ⟨h, φ, b, ha, φa, h0, φ0, l, r, dh, pg⟩ := PetalGerm.normalize (k := 2) (by norm_num) a0 (ga 0) g0 gapprox
  -- `f` in the normalising coordinate
  set f' := φ ∘ f ∘ h
  have fh0 : f (h 0) = 0 := by rw [h0, f0]
  have φd : DifferentiableAt ℂ φ (h 0) := by rw [h0]; exact φa.differentiableAt
  have dφ : deriv φ 0 = 1 := by
    have l' : (φ ∘ h) =ᶠ[𝓝 0] id := l
    have e := l'.deriv_eq
    rw [deriv_comp _ φd ha.differentiableAt, h0, dh] at e
    simpa using e
  have fha : AnalyticAt ℂ (f ∘ h) 0 := (fa (h 0)).comp ha
  have φd' : AnalyticAt ℂ φ ((f ∘ h) 0) := by rw [Function.comp_apply, fh0]; exact φa
  have f'a : AnalyticAt ℂ f' 0 := AnalyticAt.comp (g := φ) (f := f ∘ h) φd' fha
  have f'0 : f' 0 = 0 := by simp [f', h0, f0, φ0]
  have f'd : deriv f' 0 = -1 := by
    have d1 : deriv (f ∘ h) 0 = -1 := by
      rw [deriv_comp _ (fa _).differentiableAt ha.differentiableAt, h0, fd, dh]; ring
    have e : deriv (φ ∘ (f ∘ h)) 0 = deriv φ ((f ∘ h) 0) * deriv (f ∘ h) 0 :=
      deriv_comp _ φd'.differentiableAt fha.differentiableAt
    rw [Function.comp_apply, fh0, dφ, d1] at e
    rw [show f' = φ ∘ (f ∘ h) from rfl, e]; ring
  have tfh : Tendsto (fun z ↦ f (h z)) (𝓝 0) (𝓝 0) := by
    have := ((fa (h 0)).continuousAt.comp ha.continuousAt).tendsto; rwa [Function.comp_apply, fh0] at this
  have fg' : ∀ᶠ z in 𝓝 0, (φ ∘ g ∘ h) z = f' (f' z) := by
    filter_upwards [tfh.eventually r] with z e
    simp only [Function.comp_apply, f', g, e]
  -- the conjugacy, for `g` and for `f`
  obtain ⟨δ, δ0, inj, hδ⟩ := conj_setup (ga 0) g0 ha φa h0 l r one_pos
  obtain ⟨δ', δ'0, -, hδ'⟩ := conj_setup (fa 0) f0 ha φa h0 l r one_pos
  set δ₀ := min δ δ'
  have δ₀0 : 0 < δ₀ := lt_min δ0 δ'0
  have bδ : ∀ {z : ℂ}, z ∈ Metric.ball (0 : ℂ) δ₀ → z ∈ Metric.ball (0 : ℂ) δ := fun m ↦
    Metric.ball_subset_ball (min_le_left _ _) m
  have bδ' : ∀ {z : ℂ}, z ∈ Metric.ball (0 : ℂ) δ₀ → z ∈ Metric.ball (0 : ℂ) δ' := fun m ↦
    Metric.ball_subset_ball (min_le_right _ _) m
  -- the two attracting directions and the half step between them
  set cu := c * exp (π * I / ((2 : ℕ) : ℂ))
  have hcl : c * exp (-(π * I) / ((2 : ℕ) : ℂ)) = -cu := by rw [exp_half_neg]; ring
  have hcu2 : cu ^ 2 = -1 / (2 * a) := by
    have e : exp (π * I / ((2 : ℕ) : ℂ)) ^ 2 = -1 := by
      rw [← Complex.exp_nat_mul]; push_cast
      rw [show (2 : ℂ) * (π * I / 2) = π * I by ring, Complex.exp_pi_mul_I]
    simp only [cu, mul_pow, e, hc]; ring
  obtain ⟨R0u, hR0u⟩ := pg.flip_attr f'a f'0 f'd fg' hcu2
  obtain ⟨R0l, hR0l⟩ := pg.flip_attr f'a f'0 f'd fg' (c := -cu) (by rw [neg_sq]; exact hcu2)
  obtain ⟨Pu', Φu', Pl', Φl', V, Ψ', ⟨R₁, R₁ge, ePu, eΦu, ePl, eΦl⟩, ⟨Pou, Pneu, Pbu, PMu, Φau, Φeu, Φdu⟩,
    ⟨Pol, Pnel, Pbl, PMl, Φal, Φel, Φdl⟩, ⟨Vo, Vl, reach, Ψa, Ψb, Ψe, Ψd⟩, endu, endl⟩ :=
    pg.local_horn_both hc2 δ₀0 (max (max R0u R0l) 0)
  rw [hcl] at ePl eΦl
  obtain ⟨muf, fu⟩ := hR0u R₁ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) R₁ge)
  obtain ⟨mlf, fl⟩ := hR0l R₁ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) R₁ge)
  have R₁0 : 0 ≤ R₁ := le_trans (le_max_right _ _) R₁ge
  rw [neg_neg] at mlf fl
  rw [← ePu, ← ePl] at muf mlf
  -- transport through the conjugacy
  have hδ'' : ∀ z ∈ Metric.ball (0 : ℂ) δ₀, φ (h z) = z ∧ AnalyticAt ℂ h z ∧ AnalyticAt ℂ φ (h z) ∧
      g (h z) = h (φ (g (h z))) := fun z m ↦
    ⟨(hδ z (bδ m)).1, (hδ z (bδ m)).2.1, (hδ z (bδ m)).2.2.1, (hδ z (bδ m)).2.2.2.1⟩
  have inj' : InjOn h (Metric.ball 0 δ₀) := inj.mono fun z m ↦ bδ m
  obtain ⟨Pou', gPu, Φau', Φeu'⟩ := transport_attr δ₀0 inj' hδ'' Pou Pbu PMu Φau Φeu
  obtain ⟨Pol', gPl, Φal', Φel'⟩ := transport_attr δ₀0 inj' hδ'' Pol Pbl PMl Φal Φel
  obtain ⟨Ψa', Ψe'⟩ := transport_rep (fun z m ↦ ⟨(hδ'' z m).2.1, (hδ'' z m).2.2.2⟩) Vl Ψa Ψb Ψe
  obtain ⟨Dou, Dpu, Hau, Heu⟩ := horn_map ga Pou' gPu Φau' Φeu' Vo Vl reach Ψa' Ψe'
  obtain ⟨Dol, Dpl, Hal, Hel⟩ := horn_map ga Pol' gPl Φal' Φel' Vo Vl reach Ψa' Ψe'
  -- the half step in the `z`-plane: `f (h z) = h (f' z)`
  have fhz : ∀ z ∈ Metric.ball (0 : ℂ) δ₀, f (h z) = h (f' z) := fun z m ↦ (hδ' z (bδ' m)).2.2.2.1
  have half : ∀ {P₁ P₂ : Set ℂ} {Φ₁ Φ₂ : ℂ → ℂ}, P₁ ⊆ Metric.ball 0 δ₀ → P₂ ⊆ Metric.ball 0 δ₀ →
      MapsTo f' P₁ P₂ → (∀ z ∈ P₁, Φ₂ (f' z) = Φ₁ z + 1 / 2) →
      MapsTo f (h '' P₁) (h '' P₂) ∧ ∀ y ∈ h '' P₁, (Φ₂ ∘ φ) (f y) = (Φ₁ ∘ φ) y + 1 / 2 := by
    intro P₁ P₂ Φ₁ Φ₂ b1 b2 m e
    refine ⟨?_, ?_⟩
    · rintro _ ⟨z, zm, rfl⟩
      exact ⟨f' z, m zm, (fhz z (b1 zm)).symm⟩
    · rintro _ ⟨z, zm, rfl⟩
      simp only [Function.comp_apply]
      rw [fhz z (b1 zm), (hδ'' _ (b2 (m zm))).1, (hδ'' _ (b1 zm)).1]
      exact e z zm
  obtain ⟨mu, eu⟩ := half (Φ₁ := Φu') (Φ₂ := Φl') Pbu Pbl muf (by rw [eΦu, eΦl, ePu]; exact fu)
  obtain ⟨ml, el⟩ := half (Φ₁ := Φl') (Φ₂ := Φu') Pbl Pbu mlf (by rw [eΦu, eΦl, ePl]; exact fl)
  -- basins
  have comm : ∀ z, f (g z) = g (f z) := fun z ↦ rfl
  have basin_half : ∀ {P₁ P₂ : Set ℂ} {Φ₁ Φ₂ : ℂ → ℂ}, MapsTo g P₁ P₁ → MapsTo g P₂ P₂ →
      (∀ z ∈ P₁, Φ₁ (g z) = Φ₁ z + 1) → (∀ z ∈ P₂, Φ₂ (g z) = Φ₂ z + 1) →
      MapsTo f P₁ P₂ → (∀ y ∈ P₁, Φ₂ (f y) = Φ₁ y + 1 / 2) →
      MapsTo f (basin g P₁) (basin g P₂) ∧
        ∀ z ∈ basin g P₁, basinExt g Φ₂ P₂ (f z) = basinExt g Φ₁ P₁ z + 1 / 2 := by
    intro P₁ P₂ Φ₁ Φ₂ g1 g2 e1 e2 m e
    have it := iterate_commute comm
    refine ⟨fun z ⟨n, zn⟩ ↦ ⟨n, by rw [it]; exact m zn⟩, fun z ⟨n, zn⟩ ↦ ?_⟩
    have fz : g^[n] (f z) ∈ P₂ := by rw [it]; exact m zn
    rw [basinExt_eq_of g2 e2 fz, basinExt_eq_of g1 e1 zn, it, e _ zn]
    ring
  obtain ⟨mbu, ebu⟩ := basin_half gPu gPl Φeu' Φel' mu eu
  obtain ⟨mbl, ebl⟩ := basin_half gPl gPu Φel' Φeu' ml el
  have hδ3 : ∀ z ∈ Metric.ball (0 : ℂ) δ₀, φ (h z) = z ∧ AnalyticAt ℂ h z ∧ AnalyticAt ℂ φ (h z) ∧
      g (h z) = h (φ (g (h z))) := hδ''
  have hδ4 : ∀ z ∈ Metric.ball (0 : ℂ) δ₀, φ (h z) = z ∧ AnalyticAt ℂ h z ∧ AnalyticAt ℂ φ (h z) :=
    fun z m ↦ ⟨(hδ'' z m).1, (hδ'' z m).2.1, (hδ'' z m).2.2.1⟩
  obtain ⟨Φdu', Ψd'⟩ := transport_deriv hδ4 Pbu Φau Φdu Ψb Ψa Ψd
  obtain ⟨Φdl', -⟩ := transport_deriv hδ4 Pbl Φal Φdl Ψb Ψa Ψd
  have domu : ∃ T : ℝ, ∀ ζ : ℂ, T < ζ.im → ζ ∈ hornDomain g (h ∘ Ψ') (h '' Pu') V := by
    obtain ⟨T, hT⟩ := endu 1 one_pos
    refine ⟨T, fun ζ hζ ↦ ?_⟩
    obtain ⟨m, N, mV, small, land', -⟩ := hT ζ hζ
    exact (horn_shift Dpu Heu ζ m (horn_land hδ3 gPu Φeu' Vl Ψe' mV small land').1).1
  have limu : Tendsto (fun ζ ↦ hornMap g (Φu' ∘ φ) (h ∘ Ψ') (h '' Pu') V ζ - ζ) (comap Complex.im atTop)
      (𝓝 (-(π * I * petalResidue 2 a b))) := by
    rw [Metric.tendsto_nhds]
    intro ε ε0
    obtain ⟨T, hT⟩ := endu ε ε0
    rw [Filter.eventually_comap]
    filter_upwards [eventually_gt_atTop T] with y hy ζ hζ
    obtain ⟨m, N, mV, small, land', est⟩ := hT ζ (by rw [hζ]; exact hy)
    obtain ⟨dm, e⟩ := horn_land hδ3 gPu Φeu' Vl Ψe' mV small land'
    rw [dist_eq_norm, (horn_shift Dpu Heu ζ m dm).2, e]
    simpa [sub_neg_eq_add] using est
  have doml : ∃ T : ℝ, ∀ ζ : ℂ, ζ.im < T → ζ ∈ hornDomain g (h ∘ Ψ') (h '' Pl') V := by
    obtain ⟨T, hT⟩ := endl 1 one_pos
    refine ⟨-T, fun ζ hζ ↦ ?_⟩
    obtain ⟨m, N, mV, small, land', -⟩ := hT ζ (by linarith)
    exact (horn_shift Dpl Hel ζ m (horn_land hδ3 gPl Φel' Vl Ψe' mV small land').1).1
  have liml : Tendsto (fun ζ ↦ hornMap g (Φl' ∘ φ) (h ∘ Ψ') (h '' Pl') V ζ - ζ) (comap Complex.im atBot)
      (𝓝 (π * I * petalResidue 2 a b)) := by
    rw [Metric.tendsto_nhds]
    intro ε ε0
    obtain ⟨T, hT⟩ := endl ε ε0
    rw [Filter.eventually_comap]
    filter_upwards [eventually_lt_atBot (-T)] with y hy ζ hζ
    obtain ⟨m, N, mV, small, land', est⟩ := hT ζ (by rw [hζ]; linarith)
    obtain ⟨dm, e⟩ := horn_land hδ3 gPl Φel' Vl Ψe' mV small land'
    rw [dist_eq_norm, (horn_shift Dpl Hel ζ m dm).2, e]
    simpa [← sub_eq_add_neg] using est
  have tgh : Tendsto (fun z ↦ g (h z)) (𝓝 0) (𝓝 0) := by
    have := ((ga (h 0)).continuousAt.comp ha.continuousAt).tendsto
    rwa [Function.comp_apply, h0, g0] at this
  have conjg : ∀ᶠ z in 𝓝 0, h ((φ ∘ g ∘ h) z) = g (h z) := by
    filter_upwards [tgh.eventually r] with z e; exact e
  -- sector containment in the `g`-plane, through `φ z = z (1 + O(z))`
  have cu0 : cu ≠ 0 := by
    intro e; rw [e] at hcu2; rw [zero_pow two_ne_zero] at hcu2
    exact div_ne_zero (by norm_num) (mul_ne_zero two_ne_zero a0) hcu2.symm
  have hcu2' : cu ^ 2 = -1 / (((2 : ℕ) : ℂ) * a) := by push_cast; exact hcu2
  obtain ⟨εs, εs0, sect⟩ := petal_sector (k := 2) cu (by norm_num) R₁
  obtain ⟨Cφ, rφ, Cφ0, rφ0, tay⟩ := taylor2 φa
  have dφ' : deriv φ 0 = 1 := dφ
  have rr : ∀ᶠ z in 𝓝 (0 : ℂ), h (φ z) = z := r
  obtain ⟨εr, εr0, hεr⟩ := Metric.eventually_nhds_iff.mp rr
  set ε := min (min εs εr) (min rφ (1 / (16 * (Cφ + 1))))
  have ε0 : 0 < ε := by positivity
  have sectorPu : ∃ ε > 0, ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε →
      ‖z / (cu * (‖z‖ / ‖cu‖ : ℝ)) - 1‖ ≤ 1 / 16 → z ∈ h '' Pu' := by
    have ncu : 0 < ‖cu‖ := norm_pos_iff.mpr cu0
    refine ⟨ε / (‖cu‖ + 2) * ‖cu‖, by positivity, fun z z0 zε zs ↦ ?_⟩
    have nz : 0 < ‖z‖ := norm_pos_iff.mpr z0
    have zε' : ‖z‖ < ε := lt_of_lt_of_le zε (by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [ε0])
    have m1 : ε ≤ εs := le_trans (min_le_left _ _) (min_le_left _ _)
    have m2 : ε ≤ εr := le_trans (min_le_left _ _) (min_le_right _ _)
    have m3 : ε ≤ rφ := le_trans (min_le_right _ _) (min_le_left _ _)
    have m4 : ε ≤ 1 / (16 * (Cφ + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    set r := ‖z‖ / ‖cu‖
    have r0 : 0 < r := by positivity
    have rε : r < εs := by
      simp only [r]; rw [div_lt_iff₀ ncu]
      have : ε / (‖cu‖ + 2) * ‖cu‖ ≤ εs * ‖cu‖ := by
        gcongr; exact le_trans (div_le_self ε0.le (by linarith)) m1
      linarith
    have cr0 : cu * (r : ℂ) ≠ 0 := mul_ne_zero cu0 (by exact_mod_cast r0.ne')
    have ncr : ‖cu * (r : ℂ)‖ = ‖z‖ := by
      simp only [r, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos r0]; field_simp
    -- `‖φ z - z‖ ≤ C ‖z‖²`
    have tz := tay z 0 (lt_of_lt_of_le zε' m3) (by simpa using rφ0)
    simp only [φ0, dφ', sub_zero, one_mul] at tz
    set e := φ z / (cu * r) - 1
    have he : φ z = cu * r * (1 + e) := by
      rw [show 1 + e = φ z / (cu * r) by simp only [e]; ring, mul_div_cancel₀ _ cr0]
    have en : ‖e‖ ≤ 1 / (4 * ((2 : ℕ) : ℝ)) := by
      have : e = (z / (cu * r) - 1) + (φ z - z) / (cu * r) := by simp only [e]; field_simp; ring
      rw [this]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_div, ncr]
      have : ‖φ z - z‖ / ‖z‖ ≤ 1 / 16 := by
        rw [div_le_iff₀ nz]
        have : Cφ * ‖z‖ ≤ 1 / 16 := by
          have := lt_of_lt_of_le zε' m4
          rw [lt_div_iff₀ (by positivity)] at this; nlinarith
        nlinarith
      push_cast; linarith
    have mem := sect r e r0 rε en
    rw [← he, ← ePu] at mem
    exact ⟨φ z, mem, hεr (by simpa using lt_of_lt_of_le zε' m2)⟩
  have disj : Disjoint (h '' Pu') (h '' Pl') := by
    rw [ePu, ePl]
    have pd := petal_disjoint (k := 2) (a := a) (by norm_num) a0 hcu2' (by rw [neg_sq]; exact hcu2')
      (show cu ≠ -cu from fun e ↦ cu0 (by linear_combination e / 2)) R₁0 R₁0
    rw [Set.disjoint_left] at pd ⊢
    rintro _ ⟨z, zm, rfl⟩ ⟨z', zm', e⟩
    have zb : z ∈ Metric.ball (0 : ℂ) δ₀ := by rw [← ePu] at zm; exact Pbu zm
    have zb' : z' ∈ Metric.ball (0 : ℂ) δ₀ := by rw [← ePl] at zm'; exact Pbl zm'
    rw [inj' zb' zb e] at zm'
    exact pd zm zm'
  have disjB : Disjoint (basin g (h '' Pu')) (basin g (h '' Pl')) := by
    rw [Set.disjoint_left]
    rintro z ⟨n, zn⟩ ⟨m, zm⟩
    have a1 : g^[n + m] z ∈ h '' Pu' := by
      rw [add_comm, Function.iterate_add_apply]; exact (gPu.iterate m) zn
    have a2 : g^[n + m] z ∈ h '' Pl' := by
      rw [Function.iterate_add_apply]; exact (gPl.iterate n) zm
    exact Set.disjoint_left.mp disj a1 a2
  exact ⟨h '' Pu', Φu' ∘ φ, h '' Pl', Φl' ∘ φ, V, h ∘ Ψ', b, ⟨h, φ, ha, h0, dh, pg, conjg⟩, sectorPu, disjB,
    ⟨Pou', Pneu.image _, gPu, Φau', Φeu'⟩,
    ⟨Pol', Pnel.image _, gPl, Φal', Φel'⟩, ⟨Vo, Vl, reach, Ψa', Ψe'⟩, domu, limu, doml, liml,
    (horn_exp_decay Dou Dpu Hau Heu domu limu).congr_left (fun ζ ↦ by ring),
    (horn_exp_decay_lower Dol Dpl Hal Hel doml liml).congr_left (fun ζ ↦ by ring),
    fun ζ m crit ↦ horn_crit_values ga Pou' gPu Φau' Φeu' Vo Vl reach Ψa' Ψe' Φdu' Ψd' m crit,
    fun ζ m crit ↦ horn_crit_values ga Pol' gPl Φal' Φel' Vo Vl reach Ψa' Ψe' Φdl' Ψd' m crit, ⟨mbu, ebu⟩, ⟨mbl, ebl⟩,
    fun ζ m ↦ ⟨mbu m, ebu _ m⟩, fun ζ m ↦ ⟨mbl m, ebl _ m⟩⟩

/-!
### The iterative residue for `k = 2`
-/

/-- The quintic truncation `x + h₂ x² + h₃ x³ + h₄ x⁴ + h₅ x⁵` -/
noncomputable def quint (h₂ h₃ h₄ h₅ x : ℂ) : ℂ := x + h₂ * x ^ 2 + h₃ * x ^ 3 + h₄ * x ^ 4 + h₅ * x ^ 5

/-- `x + a x³ + d x⁴` -/
@[expose] public noncomputable def quart₃ (a d x : ℂ) : ℂ := x + a * x ^ 3 + d * x ^ 4

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The degree `≥ 6` part of `res_poly` -/
noncomputable def resS (a b d h₂ h₃ h₄ h₅ z : ℂ) : ℂ :=
      a*h₄ + a^2*h₂ - a*h₂^3 - 6*d*h₂^2 - 4*d*h₃ + 2*b*h₂ + b^2*h₂*z^4 + a^3*h₃*z^3 + b^3*h₃*z^9
      + a^4*h₄*z^6 + b^4*h₄*z^14 + a^5*h₅*z^9 + b^5*h₅*z^19 - a*h₃^3*z^3 - a*h₄^3*z^6 - a*h₅^3*z^9
      - d*h₂^4*z^2 - d*h₃^4*z^6 - d*h₄^4*z^10 - d*h₅^4*z^14 - 6*a*h₂*h₃ - 6*d*h₃^2*z^2 - 6*d*h₄^2*z^4
      - 6*d*h₅^2*z^6 - 4*d*h₄*z - 4*d*h₅*z^2 - 4*d*h₂^3*z - 4*d*h₃^3*z^4 - 4*d*h₄^3*z^7 - 4*d*h₅^3*z^10
      - 3*a*h₃^2*z - 3*a*h₄^2*z^3 - 3*a*h₅^2*z^5 + 2*a*h₅*z + 3*b*h₃*z + 3*a^2*h₃*z + 3*b^2*h₃*z^5
      + 4*b*h₄*z^2 + 4*a^3*h₄*z^4 + 4*b^3*h₄*z^10 + 5*b*h₅*z^3 + 5*a^4*h₅*z^7 + 5*b^4*h₅*z^15 + 6*a^2*h₄*z^2
      + 6*b^2*h₄*z^6 + 10*a^2*h₅*z^3 + 10*a^3*h₅*z^5 + 10*b^2*h₅*z^7 + 10*b^3*h₅*z^11 - 12*d*h₂*h₃*z
      - 12*d*h₂*h₄*z^2 - 12*d*h₂*h₅*z^3 - 12*d*h₂*h₃^2*z^3 - 12*d*h₂*h₄^2*z^5 - 12*d*h₂*h₅^2*z^7
      - 12*d*h₃*h₄*z^3 - 12*d*h₃*h₅*z^4 - 12*d*h₂^2*h₃*z^2 - 12*d*h₃*h₄^2*z^6 - 12*d*h₃*h₅^2*z^8
      - 12*d*h₄*h₅*z^5 - 12*d*h₂^2*h₄*z^3 - 12*d*h₃^2*h₄*z^5 - 12*d*h₄*h₅^2*z^9 - 12*d*h₂^2*h₅*z^4
      - 12*d*h₃^2*h₅*z^6 - 12*d*h₄^2*h₅*z^8 - 6*a*h₂*h₄*z - 6*a*h₂*h₅*z^2 - 6*a*h₃*h₄*z^2
      - 6*a*h₃*h₅*z^3 - 6*a*h₄*h₅*z^4 - 6*d*h₂^2*h₃^2*z^4 - 6*d*h₂^2*h₄^2*z^6 - 6*d*h₂^2*h₅^2*z^8
      - 6*d*h₃^2*h₄^2*z^8 - 6*d*h₃^2*h₅^2*z^10 - 6*d*h₄^2*h₅^2*z^12 - 4*d*h₂*h₃^3*z^5 - 4*d*h₂*h₄^3*z^8
      - 4*d*h₂*h₅^3*z^11 - 4*d*h₂^3*h₃*z^3 - 4*d*h₃*h₄^3*z^9 - 4*d*h₃*h₅^3*z^12 - 4*d*h₂^3*h₄*z^4
      - 4*d*h₃^3*h₄*z^7 - 4*d*h₄*h₅^3*z^13 - 4*d*h₂^3*h₅*z^5 - 4*d*h₃^3*h₅*z^8 - 4*d*h₄^3*h₅*z^11
      - 3*a*h₂*h₃^2*z^2 - 3*a*h₂*h₄^2*z^4 - 3*a*h₂*h₅^2*z^6 - 3*a*h₂^2*h₃*z - 3*a*h₃*h₄^2*z^5
      - 3*a*h₃*h₅^2*z^7 - 3*a*h₂^2*h₄*z^2 - 3*a*h₃^2*h₄*z^4 - 3*a*h₄*h₅^2*z^8 - 3*a*h₂^2*h₅*z^3
      - 3*a*h₃^2*h₅*z^5 - 3*a*h₄^2*h₅*z^7 + 2*a*b*h₂*z^2 + 3*a*b^2*h₃*z^7 + 3*a^2*b*h₃*z^5 + 4*a*b^3*h₄*z^12
      + 4*a^3*b*h₄*z^8 + 5*a*b^4*h₅*z^17 + 5*a^4*b*h₅*z^11 + 6*a*b*h₃*z^3 + 6*a^2*b^2*h₄*z^10
      + 10*a^2*b^3*h₅*z^15 + 10*a^3*b^2*h₅*z^13 + 12*a*b*h₄*z^4 + 12*a*b^2*h₄*z^8 + 12*a^2*b*h₄*z^6
      + 20*a*b*h₅*z^5 + 20*a*b^3*h₅*z^13 + 20*a^3*b*h₅*z^9 + 30*a*b^2*h₅*z^9 + 30*a^2*b*h₅*z^7
      + 30*a^2*b^2*h₅*z^11 - 24*d*h₂*h₃*h₄*z^4 - 24*d*h₂*h₃*h₅*z^5 - 24*d*h₂*h₄*h₅*z^6 - 24*d*h₃*h₄*h₅*z^7
      - 12*d*h₂*h₃*h₄^2*z^7 - 12*d*h₂*h₃*h₅^2*z^9 - 12*d*h₂*h₃^2*h₄*z^6 - 12*d*h₂*h₄*h₅^2*z^10
      - 12*d*h₂*h₃^2*h₅*z^7 - 12*d*h₂*h₄^2*h₅*z^9 - 12*d*h₂^2*h₃*h₄*z^5 - 12*d*h₃*h₄*h₅^2*z^11
      - 12*d*h₂^2*h₃*h₅*z^6 - 12*d*h₃*h₄^2*h₅*z^10 - 12*d*h₂^2*h₄*h₅*z^7 - 12*d*h₃^2*h₄*h₅*z^9
      - 6*a*h₂*h₃*h₄*z^3 - 6*a*h₂*h₃*h₅*z^4 - 6*a*h₂*h₄*h₅*z^5 - 6*a*h₃*h₄*h₅*z^6 - 24*d*h₂*h₃*h₄*h₅*z^8

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
lemma continuous_resS (a b d h₂ h₃ h₄ h₅ : ℂ) : Continuous (resS a b d h₂ h₃ h₄ h₅) := by
  unfold resS; fun_prop

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- The fifth-order polynomial identity behind `residue_two` -/
lemma res_poly (a b d h₂ h₃ h₄ h₅ z : ℂ) :
    quint h₂ h₃ h₄ h₅ (z + a * z ^ 3 + b * z ^ 5) - quart₃ a d (quint h₂ h₃ h₄ h₅ z) =
      (-a * h₂ - d) * z ^ 4 + (-3 * a * h₂ ^ 2 + b - 4 * d * h₂) * z ^ 5 + z ^ 6 * resS a b d h₂ h₃ h₄ h₅ z := by
  simp only [quint, quart₃, resS]; ring


/-- Two adjacent coefficients that are `O(z^(n+2))` together vanish -/
lemma coeff_zero_pair {c₁ c₂ : ℂ} {n : ℕ} (o : (fun z ↦ c₁ * z ^ n + c₂ * z ^ (n + 1)) =O[𝓝 0] fun z ↦ z ^ (n + 2)) :
    c₁ = 0 ∧ c₂ = 0 := by
  have h1 : c₁ = 0 := by
    refine coeff_zero (n := n) ?_
    refine ((o.trans (pow_isBigO_pow (by omega))).sub
      ((isBigO_refl (fun z : ℂ ↦ z ^ (n + 1)) _).const_mul_left c₂)).congr_left fun z ↦ by ring
  subst h1
  exact ⟨rfl, coeff_zero (n := n + 1) (o.congr_left fun z ↦ by ring)⟩

/-- A tangent-to-identity analytic germ to fifth order -/
lemma tangent_expand5 {h : ℂ → ℂ} (ha : AnalyticAt ℂ h 0) (h0 : h 0 = 0) (dh : deriv h 0 = 1) :
    ∃ h₂ h₃ h₄ h₅ : ℂ, (fun z ↦ h z - quint h₂ h₃ h₄ h₅ z) =O[𝓝 0] fun z ↦ z ^ 6 := by
  set F := fun z ↦ h z - z
  have Fa : AnalyticAt ℂ F 0 := ha.sub analyticAt_id
  have F0 : F 0 = 0 := by simp [F, h0]
  have Fd : deriv F 0 = 0 := by
    have := (ha.differentiableAt.hasDerivAt.sub (hasDerivAt_id (0 : ℂ))).deriv
    rw [dh] at this; rw [show F = h - id from rfl, this]; ring
  obtain ⟨C, r, -, r0, tay⟩ := taylor2 Fa
  have F2 : F =O[𝓝 0] fun z ↦ z ^ 2 := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) r0] with z zm
    have := tay z 0 (by simpa using zm) (by simpa using r0)
    simpa [F0, Fd, norm_pow] using this
  have poly : ∀ c₂ c₃ c₄ : ℂ, AnalyticAt ℂ (fun z ↦ F z - (c₂ * z ^ 2 + c₃ * z ^ 3 + c₄ * z ^ 4)) 0 :=
    fun _ _ _ ↦ Fa.sub (by fun_prop)
  obtain ⟨h₂, e2⟩ := coeff_step Fa F2
  obtain ⟨h₃, e3⟩ := coeff_step ((poly h₂ 0 0).congr (by filter_upwards with z; simp)) e2
  have e3' : (fun z ↦ F z - (h₂ * z ^ 2 + h₃ * z ^ 3 + 0 * z ^ 4)) =O[𝓝 0] fun z ↦ z ^ 4 :=
    e3.congr_left fun z ↦ by ring
  obtain ⟨h₄, e4⟩ := coeff_step (poly h₂ h₃ 0) e3'
  have e4' : (fun z ↦ F z - (h₂ * z ^ 2 + h₃ * z ^ 3 + h₄ * z ^ 4)) =O[𝓝 0] fun z ↦ z ^ 5 :=
    e4.congr_left fun z ↦ by ring
  obtain ⟨h₅, e5⟩ := coeff_step (poly h₂ h₃ h₄) e4'
  exact ⟨h₂, h₃, h₄, h₅, e5.congr_left fun z ↦ by simp only [F, quint]; ring⟩

/-- For `k = 2` the normal form coefficient `b` is determined by `g = z + a z³ + d z⁴ + O(z⁶)`: any analytic
tangent-to-identity `h` conjugating `g` to petal normal form has `b = -d² / a`.  So the iterative residue is
`β = 3/4 + d² / (2 a³)`. -/
public lemma residue_two {g h g' : ℂ → ℂ} {a b d : ℂ} (a0 : a ≠ 0)
    (gO : (fun z ↦ g z - quart₃ a d z) =O[𝓝 0] fun z ↦ z ^ 6) (ha : AnalyticAt ℂ h 0) (h0 : h 0 = 0)
    (dh : deriv h 0 = 1) (pg : PetalGerm g' 2 a b) (conj : ∀ᶠ z in 𝓝 0, h (g' z) = g (h z)) :
    b = -d ^ 2 / a := by
  obtain ⟨h₂, h₃, h₄, h₅, hO⟩ := tangent_expand5 ha h0 dh
  set H := quint h₂ h₃ h₄ h₅
  set G := fun z : ℂ ↦ z + a * z ^ 3 + b * z ^ 5
  have g'O : (fun z ↦ g' z - G z) =O[𝓝 0] fun z ↦ z ^ 6 := by
    have := pg.approx; norm_num at this; exact this
  have bnd : ∀ {F : ℂ → ℂ}, Continuous F → (fun z ↦ F z) =O[𝓝 0] fun _ ↦ (1 : ℂ) :=
    fun c ↦ (c.tendsto 0).isBigO_one ℂ
  have z6 : ∀ {m : ℕ}, m ≤ 6 → (fun z : ℂ ↦ z ^ 6) =O[𝓝 0] fun z ↦ z ^ m := fun h ↦ pow_isBigO_pow h
  have z1 : (fun z : ℂ ↦ z ^ 1) = fun z ↦ z := by funext; simp
  -- `g'` and `h` are `O(z)`
  have GO : (fun z ↦ G z) =O[𝓝 0] fun z ↦ z := by
    have c : (fun z ↦ G z) = fun z ↦ z * (1 + a * z ^ 2 + b * z ^ 4) := by funext z; simp only [G]; ring
    rw [c]
    exact ((isBigO_refl (fun z : ℂ ↦ z) _).mul (bnd (by fun_prop))).congr_right fun z ↦ by simp
  have HO : (fun z ↦ H z) =O[𝓝 0] fun z ↦ z := by
    have c : (fun z ↦ H z) = fun z ↦ z * (1 + h₂ * z + h₃ * z ^ 2 + h₄ * z ^ 3 + h₅ * z ^ 4) := by
      funext z; simp only [H, quint]; ring
    rw [c]
    exact ((isBigO_refl (fun z : ℂ ↦ z) _).mul (bnd (by fun_prop))).congr_right fun z ↦ by simp
  have g'z : g' =O[𝓝 0] fun z ↦ z :=
    ((g'O.trans ((z6 (m := 1) (by norm_num)).congr_right fun z ↦ by simp)).add GO).congr_left
      fun z ↦ by ring
  have hz : h =O[𝓝 0] fun z ↦ z :=
    ((hO.trans ((z6 (m := 1) (by norm_num)).congr_right fun z ↦ by simp)).add HO).congr_left
      fun z ↦ by ring
  have tg' : Tendsto g' (𝓝 0) (𝓝 0) := g'z.trans_tendsto tendsto_id
  have th : Tendsto h (𝓝 0) (𝓝 0) := hz.trans_tendsto tendsto_id
  -- the five pieces
  have E1 := (hO.comp_tendsto tg').trans (g'z.pow 6)
  set Q := fun u v : ℂ ↦ 1 + h₂ * (u + v) + h₃ * (u ^ 2 + u * v + v ^ 2) +
    h₄ * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) + h₅ * (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4)
  have Qe : ∀ u v, H u - H v = (u - v) * Q u v := fun u v ↦ by simp only [H, quint, Q]; ring
  have tG : Tendsto (fun z ↦ G z) (𝓝 0) (𝓝 0) := GO.trans_tendsto tendsto_id
  have cQ : Continuous (fun p : ℂ × ℂ ↦ Q p.1 p.2) := by simp only [Q]; fun_prop
  have E2 : (fun z ↦ H (g' z) - H (G z)) =O[𝓝 0] fun z ↦ z ^ 6 :=
    ((g'O.mul (((cQ.tendsto (0, 0)).comp (tg'.prodMk_nhds tG)).isBigO_one ℂ)).congr_right
      fun z ↦ by simp).congr_left fun z ↦ (Qe _ _).symm
  have E3 := (gO.comp_tendsto th).trans (hz.pow 6)
  set Q' := fun u v : ℂ ↦ 1 + a * (u ^ 2 + u * v + v ^ 2) + d * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3)
  have Qe' : ∀ u v, quart₃ a d u - quart₃ a d v = (u - v) * Q' u v := fun u v ↦ by
    simp only [quart₃, Q']; ring
  have tH : Tendsto (fun z ↦ H z) (𝓝 0) (𝓝 0) := HO.trans_tendsto tendsto_id
  have cQ' : Continuous (fun p : ℂ × ℂ ↦ Q' p.1 p.2) := by simp only [Q']; fun_prop
  have E4 : (fun z ↦ quart₃ a d (h z) - quart₃ a d (H z)) =O[𝓝 0] fun z ↦ z ^ 6 :=
    ((hO.mul (((cQ'.tendsto (0, 0)).comp (th.prodMk_nhds tH)).isBigO_one ℂ)).congr_right
      fun z ↦ by simp).congr_left fun z ↦ (Qe' _ _).symm
  -- so `H (G z) - quart₃ (H z) = O(z⁶)`, and its `z⁴`, `z⁵` coefficients vanish
  have tot : (fun z ↦ H (G z) - quart₃ a d (H z)) =O[𝓝 0] fun z ↦ z ^ 6 := by
    refine ((((E2.neg_left.sub E1).add E3).add E4)).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [conj] with z e
    simp only [Function.comp_apply]
    rw [← e]; ring
  have co := coeff_zero_pair (n := 4) (c₁ := -a * h₂ - d) (c₂ := -3 * a * h₂ ^ 2 + b - 4 * d * h₂)
    ((tot.sub ((isBigO_refl (fun z : ℂ ↦ z ^ 6) _).mul (bnd (continuous_resS a b d h₂ h₃ h₄ h₅)) |>.congr_right
      fun z ↦ by simp)).congr_left fun z ↦ by simp only [H, G]; rw [res_poly]; ring)
  obtain ⟨c4, c5⟩ := co
  have e2 : h₂ = -d / a := by field_simp; linear_combination -c4
  rw [e2] at c5
  field_simp at c5 ⊢
  linear_combination c5

/-!
### The parabolic point of `z² - 3/4`
-/

/-- `z² - 3/4` in the coordinate `w = z + 1/2` of its parabolic fixed point -/
@[expose] public def threeQuarters (w : ℂ) : ℂ := -w + w ^ 2

lemma threeQuarters_analytic (w : ℂ) : AnalyticAt ℂ threeQuarters w := by
  unfold threeQuarters; fun_prop

lemma threeQuarters_deriv (w : ℂ) : HasDerivAt threeQuarters (-1 + 2 * w) w := by
  have := (hasDerivAt_id w).neg.add ((hasDerivAt_id w).pow 2)
  convert this using 1
  · funext; simp [threeQuarters]
  · simp

/-- The critical values of `f ∘ f` for `f w = -w + w²` are `-1/4 = f (1/2)` and `5/16 = f (-1/4)` -/
lemma threeQuarters_crit {c₀ : ℂ} (h : deriv (fun w ↦ threeQuarters (threeQuarters w)) c₀ = 0) :
    threeQuarters (threeQuarters c₀) = -1 / 4 ∨ threeQuarters (threeQuarters c₀) = 5 / 16 := by
  have d := (threeQuarters_deriv (threeQuarters c₀)).comp c₀ (threeQuarters_deriv c₀)
  rw [show (fun w ↦ threeQuarters (threeQuarters w)) = threeQuarters ∘ threeQuarters from rfl, d.deriv] at h
  rcases mul_eq_zero.mp h with h | h
  · left
    have e : threeQuarters c₀ = 1 / 2 := by linear_combination h / 2
    rw [e]; simp only [threeQuarters]; norm_num
  · right
    have e : c₀ = 1 / 2 := by linear_combination h / 2
    rw [e]; simp only [threeQuarters]; norm_num

lemma exp_half : exp (π * I / (2 : ℕ)) = I := by
  rw [show π * I / ((2 : ℕ) : ℂ) = (π / 2 : ℝ) * I by push_cast; ring, Complex.exp_mul_I]
  simp

/-- `f ∘ f` on the real line -/
def gr (x : ℝ) : ℝ := x - 2 * x ^ 3 + x ^ 4

lemma gr_cast (x : ℝ) : threeQuarters (threeQuarters (x : ℂ)) = ((gr x : ℝ) : ℂ) := by
  simp only [threeQuarters, gr]; push_cast; ring

lemma gr_iter_cast (x : ℝ) (n : ℕ) :
    (fun z ↦ threeQuarters (threeQuarters z))^[n] (x : ℂ) = ((gr^[n] x : ℝ) : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, gr_cast, Function.iterate_succ_apply']

/-- The critical orbit `-1/4 ↦ ...` of `f ∘ f` increases to `0` from below -/
lemma gr_orbit {ε : ℝ} (ε0 : 0 < ε) : ∃ n : ℕ, -ε < gr^[n] (-1 / 4) ∧ gr^[n] (-1 / 4) < 0 := by
  set s := fun n : ℕ ↦ gr^[n] (-1 / 4)
  have step : ∀ x : ℝ, -1 / 4 ≤ x → x < 0 → x < gr x ∧ gr x < 0 := fun x x1 x0 ↦ by
    simp only [gr]
    constructor
    · nlinarith [mul_pos (neg_pos.mpr x0) (neg_pos.mpr x0), mul_pos (mul_pos (neg_pos.mpr x0) (neg_pos.mpr x0))
        (neg_pos.mpr x0)]
    · have : 0 < 1 - 2 * x ^ 2 + x ^ 3 := by nlinarith [sq_nonneg x]
      nlinarith
  have inv : ∀ n, -1 / 4 ≤ s n ∧ s n < 0 := by
    intro n
    induction n with
    | zero => simp [s]; norm_num
    | succ n ih =>
      have := step _ ih.1 ih.2
      simp only [s, Function.iterate_succ_apply'] at this ⊢
      have ih1 : -1 / 4 ≤ gr^[n] (-1 / 4) := ih.1
      exact ⟨by linarith [this.1], this.2⟩
  have mono : Monotone s := monotone_nat_of_le_succ fun n ↦ by
    have := step _ (inv n).1 (inv n).2
    simp only [s, Function.iterate_succ_apply']; exact this.1.le
  have bdd : BddAbove (Set.range s) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (inv n).2.le⟩
  have t := tendsto_atTop_ciSup mono bdd
  set L := ⨆ n, s n
  have L0 : L ≤ 0 := ciSup_le fun n ↦ (inv n).2.le
  have L1 : -1 / 4 ≤ L := le_trans (inv 0).1 (le_ciSup bdd 0)
  -- `L` is a fixed point of `gr`, hence `0`
  have fix : gr L = L := by
    have c : Continuous gr := by unfold gr; fun_prop
    have t1 : Filter.Tendsto (fun n ↦ s (n + 1)) Filter.atTop (𝓝 (gr L)) := by
      have := (c.tendsto L).comp t
      refine this.congr fun n ↦ ?_
      simp only [Function.comp_apply, s, Function.iterate_succ_apply']
    exact tendsto_nhds_unique t1 (t.comp (Filter.tendsto_add_atTop_nat 1))
  have L00 : L = 0 := by
    by_contra h
    have Ln : L < 0 := lt_of_le_of_ne L0 h
    have := (step L L1 Ln).1
    linarith
  rw [L00] at t
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (t.eventually (Ioi_mem_nhds (by linarith : -ε < 0)))
  exact ⟨n, hn n le_rfl, (inv n).2⟩

/-- The Lavaurs horn maps at the root `c = -3/4` of the period-2 bulb.  For `f w = -w + w²` (`z² - 3/4` at its
parabolic point `-1/2`), `g = f ∘ f = w - 2w³ + w⁴`, and the repelling direction `i/2` of `g`: there are attracting
petals `Pu`, `Pl` (directions `∓1/2`) with Fatou coordinates `Φu`, `Φl` and a repelling parametrisation `Ψ`.  The horn
maps `Hu = Φu ∘ Ψ`, `Hl = Φl ∘ Ψ` are defined on an upper and a lower half-plane, and
`Hu ζ = ζ - π i β + O(e^(-2π im ζ))`, `Hl ζ = ζ + π i β + O(e^(2π im ζ))`, with iterative residue `β = 11/16`
(so the ends differ by `11 π i / 8 = 4.3197 i`, the `τ` of the numerics).
The critical orbit `-1/4 ↦ 5/16 ↦ ...` of `f` alternates between the two (disjoint) attracting basins, so all
critical values lie in one orbit: those of `Hu` in `ζ₀ + ℤ` and those of `Hl` in `ζ₀ + 1/2 + ℤ`, `ζ₀ = Φu (-1/4)`
(in the numerics' consistent coordinate this is the lattice `ζ₀ + ℤ + ℤ (1/2 + τ)`).  `f` swaps the two attracting
basins with a half step in the Fatou coordinates. -/
public theorem lavaurs_three_quarters :
    ∃ Pu : Set ℂ, ∃ Φu : ℂ → ℂ, ∃ Pl : Set ℂ, ∃ Φl : ℂ → ℂ, ∃ V : Set ℂ, ∃ Ψ : ℂ → ℂ, ∃ b : ℂ,
      let f := threeQuarters
      let g := fun z ↦ f (f z)
      let β : ℂ := 11 / 16
      petalResidue 2 (-2) b = β ∧
      IsOpen (hornDomain g Ψ Pu V) ∧ IsOpen (hornDomain g Ψ Pl V) ∧
      (∀ ζ, ζ ∈ hornDomain g Ψ Pu V ↔ ζ + 1 ∈ hornDomain g Ψ Pu V) ∧
      (∀ ζ, ζ ∈ hornDomain g Ψ Pl V ↔ ζ + 1 ∈ hornDomain g Ψ Pl V) ∧
      (∃ T : ℝ, ∀ ζ : ℂ, T < ζ.im → ζ ∈ hornDomain g Ψ Pu V) ∧
      (∃ T : ℝ, ∀ ζ : ℂ, ζ.im < T → ζ ∈ hornDomain g Ψ Pl V) ∧
      AnalyticOnNhd ℂ (hornMap g Φu Ψ Pu V) (hornDomain g Ψ Pu V) ∧
      AnalyticOnNhd ℂ (hornMap g Φl Ψ Pl V) (hornDomain g Ψ Pl V) ∧
      (∀ ζ ∈ hornDomain g Ψ Pu V, hornMap g Φu Ψ Pu V (ζ + 1) = hornMap g Φu Ψ Pu V ζ + 1) ∧
      (∀ ζ ∈ hornDomain g Ψ Pl V, hornMap g Φl Ψ Pl V (ζ + 1) = hornMap g Φl Ψ Pl V ζ + 1) ∧
      (fun ζ ↦ hornMap g Φu Ψ Pu V ζ - ζ + π * I * β) =O[comap Complex.im atTop]
        (fun ζ ↦ Real.exp (-2 * π * ζ.im)) ∧
      (fun ζ ↦ hornMap g Φl Ψ Pl V ζ - ζ - π * I * β) =O[comap Complex.im atBot]
        (fun ζ ↦ Real.exp (2 * π * ζ.im)) ∧
      (-1 / 4 : ℂ) ∈ basin g Pu ∧ (5 / 16 : ℂ) ∈ basin g Pl ∧ Disjoint (basin g Pu) (basin g Pl) ∧
      (∀ ζ ∈ hornDomain g Ψ Pu V, deriv (hornMap g Φu Ψ Pu V) ζ = 0 →
        ∃ j : ℤ, hornMap g Φu Ψ Pu V ζ = basinExt g Φu Pu (-1 / 4) + j) ∧
      (∀ ζ ∈ hornDomain g Ψ Pl V, deriv (hornMap g Φl Ψ Pl V) ζ = 0 →
        ∃ j : ℤ, hornMap g Φl Ψ Pl V ζ = basinExt g Φu Pu (-1 / 4) + 1 / 2 + j) ∧
      (MapsTo f (basin g Pu) (basin g Pl) ∧ ∀ z ∈ basin g Pu, basinExt g Φl Pl (f z) = basinExt g Φu Pu z + 1 / 2) ∧
      (MapsTo f (basin g Pl) (basin g Pu) ∧ ∀ z ∈ basin g Pl, basinExt g Φu Pu (f z) = basinExt g Φl Pl z + 1 / 2) := by
  have fa : ∀ z, AnalyticAt ℂ threeQuarters z := threeQuarters_analytic
  have f0 : threeQuarters 0 = 0 := by simp [threeQuarters]
  have fd : deriv threeQuarters 0 = -1 := by simpa using (threeQuarters_deriv 0).deriv
  have approx : (fun z ↦ threeQuarters (threeQuarters z) - (z + -2 * z ^ 3)) =O[𝓝 0] fun z ↦ z ^ 4 := by
    have e : (fun z ↦ threeQuarters (threeQuarters z) - (z + -2 * z ^ 3)) = fun z ↦ z ^ 4 := by
      funext z; simp only [threeQuarters]; ring
    rw [e]
  have hc : (I / 2) ^ 2 = 1 / (2 * (-2 : ℂ)) := by
    rw [div_pow, Complex.I_sq]; norm_num
  obtain ⟨Pu, Φu, Pl, Φl, V, Ψ, b, ⟨h, φ, ha, h0, dh, pg, conj⟩, ⟨εs, εs0, sect⟩, disj, ⟨Pou, -, gPu, Φau, Φeu⟩,
    ⟨Pol, -, gPl, Φal, Φel⟩, ⟨Vo, Vl, reach, Ψa, Ψe⟩, domu, -, doml, -, decu, decl, critu, critl, fu, fl, -, -⟩ :=
    parabolic_flip fa f0 fd (by norm_num) approx hc
  -- the residue: `b = -d² / a = 1/2`, so `β = 3/4 - (1/2) / 8 = 11/16`
  have gO : (fun z ↦ threeQuarters (threeQuarters z) - quart₃ (-2) 1 z) =O[𝓝 0] fun z ↦ z ^ 6 := by
    have e : (fun z ↦ threeQuarters (threeQuarters z) - quart₃ (-2) 1 z) = fun _ ↦ 0 := by
      funext z; simp only [threeQuarters, quart₃]; ring
    rw [e]; exact isBigO_zero _ _
  have hb := residue_two (by norm_num) gO ha h0 dh pg conj
  have hβ : petalResidue 2 (-2) b = 11 / 16 := by
    simp only [petalResidue, hb]; norm_num
  rw [hβ] at decu decl
  have ga : ∀ z, AnalyticAt ℂ (fun z ↦ threeQuarters (threeQuarters z)) z := fun z ↦ (fa _).comp (fa z)
  obtain ⟨Dou, Dpu, Hau, Heu⟩ := horn_map ga Pou gPu Φau Φeu Vo Vl reach Ψa Ψe
  obtain ⟨Dol, Dpl, Hal, Hel⟩ := horn_map ga Pol gPl Φal Φel Vo Vl reach Ψa Ψe
  -- the critical orbit enters the upper petal `Pu` (direction `-1/2`), along the negative reals
  have cu : I / 2 * exp (π * I / (2 : ℕ)) = -1 / 2 := by rw [exp_half]; ring_nf; rw [Complex.I_sq]; ring
  have mu : (-1 / 4 : ℂ) ∈ basin (fun z ↦ threeQuarters (threeQuarters z)) Pu := by
    obtain ⟨n, n1, n0⟩ := gr_orbit (ε := εs) εs0
    refine ⟨n, ?_⟩
    have e : ((-1 / 4 : ℝ) : ℂ) = -1 / 4 := by push_cast; ring
    rw [← e, gr_iter_cast]
    set x := gr^[n] (-1 / 4)
    have x0 : (x : ℂ) ≠ 0 := by exact_mod_cast n0.ne
    refine sect _ x0 (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg n0]; linarith) ?_
    rw [cu]
    have : ((‖(x : ℂ)‖ / ‖(-1 / 2 : ℂ)‖ : ℝ) : ℂ) = -2 * x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg n0]; norm_num; ring
    rw [this, show (-1 / 2 : ℂ) * (-2 * x) = x by ring, div_self x0, sub_self, norm_zero]; norm_num
  have f14 : threeQuarters (-1 / 4) = 5 / 16 := by simp only [threeQuarters]; norm_num
  have ml : (5 / 16 : ℂ) ∈ basin (fun z ↦ threeQuarters (threeQuarters z)) Pl := by
    rw [← f14]; exact fu.1 mu
  refine ⟨Pu, Φu, Pl, Φl, V, Ψ, b, hβ, Dou, Dol, Dpu, Dpl, domu, doml, Hau, Hal, Heu, Hel, decu, decl, mu, ml,
    disj, fun ζ m crit ↦ ?_, fun ζ m crit ↦ ?_, fu, fl⟩
  · obtain ⟨c₀, dc, mc, j, e⟩ := critu ζ m crit
    beta_reduce at mc e
    rcases threeQuarters_crit dc with v | v
    · exact ⟨j, by rw [e, v]⟩
    · rw [v] at mc; exact absurd mc (Set.disjoint_right.mp disj ml)
  · obtain ⟨c₀, dc, mc, j, e⟩ := critl ζ m crit
    beta_reduce at mc e
    rcases threeQuarters_crit dc with v | v
    · rw [v] at mc; exact absurd mc (Set.disjoint_left.mp disj mu)
    · refine ⟨j, ?_⟩
      rw [e, v, ← f14, fu.2 _ mu]
