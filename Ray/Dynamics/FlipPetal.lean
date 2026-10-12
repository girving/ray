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
