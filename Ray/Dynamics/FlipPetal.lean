module
public import Ray.Dynamics.HornEnds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic
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
