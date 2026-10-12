module
public import Ray.Dynamics.Petal
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Bound

/-!
## Petal normal form

A tangent-to-identity germ `g z = z + a z^(k+1) + O(z^(k+2))` with `a ≠ 0` is locally conjugate to the petal normal
form `z + a z^(k+1) + b z^(2k+1) + O(z^(2k+2))` of `PetalGerm`: the terms `z^(k+2), …, z^(2k)` can be removed one at a
time.  Conjugating by `h z = z + c z^m` (`2 ≤ m ≤ k`) changes the `z^(k+m)` coefficient by `a c (k + 1 - m)` and leaves
lower ones alone, since `h⁻¹ ∘ g ∘ h - id = (g - id) ∘ h / h' + O(z^(2k+2))`.  The coefficient `b` of `z^(2k+1)` is
what is left: it is a conjugacy invariant (it determines the iterative residue).

The main result is `PetalGerm.normalize`.
-/

open Asymptotics Filter
open Set
open scoped Topology

variable {g : ℂ → ℂ} {k : ℕ} {a : ℂ}

/-!
### Generic tools
-/

/-- An analytic `F` with `F = O(z^n)` near `0` factors as `z^n q` with `q` analytic -/
lemma exists_pow_mul_of_isBigO {F : ℂ → ℂ} {n : ℕ} (fa : AnalyticAt ℂ F 0) (o : F =O[𝓝 0] fun z ↦ z ^ n) :
    ∃ q, AnalyticAt ℂ q 0 ∧ ∀ᶠ z in 𝓝 0, F z = z ^ n * q z := by
  suffices le : (n : ℕ∞) ≤ analyticOrderAt F 0 by
    obtain ⟨q, qa, hq⟩ := (natCast_le_analyticOrderAt fa).mp le
    exact ⟨q, qa, by simpa using hq⟩
  by_contra lt
  push Not at lt
  obtain ⟨q, qa, q0, hq⟩ := fa.analyticOrderAt_ne_top.mp (ne_top_of_lt lt)
  set N := analyticOrderNatAt F 0
  have Nn : N < n := by
    have e := Nat.cast_analyticOrderNatAt (f := F) (z₀ := 0) (ne_top_of_lt lt)
    rw [← e] at lt; exact_mod_cast lt
  obtain ⟨C, hC⟩ := o.bound
  have ev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖q z‖ ≤ C * ‖z‖ ^ (n - N) := by
    filter_upwards [self_mem_nhdsWithin, (hq.and hC).filter_mono nhdsWithin_le_nhds] with z z0 ⟨e, b⟩
    rw [e] at b
    simp only [sub_zero, smul_eq_mul, norm_mul, norm_pow] at b
    have zp : 0 < ‖z‖ ^ N := pow_pos (norm_pos_iff.mpr z0) _
    have : ‖z‖ ^ n = ‖z‖ ^ N * ‖z‖ ^ (n - N) := by rw [← pow_add, Nat.add_sub_cancel' Nn.le]
    rw [this] at b
    nlinarith
  have t1 : Tendsto (fun z ↦ ‖q z‖) (𝓝[≠] 0) (𝓝 ‖q 0‖) :=
    (qa.continuousAt.norm.tendsto).mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun z : ℂ ↦ C * ‖z‖ ^ (n - N)) (𝓝[≠] 0) (𝓝 0) := by
    have c : Continuous (fun z : ℂ ↦ C * ‖z‖ ^ (n - N)) := by fun_prop
    have := c.tendsto 0
    simp only [norm_zero, zero_pow (Nat.sub_ne_zero_of_lt Nn), mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto t1 t2 ev
  exact q0 (norm_le_zero_iff.mp this)

/-- Second-order Taylor bound for an analytic function near `0` -/
lemma taylor2 {f : ℂ → ℂ} (fa : AnalyticAt ℂ f 0) : ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ ∀ x y : ℂ, ‖x‖ < r → ‖y‖ < r →
    ‖f x - f y - deriv f y * (x - y)‖ ≤ C * ‖x - y‖ ^ 2 := by
  obtain ⟨R, R0, fa⟩ := fa.exists_ball_analyticOnNhd
  have d2 : ContinuousAt (deriv (deriv f)) 0 :=
    (fa 0 (Metric.mem_ball_self R0)).deriv.deriv.continuousAt
  obtain ⟨r1, r10, hr1⟩ := Metric.eventually_nhds_iff.mp
    (d2.norm.eventually (gt_mem_nhds (lt_add_one ‖deriv (deriv f) 0‖)))
  set M := ‖deriv (deriv f) 0‖ + 1
  set r := min r1 R
  have r0 : 0 < r := lt_min r10 R0
  refine ⟨M, r, by positivity, r0, fun x y xr yr ↦ ?_⟩
  set s := Metric.ball (0 : ℂ) r
  have sR : ∀ t ∈ s, t ∈ Metric.ball (0 : ℂ) R := fun t m ↦
    Metric.ball_subset_ball (min_le_right _ _) m
  have xs : x ∈ s := by simpa [s] using xr
  have ys : y ∈ s := by simpa [s] using yr
  -- `f'` is `M`-Lipschitz on `s`
  have lip : ∀ t ∈ s, ‖deriv f t - deriv f y‖ ≤ M * ‖t - y‖ := fun t ts ↦
    (convex_ball _ _).norm_image_sub_le_of_norm_deriv_le
      (fun u us ↦ ((fa u (sR u us)).deriv).differentiableAt)
      (fun u us ↦ (hr1 (lt_of_lt_of_le (Metric.mem_ball.mp us) (min_le_left r1 R))).le)
      ys ts
  -- `t ↦ f t - f' y t` has derivative bounded by `M ‖x - y‖` on `s ∩ closedBall y ‖x - y‖`
  set u := s ∩ Metric.closedBall y ‖x - y‖
  have uc : Convex ℝ u := (convex_ball _ _).inter (convex_closedBall _ _)
  have dφ : ∀ t ∈ u, HasDerivAt (fun t ↦ f t - deriv f y * t) (deriv f t - deriv f y) t := fun t tu ↦ by
    have := ((fa t (sR t tu.1)).differentiableAt.hasDerivAt).sub ((hasDerivAt_id t).const_mul (deriv f y))
    simp only [mul_one] at this
    exact this
  have e := uc.norm_image_sub_le_of_norm_deriv_le (f := fun t ↦ f t - deriv f y * t) (C := M * ‖x - y‖)
    (fun t tu ↦ (dφ t tu).differentiableAt)
    (fun t tu ↦ by
      rw [(dφ t tu).deriv]
      refine le_trans (lip t tu.1) ?_
      have := tu.2; rw [Metric.mem_closedBall, dist_eq_norm] at this
      have M0 : 0 ≤ M := by positivity
      gcongr)
    ⟨ys, by simp⟩ ⟨xs, by simp [dist_eq_norm]⟩
  calc ‖f x - f y - deriv f y * (x - y)‖ = ‖(f x - deriv f y * x) - (f y - deriv f y * y)‖ := by ring_nf
    _ ≤ M * ‖x - y‖ * ‖x - y‖ := e
    _ = M * ‖x - y‖ ^ 2 := by ring

/-- An analytic local inverse at a fixed point with nonzero derivative -/
lemma exists_local_inv {h : ℂ → ℂ} (ha : AnalyticAt ℂ h 0) (h0 : h 0 = 0) (d : deriv h 0 ≠ 0) :
    ∃ φ, AnalyticAt ℂ φ 0 ∧ φ 0 = 0 ∧ (∀ᶠ z in 𝓝 0, φ (h z) = z) ∧ (∀ᶠ z in 𝓝 0, h (φ z) = z) := by
  have pa := ha.analyticAt_localInverse d
  have left := HasStrictDerivAt.eventually_left_inverse ha.hasStrictDerivAt d
  have right := HasStrictDerivAt.eventually_right_inverse ha.hasStrictDerivAt d
  rw [h0] at pa right
  refine ⟨_, pa, ?_, left, right⟩
  have := left.self_of_nhds
  rwa [h0] at this

/-- `(1 + u)^n = 1 + n u + O(u²)` -/
lemma one_add_pow_lin (n : ℕ) :
    (fun u : ℂ ↦ (1 + u) ^ n - 1 - n * u) =O[𝓝 0] fun u ↦ u ^ 2 := by
  refine ((one_add_pow_expand n).trans (pow_isBigO_pow (by norm_num))).add
    ((isBigO_refl (fun u : ℂ ↦ u ^ 2) _).const_mul_left ((n : ℂ) * (n - 1) / 2)) |>.congr_left fun u ↦ ?_
  ring

/-- `(1 + u)^n = 1 + O(u)` -/
lemma one_add_pow_sub_one (n : ℕ) : (fun u : ℂ ↦ (1 + u) ^ n - 1) =O[𝓝 0] fun u ↦ u := by
  have d : HasDerivAt (fun u : ℂ ↦ (1 + u) ^ n) _ 0 :=
    ((hasDerivAt_id (0 : ℂ)).const_add 1).pow n
  simpa using d.isBigO_sub

/-!
### One coefficient at a time
-/

/-- `g z = z + a z^(k+1) + O(z^n)`, analytic, fixing `0` -/
def NForm (g : ℂ → ℂ) (k : ℕ) (a : ℂ) (n : ℕ) : Prop :=
  AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (fun z ↦ g z - (z + a * z ^ (k + 1))) =O[𝓝 0] fun z ↦ z ^ n

/-- `h` and `φ` are analytic local inverses fixing `0` -/
def InvPair (h φ : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ h 0 ∧ AnalyticAt ℂ φ 0 ∧ h 0 = 0 ∧ φ 0 = 0 ∧ (∀ᶠ z in 𝓝 0, φ (h z) = z) ∧
    (∀ᶠ z in 𝓝 0, h (φ z) = z)

lemma InvPair.id : InvPair id id :=
  ⟨analyticAt_id, analyticAt_id, rfl, rfl, by simp, by simp⟩

lemma tendsto_zero {f : ℂ → ℂ} (fa : AnalyticAt ℂ f 0) (f0 : f 0 = 0) : Tendsto f (𝓝 0) (𝓝 0) := by
  have := fa.continuousAt.tendsto; rwa [f0] at this

lemma analyticAt_comp_zero {f g : ℂ → ℂ} (fa : AnalyticAt ℂ f 0) (ga : AnalyticAt ℂ g 0) (g0 : g 0 = 0) :
    AnalyticAt ℂ (f ∘ g) 0 := by
  rw [← g0] at fa; exact fa.comp ga

lemma InvPair.comp {h₁ φ₁ h₂ φ₂ : ℂ → ℂ} (p : InvPair h₁ φ₁) (q : InvPair h₂ φ₂) :
    InvPair (h₁ ∘ h₂) (φ₂ ∘ φ₁) := by
  obtain ⟨h1a, φ1a, h10, φ10, l1, r1⟩ := p
  obtain ⟨h2a, φ2a, h20, φ20, l2, r2⟩ := q
  refine ⟨analyticAt_comp_zero h1a h2a h20, analyticAt_comp_zero φ2a φ1a φ10, by simp [h10, h20],
    by simp [φ10, φ20], ?_, ?_⟩
  · filter_upwards [(tendsto_zero h2a h20).eventually l1, l2] with z e1 e2
    simp [e1, e2]
  · filter_upwards [(tendsto_zero φ1a φ10).eventually r2, r1] with z e1 e2
    simp [e1, e2]

/-- Conjugating by `z + c z^(j+2)` kills the `z^(k+j+2)` coefficient, for the right `c` -/
lemma step {j : ℕ} (a0 : a ≠ 0) (jk : j + 2 ≤ k) (hg : NForm g k a (k + j + 2)) :
    ∃ h φ, InvPair h φ ∧ NForm (φ ∘ g ∘ h) k a (k + j + 3) := by
  obtain ⟨ga, g0, go⟩ := hg
  have Fa : AnalyticAt ℂ (fun z ↦ g z - (z + a * z ^ (k + 1))) 0 :=
    ga.sub (analyticAt_id.add (analyticAt_const.mul (analyticAt_id.pow _)))
  obtain ⟨q, qa, hq⟩ := exists_pow_mul_of_isBigO Fa go
  set d := q 0
  -- `g Y - Y = a Y^(k+1) + d Y^(k+j+2) + O(Y^(k+j+3))`
  have rexp : (fun Y ↦ g Y - Y - (a * Y ^ (k + 1) + d * Y ^ (k + j + 2))) =O[𝓝 0]
      fun Y ↦ Y ^ (k + j + 3) := by
    have qd : (fun Y ↦ q Y - d) =O[𝓝 0] fun Y ↦ Y := by
      simpa using qa.differentiableAt.hasDerivAt.isBigO_sub
    refine ((isBigO_refl (fun Y : ℂ ↦ Y ^ (k + j + 2)) _).mul qd).congr' ?_ ?_
    · filter_upwards [hq] with Y e
      rw [mul_sub, ← e]; ring
    · exact Eventually.of_forall fun Y ↦ by ring
  have rO : (fun Y ↦ g Y - Y) =O[𝓝 0] fun Y ↦ Y ^ (k + 1) := by
    refine ((rexp.trans (pow_isBigO_pow (by omega))).add (((isBigO_refl _ _).const_mul_left a).add
      ((pow_isBigO_pow (by omega : k + 1 ≤ k + j + 2)).const_mul_left d))).congr_left fun Y ↦ ?_
    ring
  -- the conjugacy
  have kj : (k : ℂ) + 1 - (j + 2) ≠ 0 := by
    have e : ((k + 1 - (j + 2) : ℕ) : ℂ) = (k : ℂ) + 1 - (j + 2) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [← e]; exact Nat.cast_ne_zero.mpr (by omega)
  set c := -d / (a * ((k : ℂ) + 1 - (j + 2)))
  set hh : ℂ → ℂ := fun z ↦ z + c * z ^ (j + 2)
  have hha : AnalyticAt ℂ hh 0 := analyticAt_id.add (analyticAt_const.mul (analyticAt_id.pow _))
  have hh0 : hh 0 = 0 := by simp [hh]
  have hhe : ∀ y, hh y = y * (1 + c * y ^ (j + 1)) := fun y ↦ by simp only [hh]; ring
  set H : ℂ → ℂ := fun y ↦ 1 + c * ((j + 2 : ℕ) * y ^ (j + 1))
  have dhh : ∀ y, HasDerivAt hh (H y) y := fun y ↦ by
    have := (hasDerivAt_id y).add ((hasDerivAt_pow (j + 2) y).const_mul c)
    convert this using 1
    · rfl
    · simp only [H]; rfl
  have dh0 : deriv hh 0 ≠ 0 := by rw [(dhh 0).deriv]; simp [H]
  obtain ⟨φ, φa, φ0, left, right⟩ := exists_local_inv hha hh0 dh0
  set G := φ ∘ g ∘ hh
  have gha : AnalyticAt ℂ (g ∘ hh) 0 := analyticAt_comp_zero ga hha hh0
  have gh0 : (g ∘ hh) 0 = 0 := by simp [hh0, g0]
  have Ga : AnalyticAt ℂ G 0 := analyticAt_comp_zero φa gha gh0
  have G0 : G 0 = 0 := by simp [G, hh0, g0, φ0]
  refine ⟨hh, φ, ⟨hha, φa, hh0, φ0, left, right⟩, Ga, G0, ?_⟩
  have thh := tendsto_zero hha hh0
  have tG := tendsto_zero Ga G0
  have conj : ∀ᶠ y in 𝓝 0, hh (G y) = g (hh y) := (tendsto_zero gha gh0).eventually right
  -- `E = (g - id) ∘ hh - H D` is quadratic in `D = G - id`
  obtain ⟨C, r, C0, r0, tay⟩ := taylor2 hha
  have small : ∀ᶠ y in 𝓝 (0 : ℂ), ‖y‖ < r ∧ ‖G y‖ < r := by
    have t1 : ∀ᶠ y in 𝓝 (0 : ℂ), ‖y‖ < r :=
      Metric.eventually_nhds_iff.mpr ⟨r, r0, fun _ hy ↦ by simpa using hy⟩
    exact t1.and (tG.eventually t1)
  have Eb : ∀ᶠ y in 𝓝 0, ‖(g (hh y) - hh y) - H y * (G y - y)‖ ≤ C * ‖G y - y‖ ^ 2 := by
    filter_upwards [small, conj] with y ⟨yr, Gr⟩ e
    have := tay (G y) y Gr yr
    rwa [e, (dhh y).deriv] at this
  -- `D = O(y^(k+1))`
  have tH : Tendsto H (𝓝 0) (𝓝 1) := by
    have c : Continuous H := by fun_prop
    simpa [H] using c.tendsto 0
  have tD : Tendsto (fun y ↦ G y - y) (𝓝 0) (𝓝 0) := by simpa using tG.sub tendsto_id
  have Hb : ∀ᶠ y in 𝓝 0, 1 / 2 ≤ ‖H y‖ := by
    have := tH.norm.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < ‖(1 : ℂ)‖))
    exact this.mono fun y h ↦ h.le
  have Db : ∀ᶠ y in 𝓝 0, C * ‖G y - y‖ ≤ 1 / 4 := by
    have t := (tD.norm.const_mul C)
    simp only [norm_zero, mul_zero] at t
    exact t.eventually (ge_mem_nhds (by norm_num))
  have rh : (fun y ↦ g (hh y) - hh y) =O[𝓝 0] fun y ↦ y ^ (k + 1) := by
    have hhO : hh =O[𝓝 0] fun y ↦ y := by
      refine ((isBigO_refl (fun y : ℂ ↦ y) _).add (((pow_isBigO_pow (by omega : 1 ≤ j + 2)).congr_right
        (fun y ↦ pow_one y)).const_mul_left c)).congr_left fun y ↦ ?_
      simp [hh]
    exact (rO.comp_tendsto thh).trans (hhO.pow (k + 1))
  have DO : (fun y ↦ G y - y) =O[𝓝 0] fun y ↦ y ^ (k + 1) := by
    refine (IsBigO.of_bound 4 ?_).trans rh
    filter_upwards [Eb, Hb, Db] with y e hb db
    set D := G y - y
    set R := g (hh y) - hh y
    have hd : ‖H y * D‖ ≤ ‖R‖ + C * ‖D‖ ^ 2 := by
      calc ‖H y * D‖ = ‖R - (R - H y * D)‖ := by ring_nf
        _ ≤ ‖R‖ + ‖R - H y * D‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [norm_mul] at hd
    have : C * ‖D‖ ^ 2 ≤ ‖D‖ / 4 := by nlinarith [norm_nonneg D]
    nlinarith [norm_nonneg D]
  have EO : (fun y ↦ (g (hh y) - hh y) - H y * (G y - y)) =O[𝓝 0] fun y ↦ y ^ (k + j + 3) := by
    refine (IsBigO.of_bound C ?_).trans ((DO.pow 2).trans ?_)
    · filter_upwards [Eb] with y e; rwa [norm_pow]
    · refine (pow_isBigO_pow (by omega : k + j + 3 ≤ (k + 1) * 2)).congr_left fun y ↦ ?_
      rw [pow_mul]
  -- the `z^(k+j+2)` coefficient of `(g - id) ∘ hh - a z^(k+1) H` cancels
  have tu : Tendsto (fun y : ℂ ↦ c * y ^ (j + 1)) (𝓝 0) (𝓝 0) := by
    have c : Continuous (fun y : ℂ ↦ c * y ^ (j + 1)) := by fun_prop
    simpa using c.tendsto 0
  have uO : (fun y : ℂ ↦ c * y ^ (j + 1)) =O[𝓝 0] fun y ↦ y ^ (j + 1) :=
    (isBigO_refl _ _).const_mul_left c
  have A1 := (rexp.comp_tendsto thh).trans (((isBigO_refl (fun y : ℂ ↦ y) _).add
    (((pow_isBigO_pow (by omega : 1 ≤ j + 2)).congr_right (fun y ↦ pow_one y)).const_mul_left c)).pow (k + j + 3))
  have A2 : (fun y ↦ hh y ^ (k + 1) - (y ^ (k + 1) + (k + 1) * c * y ^ (k + j + 2))) =O[𝓝 0]
      fun y ↦ y ^ (k + j + 3) := by
    refine (((isBigO_refl (fun y : ℂ ↦ y ^ (k + 1)) _).mul
      (((one_add_pow_lin (k + 1)).comp_tendsto tu).trans (uO.pow 2))).trans ?_).congr_left fun y ↦ ?_
    · refine (pow_isBigO_pow (by omega : k + j + 3 ≤ k + 1 + (j + 1) * 2)).congr_left fun y ↦ ?_
      ring
    · simp only [Function.comp_apply, hhe, mul_pow]; push_cast; ring
  have A3 : (fun y ↦ hh y ^ (k + j + 2) - y ^ (k + j + 2)) =O[𝓝 0] fun y ↦ y ^ (k + j + 3) := by
    refine (((isBigO_refl (fun y : ℂ ↦ y ^ (k + j + 2)) _).mul
      (((one_add_pow_sub_one (k + j + 2)).comp_tendsto tu).trans uO)).trans ?_).congr_left fun y ↦ ?_
    · refine (pow_isBigO_pow (by omega : k + j + 3 ≤ k + j + 2 + (j + 1))).congr_left fun y ↦ ?_
      ring
    · simp only [Function.comp_apply, hhe, mul_pow]; ring
  have KO : (fun y ↦ (g (hh y) - hh y) - a * y ^ (k + 1) * H y) =O[𝓝 0] fun y ↦ y ^ (k + j + 3) := by
    refine ((A1.add (A2.const_mul_left a)).add (A3.const_mul_left d)).congr_left fun y ↦ ?_
    simp only [Function.comp_apply, H]
    generalize g (hh y) = Z
    generalize hh y = W
    simp only [c]
    field_simp
    push_cast
    ring
  -- divide by `H`
  have HT : (fun y ↦ H y * (G y - (y + a * y ^ (k + 1)))) =O[𝓝 0] fun y ↦ y ^ (k + j + 3) :=
    (KO.sub EO).congr_left fun y ↦ by ring
  have Hi : (fun y ↦ (H y)⁻¹) =O[𝓝 0] fun _ ↦ (1 : ℂ) := by
    have := tH.inv₀ one_ne_zero
    simpa using this.isBigO_one ℂ
  refine (Hi.mul HT).congr' ?_ (Eventually.of_forall fun y ↦ one_mul _)
  filter_upwards [Hb] with y hb
  have : H y ≠ 0 := fun e ↦ by rw [e, norm_zero] at hb; norm_num at hb
  field_simp
  rfl

/-!
### The normal form
-/

/-- A tangent-to-identity germ `g z = z + a z^(k+1) + O(z^(k+2))`, `a ≠ 0`, is analytically conjugate near `0` to
the petal normal form: there are local inverses `h`, `φ` fixing `0` and a `b` with
`φ ∘ g ∘ h = z + a z^(k+1) + b z^(2k+1) + O(z^(2k+2))`. -/
public theorem PetalGerm.normalize (k0 : 0 < k) (a0 : a ≠ 0) (ga : AnalyticAt ℂ g 0) (g0 : g 0 = 0)
    (approx : (fun z ↦ g z - (z + a * z ^ (k + 1))) =O[𝓝 0] fun z ↦ z ^ (k + 2)) :
    ∃ h φ : ℂ → ℂ, ∃ b, AnalyticAt ℂ h 0 ∧ AnalyticAt ℂ φ 0 ∧ h 0 = 0 ∧ φ 0 = 0 ∧
      (∀ᶠ z in 𝓝 0, φ (h z) = z) ∧ (∀ᶠ z in 𝓝 0, h (φ z) = z) ∧ PetalGerm (φ ∘ g ∘ h) k a b := by
  have ind : ∀ j, j + 1 ≤ k → ∃ h φ, InvPair h φ ∧ NForm (φ ∘ g ∘ h) k a (k + j + 2) := by
    intro j
    induction j with
    | zero => exact fun _ ↦ ⟨id, id, InvPair.id, ga, g0, approx⟩
    | succ j ih =>
      intro jk
      obtain ⟨h, φ, p, n⟩ := ih (by omega)
      obtain ⟨h', φ', p', n'⟩ := step a0 (by omega : j + 2 ≤ k) n
      exact ⟨h ∘ h', φ' ∘ φ, p.comp p', n'⟩
  obtain ⟨h, φ, ⟨ha, φa, h0, φ0, l, r⟩, Ga, G0, Go⟩ := ind (k - 1) (by omega)
  rw [show k + (k - 1) + 2 = 2 * k + 1 by omega] at Go
  have Fa : AnalyticAt ℂ (fun z ↦ (φ ∘ g ∘ h) z - (z + a * z ^ (k + 1))) 0 :=
    Ga.sub (analyticAt_id.add (analyticAt_const.mul (analyticAt_id.pow _)))
  obtain ⟨q, qa, hq⟩ := exists_pow_mul_of_isBigO Fa Go
  refine ⟨h, φ, q 0, ha, φa, h0, φ0, l, r, k0, a0, Ga, ?_⟩
  have qd : (fun z ↦ q z - q 0) =O[𝓝 0] fun z ↦ z := by
    simpa using qa.differentiableAt.hasDerivAt.isBigO_sub
  refine ((isBigO_refl (fun z : ℂ ↦ z ^ (2 * k + 1)) _).mul qd).congr' ?_ ?_
  · filter_upwards [hq] with z e
    rw [mul_sub, ← e]; ring
  · exact Eventually.of_forall fun z ↦ by ring

/-- Example: the second iterate `z - 2 z³ + z⁴` of `z ↦ -z + z²` (the parabolic point of `c = -3/4`, after a
translation) has two petals and a petal normal form -/
example : ∃ h φ : ℂ → ℂ, ∃ b, AnalyticAt ℂ h 0 ∧ AnalyticAt ℂ φ 0 ∧ h 0 = 0 ∧ φ 0 = 0 ∧
    (∀ᶠ z in 𝓝 0, φ (h z) = z) ∧ (∀ᶠ z in 𝓝 0, h (φ z) = z) ∧
    PetalGerm (φ ∘ (fun z ↦ z - 2 * z ^ 3 + z ^ 4) ∘ h) 2 (-2) b := by
  refine PetalGerm.normalize (by norm_num) (by norm_num) (by fun_prop) (by simp) ?_
  have e : (fun z : ℂ ↦ z - 2 * z ^ 3 + z ^ 4 - (z + -2 * z ^ (2 + 1))) = fun z ↦ z ^ (2 + 2) := by
    ext z; ring
  rw [e]
