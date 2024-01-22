import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.MetricSpace.Basic
import Ray.Misc.AbsoluteValue
import Ray.Misc.Finset
import Ray.Tactic.Bound

/-!
## Assorted bound lemmas
-/

open Classical
open Complex (abs exp log I)
open Filter (atTop)
open scoped Real NNReal Topology symmDiff

/-- A `Finset ℕ` with only large elements -/
def Late (N : Finset ℕ) (m : ℕ) :=
  ∀ n, n ∈ N → n ≥ m

lemma late_iff_disjoint_range {m : ℕ} {A : Finset ℕ} : Late A m ↔ Disjoint A (Finset.range m) := by
  simp only [Late, ge_iff_le, Finset.disjoint_iff_ne, Finset.mem_range, ne_eq]; constructor
  · intro h n na b bm; linarith [h _ na]
  · intro h n na; specialize h n na n; simpa [not_true, imp_false, not_lt] using h

lemma sdiff_late {m : ℕ} {B : Finset ℕ} (A : Finset ℕ) : B ≥ Finset.range m → Late (A \ B) m := by
  intro Bm n nAB
  rw [Finset.mem_sdiff] at nAB
  by_contra h; simp only [not_le] at h
  have nr := Finset.mem_range.mpr h
  have nB := Finset.mem_of_subset Bm nr
  exact nAB.2 nB

/-- Summing a subset of a geometric series is ≤ the series sum -/
theorem partial_geometric_bound {a : ℝ} (N : Finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1) :
    N.sum (fun n ↦ a^n) ≤ (1 - a)⁻¹ :=
  haveI pos : ∀ n, n ∉ N → 0 ≤ a^n := by intro n _; bound
  sum_le_hasSum N pos (hasSum_geometric_of_lt_1 a0 a1)

theorem partial_scaled_geometric_bound {a : ℝ} (c : ℝ≥0) (N : Finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1)
    : N.sum (fun n ↦ (c:ℝ) * a^n) ≤ c * (1 - a)⁻¹ := by
  rw [←Finset.mul_sum]
  bound [partial_geometric_bound N a0 a1]

/-- Summing a late part of a series is equivalent to summing a shifted series -/
theorem late_series_sum {m : ℕ} {N : Finset ℕ} (h : Late N m) (f : ℕ → ℝ) :
    N.sum f = (N.image (fun n ↦ n - m)).sum (fun n ↦ f (n + m)) := by
  set Ns := Finset.image (fun n ↦ n - m) N
  have NNs : N = Finset.image (fun n ↦ n + m) Ns := by
    apply Finset.ext; intro k
    rw [Finset.image_image, Finset.mem_image]
    simp
    apply Iff.intro
    · intro kN; exists k; apply And.intro
      assumption; exact Nat.sub_add_cancel (h k kN)
    · intro ha; rcases ha with ⟨a, aN, ak⟩
      rw [Nat.sub_add_cancel (h a aN)] at ak
      rw [← ak]; assumption
  rw [NNs]; apply Finset.sum_image
  intro a _ b _; exact Nat.add_right_cancel

/-- late_series_sum, but forgetting the image set -/
theorem late_series_sum' {m : ℕ} {N : Finset ℕ} (h : Late N m) (f : ℕ → ℝ) :
    ∃ M : Finset ℕ, N.sum f = M.sum (fun n ↦ f (n + m)) := by
  exists Finset.image (fun n ↦ n - m) N
  exact late_series_sum h f

theorem late_geometric_bound {m : ℕ} {a : ℝ} {N : Finset ℕ} (h : Late N m) (a0 : 0 ≤ a) (a1 : a < 1)
    : N.sum (fun n ↦ a^n) ≤ a^m * (1 - a)⁻¹ := by
  rcases late_series_sum' h (fun n ↦ a^n) with ⟨M,L⟩
  rw [L]; clear L
  have pa : (fun n ↦ a^(n + m)) = (fun n ↦ a^n * a^m) := by apply funext; intro n; rw [pow_add]
  calc
    M.sum (fun n ↦ a^(n + m)) = M.sum (fun n ↦ a^n * a^m) := by rw [ pa ]
    _ = M.sum (fun n ↦ a^n) * a^m := (Finset.sum_mul _ _ _).symm
    _ ≤ (1 - a)⁻¹ * a^m := by bound [partial_geometric_bound M a0 a1]
    _ = a^m * (1 - a)⁻¹ := by ring

theorem finset_partition (A B : Finset ℕ) : A = A \ B ∪ A ∩ B := by
  apply Finset.ext
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  intro x; constructor
  · intro a
    by_cases b : x ∈ B
    · right; use a,b
    · left; use a,b
  · intro h
    cases' h with m m
    repeat exact m.1

theorem finset_sum_partition (A B : Finset ℕ) (f : ℕ → ℂ) :
    A.sum f = (A \ B).sum f + (A ∩ B).sum f := by
  have ha : A = A \ B ∪ A ∩ B := finset_partition A B
  nth_rw 1 [ha]
  exact Finset.sum_union (Finset.disjoint_sdiff_inter A B)

theorem sdiff_sdiff_disjoint (A B : Finset ℕ) : Disjoint (A \ B) (B \ A) :=
  Finset.disjoint_of_subset_right (Finset.sdiff_subset B A) Finset.sdiff_disjoint

theorem symmDiff_union (A B : Finset ℕ) : A ∆ B = A \ B ∪ B \ A := by
  rw [symmDiff_def, Finset.sup_eq_union]

theorem symmDiff_bound (A B : Finset ℕ) (f : ℕ → ℂ) :
    dist (A.sum f) (B.sum f) ≤ (A ∆ B).sum (fun n ↦ abs (f n)) := by
  rw [finset_sum_partition A B f, finset_sum_partition B A f, Finset.inter_comm B A]
  rw [dist_add_right ((A \ B).sum f) ((B \ A).sum f) ((A ∩ B).sum f)]
  rw [Complex.dist_eq]
  trans (A \ B).sum (fun n ↦ abs (f n)) + (B \ A).sum (fun n ↦ abs (f n))
  · have ha := finset_complex_abs_sum_le (A \ B) f
    have hb := finset_complex_abs_sum_le (B \ A) f
    calc abs ((A \ B).sum f - (B \ A).sum f)
      _ ≤ abs ((A \ B).sum f) + abs ((B \ A).sum f) := Complex.abs.sub_le' _ _
      _ ≤ (A \ B).sum (fun n ↦ abs (f n)) + (B \ A).sum (fun n ↦ abs (f n)) := by bound
  · apply le_of_eq
    rw [←Finset.sum_union (sdiff_sdiff_disjoint A B), symmDiff_union]

/-- Symmetric differences of sets containing ranges are late -/
theorem symmDiff_late {A B : Finset ℕ} {m : ℕ} (ha : A ≥ Finset.range m) (hb : B ≥ Finset.range m) :
    Late (A ∆ B) m := by
  intro n ab
  rw [symmDiff_def, Finset.sup_eq_union, Finset.mem_union] at ab
  by_contra h; simp at h
  cases' ab with a b
  · rw [Finset.mem_sdiff] at a
    have h := Finset.mem_of_subset hb (Finset.mem_range.mpr h)
    exact a.2 h
  · rw [Finset.mem_sdiff] at b
    have h := Finset.mem_of_subset ha (Finset.mem_range.mpr h)
    exact b.2 h

/-- `a - z` has similar absolute value to `a` for small `z` -/
theorem sub_near (a z : ℂ) : |abs (a - z) - abs a| ≤ abs z := by
  rw [abs_le]; constructor
  · simp only [neg_le_sub_iff_le_add]
    calc abs (a - z) + abs z
      _ ≥ |abs a - abs z| + abs z := by bound [Complex.abs.abs_abv_sub_le_abv_sub a z]
      _ ≥ abs a - abs z + abs z := by bound [le_abs_self (abs a - abs z)]
      _ = abs a := by simp only [sub_add_cancel]
  · calc
      abs (a - z) - abs a ≤ abs a + abs z - abs a := by bound
      _ = abs z := by simp only [add_sub_cancel']

theorem add_near (a z : ℂ) : |abs (a + z) - abs a| ≤ abs z := by
  have h := sub_near a (-z)
  simp only [sub_neg_eq_add, map_neg_eq_map] at h
  assumption

theorem near_one_avoids_negative_reals {z : ℂ} : abs (z - 1) < 1 → z.re > 0 ∨ z.im ≠ 0 := by
  intro h; apply Or.inl
  have hr : (1 - z).re < 1 := by
    calc
      (1 - z).re ≤ |(1 - z).re| := le_abs_self (1 - z).re
      _ ≤ abs (1 - z) := (Complex.abs_re_le_abs _)
      _ = abs (z - 1) := by rw [←Complex.abs.map_neg (1 - z)]; simp only [neg_sub]
      _ < 1 := h
  simp only [Complex.sub_re, Complex.one_re, sub_lt_self_iff] at hr
  assumption

theorem near_one_avoids_zero {z : ℂ} : abs (z - 1) < 1 → z ≠ 0 := by
  intro h
  have g := near_one_avoids_negative_reals h
  by_contra h; rw [h] at g
  simp only [Complex.zero_re, lt_self_iff_false, Complex.zero_im, ne_eq, not_true, or_self] at g

theorem derivWithin.cid {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s) :
    derivWithin (fun z ↦ z) s z = 1 :=
  derivWithin_id z s (IsOpen.uniqueDiffWithinAt o zs)

theorem derivWithin.clog {f : ℂ → ℂ} {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s)
    (hf : DifferentiableWithinAt ℂ f s z) (hx : (f z).re > 0 ∨ (f z).im ≠ 0) :
    derivWithin (fun z ↦ Complex.log (f z)) s z = derivWithin f s z / f z := by
  have hz := DifferentiableWithinAt.hasDerivWithinAt hf
  have h := HasDerivWithinAt.clog hz hx
  have u := o.uniqueDiffWithinAt (𝕜 := ℂ) zs
  rw [HasDerivWithinAt.derivWithin h u]

theorem DifferentiableOn.cpow {f : ℂ → ℂ} {g : ℂ → ℂ} {s : Set ℂ} (df : DifferentiableOn ℂ f s)
    (dg : DifferentiableOn ℂ g s) (h : ∀ z, z ∈ s → 0 < (f z).re ∨ (f z).im ≠ 0) :
    DifferentiableOn ℂ (fun z ↦ f z ^ g z) s := by
  intro z zs
  exact DifferentiableWithinAt.cpow (df z zs) (dg z zs) (h z zs)

theorem weak_log1p_small {z : ℂ} {r : ℝ} (r1 : r < 1) (h : abs z < r) :
    abs (log (1 + z)) ≤ 1/(1 - r) * abs z := by
  by_cases rp : r ≤ 0
  · have a0 : abs z < 0 := lt_of_lt_of_le h rp
    have a0' : abs z ≥ 0 := by bound
    exfalso
    linarith [a0, a0']
  · simp only [not_le] at rp
    have L : ‖log (1 + z) - log 1‖ ≤ 1/(1 - r) * ‖1 + z - 1‖ := by
      set s := Metric.ball (1:ℂ) r
      have o : IsOpen s := Metric.isOpen_ball
      have s1z : 1 + z ∈ s := by simp; assumption
      have s1 : (1:ℂ) ∈ s := by simp; assumption
      have sp : ∀ w : ℂ, w ∈ s → w.re > 0 ∨ w.im ≠ 0 := by
        intro w ws
        apply near_one_avoids_negative_reals
        simp only [Metric.mem_ball, Complex.dist_eq] at ws
        calc abs (w - 1) < r := by assumption
          _ < 1 := r1
      have sa : ∀ w : ℂ, w ∈ s → abs w ≥ 1 - r := by
        intro w ws
        simp only [Metric.mem_ball, Complex.dist_eq] at ws
        calc abs w = abs (1 + (w - 1)) := by ring_nf
          _ ≥ abs (1 : ℂ) - abs (w - 1) := by bound
          _ ≥ abs (1 : ℂ) - r := by bound
          _ = 1 - r := by rw [Complex.abs.map_one]
      refine Convex.norm_image_sub_le_of_norm_derivWithin_le ?_ ?_ ?_ s1 s1z
      · exact DifferentiableOn.clog differentiableOn_id sp
      · intro w ws
        rw [derivWithin.clog o ws, derivWithin.cid o ws]
        simp only [one_div, norm_inv, Complex.norm_eq_abs]
        rw [inv_le]
        have aw := sa w ws; simp at aw; field_simp; assumption
        have aw := sa w ws; linarith; norm_num; assumption
        exact differentiableWithinAt_id
        exact sp w ws
      · exact convex_ball _ _
    simp only [Complex.log_one, sub_zero, Complex.norm_eq_abs, one_div, add_sub_cancel'] at L
    simpa only [one_div, ge_iff_le]

theorem le_of_forall_small_le_add {a b t : ℝ} (tp : 0 < t) (h : ∀ e, 0 < e → e < t → a ≤ b + e) :
    a ≤ b := by
  apply le_of_forall_pos_lt_add
  intro e ep
  by_cases et : e ≥ t
  · specialize h (t/2) (by bound) (by bound)
    calc a ≤ b + t/2 := h
      _ ≤ b + e/2 := by bound
      _ < b + e := by bound
  · simp only [ge_iff_le, not_le] at et
    calc a ≤ b + e/2 := h (e/2) (by bound) (by linarith)
      _ < b + e := by bound

theorem one_over_one_sub_le {x : ℝ} : 0 ≤ x → x ≤ 1/2 → 1/(1 - x) ≤ 1 + 2*x := by
  intro xp xh
  have x1 : 1 - x > 0 := by linarith
  rw [div_le_iff x1]
  calc (1 + 2*x) * (1 - x) = 1 + x * (1 - 2*x) := by ring
    _ ≥ 1 + x * (1 - 2 * (1/2)) := by bound
    _ = 1 := by ring

theorem Metric.continuous_near {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (fc : ContinuousAt f z) (rp : 0 < r)
    : ∀ e, 0 < e → ∃ s, 0 < s ∧ s ≤ r ∧ ∀ {w} , abs (w - z) < s → abs (f w - f z) < e := by
  intro e ep
  rcases Metric.continuousAt_iff.mp fc e ep with ⟨s,sp,sc⟩
  simp_rw [ Complex.dist_eq ] at sc
  by_cases sr : s ≤ r; exists s
  simp only [not_le] at sr
  exists r
  refine' ⟨rp, by bound, _⟩
  intro w wr
  refine' @sc w _
  trans r; assumption; assumption

theorem slightly_smaller {z : ℂ} (nz : z ≠ 0) {r : ℝ} (rp : 0 < r) :
    ∃ w, abs (w - z) < r ∧ abs w < abs z := by
  by_cases rz : abs z < r
  · use 0
    simp only [zero_sub, map_neg_eq_map, rz, map_zero, AbsoluteValue.pos_iff, ne_eq, nz,
      not_false_eq_true, and_self]
  simp only [not_lt] at rz
  have azp : 0 < abs z := Complex.abs.pos nz
  generalize ha : 1 - r/2/abs z = a
  have a0 : 0 ≤ a := by rw [←ha, sub_nonneg, div_le_one azp]; exact _root_.trans (by bound) rz
  have a1 : a < 1 := by rw [←ha, sub_lt_self_iff]; positivity
  generalize hw : ↑a * z = w
  use w; constructor
  · rw [←hw,←ha]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_bit0]
    rw [mul_sub_right_distrib]
    simp only [one_mul, sub_sub_cancel_left, AbsoluteValue.map_neg, AbsoluteValue.map_mul, map_div₀,
      Complex.abs_ofReal, Complex.abs_two, Complex.abs_abs, abs_of_pos rp, div_mul (r/2),
      div_mul_cancel _ azp.ne', div_one, abs_two]
    bound
  · simp only [←hw, AbsoluteValue.map_mul, Complex.abs_ofReal, abs_of_nonneg a0]
    calc a * abs z < 1 * abs z := mul_lt_mul_of_pos_right a1 azp
      _ = abs z := by ring

/-- There are smaller values nearby any z ≠ 0 -/
theorem frequently_smaller {z : ℂ} (z0 : z ≠ 0) : ∃ᶠ w : ℂ in 𝓝 z, abs w < abs z := by
  simp only [Filter.Frequently, Metric.eventually_nhds_iff, not_exists, not_forall, not_not,
    Complex.dist_eq, not_and]
  intro r rp; rcases slightly_smaller z0 rp with ⟨w, b, lt⟩; use w, b, lt

theorem weak_to_strong_small {f : ℂ → ℂ} {z : ℂ} {r c : ℝ} (rp : r > 0) (cp : c > 0)
    (zr : abs z ≤ r) (fc : ContinuousAt f z) (h : ∀ z : ℂ, abs z < r → abs (f z) ≤ c * abs z) :
    abs (f z) ≤ c * abs z := by
  by_cases nz : z = 0; · refine' h z _; rw [nz]; simpa
  apply le_of_forall_small_le_add zero_lt_one
  intro e ep _
  rcases Metric.continuous_near fc rp e ep with ⟨s,sp,_,sc⟩
  rcases slightly_smaller nz sp with ⟨w,wz,awz⟩
  have wr : abs w < r := lt_of_lt_of_le awz zr
  calc abs (f z) = abs (f w - (f w - f z)) := by ring_nf
    _ ≤ abs (f w) + abs (f w - f z) := Complex.abs.sub_le' _ _
    _ ≤ c * abs w + e := by bound [h w wr, sc wz]
    _ ≤ c * abs z + e := by bound

theorem log1p_small' {z : ℂ} {r : ℝ} (r1 : r < 1) (zr : abs z ≤ r) :
    abs (log (1 + z)) ≤ 1/(1 - r) * abs z := by
  by_cases r0 : r ≤ 0
  · have z0 := le_antisymm (le_trans zr r0) (Complex.abs.nonneg _)
    simp only [map_eq_zero] at z0
    simp only [z0, add_zero, Complex.log_one, map_zero, r0, sub_zero, ne_eq, one_ne_zero,
      not_false_eq_true, div_self, mul_zero, le_refl]
  simp only [not_le] at r0
  have fc : ContinuousAt (fun z ↦ log (1 + z)) z := by
    apply ContinuousAt.clog; apply ContinuousAt.add; exact continuousAt_const; exact continuousAt_id
    refine' near_one_avoids_negative_reals _
    simp only [add_sub_cancel', lt_of_le_of_lt zr r1]
  apply weak_to_strong_small r0 (by bound) zr fc
  intro w wr
  exact @weak_log1p_small w r (by bound) wr

theorem log1p_small {z : ℂ} (zs : abs z ≤ 1/2) : abs (log (1 + z)) ≤ 2 * abs z :=
  le_trans (log1p_small' (by norm_num) zs) (le_of_eq (by norm_num))

/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small' {x r : ℝ} (r1 : r < 1) (xr : |x| ≤ r) :
    |Real.log (1 + x)| ≤ 1 / (1-r) * |x| := by
  set z := (x : ℂ)
  have zx : abs z = |x| := Complex.abs_ofReal _
  simp only [← Complex.log_ofReal_re, ← zx] at xr ⊢
  refine' _root_.trans (_root_.trans (Complex.abs_re_le_abs _) _) (_root_.log1p_small' r1 xr)
  simp only [Complex.ofReal_add, Complex.ofReal_one, le_refl]

/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small {x : ℝ} (xr : |x| ≤ 1/2) : |Real.log (1 + x)| ≤ 2 * |x| :=
  le_trans (Real.log1p_small' (by norm_num) xr) (le_of_eq (by norm_num))

/-- `log z` is small for `z ≈ 1` -/
theorem log_small {z : ℂ} (zs : abs (z - 1) ≤ 1 / 2) : abs (log z) ≤ 2 * abs (z - 1) := by
  generalize zw : z - 1 = z1; have wz : z = 1 + z1 := by rw [← zw]; ring
  rw [wz]; refine' log1p_small _; rw [← zw]; assumption

theorem weak_exp_small {z : ℂ} (h : abs z < 1) : abs (exp z - 1) ≤ 2 * abs z := by
  have hr : 0 ≤ (1 : ℝ) := by norm_num
  have L := Complex.locally_lipschitz_exp hr (by bound) 0 z
    (by simpa only [sub_zero, Complex.norm_eq_abs])
  simp only [Complex.exp_zero, Complex.norm_eq_abs, norm_one, mul_one, sub_zero] at L
  have t : 1 + 1 = (2 : ℝ) := by norm_num
  rw [t] at L; assumption

/-- `exp z ≈ 1` for `z ≈ 0` -/
theorem exp_small {z : ℂ} (zs : abs z ≤ 1) : abs (exp z - 1) ≤ 2 * abs z := by
  have rp : (1 : ℝ) > 0 := by norm_num
  have cp : (2 : ℝ) > 0 := by norm_num
  have fc : ContinuousAt (fun z ↦ exp z - 1) z := by
    apply ContinuousAt.sub; apply ContinuousAt.cexp
    exact continuousAt_id; exact continuousAt_const
  apply weak_to_strong_small rp cp zs fc
  intro w wr; exact weak_exp_small wr

theorem pow1p_small {z w : ℂ} (zs : abs z ≤ 1/2) (ws : abs w ≤ 1) :
    abs ((1 + z) ^ w - 1) ≤ 4 * abs z * abs w := by
  have z1 : 1 + z ≠ 0 := by
    rw [←Complex.abs.ne_zero_iff]; apply ne_of_gt
    calc abs (1 + z) ≥ abs (1 : ℂ) - abs z := by bound
      _ ≥ abs (1 : ℂ) - 1/2 := by bound
      _ > 0 := by norm_num
  rw [Complex.cpow_def_of_ne_zero z1]
  have ls := log1p_small zs
  have eas : abs (log (1 + z) * w) ≤ 1 := by
    rw [Complex.abs.map_mul]
    calc abs (log (1 + z)) * abs w ≤ 2 * abs z * abs w := by bound
      _ ≤ 2 * (1/2) * 1 := by bound
      _ = 1 := by norm_num
  have es := exp_small eas
  rw [Complex.abs.map_mul, ←mul_assoc] at es
  trans 2 * abs (log (1 + z)) * abs w
  exact es
  calc 2 * abs (log (1 + z)) * abs w ≤ 2 * (2 * abs z) * abs w := by bound
    _ = 4 * abs z * abs w := by ring

/-- `abs (z^w - 1) ≤ 2 * abs ((z-1)w)` for `z ≈ 1`, `w` small -/
theorem pow_small {z w : ℂ} (zs : abs (z - 1) ≤ 1 / 2) (ws : abs w ≤ 1) :
    abs (z ^ w - 1) ≤ 4 * abs (z - 1) * abs w := by
  generalize zw : z - 1 = z1; have wz : z = 1 + z1 := by rw [← zw]; ring
  rw [wz]; refine' pow1p_small _ ws; rw [← zw]; assumption

/-- `a + b ≠ 0` from `abs b < abs a` -/
theorem add_ne_zero_of_abs_lt {a b : ℂ} (h : abs b < abs a) : a + b ≠ 0 := by
  have e : a + b = a - -b := by abel
  rw [e, sub_ne_zero]; contrapose h; simp only [not_not] at h
  simp only [h, not_lt, AbsoluteValue.map_neg, le_refl]

/-- `e < 3` -/
theorem Real.exp_one_lt_3 : Real.exp 1 < 3 :=
  _root_.trans Real.exp_one_lt_d9 (by norm_num)

theorem log_add (a b : ℝ) (a0 : 0 < a) (ab0 : 0 < a + b) :
    Real.log (a + b) = Real.log a + Real.log (1 + b/a) := by
  have d0 : 0 < 1 + b/a := by field_simp [a0.ne']; bound
  rw [←Real.log_mul a0.ne' d0.ne', left_distrib, mul_one, mul_div_cancel' _ a0.ne']

/-- `log (abs (a + b)) = log (abs a) + log (abs (1 + b/a))` -/
theorem log_abs_add (a b : ℂ) (a0 : a ≠ 0) (ab0 : a + b ≠ 0) :
    Real.log (abs (a + b)) = Real.log (abs a) + Real.log (abs (1 + b/a)) := by
  have d0 : 1 + b/a ≠ 0 := by field_simp [a0, ab0]
  have a0' : abs a ≠ 0 := Complex.abs.ne_zero a0
  have d0' : abs (1 + b / a) ≠ 0 := Complex.abs.ne_zero d0
  rw [←Real.log_mul a0' d0', ←Complex.abs.map_mul, left_distrib, mul_one, mul_div_cancel' _ a0]

/-- `e^(1/4) ≤ 4/3` -/
theorem Real.exp_forth_lt_four_thirds : Real.exp (1/4) < 4/3 := by
  rw [←Real.exp_one_rpow, one_div, ←@Real.pow_rpow_inv_natCast (4/3) 4 (by norm_num) (by norm_num)]
  refine' Real.rpow_lt_rpow (Real.exp_pos _).le _ (by norm_num)
  exact _root_.trans Real.exp_one_lt_d9 (by norm_num)

/-- Bound `abs (product - 1)` in terms of `abs (sum)` -/
theorem dist_prod_one_le_abs_sum {f : ℕ → ℂ} {s : Finset ℕ} {c : ℝ}
    (le : s.sum (fun n ↦ abs (f n - 1)) ≤ c) (c1 : c ≤ 1/2) : abs (s.prod f - 1) ≤ 4 * c := by
  set g := fun n ↦ Complex.log (f n)
  have b : ∀ n, n ∈ s → abs (f n - 1) ≤ c := by
    intro n m; refine' _root_.trans _ le
    exact Finset.single_le_sum (f := fun n ↦ abs (f n - 1)) (fun _ _ ↦ Complex.abs.nonneg _) m
  have f0 : ∀ n, n ∈ s → f n ≠ 0 := by
    intro n m; specialize b n m; contrapose b; simp only [not_not] at b
    simp only [b, not_le]; norm_num; linarith
  have sg : abs (s.sum g) ≤ 2 * c := by
    refine' _root_.trans (Complex.abs.sum_le _ _) _
    refine' _root_.trans (Finset.sum_le_sum (fun n m ↦ log_small (_root_.trans (b n m) c1))) _
    rw [← Finset.mul_sum]; bound
  have e : s.prod f = Complex.exp (s.sum g) := by
    rw [Complex.exp_sum]; apply Finset.prod_congr rfl
    intro n m; rw [Complex.exp_log (f0 n m)]
  rw [e]; exact _root_.trans (exp_small (by linarith)) (by linarith)
