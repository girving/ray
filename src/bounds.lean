-- Useful bounds

import analysis.special_functions.log.deriv
import data.complex.exponential_bounds
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import tactic.field_simp
import topology.metric_space.basic

import finset
import tactics

open complex (abs exp log I)
open filter (at_top)
open_locale real nnreal topology

-- A finset ℕ with only large elements
def late (N : finset ℕ) (m : ℕ) := ∀ n, n ∈ N → n ≥ m

def sdiff_late {m : ℕ} {B : finset ℕ} (A : finset ℕ) : B ≥ finset.range m → late (A \ B) m := begin
  intros Bm n nAB,
  rw finset.mem_sdiff at nAB,
  by_contradiction, simp at h,
  have nr := finset.mem_range.mpr h,
  have nB := finset.mem_of_subset Bm nr,
  finish
end

-- Summing a subset of a geometric series is ≤ the series sum
theorem partial_geometric_bound {a : ℝ} (N : finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1)
    : N.sum (λ n, a^n) ≤ (1 - a)⁻¹ := begin
  have pos : ∀ n, n ∉ N → 0 ≤ a^n, { intros n nN, exact pow_nonneg a0 n },
  exact sum_le_has_sum N pos (has_sum_geometric_of_lt_1 a0 a1),
end

-- Summing a subset of a scaled_geometric series is ≤ the series sum
theorem partial_scaled_geometric_bound {a : ℝ} (c : ℝ≥0) (N : finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1)
    : N.sum (λ n, (c : ℝ) * a^n) ≤ c * (1 - a)⁻¹ := begin
  rw ←finset.mul_sum, bound [partial_geometric_bound N a0 a1],
end

-- Summing a late part of a series is equivalent to summing a shifted series
lemma late_series_sum {m : ℕ} {N : finset ℕ} (h : late N m) (f : ℕ → ℝ)
    : N.sum f = (finset.image (λ n, n - m) N).sum (λ n, f (n + m)) := begin
  set Ns := finset.image (λ n, n - m) N,
  have NNs : N = finset.image (λ n, n + m) Ns, {
    apply finset.ext, intro k,
    rw [finset.image_image, finset.mem_image],
    simp,
    apply iff.intro, {
      intro kN, existsi k, apply and.intro,
      assumption, exact nat.sub_add_cancel (h k kN)
    }, {
      intro ha, rcases ha with ⟨a,aN,ak⟩,
      rw nat.sub_add_cancel (h a aN) at ak,
      rw ←ak, assumption
    }
  },
  rw NNs, apply finset.sum_image,
  intros a aN b bN, exact nat.add_right_cancel
end

-- late_series_sum, but forget the image set
lemma late_series_sum' {m : ℕ} {N : finset ℕ} (h : late N m) (f : ℕ → ℝ)
    : ∃ M : finset ℕ, N.sum f = M.sum (λ n, f (n + m)) := begin
  existsi finset.image (λ n, n - m) N,
  exact late_series_sum h f
end

-- Summing a late subset of a geometric series is even smaller
theorem late_geometric_bound {m : ℕ} {a : ℝ} {N : finset ℕ}
    (h : late N m) (a0 : a ≥ 0) (a1 : a < 1)
    : N.sum (λ n, a^n) ≤ a^m * (1 - a)⁻¹ := begin
  rcases late_series_sum' h (λ n, a^n) with ⟨M, L⟩,
  rw L, clear L, simp,
  have pa : (λ n, a^(n + m)) = (λ n, a^n * a^m), { apply funext, intro n, rw pow_add },
  calc M.sum (λ n, a^(n + m)) = M.sum (λ n, a^n * a^m) : by rw pa
  ... = M.sum (λ n, (λ n, a^n) n * a^m) : by simp
  ... = M.sum (λ n, a^n) * a^m : (@finset.sum_mul _ _ M (a^m) (λ n, a^n) _).symm
  ... ≤ (1 - a)⁻¹ * a^m : by bound [partial_geometric_bound M a0 a1]
  ... = a^m * (1 - a)⁻¹ : by ring
end

lemma finset_partition (A B : finset ℕ) : A = (A \ B) ∪ (A ∩ B) := begin
  apply finset.ext, intro a,
  apply iff.intro, {
    finish
  }, {
    rw [finset.mem_union, finset.mem_inter, finset.mem_sdiff],
    finish
  }
end

lemma finset_sum_partition (A B : finset ℕ) (f : ℕ → ℂ)
    : A.sum (λ n, f n) = (A \ B).sum (λ n, f n) + (A ∩ B).sum (λ n, f n) := begin
  have ha : A = (A \ B) ∪ (A ∩ B) := finset_partition A B,
  nth_rewrite 0 ha,
  exact finset.sum_union (finset.disjoint_sdiff_inter A B)
end

lemma sdiff_sdiff_disjoint (A B : finset ℕ) : disjoint (A \ B) (B \ A) :=
  finset.disjoint_of_subset_right (finset.sdiff_subset B A) finset.sdiff_disjoint

lemma symm_diff_union (A B : finset ℕ) : A ∆ B = A \ B ∪ B \ A :=
  by rw [symm_diff_def, finset.sup_eq_union]

-- Bound the difference of two finset sums based on their symmetric difference
theorem symm_diff_bound (A B : finset ℕ) (f : ℕ → ℂ)
    : dist (A.sum (λ n, f n)) (B.sum (λ n, f n)) ≤ (A ∆ B).sum (λ n, abs (f n)) := begin
  rw finset_sum_partition A B f,
  rw finset_sum_partition B A f,
  rw finset.inter_comm B A,
  rw dist_add_right ((A\B).sum (λn,f n)) ((B\A).sum (λn,f n)) ((A∩B).sum (λn,f n)),
  rw complex.dist_eq,
  transitivity (A \ B).sum (λ n, abs (f n)) + (B \ A).sum (λ n, abs (f n)), {
    have ha := finset_complex_abs_sum_le (A \ B) f,
    have hb := finset_complex_abs_sum_le (B \ A) f,
    calc abs ((A \ B).sum (λ n, f n) - (B \ A).sum (λ n, f n))
        ≤ abs ((A \ B).sum (λ n, f n)) + abs ((B \ A).sum (λ n, f n)) : complex.abs.sub_le' _ _
    ... ≤ (A \ B).sum (λ n, abs (f n)) + (B \ A).sum (λ n, abs (f n)) : by bound [ha, hb],
  }, {
    apply le_of_eq,
    rw [←finset.sum_union (sdiff_sdiff_disjoint A B), symm_diff_union]
  }
end

-- Symmetric differences of sets containing ranges are late
theorem symm_diff_late {A B : finset ℕ} {m : ℕ} (ha : A ≥ finset.range m) (hb : B ≥ finset.range m)
    : late (A ∆ B) m := begin
  intros n ab, 
  rw [symm_diff_def, finset.sup_eq_union, finset.mem_union] at ab,
  by_contradiction, simp at h,
  cases ab, {
    rw finset.mem_sdiff at ab,
    have h := finset.mem_of_subset hb (finset.mem_range.mpr h),
    finish
  }, {
    rw finset.mem_sdiff at ab,
    have h := finset.mem_of_subset ha (finset.mem_range.mpr h),
    finish
  }
end

lemma sub_near (a z : ℂ) : |abs (a - z) - abs a| ≤ abs z := begin
  rw abs_le, constructor, {
    simp,
    calc abs (a - z) + abs z ≥ |abs a - abs z| + abs z : by bound [complex.abs.abs_abv_sub_le_abv_sub  a z]
    ... ≥ abs a - abs z + abs z : by bound [le_abs_self (abs a - abs z)]
    ... = abs a : by simp,
  }, {
    calc abs (a - z) - abs a ≤ abs a + abs z - abs a : by bound
    ... = abs z : by simp,
  }
end

lemma add_near (a z : ℂ) : |abs (a + z) - abs a| ≤ abs z := begin
  have h := sub_near a (-z),
  simp at h,
  assumption
end

lemma near_one_avoids_negative_reals {z : ℂ} : abs (z - 1) < 1 → z.re > 0 ∨ z.im ≠ 0 := begin
  intro h, apply or.inl,
  have hr : (1 - z).re < 1, {
    calc (1 - z).re ≤ |(1 - z).re| : le_abs_self (1 - z).re
    ... ≤ abs (1 - z) : complex.abs_re_le_abs _
    ... = abs (z - 1) : by { rw ←complex.abs.map_neg (1 - z), simp }
    ... < 1 : h
  },
  simp at hr, assumption
end

lemma near_one_avoids_zero {z : ℂ} : abs (z - 1) < 1 → z ≠ 0 := begin
  intro h,
  have g := near_one_avoids_negative_reals h,
  by_contradiction, rw h at g, simp at g, assumption
end

theorem deriv_within.cid {z : ℂ} {s : set ℂ}
    (o : is_open s) (zs : z ∈ s) : deriv_within (λ z, z) s z = 1 :=
  deriv_within_id z s (is_open.unique_diff_within_at o zs)

theorem deriv_within.clog {f : ℂ → ℂ} {z : ℂ} {s : set ℂ}
    (o : is_open s) (zs : z ∈ s)
    (hf : differentiable_within_at ℂ f s z) (hx : (f z).re > 0 ∨ (f z).im ≠ 0)
    : deriv_within (λ z, log (f z)) s z = deriv_within f s z / f z := begin
  have hz := differentiable_within_at.has_deriv_within_at hf,
  have h := has_deriv_within_at.clog hz _,
  repeat { rw has_deriv_within_at.deriv_within },
  repeat { assumption <|> exact is_open.unique_diff_within_at o zs }
end

theorem differentiable_on.cpow {f : ℂ → ℂ} {g : ℂ → ℂ} {s : set ℂ}
    (df : differentiable_on ℂ f s)
    (dg : differentiable_on ℂ g s)
    (h : ∀ z, z ∈ s → 0 < (f z).re ∨ (f z).im ≠ 0)
    : differentiable_on ℂ (λ z, f z ^ g z) s := begin
  intros z zs,
  exact differentiable_within_at.cpow (df z zs) (dg z zs) (h z zs)
end

-- log (1+z) is small for small z (complex case, assuming strict inequality)
theorem weak_log1p_small {z : ℂ} {r : ℝ} (r1 : r < 1) (h : abs z < r)
    : abs (log (1+z)) ≤ 1 / (1 - r) * abs z := begin
  by_cases rp : r ≤ 0, {
    have a0 : abs z < 0 := lt_of_lt_of_le h rp,
    have a0' : abs z ≥ 0 := by bound,
    linarith
  }, {
    simp at rp,
    have L : ‖log (1+z) - log 1‖ ≤ 1 / (1-r) * ‖1+z-1‖, {
      set s := metric.ball (1 : ℂ) r,
      have o : is_open s := metric.is_open_ball,
      have s1z : (1+z) ∈ s, { simp, assumption },
      have s1 : (1 : ℂ) ∈ s := by { simp, assumption },
      have sp : ∀ w : ℂ, w ∈ s → w.re > 0 ∨ w.im ≠ 0, {
        intros w ws,
        apply near_one_avoids_negative_reals,
        simp at ws, rw complex.dist_eq at ws,
        calc abs (w - 1) < r : by assumption
        ... < 1 : r1
      },
      have sa : ∀ w : ℂ, w ∈ s → abs w ≥ 1 - r, {
        intros w ws, simp at ws, rw complex.dist_eq at ws,
        calc abs w = abs (1 + (w - 1)) : by abel
        ... ≥ abs (1 : ℂ) - abs (w - 1) : by bound
        ... ≥ abs (1 : ℂ) - r : by bound
        ... = 1 - r : by rw complex.abs.map_one
      },
      refine convex.norm_image_sub_le_of_norm_deriv_within_le _ _ _ s1 s1z, {
        exact differentiable_on.clog differentiable_on_id sp
      }, {
        intros w ws,
        rw [deriv_within.clog o ws, deriv_within.cid o ws],
        simp, rw inv_le, have aw := sa w ws, simp at aw, field_simp, assumption,
        have aw := sa w ws, linarith, norm_num,
        assumption,
        exact differentiable_within_at_id,
        exact sp w ws
      }, {
        exact convex_ball _ _
      }
    },
    simp at L, simp, assumption
  }
end

-- To show a ≤ b, it suffices to show a ≤ b + e for small positive e
lemma le_of_forall_small_le_add {a b t : ℝ}
    (tp : t > 0) (h : ∀ e, 0 < e → e < t → a ≤ b + e) : a ≤ b := begin
  apply le_of_forall_pos_lt_add,
  intros e ep,
  by_cases et : e ≥ t, {
    specialize h (t/2) (by bound) (by bound),
    calc a ≤ b + t/2 : h
    ... ≤ b + e/2 : by bound
    ... < b + e : by bound
  }, {
    simp at et,
    calc a ≤ b + e/2 : h (e/2) (by bound) (by linarith)
    ... < b + e : by bound
  }
end

-- 1 / (1 - x) ≤ 1 + 2*x for small positive x
theorem one_over_one_sub_le {x : ℝ} : 0 ≤ x → x ≤ 1/2 → 1 / (1 - x) ≤ 1 + 2*x := begin
  intros xp xh,
  have x1 : 1 - x > 0 := by linarith,
  rw div_le_iff x1,
  calc (1 + 2*x) * (1 - x) = 1 + x*(1 - 2*x) : by ring
  ... ≥ 1 + x*(1 - 2*(1/2)) : by bound
  ... = 1 : by ring,
end

-- Version of metric.continuous_at_iff.mp which provides an upper bound on the radius.
-- This makes downstream usage more convenient in some cases.
lemma metric.continuous_near {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (fc : continuous_at f z) (rp : r > 0)
    : ∀ e, e > 0 → ∃ s, 0 < s ∧ s ≤ r ∧ ∀ {w}, abs (w - z) < s → abs (f w - f z) < e := begin
  intros e ep,
  rcases metric.continuous_at_iff.mp fc e ep with ⟨s,sp,sc⟩,
  simp_rw complex.dist_eq at sc,
  by_cases sr : s ≤ r, { existsi s, exact ⟨sp,sr,λ w wr, sc wr⟩ },
  simp at sr, existsi r, refine ⟨rp, by bound, _⟩,
  intros w wr, refine @sc w _,
  transitivity r, assumption, assumption
end

-- Given z ≠ 0, we can find a slightly smaller nearby w
lemma slightly_smaller {z : ℂ} (nz : z ≠ 0) {r : ℝ} (rp : 0 < r)
    : ∃ w, abs (w - z) < r ∧ abs w < abs z := begin
  by_cases rz : abs z < r, {
    use 0, simp [rz, nz],
  },
  simp only [not_lt] at rz,
  have azp : abs z > 0 := complex.abs.pos nz,
  generalize ha : 1 - r / 2 / abs z = a,
  have a0 : a ≥ 0, {
    rw ←ha, refine sub_nonneg.mpr ((div_le_one azp).mpr _),
    refine trans _ rz,
    bound,
  },
  have a1 : a < 1, { rw ←ha, simp only [sub_lt_self_iff], positivity },
  generalize hw : ↑a * z = w,
  use w, constructor, {
    rw [←hw,←ha],
    simp only [complex.of_real_sub, complex.of_real_one, complex.of_real_div, complex.of_real_bit0],
    rw mul_sub_right_distrib,
    simp only [one_mul, sub_sub_cancel_left, absolute_value.map_neg, absolute_value.map_mul, map_div₀,
      complex.abs_of_real, complex.abs_two, complex.abs_abs, abs_of_pos rp, div_mul (r / 2),
      div_self (ne_of_gt azp), div_one],
    bound,
  }, {
    simp only [←hw, absolute_value.map_mul, complex.abs_of_real, abs_of_nonneg a0],
    calc a * abs z < 1 * abs z : mul_lt_mul_of_pos_right a1 azp
    ... = abs z : by ring
  },
end

-- There are smaller values nearby any z ≠ 0
lemma frequently_smaller {z : ℂ} (z0 : z ≠ 0) : ∃ᶠ w : ℂ in 𝓝 z, abs w < abs z := begin
  simp only [filter.frequently, metric.eventually_nhds_iff, not_exists, not_forall, not_not, complex.dist_eq],
  intros r rp, rcases slightly_smaller z0 rp with ⟨w,b,lt⟩, use [w,b,lt],
end

-- Turn a weak small theorem into a strong small theorem
lemma weak_to_strong_small {f : ℂ → ℂ} {z : ℂ} {r c : ℝ}
    (rp : r > 0) (cp : c > 0) (zr : abs z ≤ r) (fc : continuous_at f z)
    (h : ∀ z : ℂ, abs z < r → abs (f z) ≤ c * abs z)
    : abs (f z) ≤ c * abs z := begin
  by_cases nz : z = 0, { refine h z _, rw nz, simpa },
  apply le_of_forall_small_le_add zero_lt_one,
  intros e ep e1,
  rcases metric.continuous_near fc rp e ep with ⟨s,sp,sr,sc⟩,
  rcases slightly_smaller nz sp with ⟨w,wz,awz⟩,
  have wr : abs w < r := lt_of_lt_of_le awz zr,
  calc abs (f z) = abs (f w - (f w - f z)) : by abel
  ... ≤ abs (f w) + abs (f w - f z) : complex.abs.sub_le' _ _
  ... ≤ c * abs w + e : by bound [h w wr, sc wz]
  ... ≤ c * abs z + e : by bound,
end

-- log (1+z) is small for small z
theorem log1p_small {z : ℂ} (zs : abs z ≤ 1/2) : abs (log (1+z)) ≤ 2 * abs z := begin
  have rp : (1/2 : ℝ) > 0 := by norm_num,
  have cp : (2 : ℝ) > 0 := by norm_num,
  have fc : continuous_at (λ z, log (1 + z)) z, {
    apply continuous_at.clog, apply continuous_at.add,
    exact continuous_at_const, exact continuous_at_id,
    refine near_one_avoids_negative_reals _,
    simp, exact lt_of_le_of_lt zs (by bound)
  },
  apply weak_to_strong_small rp cp zs fc,
  intros w wr,
  have ws := @weak_log1p_small w (1/2) (by bound) wr,
  have t : 1 / (1 - 1 / 2) = (2 : ℝ) := by norm_num,
  rw t at ws, simpa
end

-- log (1+x) is small for small x
theorem real.log1p_small {x : ℝ} (xs : |x| ≤ 1/2) : |real.log (1+x)| ≤ 2 * |x| := begin
  set z := (x : ℂ),
  have zx : abs z = |x| := complex.abs_of_real _,
  simp only [←complex.log_of_real_re, ←zx] at xs ⊢,
  refine trans (trans (complex.abs_re_le_abs _) _) (log1p_small xs),
  simp only [complex.of_real_add, complex.of_real_one],
end

-- log z is small for z ≈ 1
theorem log_small {z : ℂ} (zs : abs (z - 1) ≤ 1/2) : abs (log z) ≤ 2 * abs (z - 1) := begin
  generalize zw : z - 1 = z1, have wz : z = 1 + z1, { rw ←zw, ring },
  rw wz, refine log1p_small _, rw ←zw, assumption
end

-- exp z ≈ 1 for z ≈ 0, strict inequality version
theorem weak_exp_small {z : ℂ} (h : abs z < 1) : abs (exp z - 1) ≤ 2 * abs z := begin
  have hr : 0 ≤ (1 : ℝ) := by norm_num,
  have L := complex.locally_lipschitz_exp hr (by bound) 0 z (by { simp, assumption }),
  simp at L,
  have t : 1 + 1 = (2 : ℝ) := by norm_num,
  rw t at L, assumption
end

-- exp z ≈ 1 for z ≈ 0
theorem exp_small {z : ℂ} (zs : abs z ≤ 1) : abs (exp z - 1) ≤ 2 * abs z := begin
  have rp : (1 : ℝ) > 0 := by norm_num,
  have cp : (2 : ℝ) > 0 := by norm_num,
  have fc : continuous_at (λ z, exp z - 1) z, {
    apply continuous_at.sub, apply continuous_at.cexp,
    exact continuous_at_id, exact continuous_at_const
  },
  apply weak_to_strong_small rp cp zs fc,
  intros w wr, simp, 
  exact weak_exp_small wr,
end

-- abs ((1+z)^w - 1) ≤ 2 * abs (zw) for small z,w
theorem pow1p_small {z w : ℂ} (zs : abs z ≤ 1/2) (ws : abs w ≤ 1)
    : abs ((1+z)^w - 1) ≤ 4 * abs z * abs w := begin
  have z1 : 1 + z ≠ 0, {
    rw ←complex.abs.ne_zero_iff, apply ne_of_gt,
    calc abs (1 + z) ≥ abs (1 : ℂ) - abs z : by bound
    ... ≥ abs (1 : ℂ) - 1/2 : by bound
    ... > 0 : by norm_num
  },
  rw complex.cpow_def_of_ne_zero z1,
  have ls := log1p_small zs,
  have eas : abs (log (1 + z) * w) ≤ 1, {
    rw complex.abs.map_mul,
    calc abs (log (1 + z)) * abs w ≤ 2 * abs z * abs w : by bound
    ... ≤ 2 * (1/2) * 1 : by bound
    ... = 1 : by norm_num
  },
  have es := exp_small eas,
  rw [complex.abs.map_mul, ←mul_assoc] at es,
  transitivity 2 * abs (log (1 + z)) * abs w,
  assumption,
  calc 2 * abs (log (1 + z)) * abs w ≤ 2 * (2 * abs z) * abs w : by bound
  ... = 4 * abs z * abs w : by ring,
end

-- abs (z^w - 1) ≤ 2 * abs ((z-1)w) for z ≈ 1, w small
theorem pow_small {z w : ℂ} (zs : abs (z - 1) ≤ 1/2) (ws : abs w ≤ 1)
    : abs (z^w - 1) ≤ 4 * abs (z - 1) * abs w := begin
  generalize zw : z - 1 = z1, have wz : z = 1 + z1, { rw ←zw, ring },
  rw wz, refine pow1p_small _ ws, rw ←zw, assumption,
end

-- a + b ≠ 0 from abs b < abs a
lemma add_ne_zero_of_abs_lt {a b : ℂ} (h : abs b < abs a) : a + b ≠ 0 := begin
  have e : a + b = a - (-b) := by abel,
  rw [e, sub_ne_zero], contrapose h, simp only [not_not] at h,
  simp only [h, not_lt, absolute_value.map_neg],
end 

-- e < 3
lemma real.exp_one_lt_3 : real.exp 1 < 3 := trans real.exp_one_lt_d9 (by norm_num)

-- log (a + b) = log a + log (1 + b/a)
lemma log_add (a b : ℝ) (a0 : 0 < a) (ab0 : 0 < a + b) : real.log (a + b) = real.log a + real.log (1 + b/a) := begin
  have d0 : 0 < 1 + b/a, { field_simp [ne_of_gt a0], bound },
  rw [←real.log_mul (ne_of_gt a0) (ne_of_gt d0), left_distrib, mul_one, mul_div_cancel' _ (ne_of_gt a0)],
end

-- log (abs (a + b)) = log (abs a) + log (abs (1 + b/a))
lemma log_abs_add (a b : ℂ) (a0 : a ≠ 0) (ab0 : a + b ≠ 0)
    : real.log (abs (a + b)) = real.log (abs a) + real.log (abs (1 + b/a)) := begin
  have d0 : 1 + b/a ≠ 0 := by field_simp [a0, ab0],
  have a0' : abs a ≠ 0 := complex.abs.ne_zero a0,
  have d0' : abs (1 + b/a) ≠ 0 := complex.abs.ne_zero d0,
  rw [←real.log_mul a0' d0', ←complex.abs.map_mul, left_distrib, mul_one, mul_div_cancel' _ a0],
end

-- e^(1/4) ≤ 4/3
lemma real.exp_forth_lt_four_thirds : real.exp (1/4) < 4/3 := begin
  rw [←real.exp_one_rpow, one_div, ←@real.pow_nat_rpow_nat_inv (4/3) (by norm_num) 4 (by norm_num),
    nat.cast_bit0, nat.cast_bit0, nat.cast_one],
  refine real.rpow_lt_rpow (le_of_lt (real.exp_pos _)) _ (by norm_num),
  exact trans real.exp_one_lt_d9 (by norm_num),
end

-- Bound abs (product - 1) in terms of abs (sum)
lemma dist_prod_one_le_abs_sum {f : ℕ → ℂ} {s : finset ℕ} {c : ℝ} (le : s.sum (λ n, abs (f n - 1)) ≤ c) (c1 : c ≤ 1/2)
    : abs (s.prod f - 1) ≤ 4*c := begin
  set g := λ n, complex.log (f n),
  have b : ∀ n, n ∈ s → abs (f n - 1) ≤ c, {
    intros n m, refine trans _ le,
    exact @finset.single_le_sum _ _ _ (λ n, abs (f n - 1)) _ (λ _ _, complex.abs.nonneg _) _ m,
  },
  have f0 : ∀ n, n ∈ s → f n ≠ 0, {
    intros n m, specialize b n m, contrapose b, simp only [not_not] at b,
    simp only [b, not_le], norm_num, linarith,
  },
  have a0 : ∀ n, n ∈ s → abs (f n) ≠ 0 := λ n m, complex.abs.ne_zero_iff.mpr (f0 n m),
  have sg : abs (s.sum g) ≤ 2*c, {
    refine trans (complex.abs.sum_le _ _) _,
    refine trans (finset.sum_le_sum (λ n m, log_small (trans (b n m) c1))) _,
    rw ←finset.mul_sum, linarith,
  },
  have e : s.prod f = complex.exp (s.sum g), {
    rw complex.exp_sum, apply finset.prod_congr rfl, intros n m, rw complex.exp_log (f0 n m),
  },
  rw e, exact trans (exp_small (by linarith)) (by linarith),
end

