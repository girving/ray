module
public import Ray.Multibrot.Defs
import Mathlib.Tactic.Cases
import Ray.Analytic.Series
import Ray.Misc.Bound
import Ray.Misc.Bounds
import Ray.Misc.Cobounded
import Ray.Multibrot.Basic
import Ray.Multibrot.D
import Ray.Multibrot.Log1p
import Ray.Multibrot.Specific

/-!
## Effective bounds on Multibrot iterates

We derive effective bounds and estimates for the growth rate of the Multibrot iteration
`z ← z^d + c`, for downstream use in theoretical results and numerical calculation.  Theoretical
results such as Multibrot connectness need only weak bounds, but numerical want them to be as tight
as possible, so we put significant effort towards tightening.  However, we strive for tightness only
when `d = 2`.  Effective bounds are continued in
`Ray.Multibrot.{Potential,Postcritical,Bottcher.lean`.

Our main result in this file is `iter_approx`, which shows that iterates grow as
`z^d^(n + o(1))` for large `z`.  Concretely, if if `3 ≤ b` and `max b (abs c) ≤ abs z`, then

  `|log (log (abs ((f' d c)^[n] z))) - log (log (abs z)) - n * log d| ≤` `k / (abs z * log (abs z))`

where `k` varies depending on `b` (see `iter_error_le_of_z3` and `iter_error_le_of_z4`).
-/

open Bornology (cobounded)
open Filter (Tendsto atTop)
open Real (exp log)
open Set
open scoped Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

-- We use large `norm_num`s in this file. Let them all through.
set_option exponentiation.threshold 10000

/-!
## Warmup bounds on iterates

Our iterations increase way faster than exponentially, but exponentials are nice for geometric
series bounds.
-/

/-- A warmup exponential lower bound on iterates, `3 ≤ abs z` version -/
lemma iter_large_z3 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    2^n * ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  rw [(by norm_num : (2:ℝ) = 3-1)]
  exact iter_large d 3 (by norm_num) z3 cz n

/-- A warmup exponential lower bound on iterates, `4 ≤ abs z` version -/
lemma iter_large_z4 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    3^n * ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  rw [(by norm_num : (3:ℝ) = 4-1)]
  exact iter_large d 4 (by norm_num) z4 cz n

/-- Iteration increases `abs z` -/
public lemma le_self_iter (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖((f' d c)^[n] z)‖ := by
  refine le_trans ?_ (iter_large_z3 d z3 cz n)
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))

/-- Iterates tend to infinity for large `z` -/
public theorem tendsto_iter_cobounded (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : Tendsto (fun n ↦ (f' d c)^[n] z) atTop (cobounded ℂ) := by
  simp only [tendsto_cobounded_iff_norm_tendsto_atTop]
  refine Filter.tendsto_atTop_mono (iter_large_z3 d z3 cz) ?_
  exact Filter.Tendsto.atTop_mul_const (by linarith) (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Large iterates are `≠ 0` -/
lemma f_ne_zero {c z : ℂ} (cz : ‖c‖ ≤ ‖z‖) (z3 : 3 ≤ ‖z‖) : z^d + c ≠ 0 := by
  rw [← norm_ne_zero_iff]; apply ne_of_gt
  have z1 : 1 ≤ ‖z‖ := le_trans (by norm_num) z3
  calc ‖z ^ d + c‖
    _ ≥ ‖z ^ d‖ - ‖c‖ := by bound
    _ = ‖z‖ ^ d - ‖c‖ := by rw [norm_pow]
    _ ≥ ‖z‖ ^ 2 - ‖z‖ := by bound
    _ = ‖z‖ * (‖z‖ - 1) := by ring
    _ ≥ 3 * (3 - 1) := by bound
    _ > 0 := by norm_num

/-!
## Error bound functions

In the desire to be reasonably tight, our bounds are quite complicated.  We record them as functions
so that we can state the bounds simply.
-/

/-- Bounds on `log (abs z)` -/
lemma le_log_abs_z {z : ℂ} (z3 : 3 ≤ ‖z‖) : 1.0986 ≤ log (‖z‖) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  refine le_trans ?_ z3
  norm_num
  exact (exp_div_lt).le

/-- The inside of `f_error` is nonnegative -/
lemma f_error_inner_nonneg (d : ℕ) {z : ℂ} (z3 : 3 ≤ ‖z‖) :
    0 ≤ -log (1 - 1 / ‖z‖) / (d * log (‖z‖)) := by
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) z3
  have z0' : z ≠ 0 := by exact nnnorm_pos.mp z0
  have i1 : 1 / ‖z‖ ≤ 1 := by rw [one_div_le z0]; exact le_trans (by norm_num) z3; norm_num
  have s1 : 1 - 1 / ‖z‖ < 1 := by rw [tsub_lt_iff_tsub_lt]; norm_num; exact z0'; exact i1; rfl
  have l1 := le_log_abs_z z3
  exact div_nonneg (neg_nonneg.mpr (Real.log_nonpos (sub_nonneg.mpr i1) s1.le)) (by positivity)

/-- `0 ≤ f_error` for `3 ≤ abs z` -/
lemma f_error_nonneg {d : ℕ} [Fact (2 ≤ d)] {z : ℂ} (z3 : 3 ≤ ‖z‖) : 0 ≤ f_error d z := by
  rw [f_error, le_neg, neg_zero]
  have d0 : 0 < d := d_pos d
  have  l1 : 1 ≤ log ‖z‖ := le_trans (by norm_num) (le_log_abs_z z3)
  apply Real.log_nonpos
  · simp only [one_div, neg_div, sub_nonneg, neg_le]
    rw [le_div_iff₀ (by positivity), neg_one_mul, neg_le]
    trans 2
    · refine le_trans (neg_log_one_sub_le_linear (c := 2) (by positivity) (by norm_num) ?_) ?_
      · exact le_trans (inv_anti₀ (by positivity) z3) (by norm_num)
      · simp only [zero_lt_two, mul_le_iff_le_one_right]; apply inv_le_one_of_one_le₀; linarith
    · exact le_trans (by norm_num) (mul_le_mul (two_le_cast_d d) l1 zero_le_one (by positivity))
  · linarith [f_error_inner_nonneg d z3]

/-- `f_error` bound if `b ≤ abs z`, with tunable parameters to adjust for each `b`.
    To use, pick `b`, choose `l` accordingly, then `tune `s, t, c, g` in order to be small.  -/
lemma f_error_le_generic (d : ℕ) [Fact (2 ≤ d)] (b l s t c g : ℝ) {z : ℂ} (bz : b ≤ ‖z‖)
    (lb : exp l ≤ b)
    (b3 : 3 ≤ b := by norm_num)
    (st : s / b / (2 * l) ≤ t := by norm_num)
    (tc : t ≤ min 1 (((c - 1) * 2)⁻¹ + 1)⁻¹ := by norm_num)
    (bs : b⁻¹ ≤ min 1 (((s - 1) * 2)⁻¹ + 1)⁻¹ := by norm_num)
    (csg : 1 / 2 * c * s ≤ g := by norm_num)
    (l0 : 0 < l := by norm_num) (c1 : 1 < c := by norm_num) (s1 : 1 < s := by norm_num) :
     f_error d z ≤ g / (‖z‖ * log (‖z‖)) := by
  have z3 := le_trans b3 bz
  replace lb := (Real.le_log_iff_exp_le (by positivity)).mpr (le_trans lb bz)
  have l0' : 0 < log ‖z‖ := trans l0 lb
  have inner_le : -log (1 - 1 / ‖z‖) ≤ s / ‖z‖ := by
    rw [one_div, div_eq_mul_inv]
    apply neg_log_one_sub_le_linear (by positivity) s1
    exact le_trans (inv_anti₀ (by positivity) bz) bs
  have dm : 2 * log ‖z‖ ≤ d * log ‖z‖ := by bound
  have div_le : -log (1 - 1 / ‖z‖) / (d * log ‖z‖) ≤ t := by
    have sz : s / ‖z‖ ≤ s / b := div_le_div_of_nonneg_left (by positivity) (by positivity) bz
    exact le_trans (div_le_div₀ (by positivity) (le_trans inner_le sz) (by positivity)
      (le_trans (mul_le_mul_of_nonneg_left lb (by norm_num)) dm)) st
  refine le_trans (neg_log_one_sub_le_linear (f_error_inner_nonneg d z3) c1 ?_) ?_
  · exact le_trans div_le tc
  · refine le_trans (mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) inner_le
      (by positivity) dm) (by positivity)) ?_
    simp only [div_eq_mul_inv, ←mul_assoc, mul_inv, mul_comm _ (2⁻¹ : ℝ)]
    norm_num
    simp only [mul_assoc _ (‖z‖)⁻¹ _]
    exact mul_le_mul_of_nonneg_right csg (by positivity)

/-- `f_error` bound if `3 ≤ abs z` -/
lemma f_error_le_of_z3 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z3 : 3 ≤ ‖z‖) :
    f_error d z ≤ 0.699 / (‖z‖ * log (‖z‖)) := by
  refine f_error_le_generic d 3 1.0986 (s := 1.25) (t := 0.1897) (c := 1.1171) _ z3 ?_
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `4 ≤ abs z` -/
lemma f_error_le_of_z4 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z4 : 4 ≤ ‖z‖) :
    f_error d z ≤ 0.619 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 4) (l := 1.3862) (s := 1.167) (t := 0.106) (c := 1.06)
    (g := _) z4 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `6 ≤ abs z` -/
lemma f_error_le_of_z6 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z6 : 6 ≤ ‖z‖) :
    f_error d z ≤ 0.565 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 6) (l := 1.791) (s := 1.1) (t := 0.0512) (c := 1.027)
    (g := _) z6 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `12 ≤ abs z` -/
lemma f_error_le_of_z12 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z12 : 12 ≤ ‖z‖) :
    f_error d z ≤ 0.528 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 12) (l := 2.48) (s := 1.046) (t := 0.0176) (c := 1.009)
    (g := _) z12 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `33 ≤ abs z` -/
lemma f_error_le_of_z33 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z33 : 33 ≤ ‖z‖) :
    f_error d z ≤ 0.512 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 33) (l := 3.49) (s := 1.02) (t := 0.0045) (c := 1.003)
    (g := _) z33 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- `f_error` bound if `140 ≤ abs z` -/
lemma f_error_le_of_z140 (d : ℕ) [Fact (2 ≤ d)] {z : ℂ} (z140 : 140 ≤ ‖z‖) :
    f_error d z ≤ 0.5023 / (‖z‖ * log ‖z‖) := by
  refine f_error_le_generic d (b := 140) (l := 4.94) (s := 1.004) (t := 0.00073) (c := 1.0004)
    (g := _) z140 (lb := ?_) (b3 := by norm_num) (st := by norm_num) (tc := by norm_num)
    (bs := by norm_num) (csg := by norm_num) (l0 := by norm_num) (c1 := by norm_num)
  norm_num; exact (exp_div_lt).le

/-- Finite sums of `f_error` -/
def iter_error_sum (d : ℕ) (c z : ℂ) (N : Finset ℕ) :=
  N.sum (fun k ↦ f_error d ((f' d c)^[k] z))

/-- `0 ≤ iter_error` -/
public lemma iter_error_nonneg (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    0 ≤ iter_error d c z :=
  tsum_nonneg (fun n ↦ f_error_nonneg (le_trans z3 (le_self_iter d z3 cz n)))

/-- Weak `iter_error_sum` bound based on geometric series -/
lemma iter_error_sum_weak (d : ℕ) [Fact (2 ≤ d)] {b s : ℝ} {c : ℂ} (b3 : 3 ≤ b) (s0 : 0 ≤ s)
    (bs : ∀ {w : ℂ}, b ≤ ‖w‖ → f_error d w ≤ s / (‖w‖ * log (‖w‖)))
    {z : ℂ} (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) {N : Finset ℕ} :
    iter_error_sum d c z N ≤ s / (1 - (b-1)⁻¹) / (‖z‖ * log (‖z‖)) := by
  have mf : ∀ k (w : ℂ), b ≤ ‖w‖ → ‖c‖ ≤ ‖w‖ → (b-1)^k * ‖w‖ ≤ ‖((f' d c)^[k] w)‖ :=
    fun k w bw cw ↦ iter_large d b (by linarith) bw cw k
  have z3 : 3 ≤ ‖z‖ := by linarith
  have l0 : 0 < log ‖z‖ := lt_of_lt_of_le (by norm_num) (le_log_abs_z z3)
  have b1 : 1 < b - 1 := by linarith
  have fb : ∀ k, f_error d ((f' d c)^[k] z) ≤ s / ((b-1)^k * ‖z‖ * log (‖z‖)) := by
    intro k
    have mk := mf k z bz cz
    have mk' : ‖z‖ ≤ ‖((f' d c)^[k] z)‖ :=
      le_trans (le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ b1.le)) mk
    refine le_trans (bs (le_trans bz mk')) ?_
    refine div_le_div_of_nonneg_left s0 (by positivity) ?_
    exact mul_le_mul mk (Real.log_le_log (by positivity) mk') l0.le (by positivity)
  simp only [div_eq_mul_inv, ←mul_assoc, mul_inv, mul_comm _ ((b-1)^_)⁻¹,
    mul_comm _ (1-(b-1)⁻¹)⁻¹] at fb ⊢
  simp only [mul_assoc] at fb ⊢
  generalize ht : s * ((‖z‖)⁻¹ * (log (‖z‖))⁻¹) = t at fb
  have t0 : 0 ≤ t := by rw [←ht]; positivity
  apply le_trans (Finset.sum_le_sum (fun k _ ↦ fb k))
  simp only [mul_comm _ t, ←Finset.mul_sum, ←inv_pow] at fb ⊢
  exact mul_le_mul_of_nonneg_left (partial_geometric_bound _ (by positivity)
    (inv_lt_one_of_one_lt₀ b1)) t0

/-- `iter_error` converges -/
lemma iter_error_summable (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : Summable (fun n ↦ f_error d ((f' d c)^[n] z)) := by
  apply summable_of_sum_le
  · intro n; exact f_error_nonneg (le_trans z3 (le_self_iter d z3 cz n))
  · intro N; exact iter_error_sum_weak d (le_refl _) (by norm_num) (f_error_le_of_z3 d) z3 cz

/-- Peel off the first step of the `iter_error` sum -/
lemma iter_error_peel {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖):
    iter_error d c z = f_error d z + iter_error d c (f' d c z) := by
  have h0 := sum_drop (iter_error_summable d z3 cz).hasSum
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq] at h0
  simp only [iter_error, h0.tsum_eq]; abel

/-- Weak `iter_error` bound based on geometric series -/
lemma iter_error_weak (d : ℕ) [Fact (2 ≤ d)] {b s : ℝ} {c : ℂ} (b3 : 3 ≤ b) (s0 : 0 ≤ s)
    (bs : ∀ {w : ℂ}, b ≤ ‖w‖ → f_error d w ≤ s / (‖w‖ * log (‖w‖)))
    {z : ℂ} (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ s / (1 - (b-1)⁻¹) / (‖z‖ * log (‖z‖)) := by
  have z3 : 3 ≤ ‖z‖ := by linarith
  have l0 : 0 < log ‖z‖ := lt_of_lt_of_le (by norm_num) (le_log_abs_z z3)
  have b1 : 1 < b - 1 := by linarith
  have b0 : 0 ≤ 1 - (b - 1)⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ b1.le)
  refine tsum_le_of_sum_le' ?_ ?_
  · positivity
  · intro N; exact iter_error_sum_weak d b3 s0 bs bz cz

/-- `iter_error_weak` for `33 ≤ abs z` (what you get from `3 ≤ abs z` after 2 iterations) -/
lemma iter_error_weak_of_z33 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z33 : 33 ≤ ‖z‖)
    (cz : ‖c‖ ≤ ‖z‖) : iter_error d c z ≤ 0.529 / (‖z‖ * log (‖z‖)) := by
  refine le_trans (iter_error_weak d (b := 33) (by norm_num) (by norm_num)
    (fun {_} bz ↦ f_error_le_of_z33 d bz) z33 cz) ?_
  have l0 : 0 < log ‖z‖ :=
    lt_of_lt_of_le (by norm_num) (le_log_abs_z (le_trans (by norm_num) z33))
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- Stronger `iter_error` bound based on expanding the first two terms -/
lemma iter_error_le (i : ℝ) {b s0 s1 s2 : ℝ} {c : ℂ} (b3 : 3 ≤ b)
    (s1p : 0 ≤ s1) (s2p : 0 ≤ s2)
    (bs0 : ∀ {w : ℂ}, b ≤ ‖w‖ → f_error d w ≤ s0 / (‖w‖ * log (‖w‖)))
    (bs1 : ∀ {w : ℂ}, (b^(d-1)-1)*b ≤ ‖w‖ → f_error d w ≤ s1 / (‖w‖ * log (‖w‖)))
    (bs2 : ∀ {w : ℂ}, ((b^(d-1)-1)^d * b^(d-1) - 1)*b ≤ ‖w‖ →
      f_error d w ≤ s2 / (‖w‖ * log (‖w‖)))
    (b11 : 11 ≤ (b^(d-1) - 1) ^ d * b^(d-1) - 1)
    (bb3 : 3 ≤ ((b^(d-1) - 1) ^ d * b^(d-1) - 1) * b)
    (b0' : 0 < b^(d-1) - 1)
    (b0'' : 0 < 1 - (((b^(d-1)-1)^d * b^(d-1) - 1) * b - 1)⁻¹)
    (si : s0 + s1 / (b ^ (d - 1) - 1) + s2 /
      ((1 - (((b^(d-1)-1)^d * b^(d-1) - 1) * b - 1)⁻¹) * ((b^(d-1)-1)^d * b^(d-1) - 1)) ≤ i)
    {z : ℂ} (bz : b ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ i / (‖z‖ * log (‖z‖)) := by
  have b0 : 0 < b := lt_of_lt_of_le (by norm_num) b3
  have z0 : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) (le_trans b3 bz)
  have z3 : 3 ≤ ‖z‖ := le_trans (by norm_num) (le_trans b3 bz)
  have l0 : 1 < log ‖z‖ := lt_of_lt_of_le (by norm_num) (le_log_abs_z z3)
  generalize hbb : (b^(d-1)-1)^d * b^(d-1) - 1 = bb at b11 bb3 bs2 b0'' si
  have fz : ‖z‖^d - ‖c‖ ≤ ‖f' d c z‖ := by
    calc ‖z^d + c‖
      _ ≥ ‖z^d‖ - ‖c‖ := by bound
      _ = ‖z‖^d - ‖c‖ := by rw [norm_pow]
  have fz' : (b^(d-1)-1) * ‖z‖ ≤ ‖f' d c z‖ := by
    calc ‖f' d c z‖
      _ ≥ ‖z‖^d - ‖c‖ := fz
      _ ≥ ‖z‖^d - ‖z‖ := by bound
      _ = ‖z‖^(d-1) * ‖z‖ - ‖z‖ := by rw [←pow_succ, Nat.sub_add_cancel (d_ge_one d)]
      _ = (‖z‖^(d-1) - 1) * ‖z‖ := by rw [sub_one_mul]
      _ ≥ (b^(d-1)-1) * ‖z‖ := by bound
  have zfz : ‖z‖ ≤ ‖f' d c z‖ := le_self_iter d z3 cz 1
  have zffz : ‖z‖ ≤ ‖f' d c (f' d c z)‖ := le_self_iter d z3 cz 2
  have bfz : b ≤ ‖f' d c z‖ := le_trans bz zfz
  have ffz : bb * ‖z‖ ≤ ‖f' d c (f' d c z)‖ := by
    calc ‖((f' d c z)^d + c)‖
      _ ≥ ‖(f' d c z)^d‖ - ‖c‖ := by bound
      _ = ‖f' d c z‖^d - ‖c‖ := by rw [norm_pow]
      _ ≥ ((b^(d-1)-1) * ‖z‖)^d - ‖z‖ := by bound
      _ = (b^(d-1)-1)^d * ‖z‖^(d-1) * ‖z‖ - ‖z‖ := by
          rw [mul_assoc, ←pow_succ, mul_pow, Nat.sub_add_cancel (d_ge_one d)]
      _ ≥ (b^(d-1)-1)^d * b^(d-1) * ‖z‖ - ‖z‖ := by bound
      _ = bb * ‖z‖ := by rw [←hbb, sub_one_mul]
  have e0 : f_error d z ≤ s0 / (‖z‖ * log (‖z‖)) := bs0 bz
  have e1 : f_error d (f' d c z) ≤ s1 / (b^(d-1)-1) / (‖z‖ * log (‖z‖)) := by
    refine le_trans (bs1 ?_) ?_
    · exact le_trans (mul_le_mul_of_nonneg_left bz b0'.le) fz'
    · simp only [div_eq_mul_inv, mul_inv, ←mul_assoc _ (‖z‖)⁻¹, mul_assoc s1 _ (‖z‖)⁻¹]
      simp only [←mul_inv, mul_assoc s1]
      refine mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) ?_) s1p
      exact mul_le_mul fz' (Real.log_le_log (by positivity) zfz) (by positivity)
        (le_trans b0.le bfz)
  have e2 : iter_error d c (f' d c (f' d c z)) ≤
      s2 / ((1 - (bb*b-1)⁻¹) * bb) / (‖z‖ * log (‖z‖)) := by
    refine le_trans (iter_error_weak d bb3 s2p bs2 ?_ (le_trans cz zffz)) ?_
    · exact le_trans (mul_le_mul_of_nonneg_left bz (by positivity)) ffz
    · simp only [div_eq_mul_inv, mul_assoc s2]
      refine mul_le_mul_of_nonneg_left ?_ s2p
      simp only [←mul_inv, ←mul_assoc]
      refine inv_anti₀ (by positivity) ?_
      refine mul_le_mul ?_ (Real.log_le_log z0 zffz) (by positivity) (by positivity)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ffz (by positivity)
  rw [iter_error_peel z3 cz, iter_error_peel (le_trans b3 bfz) (le_trans cz zfz), ←add_assoc]
  refine le_trans (add_le_add (add_le_add e0 e1) e2) ?_
  simp only [← add_div]
  exact div_le_div_of_nonneg_right si (by positivity)

/-- `iter_error_string` for `3 ≤ abs z` -/
lemma iter_error_le_of_z3 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ 1.03 / (‖z‖ * log (‖z‖)) := by
  have b3 : (3:ℝ) ≤ 3^(d-1) := by
    calc (3:ℝ)^(d-1)
      _ ≥ 3^(2-1) := by bound
      _ = 3 := by norm_num
  generalize hb3 : (3:ℝ)^(d-1) = t3 at b3
  have b2 : (2:ℝ) ≤ t3 - 1 := by linarith
  generalize hb2 : t3 - 1 = t2 at b2
  have t2p : 0 ≤ t2 := by positivity
  have b6 : (6:ℝ) ≤ t2 * 3 := by linarith
  have b11 : (11:ℝ) ≤ t2^d * t3 - 1 := by
    calc t2^d * t3 - 1
      _ ≥ 2^d * 3 - 1 := by bound
      _ ≥ 2^2 * 3 - 1 := by bound
      _ = 11 := by norm_num
  generalize hb11 : t2^d * t3 - 1 = t11 at b11
  have b33 : (33:ℝ) ≤ t11 * 3 := by linarith
  generalize hb33 : t11 * 3 = t33 at b33
  have b10 : 10.65 ≤ (1 - (t33 - 1)⁻¹) * t11 := by
    have h : 1 ≤ t33 - 1 := by linarith
    calc (1 - (t33 - 1)⁻¹) * t11
      _ ≥ (1 - (33 - 1)⁻¹) * 11 := by bound
      _ ≥ 10.65 := by norm_num
  simp only [←hb2, ←hb3, ←hb11, ←hb33] at b2 b6 b11 b33
  refine iter_error_le _ (by norm_num) (by norm_num) (by norm_num)
    (bs0 := f_error_le_of_z3 d)
    (bs1 := fun {_} bz ↦ f_error_le_of_z6 d (le_trans b6 bz))
    (bs2 := fun {_} bz ↦ f_error_le_of_z33 d (le_trans b33 bz))
    b11 (le_trans (by norm_num) b33) (by positivity) ?_ ?_ z3 cz
  · exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  · simp only [hb2, hb3, hb11, hb33] at b2 b3 b6 b11 b33 ⊢
    exact le_trans (add_le_add (add_le_add_right
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b2) _)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b10)) (by norm_num)

/-- `iter_error_string` for `4 ≤ abs z` -/
public lemma iter_error_le_of_z4 (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z4 : 4 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    iter_error d c z ≤ 0.8095 / (‖z‖ * log (‖z‖)) := by
  have b3 : (4:ℝ) ≤ 4^(d-1) := by
    calc (4:ℝ)^(d-1)
      _ ≥ 4^(2-1) := by bound
      _ = 4 := by norm_num
  generalize hb3 : (4:ℝ)^(d-1) = t3 at b3
  have b2 : (3:ℝ) ≤ t3 - 1 := by linarith
  generalize hb2 : t3 - 1 = t2 at b2
  have t2p : 0 ≤ t2 := by positivity
  have b6 : (12:ℝ) ≤ t2 * 4 := by linarith
  have b11 : (35:ℝ) ≤ t2^d * t3 - 1 := by
    calc t2^d * t3 - 1
      _ ≥ 3^d * 4 - 1 := by bound
      _ ≥ 3^2 * 4 - 1 := by bound
      _ = 35 := by norm_num
  generalize hb11 : t2^d * t3 - 1 = t11 at b11
  have b33 : (140:ℝ) ≤ t11 * 4 := by linarith
  generalize hb33 : t11 * 4 = t33 at b33
  have b10 : 34.748 ≤ (1 - (t33 - 1)⁻¹) * t11 := by
    have h : 1 ≤ t33 - 1 := by linarith
    calc (1 - (t33 - 1)⁻¹) * t11
      _ ≥ (1 - (140 - 1)⁻¹) * 35 := by bound
      _ ≥ 34.748 := by norm_num
  simp only [←hb2, ←hb3, ←hb11, ←hb33] at b2 b6 b11 b33
  refine iter_error_le _ (by norm_num) (by norm_num) (by norm_num)
    (bs0 := f_error_le_of_z4 d)
    (bs1 := fun {_} bz ↦ f_error_le_of_z12 d (le_trans b6 bz))
    (bs2 := fun {_} bz ↦ f_error_le_of_z140 d (le_trans b33 bz))
    (le_trans (by norm_num) b11) (le_trans (by norm_num) b33) (by positivity) ?_ ?_ z4 cz
  · exact sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))
  · simp only [hb2, hb3, hb11, hb33] at b2 b3 b6 b11 b33 ⊢
    exact le_trans (add_le_add (add_le_add_right
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b2) _)
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) b10)) (by norm_num)

/-!
## Effective bounds on iterates
-/

/-- The approximate change of `log (log (abs z))` across one iterate -/
theorem f_approx {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖) :
    |log (log (‖z ^ d + c‖)) - log (log (‖z‖)) - log d| ≤ f_error d z := by
  have dp : 0 < d := d_pos d
  have d2 : 2 ≤ (d : ℝ) := two_le_cast_d d
  have z1' : 1 < ‖z‖ := lt_of_lt_of_le (by norm_num) z3
  have z0' : 0 < ‖z‖ := by positivity
  have iz1 : 1 / ‖z‖ < 1 := (div_lt_one z0').mpr z1'
  have z0 : z ≠ 0 := norm_ne_zero_iff.mp (by positivity)
  have cz_le : ‖c / z^d‖ ≤ 1 / ‖z‖ := by
    have d1 : z^d = z^(d - 1 + 1) := by rw [Nat.sub_add_cancel (d_ge_one d)]
    simp only [d1, norm_div, norm_pow, pow_succ', div_mul_eq_div_div]
    bound
  have l0s : 1 ≤ log ‖z‖ := by
    rw [Real.le_log_iff_exp_le z0']; exact le_trans Real.exp_one_lt_3.le z3
  have l0 : 0 < log ‖z‖ := by positivity
  have l1 : 0 < ↑d * log ‖z‖ := by positivity
  have l1' : 1 < log ‖z‖ := by
    rw [Real.lt_log_iff_exp_lt z0']; exact lt_of_lt_of_le Real.exp_one_lt_3 z3
  have l2 : |log (‖1 + c / z ^ d‖)| ≤ -log (1 - 1 / ‖z‖) := by
    nth_rw 1 [← Complex.log_re]
    apply le_trans (Complex.abs_re_le_norm _)
    apply le_trans (Complex.norm_log_one_add_le' (trans cz_le iz1))
    exact Real.neg_log_one_sub_mono cz_le iz1
  have dl2 : 2 < d * log ‖z‖ := by
    calc ↑d * log ‖z‖
      _ ≥ 2 * log ‖z‖ := by gcongr
      _ > 2 * 1 := by gcongr
      _ = 2 := by norm_num
  have l3 : 0 < ↑d * log ‖z‖ + log ‖1 + c / z ^ d‖ := by
    have i2 : 1/‖z‖ ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    suffices h : -log ‖1 + c / z ^ d‖ < ↑d * log ‖z‖ by linarith
    apply lt_of_le_of_lt (neg_le_neg_iff.mpr (abs_le.mp l2).1); simp only [neg_neg]
    exact lt_of_le_of_lt (neg_log_one_sub_le_two i2) dl2
  rw [log_abs_add (z ^ d) c (pow_ne_zero _ z0) (f_ne_zero cz z3), norm_pow, Real.log_pow,
    log_add _ _ l1 l3, Real.log_mul (Nat.cast_ne_zero.mpr (d_ne_zero d)) l0.ne']
  generalize hu : log (‖1 + c / z ^ d‖) / (d * log ‖z‖) = u
  ring_nf
  have inner : |u| ≤ -log (1 - 1/‖z‖) / (d * log ‖z‖) := by
    simp only [← hu, abs_div, abs_of_pos l1, div_le_iff₀ l1]
    apply le_trans l2; apply le_of_eq; field_simp
  have weak : -log (1 - 1/‖z‖) / (d * log ‖z‖) < 1 := by
    rw [div_lt_one l1]
    refine lt_of_le_of_lt (neg_log_one_sub_le_two ?_) dl2
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  apply le_trans (Real.abs_log_one_add_le (trans inner weak))
  apply le_trans (Real.neg_log_one_sub_mono inner weak)
  rw [f_error]

/-- Absolute values of iterates grow roughly as `z^d^n` for large `z` -/
public theorem iter_approx (d : ℕ) [Fact (2 ≤ d)] {c z : ℂ} (z3 : 3 ≤ ‖z‖) (cz : ‖c‖ ≤ ‖z‖)
    (n : ℕ) : |log (log (‖(f' d c)^[n] z‖)) - log (log (‖z‖)) - n * log d| ≤ iter_error d c z := by
  induction' n with n h generalizing z
  · simp only [Function.iterate_zero, id_eq, sub_self, CharP.cast_eq_zero, zero_mul, abs_zero,
    iter_error_nonneg d z3 cz]
  · simp only [Function.iterate_succ_apply, Nat.cast_add_one]
    have e : log (log (‖(f' d c)^[n] (f' d c z)‖)) - log (log (‖z‖)) - (n+1) * log d =
        (log (log (‖f' d c z‖)) - log (log (‖z‖)) - log d) +
        (log (log (‖(f' d c)^[n] (f' d c z)‖)) - log (log (‖f' d c z‖)) - n * log d) := by
      ring
    rw [e, iter_error_peel z3 cz]
    have le : ‖z‖ ≤ ‖f' d c z‖ := le_self_iter d z3 cz 1
    exact le_trans (abs_add_le _ _) (add_le_add (f_approx z3 cz)
      (h (le_trans z3 le) (le_trans cz le)))
