-- Tactics

-- Based on the nice tactic tutorial at
--   https://leanprover-community.github.io/extras/tactic_writing.html

import algebra.order.ring
import analysis.calculus.tangent_cone
import data.real.basic
import data.complex.basic
import init.meta.interactive_base
import init.meta.rewrite_tactic
import simple
import tactic.norm_num

open complex (abs)
open interactive (parse)
open interactive.types
open lean.parser (ident many tk)
open_locale nnreal

meta def aux (q : pexpr) (t : tactic unit) : tactic expr := do
  e ← tactic.i_to_expr q,
  (_, h) ← tactic.solve_aux e t,
  return h

meta def try_aux (q : pexpr) (t : tactic unit) : tactic (option expr) := do
  e ← tactic.i_to_expr q,
  (tactic.solve_aux e t >>= λ h, pure $ some h.snd) <|> return none

meta def pexact (q : pexpr) : tactic unit := do
  t ← tactic.i_to_expr q,
  tactic.exact t

meta def is_ineq : expr → bool
| `(_ ≤ _) := tt
| `(_ < _) := tt
| `(_ ≥ _) := tt
| `(_ > _) := tt
| _ := ff

-- Flip ≤/≥ and </> in target
meta def tactic.interactive.flip_ineq : tactic unit := do
  t ← tactic.target,
  match t with
  | `(%%a ≤ %%b) := do t ← tactic.i_to_expr ``(simple.ge_to_le), _ ← tactic.apply t, return ()
  | `(%%a < %%b) := do t ← tactic.i_to_expr ``(simple.gt_to_lt), _ ← tactic.apply t, return ()
  | `(%%a ≥ %%b) := do t ← tactic.i_to_expr ``(simple.le_to_ge), _ ← tactic.apply t, return ()
  | `(%%a > %%b) := do t ← tactic.i_to_expr ``(simple.lt_to_gt), _ ← tactic.apply t, return ()
  | _ := tactic.fail "flip_ineq got a non-inequality"
  end

-- [f h | f ∈ fs, h ∈ hs]
meta def calls (fs : list pexpr) (hs : list pexpr) : tactic (list expr) := do
  ys ← flip monad.mapm fs (λ f, do
    let maybe_p := λ e : pexpr, some <$> tactic.i_to_expr ``(%%f %%e) <|> return none,
    let maybe_e := λ e : expr, maybe_p (to_pexpr e),
    ys0 ← tactic.local_context >>= monad.mapm maybe_e,
    ys1 ← monad.mapm maybe_p hs,
    return (ys0 ++ ys1)),
  return (list.filter_map id ys.join)

-- note each f h for f ∈ fs, h ∈ hs
meta def notes (fs : list pexpr) (hs : list pexpr) : tactic unit :=
  calls fs hs >>= monad.mapm' (λ e, do _ ← tactic.note `this none e, return ())

-- Straightforward propagation of inequalities.
-- Roughly, handles a bunch of cases of the form
--   f x {≤,<} f y
-- where f is increasing and x ≤ y is immediate.
meta def bound (hs : list pexpr) : tactic unit := do
  -- Helpful diagnostic: tactic.target >>= λ e, tactic.fail format! "bailing: {e}"
  notes [``(le_of_lt)] hs,  -- Turn each < into a ≤
  let lemmas := hs ++ [
    -- Basics
    ``(le_rfl),
    -- 0 ≤, 0 <
    ``(sq_nonneg _),
    ``(mul_pos), ``(mul_nonneg), ``(div_pos), ``(div_nonneg),
    ``(simple.pow_pos'), ``(simple.pow_nonneg'),
    ``(simple.ring_sub_nonneg), ``(simple.ring_add_nonneg), ``(simple.ring_sub_pos),
    ``(inv_nonneg.mpr), ``(inv_pos.mpr),
    ``(nnreal.coe_pos.mpr), ``(simple.nat_nonneg _), ``(nnreal.coe_nonneg _),
    ``(simple.real_abs_nonneg), ``(complex.abs_nonneg _), ``(norm_nonneg), ``(dist_nonneg),
    ``(nat.zero_lt_succ _),
    -- ≤
    ``(simple.div_le_div_right), ``(div_le_div),
    ``(simple.sq_increasing),
    ``(mul_le_mul_of_nonneg_left), ``(mul_le_mul_of_nonneg_right), ``(mul_le_mul),
    ``(simple.ring_sub_le_sub), ``(simple.ring_add_le_add),
    ``(simple.div_le_one), ``(simple.div_cancel_le), ``(div_le_self),
    ``(simple.le_add_nonneg_right), ``(simple.le_add_nonneg_left),
    ``(pow_le_pow_of_le_left), ``(inv_le_inv_of_le),
    -- Triangle inequalities
    ``(dist_triangle _ _ _), ``(simple.abs_sub'), ``(simple.abs_sub_ge'), ``(complex.abs_add _ _), ``(norm_sub_le),
    -- <
    ``(div_lt_self),
    ``(simple.ring_add_lt_add_left), ``(simple.ring_add_lt_add_right),
    ``(nnreal.coe_lt_coe.mpr),
    -- min and max
    ``(min_le_right), ``(min_le_left), ``(le_max_left), ``(le_max_right), ``(le_min), ``(max_le),
    ``(lt_min), ``(max_lt),
    -- Constants
    ``(zero_le_one), ``(zero_lt_one), ``(ennreal.zero_lt_one),
    ``(zero_le_bit0.mpr), ``(zero_lt_bit0.mpr),
    ``(simple.zero_lt_bit1), ``(simple.zero_le_bit1),
    ``(nat.bit0_lt), ``(nat.bit1_lt), 
    ``(nat.bit0_le), ``(nat.bit1_le),
    ``(bit0_le_bit0.mpr), ``(bit0_lt_bit0.mpr), ``(bit1_le_bit1.mpr), ``(bit1_lt_bit1.mpr),
    ``(norm_num.le_one_bit0 _), ``(norm_num.lt_one_bit0 _),
    ``(with_top.zero_lt_top)
  ],
  tactic.apply_rules lemmas [] 32 {unify := ff}

meta def tactic.interactive.notes (fs : parse pexpr_list) (hs : parse opt_pexpr_list) : tactic unit := notes fs hs
meta def tactic.interactive.bound (hs : parse opt_pexpr_list) : tactic unit := bound hs

section positive_tests
variables n : ℕ
variables x y : ℝ
variables u : ℝ≥0
variables z : ℂ
lemma test_pos_sq (h : x > 0) : x^2 > 0 := by bound
lemma test_pos_mul (p : x > 0) (q : y > 0) : x * y > 0 := by bound
lemma test_pos_div (p : x > 0) (q : y > 0) : x / y > 0 := by bound
lemma test_pos_4 : 0 < 4 := by bound
lemma test_pos_7 : 0 < 7 := by bound
lemma test_pos_4_real : 0 < (4 : ℝ) := by bound
lemma test_pos_7_real : 0 < (7 : ℝ) := by bound
lemma test_pos_zero_one : 0 < (1 : ℝ) := by bound
lemma test_pos_nnreal (h : u > 0) : 0 < (u : ℝ) := by bound
lemma test_pos_pow : 0 < 2^n := by bound
lemma test_pos_inv : 0 < (1 : ℝ)⁻¹ := by bound
end positive_tests

section nonneg_tests
variables n : ℕ
variables x y : ℝ
variables u : ℝ≥0
variables z : ℂ
lemma test_abs : 0 ≤ abs z := by bound
lemma test_abs_ge : abs z ≥ 0 := by bound
lemma test_nn_sq : x^2 ≥ 0 := by bound
lemma test_mul (p : x ≥ 0) (q : y ≥ 0) : x * y ≥ 0 := by bound
lemma test_div (p : x ≥ 0) (q : y ≥ 0) : x / y ≥ 0 := by bound
lemma test_add (p : x ≥ 0) (q : y ≥ 0) : x + y ≥ 0 := by bound
lemma test_nat : (n : ℝ) ≥ 0 := by bound
lemma test_num : 0 ≤ 7 := by bound
lemma test_num_real : 0 ≤ (7 : ℝ) := by bound
lemma test_zero_one : 0 ≤ (1 : ℝ) := by bound
lemma test_nnreal : 0 ≤ (u : ℝ) := by bound
lemma test_zero : 0 ≤ (0 : ℝ) := by bound
lemma test_pow : 0 ≤ 2^n := by bound
lemma test_inv : 0 ≤ (0 : ℝ)⁻¹ := by bound
end nonneg_tests

section bound_tests
variables a b c x y : ℝ
variables z : ℂ
variables n : ℕ
lemma test_sq (n : x ≥ 0) (h : x ≤ y) : x^2 ≤ y^2 := by bound
lemma test_sq_ge (n : x ≥ 0) (h : x ≤ y) : y^2 ≥ x^2 := by bound
lemma test_mul_left (n : a ≥ 0) (h : x ≤ y) : a * x ≤ a * y := by bound
lemma test_mul_right (n : a ≥ 0) (h : x ≤ y) : x * a ≤ y * a := by bound
lemma test_mul_both (bp : b ≥ 0) (xp : x ≥ 0) (ab : a ≤ b) (xy : x ≤ y) : a * x ≤ b * y := by bound
lemma test_abs_mul (h : x ≤ y) : abs z * x ≤ abs z * y := by bound
lemma test_add_left (h : x ≤ y) : a + x ≤ a + y := by bound
lemma test_add_right (h : x ≤ y) : x + a ≤ y + a := by bound
lemma test_add_both (ab : a ≤ b) (xy : x ≤ y) : a + x ≤ b + y := by bound
lemma test_sub_left (h : x ≥ y) : a - x ≤ a - y := by bound
lemma test_sub_right (h : x ≤ y) : x - a ≤ y - a := by bound
lemma test_sub_both (ab : a ≤ b) (xy : x ≥ y) : a - x ≤ b - y := by bound
lemma test_sub_pos (h : x < y) : y - x > 0 := by bound
lemma test_le_of_lt (h : x > 0) : x ≥ 0 := by bound
lemma test_extra (f : ℕ → ℝ) (h : ∀ n, f n ≥ 0) : f n ≥ 0 := by bound [h n]
lemma test_1_4 : (1 : ℝ) < 4 := by bound
lemma test_2_4 : (2 : ℝ) < 4 := by bound
lemma test_div_left (hc : c ≥ 0) (h : a ≤ b) : a / c ≤ b / c := by bound
lemma test_div_right (ha : a ≥ 0) (hc : c > 0) (h : b ≥ c) : a / b ≤ a / c := by bound
lemma test_coe (x y : ℝ≥0) (h : x < y) : (x : ℝ) < y := by bound
lemma test_dist : dist a c ≤ dist a b + dist b c := by bound
end bound_tests

-- Interactive test for notes
/-
lemma test_calls {a b c : ℝ} (ab : a < b) (cp : c > 0) : a ≤ c := begin
  notes [le_of_lt] [norm_sum_le],
end
-/