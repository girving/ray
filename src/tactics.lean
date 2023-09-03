-- Tactics

-- Based on the nice tactic tutorial at
--   https://leanprover-community.github.io/extras/tactic_writing.html

import analysis.calculus.tangent_cone
import algebra.order.absolute_value
import data.real.basic
import data.complex.basic
import init.meta.interactive_base
import init.meta.rewrite_tactic
import tactic.norm_num

import absolute_value

open complex (abs)
open interactive (parse)
open interactive.types
open lean.parser (ident many tk)
open_locale nnreal

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

-- Rules used by the bound tactic
@[user_attribute] meta def bound_rules : user_attribute := {
  name := `bound_rules, descr := "Rules for the bound tactic" }

-- Extra bound lemmas
lemma sq_le_sq_of_nonneg {x y : ℝ} (p : 0 ≤ x) (h : x ≤ y) : x^2 ≤ y^2 := by nlinarith
lemma sq_lt_sq_of_nonneg {x y : ℝ} (p : 0 ≤ x) (h : x < y) : x^2 < y^2 := by nlinarith
lemma nnreal.coe_pos_of_lt {r : nnreal} : 0 < r → 0 < (r : ℝ) := nnreal.coe_pos.mpr
lemma nnreal.coe_lt_coe_of_lt {r₁ r₂ : nnreal} : r₁ < r₂ → (r₁ : ℝ) < r₂ := nnreal.coe_lt_coe.mpr
lemma mul_inv_le_one_of_le {α : Type} [group α] [has_le α] [covariant_class α α (function.swap has_mul.mul) has_le.le]
    {a b : α} : a ≤ b → a * b⁻¹ ≤ 1 := mul_inv_le_one_iff_le.mpr

-- Basics
attribute [bound_rules] le_rfl
-- 0 ≤, 0 <
attribute [bound_rules] sq_nonneg mul_pos mul_nonneg div_pos div_nonneg pow_pos pow_nonneg sub_nonneg_of_le add_nonneg
attribute [bound_rules] sub_pos_of_lt inv_nonneg_of_nonneg inv_pos_of_pos nnreal.coe_pos_of_lt nat.cast_nonneg
attribute [bound_rules] nnreal.coe_nonneg abs_nonneg absolute_value.nonneg norm_nonneg dist_nonneg nat.zero_lt_succ
-- ≤
attribute [bound_rules] div_le_div_of_le_of_nonneg div_le_div sq_le_sq_of_nonneg mul_le_mul_of_nonneg_left
attribute [bound_rules] mul_le_mul_of_nonneg_right mul_le_mul sub_le_sub add_le_add div_le_one_of_le mul_inv_le_one_of_le
attribute [bound_rules] div_le_self le_add_of_nonneg_right le_add_of_nonneg_left pow_le_pow_of_le_left inv_le_inv_of_le
-- Triangle inequalities
attribute [bound_rules] dist_triangle absolute_value.le_add absolute_value.le_sub absolute_value.add_le
attribute [bound_rules] absolute_value.sub_le' absolute_value.abs_abv_sub_le_abv_sub norm_sub_le
-- <
attribute [bound_rules] div_lt_self add_lt_add_left add_lt_add_right nnreal.coe_lt_coe_of_lt sq_lt_sq_of_nonneg
-- min and max
attribute [bound_rules] min_le_right min_le_left le_max_left le_max_right le_min max_le lt_min max_lt
-- Deal with covariant_class instances
attribute [bound_rules] covariant_swap_add_lt_of_covariant_add_lt
 
-- Straightforward propagation of inequalities.
-- Roughly, handles a bunch of cases of the form
--   f x {≤,<} f y
-- where f is increasing and x ≤ y is immediate.
meta def bound (args : list pexpr) : tactic unit := do
  -- Helpful diagnostic: tactic.target >>= λ e, tactic.fail format! "bailing: {e}"
  notes [``(le_of_lt)] args,  -- Turn each < into a ≤
  -- Do apply_rules, but with assumption <|> positivity <|> apply_list ... <|> norm_num
  let n := 32,  -- maximum iteration depth
  let opt : tactic.apply_cfg := {unify := ff},
  let attrs := [`bound_rules],
  attr_exprs ← tactic.lock_tactic_state $ attrs.mfoldl
    (λ l n, list.append l <$> tactic.resolve_attribute_expr_list n) [],
  let args_exprs := args.map tactic.i_to_expr_for_apply ++ attr_exprs,
  tactic.iterate_at_most_on_subgoals n (
    tactic.assumption <|>
    tactic.interactive.positivity <|>
    tactic.apply_list_expr opt args_exprs <|>
    tactic.interactive.norm_num [] (interactive.loc.ns [none]))

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