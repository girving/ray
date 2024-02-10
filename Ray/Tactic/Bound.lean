import Aesop
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Ray.Misc.AbsoluteValue
import Ray.Tactic.BoundRuleSet

/-!
## The `bound` tactic

`bound` is an `aesop` wrapper that proves inequalities which follow by straightforward recursion on
structure, assuming that intermediate terms are nonnegative or positive as needed.  It also has some
report for guessing where it is unclear where to recurse, such as which side of a `min` or `max` to
use as the bound or whether to assume a power is less than or greater than one.

The functionality of `bound` overlaps with `positivity` and `gcongr`, but can jump back and forth
between `0 ≤ x` and `x ≤ y`-type inequalities.  For example, `bound` proves
  `0 ≤ c → b ≤ a → 0 ≤ a * c - b * c`
By turning the goal into `b * c ≤ a * c`, then using `mul_le_mul_of_nonneg_right`.  `bound` also
has used specialized lemmas for goals of the form `1 ≤ x, 1 < x, x ≤ 1, x < 1`.

Additional hypotheses can be passed as `bound [h0, h1 n, ...]`.  This is equivalent to declaring
them via `have` before calling `bound`.

See `Ray.Tactic.BoundTests` for tests.

### Aesop heuristics

`bound` uses a `bound` aesop rule set, with rules organized as follows:

#### High-confidence apply rules

1. `norm apply`: Lemmas which close inequalities immediately, such as `le_refl, Real.exp_pos`,
    triangle inequalities, etc.
2. `safe 2 apply`: High-confidence lemmas which produce one new goal, such as `inv_le_one`.  Here by
    high-confidence we mean roughly "are how one would naively prove the inequality, assuming
    intermediate terms are nonnegative or positive when necessary".  It is important that these are
    `safe 2`, not `safe 1`, so that `assumption` can fire early in case the naive proof is wrong
    and we have an assumption that can close the goal immediately.
3. `safe 3 apply`; High-confidence lemmas which produce one new general inequality goal, but
    possibly additional nonnegativity goals.  The standard example is `mul_le_mul_of_nonneg_left`.
4. `safe 4 apply`: High-confidence lemmas which produce multiple general inequality goals, such as
    `add_le_add` and `mul_le_mul`.  Note that we still declare these as `safe` for speed, even
    though they can certainly be wrong (e.g., we could have `0 ≤ x * y` because `x, y ≤ 0`),
    following the general heuristic of `bound` to assume nonnegativity where useful.

### Guessing apply rules

There are several cases where there two standard ways to recurse down an inequality, and not obvious
which is correct without more information.  For example, `a ≤ min b c` is registered as a `norm`
rule, since we always need to prove `a ≤ b ∧ a ≤ c`.  But if we see `min a b ≤ c`, either
`a ≤ b` and `a ≤ c` suffices, and we don't know which.

In these cases we register the pair of rules as `unsafe apply 50%`, so that `aesop` tries both.

Currently the two types of guessing rules are
1. `min` and `max` rules, for both `≤` and `<`
2. `pow` and `rpow` monotonicity rules which branch on `1 ≤ a` or `a ≤ 1`.


### Forward rules

1. `le_of_lt`: Most importantly, we register `le_of_lt` as a forward rule so that weak inequalities
   can be proved from strict inequalities.  Note that we treat weak vs. strict separately for
   apply rules, as usually the hypotheses needed to prove weak inequalities are importantly weaker.
2. Inequalities from structures: We register lemmas which extract inequalities from structures.
   In this file, the only example is `HasFPowerSeriesOnBall.r_pos`, so that `bound` knows that any
   power series in the context have positive radii of convergence, but other theories in this repo
   add further forward rules of this type.

### Tactics

We close numerical goals with `norm_num`.
-/

open Parser
open Lean Elab Meta Term Mathlib.Tactic Mathlib.Meta Syntax
open Lean.Elab.Tactic (liftMetaTactic liftMetaTactic' TacticM getMainGoal)

-- Extra bound lemmas
lemma NNReal.coe_pos_of_lt {r : NNReal} : 0 < r → 0 < (r : ℝ) := NNReal.coe_pos.mpr
lemma NNReal.coe_lt_coe_of_lt {r₁ r₂ : NNReal} : r₁ < r₂ → (r₁ : ℝ) < r₂ := NNReal.coe_lt_coe.mpr
lemma mul_inv_le_one_of_le {α : Type} [Group α] [LE α]
    [CovariantClass α α (Function.swap fun x y ↦ x * y) (fun x y ↦ x ≤ y)]
    {a b : α} : a ≤ b → a * b⁻¹ ≤ 1 := mul_inv_le_one_iff_le.mpr
lemma mul_inv_le_one_of_nonneg_of_le {α : Type} [LinearOrderedSemifield α] {a b : α}
    (a0 : 0 ≤ a) (ab : a ≤ b) : a * b⁻¹ ≤ 1 := by
  by_cases b0 : b = 0
  · simp only [b0, inv_zero, mul_zero, zero_le_one]
  · have bp : 0 < b := Ne.lt_of_le (Ne.symm b0) (le_trans a0 ab)
    simp only [mul_inv_le_iff bp, mul_one, ab]
lemma mul_lt_mul_left_of_pos_of_lt {α : Type} {a b c : α} [Mul α] [Zero α] [Preorder α]
    [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) (bc : b < c) : a * b < a * c := by
  rw [mul_lt_mul_left]; repeat assumption
lemma mul_lt_mul_right_of_pos_of_lt {α : Type} {a b c : α} [Mul α] [Zero α] [Preorder α]
    [MulPosStrictMono α] [MulPosReflectLT α] (ab : a < b) (c0 : 0 < c) : a * c < b * c := by
  rw [mul_lt_mul_right]; repeat assumption
lemma one_lt_div_of_pos_of_lt {α : Type} [LinearOrderedSemifield α] {a b : α} (b0 : 0 < b)
    (ba : b < a) : 1 < a / b := by rwa [one_lt_div]; assumption
lemma div_lt_one_of_pos_of_lt {α : Type} [LinearOrderedSemifield α] {a b : α} (b0 : 0 < b)
    (ab : a < b) : a / b < 1 := by rwa [div_lt_one]; assumption
lemma Real.pi_nonneg : 0 ≤ (Real.pi:ℝ) := Real.pi_pos.le
lemma ENNReal.ofReal_pos_of_pos {p : ℝ} (h : 0 < p) : 0 < ENNReal.ofReal p := by
  rwa [ENNReal.ofReal_pos]
lemma Real.one_lt_exp_of_pos {x : ℝ} (x0 : 0 < x) : 1 < Real.exp x := by rwa [Real.one_lt_exp_iff]
lemma Nat.cast_pos_of_pos {R : Type} [OrderedSemiring R] [Nontrivial R] {n : ℕ} (n0 : 0 < n) :
    0 < (n : R) := by rwa [Nat.cast_pos]
lemma le_self_pow_of_pos {R : Type} [OrderedSemiring R] {a : R} {m : ℕ} (ha : 1 ≤ a) (h : 0 < m) :
    a ≤ a^m :=
  le_self_pow ha h.ne'
lemma Nat.one_le_cast_of_le {α : Type} [AddCommMonoidWithOne α] [PartialOrder α]
    [CovariantClass α α (fun (x y : α) => x + y) fun (x y : α) => x ≤ y] [ZeroLEOneClass α]
    [CharZero α] {n : ℕ} (n1 : 1 ≤ n) : 1 ≤ (n : α) := by rwa [Nat.one_le_cast]

-- `bound` apply rules, starting with the basics
attribute [aesop norm apply (rule_sets [bound])] le_refl
-- 0 ≤, 0 <
attribute [aesop norm apply (rule_sets [bound])] sq_nonneg Nat.cast_nonneg NNReal.coe_nonneg
  abs_nonneg AbsoluteValue.nonneg norm_nonneg dist_nonneg Nat.zero_lt_succ Real.exp_pos
  Real.exp_nonneg Real.pi_pos Real.pi_nonneg Int.ceil_lt_add_one
attribute [aesop safe apply 2 (rule_sets [bound])] pow_pos pow_nonneg sub_nonneg_of_le sub_pos_of_lt
  inv_nonneg_of_nonneg inv_pos_of_pos NNReal.coe_pos_of_lt Real.sqrt_pos_of_pos
  ENNReal.ofReal_pos_of_pos Real.log_pos Real.rpow_nonneg Real.log_nonneg tsub_pos_of_lt
attribute [aesop safe apply 3 (rule_sets [bound])] mul_pos mul_nonneg div_pos div_nonneg add_nonneg
  Real.rpow_pos_of_pos
-- 1 ≤, ≤ 1
attribute [aesop safe apply 2 (rule_sets [bound])] inv_le_one Nat.one_le_cast_of_le
attribute [aesop safe apply 3 (rule_sets [bound])] one_le_pow_of_one_le
  one_le_mul_of_one_le_of_one_le div_le_one_of_le mul_inv_le_one_of_le
  mul_inv_le_one_of_nonneg_of_le pow_le_one
-- ≤
attribute [aesop norm apply (rule_sets [bound])] le_abs_self norm_smul_le Int.le_ceil neg_abs_le
  Complex.abs_re_le_abs Complex.abs_im_le_abs Real.abs_rpow_le_abs_rpow
attribute [aesop safe apply 2 (rule_sets [bound])] Real.exp_le_exp_of_le neg_le_neg Real.sqrt_le_sqrt
  Real.one_lt_exp_of_pos tsub_le_tsub_right Real.log_le_log ENNReal.ofReal_le_ofReal
attribute [aesop safe apply 3 (rule_sets [bound])] pow_le_pow_left Real.rpow_le_rpow
  div_le_div_of_le mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right div_le_self
  le_add_of_nonneg_right le_add_of_nonneg_left inv_le_inv_of_le le_self_pow_of_pos
  le_mul_of_one_le_right mul_le_of_le_one_right le_div_self Finset.sum_le_sum
attribute [aesop safe apply 4 (rule_sets [bound])] sub_le_sub add_le_add div_le_div mul_le_mul
-- Triangle inequalities
attribute [aesop norm apply (rule_sets [bound])] dist_triangle AbsoluteValue.le_add
  AbsoluteValue.le_sub AbsoluteValue.add_le AbsoluteValue.sub_le'
  AbsoluteValue.abs_abv_sub_le_abv_sub norm_sub_le norm_sum_le
-- <
attribute [aesop norm apply (rule_sets [bound])] Nat.cast_pos_of_pos NNReal.coe_lt_coe_of_lt
attribute [aesop safe apply 2 (rule_sets [bound])] neg_lt_neg
  Real.sqrt_lt_sqrt sub_lt_sub_left sub_lt_sub_right add_lt_add_left add_lt_add_right
attribute [aesop safe apply 3 (rule_sets [bound])] mul_lt_mul_left_of_pos_of_lt
  mul_lt_mul_right_of_pos_of_lt div_lt_div_of_lt_left div_lt_div_of_lt pow_lt_pow_left
  Real.rpow_lt_rpow div_lt_self one_lt_div_of_pos_of_lt
  div_lt_one_of_pos_of_lt
-- min and max
attribute [aesop norm apply (rule_sets [bound])] min_le_right min_le_left le_max_left le_max_right
attribute [aesop safe apply 4 (rule_sets [bound])] le_min max_le lt_min max_lt
-- Memorize a few constants to avoid going to `norm_num`
attribute [aesop norm apply (rule_sets [bound])] zero_le_one zero_lt_one zero_le_two zero_lt_two

-- Bound applies `le_of_lt` to all hypotheses
attribute [aesop safe forward (rule_sets [bound])] le_of_lt

-- Power series have positive radius
attribute [aesop safe forward (rule_sets [bound])] HasFPowerSeriesOnBall.r_pos

-- Guessing rules: when we don't know which side to branch down.
-- Each line is a pair where we expect exactly one side to work.
attribute [aesop unsafe apply 50% (rule_sets [bound])]
  -- Which side of the `max` should we use as the lower bound?
  le_max_of_le_left le_max_of_le_right
  lt_max_of_lt_left lt_max_of_lt_right
  -- Which side of the `min` should we use as the upper bound?
  min_le_of_left_le min_le_of_right_le
  min_lt_of_left_lt min_lt_of_right_lt
  -- Given `a^m ≤ a^n`, is `1 ≤ a` or `a ≤ 1`?
  pow_le_pow_right pow_le_pow_of_le_one
  Real.rpow_le_rpow_of_exponent_le Real.rpow_le_rpow_of_exponent_ge

-- Close numerical goals with `norm_num`
def boundNormNum : Aesop.RuleTac :=
  Aesop.SingleRuleTac.toRuleTac fun i => do
    let tac := do NormNum.elabNormNum .missing .missing
    let goals ← Lean.Elab.Tactic.run i.goal tac |>.run'
    if !goals.isEmpty then failure
    return (#[], some (.ofTactic 1  `(tactic| norm_num)), some .hundred)
attribute [aesop unsafe 10% tactic (rule_sets [bound])] boundNormNum

/-- Pull the array out of an optional `"[" term,* "]"` syntax, or return `#[]` -/
def maybeTerms : Syntax → Array Syntax
  | node _ _ #[_, node _ _ s, _] => s.getEvenElems
  | _ => #[]

/-- Add extra hypotheses -/
def addHyps (xs : Array Syntax) : TacticM Unit :=
  if xs.isEmpty then pure () else Tactic.withMainContext do
    for x in xs do
      let v ← elabTerm x none
      let t ← inferType v
      liftMetaTactic fun g ↦ do
        let g ← g.assert `h t v
        let (_, g) ← g.intro1P
        return [g]

def boundConfig : Aesop.Options := {
  maxRuleApplicationDepth := 32
  enableSimp := false
}

/-- `bound` tactic for proving inequalities via straightforward recursion on expression structure -/
elab "bound" lemmas:(("[" term,* "]")?) : tactic => do
  addHyps (maybeTerms lemmas)
  let tac ← `(tactic| aesop (rule_sets [bound, -default]) (config := boundConfig))
  liftMetaTactic fun g ↦ do return (←Lean.Elab.runTactic g tac.raw).1

/-- `bound?`, but return a proof script -/
elab "bound?" lemmas:(("[" term,* "]")?) : tactic => do
  addHyps (maybeTerms lemmas)
  let tac ← `(tactic| aesop? (rule_sets [bound, -default]) (config := boundConfig))
  liftMetaTactic fun g ↦ do return (←Lean.Elab.runTactic g tac.raw).1
