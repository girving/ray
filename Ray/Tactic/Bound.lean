import Lean.Elab.Tactic.Basic
import Lean.Elab.Term
import Lean.Expr
import Lean.Parser.Syntax
import Mathlib.Analysis.Calculus.TangentCone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum.Core
import Ray.Misc.AbsoluteValue
import Ray.Tactic.BoundRules
import Std.Tactic.LabelAttr
import Std.Util.Cache

/-!
## The `bound` tactic

`bound` iteratively applies "straightforward" inequalities, for example proving that `f x ≤ f y`
given `x ≤ y` for monotonic `f` of various kinds (arithmetic, `Complex.exp`, etc.).  This
functionality overlaps with `mono` and `positivity`, but was (1) written before I knew about those
and (2) even now that I do it seems more optimized for working with nontrivial calculations.  A
common use is within `calc`, by alternating equational rewrites with `bound` such that each `bound`
steps is a staightforward consequence of assumptions and the structure of the expression.

`bound` uses `DiscrTree` internally for speed.

References:
1. Lean 3 tactic tutorial: https://leanprover-community.github.io/extras/tactic_writing.html
2. Lean 4 metaprogramming book: https://github.com/leanprover-community/lean4-metaprogramming-book
-/

open Complex (abs)
open Parser
open Lean Elab Meta Term Mathlib.Tactic Mathlib.Meta Syntax
open Lean.Elab.Tactic (liftMetaTactic liftMetaTactic' TacticM getMainGoal)
open scoped NNReal

variable {m : Type → Type} [Monad m]

/-- Pull the array out of an optional `"[" term,* "]"` syntax, or return `#[]` -/
def maybeTerms : Syntax → Array Syntax
  | node _ _ #[_, node _ _ s, _] => s.getEvenElems
  | _ => #[]

/-- Depth-limited `repeat1'` in `TacticM` -/
def repeatD (t : TacticM Unit) : ℕ → TacticM Unit
| 0 => return
| n+1 => Tactic.andThenOnSubgoals t (repeatD t n)

/-- `f x`, elaborated -/
def call (f x : Expr) : TermElabM Expr :=
  Term.elabAppArgs f #[] #[.expr x] none false false

/-- `f x`, elaborated -/
def call' (f : Name) (x : Expr) : TermElabM Expr := do
  call (←elabTerm (mkIdent f) none) x

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

-- Basics
attribute [bound_rules] le_rfl
-- 0 ≤, 0 <
attribute [bound_rules] sq_nonneg mul_pos mul_nonneg div_pos div_nonneg pow_pos Real.rpow_pos_of_pos
  pow_nonneg sub_nonneg_of_le add_nonneg sub_pos_of_lt inv_nonneg_of_nonneg inv_pos_of_pos
  NNReal.coe_pos_of_lt Nat.cast_nonneg NNReal.coe_nonneg abs_nonneg AbsoluteValue.nonneg norm_nonneg
  dist_nonneg Nat.zero_lt_succ Real.exp_pos Real.exp_nonneg Real.pi_pos Real.pi_nonneg
  Int.ceil_lt_add_one Real.sqrt_pos_of_pos ENNReal.ofReal_pos_of_pos Real.log_pos
  Real.rpow_nonneg Real.log_nonneg
-- ≤
attribute [bound_rules] sub_le_sub add_le_add pow_le_pow_left Real.rpow_le_rpow
  div_le_div_of_le div_le_div mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right
  mul_le_mul div_le_one_of_le mul_inv_le_one_of_le mul_inv_le_one_of_nonneg_of_le div_le_self
  le_add_of_nonneg_right le_add_of_nonneg_left inv_le_inv_of_le Real.exp_le_exp_of_le le_abs_self
  Real.sqrt_le_sqrt neg_le_neg Real.one_lt_exp_of_pos le_self_pow_of_pos pow_le_one
  one_le_pow_of_one_le le_mul_of_one_le_right mul_le_of_le_one_right le_div_self
  tsub_le_tsub_right inv_le_one Real.log_le_log
-- Triangle inequalities
attribute [bound_rules] dist_triangle AbsoluteValue.le_add AbsoluteValue.le_sub AbsoluteValue.add_le
  AbsoluteValue.sub_le' AbsoluteValue.abs_abv_sub_le_abv_sub norm_sub_le
-- <
attribute [bound_rules] mul_lt_mul_left_of_pos_of_lt mul_lt_mul_right_of_pos_of_lt
  div_lt_div_of_lt_left div_lt_div_of_lt pow_lt_pow_left Real.rpow_lt_rpow div_lt_self
  add_lt_add_left add_lt_add_right one_lt_div_of_pos_of_lt div_lt_one_of_pos_of_lt
  NNReal.coe_lt_coe_of_lt sub_lt_sub_left sub_lt_sub_right Real.sqrt_lt_sqrt neg_lt_neg
  Nat.cast_pos_of_pos
-- min and max
attribute [bound_rules] min_le_right min_le_left le_max_left le_max_right le_min max_le lt_min
  max_lt

/-- Lemma information for use in `bound`'s `DiscrTrees` -/
inductive Lemma where
  | expr : Expr → Lemma
  | syn : Syntax → Bool → Lemma  -- If the Bool is true, the syntax for <, but we want ≤
  deriving BEq

/-- How to print Lemma -/
instance : ToFormat Lemma where
  format lem := match lem with
    | .expr e => format e
    | .syn e _ => format e

/-- Configuration for our `DiscrTree` -/
def discrTreeConfig : WhnfCoreConfig := {}

/-- Cache a `DiscrTree` of bound lemmas.  Ideally this would update if new lemmas are added
    to `bound_rules`, but for now it does not.

    Example of how to make it update: https://github.com/leanprover-community/mathlib4/blob/9fbca06f59749829b28b94be963b5592d591dc6a/Mathlib/Tactic/Relation/Rfl.lean#L20-L26
    -/
def boundDiscrTree : IO (Std.Tactic.Cache (DiscrTree Lemma)) := Std.Tactic.Cache.mk do
  let mut tree := DiscrTree.empty
  for rule in (←Std.Tactic.LabelAttr.labelled "bound_rules").reverse do
    tree ← withNewMCtxDepth do withReducible do
      let (_, _, type) ← forallMetaTelescope (←getConstInfo rule).type
      return tree.insertCore (←DiscrTree.mkPath type discrTreeConfig) (.syn (mkIdent rule) false)
  return tree

/-- Check if a name is an inequality operator -/
def Lean.Name.isIneq : Name → Bool
| `LT.lt => true
| `LE.le => true
| `GT.gt => true
| `GE.ge => true
| _ => false

/-- Check if an expression is an inequality -/
def Lean.Expr.isIneq : Expr → Bool
  | .app (.const n _) _ => n.isIneq
  | _ => false

/-- Insert a type into our discrimination tree, adjusting <,≥,> for generality -/
def insertLemma (tree : DiscrTree Lemma) (type : Expr) (lem : Lemma) :
    TacticM (DiscrTree Lemma) := do
  let type ← withReducible (whnf type)
  match type with
  | .app (.app (.app (.app (.const n l) α) i) x) y => do
    let mut tree := tree
    if n == ``LT.lt || n == ``LE.le then
      tree ← tree.insert type lem discrTreeConfig
    else if n == ``GT.gt || n == ``GE.ge then
      let r := if n == ``GT.gt then ``LT.lt else ``LE.le  -- Swap ≥,> to ≤,<
      tree ← tree.insert (Lean.mkApp4 (.const r l) α i y x) lem discrTreeConfig
    if n == ``LT.lt || n == ``GT.gt then  -- Record le_of_lt version as well
      match lem with
      | .expr e => do
        let e ← call' ``le_of_lt e
        tree ← tree.insert (←inferType e) (.expr e) discrTreeConfig
      | .syn e _ => do
        let (x,y) := if n == `LT.lt then (x,y) else (y,x)
        let i ← mkFreshExprMVar (some (.app (.const ``LE l) α))
        tree ← tree.insert (Lean.mkApp4 (.const ``LE.le l) α i x y) (.syn e true) discrTreeConfig
    return tree
  | _ => return tree

/-- Straightforward propagation of inequalities.
    Roughly, handles a bunch of cases of the form `f x {≤,<} f y`
    where `f` is increasing and `x ≤ y` is immediate or handled recursively. -/
def bound (lemmas : Array Syntax) : TacticM Unit := Tactic.withMainContext do
  -- Start out with cached lemmas, then add assumptions and explicit lemmas.
  -- Explicit lemmas will have higher priority.
  let mut tree ← (←boundDiscrTree).get
  for d in ←getLCtx do
    if !d.isImplementationDetail then
      tree ← insertLemma tree d.type (.expr d.toExpr)
  let s ← saveState
  for s in lemmas.reverse do
    tree ← withNewMCtxDepth do withReducible do
      let (_, _, type) ← forallMetaTelescope (←inferType (←elabTerm s none))
      insertLemma tree type (.syn s false)
  s.restore  -- Forget tree generation mvars
  -- Inner loop apply machinery
  let cfg : ApplyConfig := {allowSynthFailures := true, approx := false}
  --let apply (e : Syntax) (g : MVarId) := g.withContext do g.apply (←elabTerm e none) cfg
  let apply (e : Syntax) (g : MVarId) : TacticM (List MVarId) := g.withContext do
    let gs ← withTransparency .default (g.apply (←elabTerm e none) cfg)
    gs.filterM (fun g ↦ try g.inferInstance; pure false catch _ => pure true)
  -- Find matches and try to apply them
  let search (g : MVarId) : TacticM Unit := g.withContext do
    let s ← saveState
    let t ← g.getType
    -- Loop over matches in reverse order
    for v in (←tree.getMatch t discrTreeConfig).reverse do match v with
      | .expr e =>
        g.assign e
        Tactic.setGoals []
        return
      | .syn e lt => do
        try
          if lt then
            let [g] ← apply (mkIdent ``le_of_lt) g | failure
            Tactic.setGoals (←apply e g)
          else
            Tactic.setGoals (←apply e g)
          return
        catch _ => s.restore
    failure
  -- norm_num as a finishing tactic
  let norm_num := do NormNum.elabNormNum .missing .missing; Tactic.done
  -- Iterate!
  let step := do
    search (←getMainGoal) <|> norm_num
  repeatD step 10

/-- `bound` tactic for proving inequalities via straightforward recursion on expression structure -/
elab "bound" lemmas:(("[" term,* "]")?) : tactic => do
  bound (maybeTerms lemmas)

section positive_tests
variable {n : ℕ}
variable {x y : ℝ}
variable {u : ℝ≥0}
variable {z : ℂ}
lemma test_pos_lt_sq (h : 0 < x) : x^2 > 0 := by bound
lemma test_pos_gt_sq (h : x > 0) : x^2 > 0 := by bound
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
variable {n : ℕ}
variable {x y : ℝ}
variable {u : ℝ≥0}
variable {z : ℂ}
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
variable {a b c x y : ℝ}
variable {z : ℂ}
variable {n : ℕ}
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
lemma test_log (x y : ℝ) (x0 : 0 < x) (h : x ≤ y) : x.log ≤ y.log := by bound [Real.log_le_log]
end bound_tests

-- This breaks without appropriate g.withContext use
lemma test_with_context {s : Set ℂ} (o : IsOpen s) (z) (h : z ∈ s) : ∃ r : ℝ, r > 0 := by
  rw [Metric.isOpen_iff] at o
  rcases o z h with ⟨t, tp, bs⟩
  exists t/2
  clear o h bs z s
  bound

-- Test various elaboration issues
lemma test_try_elab {f : ℂ → ℂ} {z w : ℂ} {s r c e : ℝ}
      (sc : ∀ {w}, abs (w - z) < s → abs (f w - f z) < e) (wz : abs (w - z) < s) (wr : abs w < r)
      (h : ∀ z : ℂ, abs z < r → abs (f z) ≤ c * abs z) :
      abs (f z) ≤ c * abs w + e := by
  calc abs (f z) = abs (f w - (f w - f z)) := by ring_nf
    _ ≤ abs (f w) + abs (f w - f z) := Complex.abs.sub_le' _ _
    _ ≤ c * abs w + e := by bound [h w wr, sc wz]

-- Test a lemma that requires function inference
lemma test_fun_inference {α : Type} {s : Finset α} {f g : α → ℂ} :
    ‖s.sum (fun x ↦ f x + g x)‖ ≤ s.sum (fun x ↦ ‖f x + g x‖) := by
  bound [norm_sum_le]

-- A test that requires reduction to weak head normal form to work (surfaced by `Hartogs.lean`)
lemma test_whnf (x y : ℝ) (h : x < y ∧ True) : x ≤ y := by
  bound [h.1]
