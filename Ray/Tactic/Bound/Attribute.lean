/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Aesop.Frontend.Attribute
import Ray.Tactic.Bound.Init

/-!
# The `bound` attribute

Any lemma tagged with `@[bound]` is registered as an apply rule for the `bound` tactic, by
converting it to either `norm apply` or `safe apply <priority>`.  The classification is based
on the number and types of the lemmas hypotheses.
-/

namespace Bound

initialize Lean.registerTraceClass `bound.attribute

/-- Map a hypothesis type to a score -/
partial def hypPriority (decl name : Lean.Name) (hyp : Lean.Expr) : Lean.MetaM Nat := do
  match hyp.getAppFnArgs with
    -- Conjections add scores
    | (`And, #[a, b]) => pure <| (← hypPriority decl name a) + (← hypPriority decl name b)
    -- Guessing (disjunction) gets a big penalty
    | (`Or, #[a, b]) => pure <| 100 + (← hypPriority decl name a) + (← hypPriority decl name b)
    -- Inequalities get score 1 if they contain zero, 10 otherwise
    | (`LE.le, #[_, _, a, b]) => pure <| ineq a b
    | (`LT.lt, #[_, _, a, b]) => pure <| ineq a b
    | (`GE.ge, #[_, _, a, b]) => pure <| ineq a b
    | (`GT.gt, #[_, _, a, b]) => pure <| ineq a b
    -- Assume anything else is non-relevant
    | _ => pure 0
    where
    ineq (a b : Lean.Expr) : Nat := if isZero a || isZero b then 1 else 10
    isZero : Lean.Expr → Bool
      | .lit (.natVal 0) => true
      | .const `Zero.zero _ => true
      | .app (.app (.app (.const `OfNat.ofNat _) _) z) _ => isZero z
      | _ => false

/-- Map a type to a score -/
def typePriority (decl : Lean.Name) (type : Lean.Expr) : Lean.MetaM Nat := do
  match type with
    | .forallE a h t i => do
      pure <| (← typePriority decl t) +
        (← bif i == .default then do
          let p ← hypPriority decl a h
          pure p
        else pure 0)
    | _ => match type.getAppFnArgs.1 with
      | `LE.le => return 0
      | `LT.lt => return 0
      | `GE.ge => return 0
      | `GT.gt => return 0
      | _ => throwError (f!"`{decl}` has invalid type `{type}` as a bound lemma")

/-- Map a theorem decl to a score (0 means `norm apply`, `0 <` means `safe apply`) -/
def declPriority (decl : Lean.Name) : Lean.MetaM Nat := do
  match (← Lean.getEnv).find? decl with
    | some info => do
        typePriority decl info.type
    | none => throwError "unknown declaration {decl}"

/-- Map a score to either `norm apply` or `safe apply <priority>` -/
def scoreToConfig (decl : Lean.Name) (score : Nat) : Aesop.Frontend.RuleConfig :=
  let (phase, priority) := match score with
    | 0 => (Aesop.PhaseName.norm, 0)  -- No hypotheses: this rule closes the goal immediately
    | s => (Aesop.PhaseName.safe, s)
  { term? := some (Lean.mkIdent decl)
    phase? := phase
    priority? := some (Aesop.Frontend.Priority.int priority)
    builder? := some (.regular .apply)
    builderOptions := {}
    ruleSets := ⟨#[`Bound]⟩ }

initialize Lean.registerBuiltinAttribute {
  name := `bound
  descr := "Register a theorem as an apply rule for the `bound` tactic."
  applicationTime := .afterCompilation
  add := fun decl stx attrKind => Lean.withRef stx do
    let score ← Aesop.runTermElabMAsCoreM <| declPriority decl
    trace[bound.attribute] "{decl} has score {score}"
    let context ← Aesop.runMetaMAsCoreM Aesop.ElabM.Context.forAdditionalGlobalRules
    let (rule, ruleSets) ← Aesop.runTermElabMAsCoreM <|
      (scoreToConfig decl score).buildGlobalRule.run context
    for ruleSet in ruleSets do
      Aesop.Frontend.addGlobalRule ruleSet rule attrKind (checkNotExists := true)
  erase := fun decl =>
    let ruleFilter := { name := decl, scope := .global, builders := #[], phases := #[] }
    Aesop.Frontend.eraseGlobalRules Aesop.RuleSetNameFilter.all ruleFilter (checkExists := true)
}

-- Attribute for `forward` rules for the `bound` tactic
macro "bound_forward" : attr =>
  `(attr|aesop safe forward (rule_sets := [$(Lean.mkIdent `Bound):ident]))
