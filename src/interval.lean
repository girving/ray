-- Interval membership tactic

import tactics

open interactive (parse)
open interactive.types
open lean.parser (ident many tk)
open set

-- Apply versions of mem_Ixx
variables {P : Type} [preorder P]
lemma mem_Ioo' {x a b : P} (ax : a < x) (xb : x < b) : x ∈ Ioo a b := mem_Ioo.mpr ⟨ax,xb⟩
lemma mem_Ico' {x a b : P} (ax : a ≤ x) (xb : x < b) : x ∈ Ico a b := mem_Ico.mpr ⟨ax,xb⟩
lemma mem_Icc' {x a b : P} (ax : a ≤ x) (xb : x ≤ b) : x ∈ Icc a b := mem_Icc.mpr ⟨ax,xb⟩
lemma mem_Ioc' {x a b : P} (ax : a < x) (xb : x ≤ b) : x ∈ Ioc a b := mem_Ioc.mpr ⟨ax,xb⟩
lemma mem_Ioi' {x a : P} (ax : a < x) : x ∈ Ioi a := mem_Ioi.mpr ax
lemma mem_Ici' {x a : P} (ax : a ≤ x) : x ∈ Ici a := mem_Ici.mpr ax
lemma mem_Iio' {x b : P} (xb : x < b) : x ∈ Iio b := mem_Iio.mpr xb
lemma mem_Iic' {x b : P} (xb : x ≤ b) : x ∈ Iic b := mem_Iic.mpr xb

-- Rules used by the interval tactic
@[user_attribute] meta def interval_rules : user_attribute := {
  name := `interval_rules, descr := "Rules for the interval tactic" }
attribute [interval_rules] mem_Ioo' mem_Ico' mem_Icc' mem_Ioc' mem_Ioi' mem_Ici' mem_Iio' mem_Iic'

-- Resolution of interval membership queries by reduction to linarith
meta def interval (args : list pexpr) : tactic unit := do
  -- Add args to local context
  monad.mapm' (λ e, do e ← tactic.to_expr e, _ ← tactic.note `this none e, return ()) args,
  -- Expand mem_Ixx and ands
  notes [``(mem_Ioo.mp), ``(mem_Ico.mp), ``(mem_Icc.mp), ``(mem_Ioc.mp),
         ``(mem_Ioi.mp), ``(mem_Ici.mp), ``(mem_Iio.mp), ``(mem_Iic.mp),
         ``(and.elim_left), ``(and.elim_right)] [],
  -- Apply interval_rules, then close with linarith
  /-
  tactic.apply_rules [] [`interval_rules] 32 {unify := ff},
  tactic.repeat (tactic.linarith false false [] {})
  -/
  attr_exprs ← tactic.lock_tactic_state $ [`interval_rules].mfoldl
    (λ l n, list.append l <$> tactic.resolve_attribute_expr_list n) [],
  tactic.iterate_at_most_on_subgoals 8 (
    tactic.assumption <|>
    tactic.apply_list_expr {unify := ff} attr_exprs <|>
    tactic.linarith false false [] {})

-- Extract all inequalities from 

-- Resolve inequalities and interval membership by chaining inequalities

meta def tactic.interactive.interval (hs : parse opt_pexpr_list) : tactic unit := interval hs