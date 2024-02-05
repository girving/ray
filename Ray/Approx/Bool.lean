import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.NormNum.Core

open Classical

/-!
## `Bool` lemmas
-/

variable {α : Type}

@[simp] lemma decide_eq_not_decide (p q : Prop) [Decidable p] [Decidable q] :
    (decide p = !decide q) = decide (p ↔ ¬q) := by
  by_cases h : q
  · simp only [h, decide_True, Bool.not_true, decide_eq_false_iff_not, not_true, iff_false,
      decide_not, Bool.not_eq_true']
  · simp only [h, decide_False, Bool.not_false, decide_eq_true_eq, not_false_eq_true, iff_true]

lemma bif_if_congr {x : Bool} {y : Prop} {a b c d : α} {dy : Decidable y}
    (xy : x = y) (ac : a = c) (bd : b = d) :
    (bif x then a else b) = (@ite _ y dy c d) := by
  rw [ac, bd]
  by_cases h : y
  · simp only [h, decide_True] at xy
    simp only [h, xy, if_true, cond_true]
  · simp only [h, decide_False] at xy
    simp only [h, xy, if_false, cond_false]

/-- Better version of `Bool.beq_eq_decide_eq` that uses any `BEq` instance -/
lemma Bool.beq_eq_decide_eq' [BEq α] [DecidableEq α] [LawfulBEq α ] (x y : α) :
    (x == y) = decide (x = y) := by
  by_cases h : x == y
  · simp only [h, true_eq_decide_iff]; exact eq_of_beq h
  · simp only [h]
    by_cases e : x = y
    · simp only [e, beq_self_eq_true, not_true_eq_false] at h
    · simp only [e, _root_.decide_False]

@[simp] lemma Bool.beq_not_iff_ne (x y : Bool) : x = !y ↔ x ≠ y := by
  induction y
  · simp only [not_false, ne_eq, not_eq_false]
  · simp only [not_true, ne_eq, not_eq_true]

lemma bif_congr {x y : Bool} {a b c d : α} (xy : x = y) (ac : a = c) (bd : b = d) :
    (bif x then a else b) = bif y then c else d := by
  simp only [xy, ac, bd]

/-- Change `== !` to `!=` -/
@[simp] lemma Bool.beq_not_iff_bne (x y : Bool) : (x == !y) = (x != y) := by
  induction x; repeat { induction y; repeat norm_num }

/-- Change `bif` to `if` -/
lemma bif_eq_if {b : Bool} {x y : α} : (bif b then x else y) = if b then x else y := by
  induction b
  · simp only [_root_.cond_false, ite_false]
  · simp only [_root_.cond_true, ite_true]

lemma apply_decide {f : Bool → α} {p : Prop} {dp : Decidable p} :
    (f (@decide p dp)) = if p then f true else f false := by
  by_cases h : p; repeat simp [h]

lemma or_decide_eq_if {a : Bool} {p : Prop} {dp : Decidable p} :
    (a || (@decide p dp)) = if p then true else a := by
  by_cases h : p; repeat simp [h]

lemma decide_and_eq_if' {a : Bool} {p : Prop} {dp : Decidable p} :
    ((@decide p dp) && a) = if p then a else false := by
  by_cases h : p; repeat simp [h]

lemma and_decide_eq_if {a : Bool} {p : Prop} {dp : Decidable p} :
    (a && (@decide p dp)) = if p then a else false := by
  by_cases h : p; repeat simp [h]

lemma decide_and_eq_if {p q : Prop} {dp : Decidable (p ∧ q)} :
    @decide (p ∧ q) dp = if p then decide q else false := by
  by_cases h : p; repeat simp [h]

lemma decide_eq_if {p : Prop} {dp : Decidable p} : @decide p dp = if p then true else false := by
  by_cases h : p; repeat simp [h]

lemma if_or {X : Type} {p q : Prop} {dp : Decidable (p ∨ q)} {x y : X} :
    @ite _ (p ∨ q) dp x y = if p then x else if q then x else y := by
  by_cases h : p; repeat simp [h]

lemma if_and {X : Type} {p q : Prop} {dp : Decidable (p ∧ q)} {x y : X} :
    @ite _ (p ∧ q) dp x y = if p then if q then x else y else y := by
  by_cases h : p; repeat simp [h]

@[simp] lemma if_true_false {p : Prop} {dp : Decidable p} : @ite _ p dp True False = p := by
  by_cases h : p; repeat simp [h]

@[simp] lemma Bool.bne_eq_false {x y : Bool} : (x != y) = false ↔ x = y := by
  induction x; all_goals induction y; all_goals decide
