module
public import Mathlib.Data.Set.Basic
public import Mathlib.Tactic

/-!
## `Set` facts
-/

open Set

variable {α : Type}

public lemma Set.diff_union {s u v : Set α} : s \ (u ∪ v) = (s \ u) \ v := by
  ext x
  aesop
