import Mathlib.Tactic.Linarith.Frontend

/-!
## `Array` lemmas
-/

variable {α : Type}

@[simp] lemma Array.range_getElem (n k : ℕ) (kn : k < (range n).size) :
    ((Array.range n)[↑k]'kn) = k := by
  have nn : ∀ n, (Nat.fold (fun b a ↦ push a b) n #[]).size = n := by
    intro n; induction' n with n h
    · simp only [Nat.fold, size_toArray, List.length_nil, Nat.zero_eq]
    · simp only [Nat.fold, size_push, h]
  induction' n with n h
  · simp only [range, Nat.fold, size_toArray, List.length_nil, not_lt_zero'] at kn
  · simp only [Nat.fold, flip, Array.get_push, range] at kn h ⊢
    by_cases lt : k < size (Nat.fold (fun b a ↦ push a b) n #[])
    · simp only [lt, h lt, dite_eq_ite, ite_true]
    · simp only [nn] at lt
      simp only [size_push, lt, dite_false, nn] at kn ⊢
      linarith
