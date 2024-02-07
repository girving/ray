import Mathlib.Data.Fin.Basic
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

@[simp] lemma ByteArray.size_mkEmpty (c : ℕ) : (ByteArray.mkEmpty c).size = 0 := by
  simp only [ByteArray.size, ByteArray.mkEmpty, Array.size_toArray, List.length_nil]

lemma ByteArray.getElem_eq_data_getElem' (d : ByteArray) (i : Fin d.size) :
    d[i] = d.data[i] := by
  rfl

lemma ByteArray.getElem_eq_get! (d : ByteArray) (i : Fin d.size) :
    d[i] = d.get! i := by
  simp only [ByteArray.get!, ByteArray.getElem_eq_data_getElem']
  rw [Array.get!_eq_getD, Array.getD]
  split_ifs with h
  · rfl
  · exfalso; exact h i.prop

lemma ByteArray.getElemNat_eq_get! (d : ByteArray) (i : ℕ) (h : i < d.size) :
    d[i] = d.get! i := by
  simp only [ByteArray.get!, ByteArray.getElem_eq_data_getElem']
  rw [Array.get!_eq_getD, Array.getD]
  split_ifs with b
  · rfl
  · exfalso; exact b h

lemma ByteArray.get!_push (d : ByteArray) (c : UInt8) (i : ℕ) :
    (d.push c).get! i = if i < d.size then d.get! i else if i = d.size then c else default := by
  split_ifs with lt e
  · have lt' : i < (d.push c).size := by simp only [ByteArray.size_push]; omega
    rw [←getElemNat_eq_get! _ _ lt', ←getElemNat_eq_get! _ _ lt, ByteArray.get_push_lt _ _ _ lt]
  · rw [e, ←getElemNat_eq_get!, ByteArray.get_push_eq]
  · simp only [not_lt] at lt
    simp only [ByteArray.get!, Array.get!, ByteArray.push_data, Array.getD_eq_get?, Array.get?,
      Array.size_push]
    split_ifs with b
    · omega
    · simp only [Option.getD_none]
