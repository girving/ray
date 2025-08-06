import Batteries.Data.ByteArray
import Mathlib.Data.Nat.Basic
import Interval.Misc.Array

/-!
# `Array` and `ByteArray` lemmas
-/

lemma ByteArray.get!_eq_getElem! {d : ByteArray} {k : ℕ} :
    d.get! k = d[k]! := by
  simp only [ByteArray.get!, GetElem?.getElem!, outOfBounds_eq_default, decidableGetElem?]
  split_ifs with h
  · rw [Array.get!Internal_eq_getElem!, ByteArray.getElem_eq_data_getElem, getElem!_pos d.data k h]
  · simp only [not_lt, ByteArray.size] at h
    simp only [Array.get!Internal_eq_getElem!, Array.getElem!_eq_getD, Array.getD,
      Array.getInternal_eq_getElem, dite_eq_right_iff]
    omega

lemma ByteArray.getElem_eq_getElem!' {d : ByteArray} {i : ℕ} {h : i < d.size} :
    d[i]'h = d[i]! := by
  exact Eq.symm (getElem!_pos d i h)
