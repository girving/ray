import Mathlib

open Ideal Quotient

variable {R : Type*} [CommRing R] (m : Ideal R) [hmax : m.IsMaximal]

theorem isLocalRing_of_isAdicComplete_maximal [IsAdicComplete m R] : IsLocalRing R where
  exists_pair_ne := ⟨0, 1, ne_of_mem_of_not_mem m.zero_mem
    (m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax))⟩
  isUnit_or_isUnit_of_add_one {a b} hab := by
    simp only [isUnit_iff_notMem_of_isAdicComplete_maximal m]
    by_contra! h
    absurd m.add_mem h.1 h.2
    simpa [hab] using m.ne_top_iff_one.mp (Ideal.IsMaximal.ne_top hmax)
