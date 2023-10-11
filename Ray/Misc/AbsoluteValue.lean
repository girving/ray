import Mathlib.Algebra.Order.AbsoluteValue

/-!
## Absolute value facts
-/

/-- Bound `abv (a + b)` from below via the triangle inequality -/
lemma AbsoluteValue.le_add {R S : Type} [Ring R] [OrderedCommRing S] [NoZeroDivisors S]
    (abv : AbsoluteValue R S) (a b : R) :
    abv a - abv b ≤ abv (a + b) := by
  have h := abv.add_le (a + b) (-b)
  simp at h
  simpa

/-- Bound `abv (a - b)` from above via the triangle inequality -/
lemma AbsoluteValue.sub_le' {R S : Type} [CommRing R] [OrderedCommRing S] [NoZeroDivisors S]
    (abv : AbsoluteValue R S) (a b : R)
    : abv (a - b) ≤ abv a + abv b := by
  have h := abv.add_le a (-b)
  simp [←sub_eq_add_neg] at h
  exact h
