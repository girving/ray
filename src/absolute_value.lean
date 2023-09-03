-- Absolute value theorems

import algebra.order.absolute_value

lemma absolute_value.le_add {R S : Type} [ring R] [ordered_comm_ring S] [no_zero_divisors S]
    (abv : absolute_value R S) (a b : R)
    : abv a - abv b ≤ abv (a + b) := begin
  have h := abv.add_le (a + b) (-b),
  simp at h,
  simpa,
end

lemma absolute_value.sub_le' {R S : Type} [comm_ring R] [ordered_comm_ring S] [no_zero_divisors S]
    (abv : absolute_value R S) (a b : R)
    : abv (a - b) ≤ abv a + abv b := begin
  have h := abv.add_le a (-b),
  simp [←sub_eq_add_neg] at h,
  exact h,
end