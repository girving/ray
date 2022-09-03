-- Bottcher map for Julia sets

import logic.basic
noncomputable theory

-- Values that make sense only on a set
def if_p {A : Type} [has_zero A] (P : Prop) (f : P → A) : A :=
  @dite _ _ (classical.dec P) (λ p, f p) (λ _, 0)

lemma if_p_true {A : Type} [has_zero A] {P : Prop} {f : P → A} (p : P) : if_p P f = f p := by { rw if_p, simp [p] }
lemma if_p_false {A : Type} [has_zero A] {P : Prop} {f : P → A} (p : ¬P) : if_p P f = 0 := by { rw if_p, simp [p] }

-- If the body of if_p does not depend on the P, we can drop it on a set where P holds
lemma if_p_const' {A B : Type} [has_zero B] {f : A → B}
    (s : set A) (P : A → Prop) (p : ∀ a, a ∈ s → P a)
    : ∀ a, a ∈ s → if_p (P a) (λ _, f a) = f a := begin
  intros a m, rw if_p_true (p a m)
end

-- Special case of if_p_const' where P = a ∈ s
lemma if_p_const {A B : Type} [has_zero B] {f : A → B} (s : set A)
    : ∀ a : A, a ∈ s → if_p (a ∈ s) (λ _, f a) = f a := begin
  intros a m, rw if_p_true m
end