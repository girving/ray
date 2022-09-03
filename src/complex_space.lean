-- Type class for ℂ or ℂ × ℂ

import analysis.complex.basic
import analysis.normed.group.basic
import analysis.normed_space.basic
import data.complex.basic

open complex (abs I)
open_locale topological_space
noncomputable theory

-- The finite dimensional complex vector spaces.
-- Actually just ℂ or ℂ × ℂ, since we only have 2D Osgood.
@[class]
structure complex_space (T : Type) [normed_add_comm_group T] [normed_space ℂ T] : Type :=
  (to_normed_add_comm_group : normed_add_comm_group T)
  (to_normed_space : normed_space ℂ T)
  (is_C_or_C2 : T = ℂ ∨ T = (ℂ × ℂ))

@[instance]
def complex.complex_space : complex_space ℂ := {
  to_normed_add_comm_group := complex.normed_add_comm_group,
  to_normed_space := normed_field.to_normed_space,
  is_C_or_C2 := or.inl rfl,
}

@[instance]
def complex2.complex_space : complex_space (ℂ × ℂ) := {
  to_normed_add_comm_group := prod.normed_add_comm_group,
  to_normed_space := prod.normed_space,
  is_C_or_C2 := or.inr rfl,
}