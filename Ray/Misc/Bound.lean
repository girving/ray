import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Trigonometric

/-!
## Register some bound lemmas
-/

attribute [bound] norm_add_le mul_lt_of_lt_one_left Complex.normSq_nonneg norm_inner_le_norm
  Units.norm_pos Real.cosh_pos
