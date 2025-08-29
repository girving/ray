import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Trigonometric

/-!
## Register some bound lemmas
-/

variable {α G₀ : Type*}

attribute [bound] norm_add_le mul_lt_of_lt_one_left Complex.normSq_nonneg norm_inner_le_norm
  Units.norm_pos Real.cosh_pos norm_sub_norm_le neg_le_self Finset.norm_prod_le
  Real.toNNReal_le_toNNReal

@[bound] private alias ⟨_, Bound.ennreal_coe_pos⟩ := ENNReal.coe_pos

@[bound] private lemma Bound.lt_mul_of_one_lt_left [MulOneClass α] [Zero α] {a b : α} [Preorder α]
    [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) (b1 : 1 < b) : a < b * a :=
  (lt_mul_iff_one_lt_left a0).mpr b1

@[bound] private lemma Bound.one_le_div₀ [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀]
    {a b : G₀} (hb : 0 < b) (ba : b ≤ a) : 1 ≤ a / b :=
  (_root_.one_le_div₀ hb).mpr ba

@[bound] private lemma Bound.nat_cast_le [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α]
    [ZeroLEOneClass α] [CharZero α] {m n : ℕ} (h : m ≤ n) : (m : α) ≤ n :=
  Nat.cast_le.mpr h
