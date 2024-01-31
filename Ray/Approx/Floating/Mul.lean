import Ray.Approx.Floating.Abs
import Ray.Approx.Floating.Neg
import Ray.Approx.Floating.Standardization

open Pointwise

/-!
## Floating point multiplication

For floating point, multiplication is easier than addition, as the exponent adds.
If `z = x * y`, we have

  `z.n * 2^(z.s - 2^63) = x.n * y.n * 2^(x.s + y.s - 2^63 - 2^63)`
-/

open Set
open scoped Real
namespace Floating

/-!
### Auxiliary lemmas
-/

/-- The limit for our 64 bit → 128 bit multiplication -/
def mul_n_max : ℕ := (2^63 - 1) ^ 2

/-- Our 64 → 128 bit multiplication doesn't get too big -/
lemma mul_n_le {x y : Floating} (x0 : 0 ≤ x.val) (y0 : 0 ≤ y.val) :
    (mul128 x.n.n y.n.n).toNat ≤ mul_n_max := by
  rw [toNat_mul128, mul_n_max, pow_two]
  have hx := n_lt_of_nonneg x0
  have hy := n_lt_of_nonneg y0
  exact Nat.mul_le_mul (by omega) (by omega)

/-!
### The definition of multiplication
-/

/-- Normalize a 128-bit `n` into a 64-bit one, rounding and shifting as necessary. -/
@[irreducible, inline] def mul_norm (n : UInt128) (up : Bool) : UInt64 × UInt64 :=
  let t := n.log2
  -- Shift left to normalize
  let z : UInt128 := n <<< (126 - t)
  -- Round to a single word
  let r : UInt64 := z.hi + bif z.lo != 0 && up then 1 else z.hi
  (r, t)

/-- `mul_norm` returns a normalized value -/
lemma mul_norm_norm (n : UInt128) (up : Bool) (lo : n.toNat ≤ mul_n_max) :
    (mul_norm n up).1.toNat ∈ Ico (2^62) (2^63) := by
  sorry

/-- Build a `Floating` with value `n * 2^s`, rounding if necessary -/
@[irreducible, inline] def mul_finish (n : UInt64) (s : UInt128) (up : Bool)
    (norm : n.toNat ∈ Ico (2^62) (2^63)) : Floating :=
  bif s.hi == 0 then { -- Exponent is already 64 bits, so not much to do
    n := ⟨n⟩
    s := s.lo
    zero_same := by
      intro n0
      simp only [Int64.ext_iff, Int64.n_zero] at n0
      simp only [n0, UInt64.toNat_zero, mem_Ico, nonpos_iff_eq_zero, gt_iff_lt, zero_lt_two,
        pow_pos, and_true] at norm
    nan_same := by
      intro nm
      simp only [Int64.ext_iff, Int64.n_min] at nm
      simp only [nm, UInt64.toNat_2_pow_63, mem_Ico, lt_self_iff_false, and_false] at norm
    norm := by
      intro _ _ _
      simp only [mem_Ico] at norm
      rw [Int64.abs_eq_self']
      · simp only [UInt64.le_iff_toNat_le, up62, norm.1]
      · simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, norm.2] }
  else bif s.hi < 1 <<< 63 then nan -- Overflow, exponent too big
  else bif up then min_norm else 0  -- Flush denormals for now

/-- Twos complement, 128-bit exponent `e = xs + ys + t - 126 - 2^64` -/
@[irreducible, inline] def mul_exponent (xs ys t : UInt64) : UInt128 :=
  let xs : UInt128 := ⟨xs,0⟩
  let ys : UInt128 := ⟨ys,0⟩
  let t : UInt128 := ⟨t,0⟩
  let c : UInt128 := ⟨62,1⟩
  xs + ys + t - c

/-- Multiply two positive, non-nan `Floating`s -/
@[irreducible, inline] def mul_of_pos (x y : Floating) (up : Bool)
    (x0 : 0 ≤ x.val) (y0 : 0 ≤ y.val) : Floating :=
  let z := mul128 x.n.n y.n.n  -- `z * 2^(x.s + y.s - 2^64)`.
  let n := mul_norm z up  -- `n.1 * 2^(x.s + y.s + n.2 - 62 - 2^64)`
  let e := mul_exponent x.s y.s n.2  -- `n.1 * 2^e`
  mul_finish n.1 e up (mul_norm_norm z up (mul_n_le x0 y0))

/-- Floating point multiply -/
@[irreducible] def mul (x y : Floating) (up : Bool) : Floating :=
  if n : x = nan ∨ y = nan then nan else
  bif x == 0 || y == 0 then 0 else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_pos x.abs y.abs (up.xor p)
    (abs_nonneg (not_or.mp n).1) (abs_nonneg (not_or.mp n).2)
  bif p then -z else z
