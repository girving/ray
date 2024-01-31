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

/-- Multiply two positive, non-nan `Floating`s -/
@[irreducible, inline] def mul_of_pos (x y : Floating) (up : Bool) : Floating :=
  let z := mul128 x.n.n y.n.n
  let t := z.log2
  
  sorry
  --let d : Fixed 0 := ⟨s⟩ + ⟨t⟩ - ⟨u⟩
  --bif d == nan then nan else
  --let z := mul128 x.n.n y.n.n
  --of_raw_uint128 (bif d.n.isNeg then z.shiftRightRound (-d.n).n up else z.shiftLeftSaturate d.n.n)

/-- Floating point multiply -/
@[irreducible] def mul (x y : Floating) (up : Bool) : Floating :=
  bif x == nan || y == nan then nan else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_pos x.abs y.abs (up.xor p)
  bif p then -z else z
