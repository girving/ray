import Ray.Approx.Floating.Basic
import Ray.Approx.Floating.Conversion

/-!
## Floating point `log2`
-/

open Set
open scoped Real
namespace Floating

/-- `n` s.t. `2^n ≤ |x| < 2^(n+1)`, or `nan` -/
@[irreducible, pp_dot] def log2 (x : Floating) : Fixed 0 :=
  bif x == 0 || x == nan || x.s == .max then nan else
  -- The result is `x.n.abs.log2 + x.s - 2^63` if that doesn't overflow.
  let a : Fixed 0 := ⟨⟨x.n.abs.log2⟩ - 1⟩
  let b : Fixed 0 := ⟨⟨x.s - 2^63 + 1⟩⟩
  a + b

/-!
### Unit tests

For now we only test `Floating.log2`, not prove it correct.  We can add the
proofs if we start using it in trusted settings.
-/

example : log2 (ofNat (2^157) false) == 157 := by native_decide
example : log2 (ofInt (-2^157) false) == 157 := by native_decide
example : log2 (ofNat (2^157 + 1) true) == 157 := by native_decide
example : log2 (ofInt (-1 - 2^157) false) == 157 := by native_decide
example : log2 (ofNat (2^157 - 1) false) == 156 := by native_decide
example : log2 (ofInt (1 - 2^157) true) == 156 := by native_decide
example : log2 (ofRat (2^(-157 : ℤ)) false) == -157 := by native_decide
example : log2 (ofRat (-2^(-157 : ℤ)) false) == -157 := by native_decide
