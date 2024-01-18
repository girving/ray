import Ray.Dynamics.Mandelbrot
import Ray.Render.Color

/-!
## Approximate computation of the Mandelbrot potential function

Fix `c`, and let `p z = potential 2 c z` be the potential function for the `c`-Julia set.  Say we
iterate `n` times to get `w = f^[n] z`.  There are two cases

#### Case 1: `abs w ≤ 4`

By `le_potential`, we have

  `0.216 ≤ p w`
  `0.216 ^ (2^n)⁻¹ ≤ p z`.

Not very many iterations will give us a lower bound very close to `1`.

#### Case 2: `4 ≤ abs w`

Increasing `n` by 1 if necessary, we have `6 ≤ abs w`.  By `potential_approx` and
`potential_error_le_of_z6`, we have

  `|p w - 1/abs w| ≤ 0.8095 / abs z ^ 1.927`

Here is an `abs w : 1/abs w, RHS` table for various `abs w` values:

  `w    6: 1/w 0.16667, error 2.563e-2, ratio 0.153`
  `w   32: 1/w 0.03125, error 1.018e-3, ratio 0.032`
  `w 1020: 1/w 0.00098, error 1.290e-6, ratio 0.001`

### What to do about the `rpow`?

In either case, we get a nice estimate for `p w`, and need to apply `fun p ↦ p ^ (2^n)⁻¹` to
recover an estimate for `p z.`  The straightforward thing to do is implement `Interval.rpow`, though
that would take significant effort: I'd do it via Taylor series for `log` and `exp`.
-/

open Complex (abs)
open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩
