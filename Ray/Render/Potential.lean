import Ray.Approx.Box
import Ray.Approx.Floating.Conversion
import Ray.Approx.Series
import Ray.Dynamics.Mandelbrot
import Ray.Render.Color
import Ray.Render.Iterate

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

  `|p w - 1/abs w| ≤ 0.8095 / abs w ^ 1.927`

Here is an `abs w : 1/abs w, RHS` table for various `abs w` values:

  `w    6: 1/w 0.16667, error 2.563e-2, ratio 0.153`
  `w   32: 1/w 0.03125, error 1.018e-3, ratio 0.032`
  `w 1020: 1/w 0.00098, error 1.290e-6, ratio 0.001`

We then finish with

  `p z = p w ^ (2^n)⁻¹`
-/

open Complex (abs)
open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-!
### Potential approximation routines
-/

/-- Repeated square roots: `x ^ (2 ^ -n)` -/
@[irreducible] def Interval.iter_sqrt (x : Interval) (n : ℕ) : Interval :=
  exp ((log x).scaleB' (-.ofNat0 n))

/-- Approximate the potential of a large `z`.
    The estimate is independent of `c`, but is only valid if `6, abs c ≤ abs z` -/
@[irreducible] def Box.potential_large (z : Box) : Interval :=
  let s := z.normSq
  -- We have `|p j.z - s ^ (-1/2)| ≤ 0.8095 * s ^ -0.9635`
  -- `s ^ a = exp (a * log s)`, so we'll CSE the `log s`
  let log_s := s.log
  (-log_s.scaleB (-1)).exp.grow (0.8095 * (-0.9635 * log_s).exp).hi

/-- Approximate the potential of a small `z` (valid for `abs c, abs z ≤ 4`) -/
@[irreducible] def Box.potential_small : Interval :=
  0.216 ∪ 1

/-- Approximate the Mandelbrot potential function at any point -/
@[irreducible] def Box.potential (c z : Box) (n : ℕ) (r : Floating) : Interval :=
  let i := iterate c z 3 n
  match i.exit with
  | .nan => nan
  | .large =>
    -- We're outside radius `3` after `i.n` iterations.  Iterate a bit more to make `z` very large,
    -- then use our large `z` potential bound.  This should always work, so we use a large count.
    let rc := (r.mul r true).max (c.normSq.hi.max 36)  -- We need `6, abs c ≤ abs z`
    if rc = nan then nan else
    let j := iterate' c i.z rc i.n 1000
    match j.exit with
    | .large => (potential_large j.z).iter_sqrt j.n
    | _ => nan  -- If we fail to leave the large radius, give up
  | .count =>
    -- We know we're `≤ 3`.  Check that we're `≤ 4`, bail if not, and use the small bound if so.
    bif 4 < i.z.normSq.hi then nan else
    potential_small.iter_sqrt i.n

/-!
### Correctness proof
-/

/-- `Interval.iter_sqrt` is conservative -/
@[mono] lemma Interval.mem_approx_iter_sqrt {a : ℝ} {x : Interval} {n : ℕ} (ax : a ∈ approx x) :
    a ^ (2 ^ (-n : ℝ) : ℝ) ∈ approx (x.iter_sqrt n) := by
  rw [iter_sqrt]
  by_cases a0 : a ≤ 0
  · simp only [log_nonpos a0 ax, nan_scaleB', exp_nan, approx_nan, mem_univ]
  · rw [Real.rpow_def_of_pos (not_le.mp a0)]
    mono

/-- `Box.potential` is conservative -/
@[mono] lemma Box.mem_approx_potential {c' z' : ℂ} {c z : Box}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (n : ℕ) (r : Floating) :
    (superF 2).potential c' z' ∈ approx (Box.potential c z n r) := by
  set s := superF 2
  rw [Box.potential]
  sorry
