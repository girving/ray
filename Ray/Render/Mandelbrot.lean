import Mathlib.Data.Pi.Algebra
import Ray.Dynamics.Mandelbrot
import Ray.Render.Color

/-!
## Pictures of the Mandelbrot set

We define some maps `ℂ → Color` which illustrate the Mandelbrot set.
-/

open Classical
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

-- Colors used below
def clear : Color32 := ⟨0, 0, 0, 0⟩
def inside : Color32 := ⟨0, 0, 0, 255⟩
def outside : Color32 := ⟨50, 70, 245, 255⟩
def far : Color32 := ⟨95, 205, 250, 255⟩

/-- Blue outside, black inside -/
noncomputable def solid_image (z : ℂ) : Color :=
  if z ∈ mandelbrot then inside.val else outside.val

/-- Blue outside varying with potential, black inside -/
noncomputable def smooth_image (z : ℂ) : Color :=
  if z ∈ mandelbrot then inside.val else
  let p := potential 2 z
  (1-p) • far.val + p • outside.val

/-- Transparent at infinity, blue at the Mandelbrot set -/
noncomputable def potential_image (z : ℂ) : Color :=
  let p := potential 2 z
  (1-p) • clear.val + p • outside.val
