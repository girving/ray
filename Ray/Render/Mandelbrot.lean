import Mathlib.Data.Pi.Algebra
import Ray.Dynamics.Mandelbrot
import Ray.Render.Color

/-!
## Pictures of the Mandelbrot set

We define a variety (at least one?) of maps from `ℂ → Color`, illustrating the Mandelbrot set.
-/

open Classical
open Set

local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

-- Colors used below
def inside : Color32 := ⟨0, 0, 0, 255⟩
def outside : Color32 := ⟨50, 70, 245, 255⟩
def far : Color32 := ⟨95, 205, 250, 255⟩

/-- Blue outside, black inside -/
noncomputable def solid (z : ℂ) : Color :=
  if z ∈ mandelbrot then inside.val else outside.val

/-- Blue outside varying with potential, black inside -/
noncomputable def smooth (z : ℂ) : Color :=
  if z ∈ mandelbrot then inside.val else
  let p := potential 2 z
  (1-p) • far.val + p • outside.val
