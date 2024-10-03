import Interval.Box.Basic
import Interval.Interval.Conversion
import Ray.Dynamics.Mandelbrot
import Ray.Render.Color
import Ray.Render.Potential

/-!
## Pictures of the Mandelbrot set

We define some maps `ℂ → Color` which illustrate the Mandelbrot set.
-/

open Classical
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

-- Colors used below
def clear : Color ℚ := ⟨0, 0, 0, 0⟩
def inside : Color ℚ := ⟨0, 0, 0, 1⟩
def outside : Color ℚ := ⟨0.196, 0.274, 0.96, 1⟩
def green : Color ℚ := ⟨0.196, 0.96, 0.274, 1⟩
def far : Color ℚ := ⟨0.372, 0.803, 1, 1⟩

/-- Blue outside, black inside -/
noncomputable def solid_image (c : ℂ) : Color ℚ :=
  if c ∈ mandelbrot then inside else outside

/-- Blue outside varying with potential, black inside -/
noncomputable def smooth_image (c : ℂ) : Color ℝ :=
  if c ∈ mandelbrot then (inside : Color ℝ) else
  let p := potential 2 c
  lerp p far outside

/-- Transparent at infinity, blue at the Mandelbrot set -/
noncomputable def potential_image (c : ℂ) : Color ℝ :=
  let p := potential 2 c
  let t := p ^ 16
  lerp t clear outside

/-!
### Bad intervals approximations, evaluating at single points only
-/

-- Interval versions of colors
def clear' : Color Interval := .ofRat clear
def inside' : Color Interval := .ofRat inside
def outside' : Color Interval := .ofRat outside
def green' : Color Interval := .ofRat green
def far' : Color Interval := .ofRat far

/-- Transparent at infinity, blue at the Mandelbrot set -/
def bad_potential_image (n : ℕ) (r : Floating) (c : ℚ × ℚ) : Color UInt8 :=
  let c := Box.ofRat c
  let p := c.potential c n r
  let t := p.1.sqr.sqr.sqr.sqr
  let i := lerp t clear' outside'
  i.quantize

/-- `potential_image'` is conservative -/
lemma approx_bad_potential_image {c : ℚ × ℚ} {n : ℕ} {r : Floating} :
    potential_image c ∈ approx (bad_potential_image n r c) := by
  rw [potential_image, bad_potential_image]
  have e : ∀ p : ℝ, p^16 = (((p^2)^2)^2)^2 := by intro p; simp only [← pow_mul]
  simp only [far', outside', clear', green', e]
  -- mono is timing out for some reason, so we expand a bit
  apply Color.mem_approx_quantize
  apply mem_approx_lerp
  · repeat apply Interval.mem_approx_sqr
    approx
  · approx
  · approx
