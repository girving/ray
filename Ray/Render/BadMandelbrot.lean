import Interval.Box.Basic
import Ray.Render.Grid
import Ray.Render.Mandelbrot
import Ray.Render.PNG
import Ray.Render.Potential

/-!
## Bad Mandelbrot images where each pixel corresponds to just one point

This is a warmup: our real images will have each pixel corresponding to an integral
over a square, partitioning the plain.  But these we can draw without the Koebe quarter theorem.
-/

/-- A particular grid around the Mandelbrot set -/
def grid : Grid :=
  .square ⟨-2.6, -1.8⟩ ⟨1.3, 1.8⟩ 200 -- 2048  -- 256

/-- Transparent at infinity, blue near Mandelbrot set, black if we use the lower bound -/
def worse_potential_image (n : ℕ) (r : Floating) (c : ℚ × ℚ) : Color UInt8 :=
  let c := Box.ofRat c
  let p := c.potential c n r
  match p with
    | (_, .nan) => nan
    | (_, .small) => inside'.quantize
    | (p, .large) => (lerp p.sqr.sqr.sqr.sqr clear' outside').quantize

def main : IO Unit := do
  let f := worse_potential_image (n := 50) (r := 1000)
  let i := Image.ofGrid grid (chunk := 128) f
  let n := (i.find_grid grid (fun _ c ↦ c == nan))[:10]
  IO.print ("nans = " ++ repr n)
  i.write_png "bad-mandelbrot.png"
