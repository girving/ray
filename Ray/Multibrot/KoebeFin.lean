import Ray.Koebe.Koebe
import Ray.Multibrot.BottcherInv

/-!
# The Koebe quarter theorem at finite values, for ruling disks out of the Mandelbrot set
-/

open Complex
open Function (uncurry)
open Filter (Tendsto)
open Metric (ball)
open RiemannSphere
open OneDimension
open Set
open scoped OneDimension OnePoint RiemannSphere Topology
noncomputable section

variable {c x z : ℂ} {r : ℝ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

