import Ray.Approx.Box

/-!
## Approximate rendering definitions

We define what it means to approximately render a continuous image into a grid.
-/

open Set

variable {s : Int64}

structure Grid where
  /-- Lower left corner of the grid -/
  lo : Box s
  /-- Upper right corner of the grid -/
  hi : Box s
  /-- Number of grid cells in the real dimension -/
  nr : UInt64
  /-- Number of grid cells in the imaginary dimension -/
  ni : UInt64
  /-- We cache `dz` as it requires a division -/
  dz : Box s := ⟨(hi.re - lo.re) / nr, (hi.im - lo.im) / ni⟩

/-- Conservative estimate of a cell -/
def Grid.cell (g : Grid s) (r : UInt64) (i : UInt64) : Box s :=
