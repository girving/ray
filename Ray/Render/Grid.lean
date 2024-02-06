import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
## Rectangular grids over `ℂ`

These define what it means to exactly render a continuous image into a grid.
-/

open Set

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A rectangular grid in `ℂ` -/
structure Grid where
  /-- Lower left corner of our box -/
  lo : ℚ × ℚ
  /-- Upper right corner of our box -/
  hi : ℚ × ℚ
  /-- Number of cells in each dimension -/
  n : ℕ × ℕ

/-- Grid spacing -/
noncomputable def Grid.dz (g : Grid) : ℂ :=
  ⟨(g.hi.1 - g.lo.1) / g.n.1, (g.hi.2 - g.lo.2) / g.n.2⟩

/-- A vertex of the grid -/
noncomputable def Grid.vertex (g : Grid) (k : ℕ × ℕ) : ℂ :=
  ⟨g.lo.1 + k.1 * g.dz.1, g.lo.2 + k.2 * g.dz.2⟩

/-- The set of points in a cell -/
noncomputable def Grid.cell (g : Grid) (k : ℕ × ℕ) : Set ℂ :=
  let lo := g.vertex k
  let hi := g.vertex (k + 1)
  Complex.equivRealProdCLM.symm '' Icc lo.re hi.re ×ˢ Icc lo.im hi.im

/-- The mean of a function over a grid cell -/
noncomputable def Grid.mean (g : Grid) (k : ℕ × ℕ) (f : ℂ → E) : E :=
  ⨍ z in g.cell k, f z
