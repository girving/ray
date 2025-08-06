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

namespace Grid

/-- Grid spacing, `ℚ` version -/
def dz (g : Grid) : ℚ × ℚ :=
  ⟨(g.hi.1 - g.lo.1) / g.n.1, (g.hi.2 - g.lo.2) / g.n.2⟩

/-- A vertex of the grid -/
def vertex (g : Grid) (k : ℕ × ℕ) : ℚ × ℚ :=
  ⟨g.lo.1 + k.1 * g.dz.1, g.lo.2 + k.2 * g.dz.2⟩

/-- The center of a grid cell -/
def center (g : Grid) (k : ℕ × ℕ) : ℚ × ℚ :=
  ⟨g.lo.1 + (k.1 + 1/2) * g.dz.1, g.lo.2 + (k.2 + 1/2) * g.dz.2⟩

/-- `ℚ × ℚ → ℂ` -/
def lift (z : ℚ × ℚ) : ℂ := ⟨z.1, z.2⟩

/-- The set of points in a cell -/
noncomputable def cell (g : Grid) (k : ℕ × ℕ) : Set ℂ :=
  let lo := lift (g.vertex k)
  let hi := lift (g.vertex (k + 1))
  Complex.equivRealProdCLM.symm '' Icc lo.re hi.re ×ˢ Icc lo.im hi.im

/-- The mean of a function over a grid cell -/
noncomputable def mean (g : Grid) (k : ℕ × ℕ) (f : ℂ → E) : E :=
  ⨍ z in g.cell k, f z

/-- Make a grid with square cells, slightly enlarging the corners if necessary -/
def square (lo hi : ℚ × ℚ) (n : ℕ) : Grid :=
  let c : ℚ × ℚ := ⟨(lo.1 + hi.1) / 2, (lo.2 + hi.2) / 2⟩
  let d := hi - lo
  let dx := max d.1 d.2 / n
  let n : ℕ × ℕ := (max 1 (d.1 / dx).ceil.toNat, max 1 (d.2 / dx).ceil.toNat)
  let h := (dx / 2) • ((n.1 : ℚ), (n.2 : ℚ))
  ⟨c - h, c + h, n⟩

/-- `Grid.square` makes square cells -/
lemma square_dz (lo hi : ℚ × ℚ) (n : ℕ) :
    (square lo hi n).dz.1 = (square lo hi n).dz.2 := by
  rw [square]
  generalize ((lo.1 + hi.1) / 2, (lo.2 + hi.2) / 2) = c
  generalize hi - lo = d
  generalize hdx : max d.1 d.2 / (n : ℚ) = dx
  generalize hn1 : max 1 (d.1 / dx).ceil.toNat = n1
  generalize hn2 : max 1 (d.2 / dx).ceil.toNat = n2
  have n1z : (n1 : ℚ) ≠ 0 := by
    rw [←hn1]; exact Nat.cast_ne_zero.mpr (ne_of_gt (lt_max_of_lt_left zero_lt_one))
  have n2z : (n2 : ℚ) ≠ 0 := by
    rw [←hn2]; exact Nat.cast_ne_zero.mpr (ne_of_gt (lt_max_of_lt_left zero_lt_one))
  simp only [dz, Prod.smul_mk, smul_eq_mul, Prod.fst_add, Prod.fst_sub, add_sub_sub_cancel, add_div,
    mul_div_assoc, div_self n1z, mul_one, add_halves, Prod.snd_add, Prod.snd_sub, div_self n2z]
