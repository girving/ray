import Ray.Approx.Interval

/-!
## Approximate colors

We define the infinite precision `Color` type, and a finite precision `Color32` type
with an `Approx Color32 Color` instance.
-/

open Set

/-- Infinite precision RGBA colors, supposed to be in `[0,1]^4` -/
abbrev Color := Fin 4 → ℝ

/-- 32-bit RGBA colors -/
structure Color32 where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
  deriving DecidableEq

/-- We define `nan` as red for now, even if it's a bit specific -/
instance : Nan Color32 where
  nan := ⟨255, 0, 0, 255⟩

/-- Approximation interval around a color channel -/
def UInt8.approx (v : UInt8) : Set ℝ :=
  let x : ℝ := v.toNat
  Icc (x / 256) ((x + 1) / 256)

/-- Approximation midpoint for a color channel -/
noncomputable def UInt8.color (v : UInt8) : ℝ :=
  (v.toNat + 1/2) / 256

/-- `Color32` has an approximation radius of `1/255` -/
instance : Approx Color32 Color where
  approx c :=
    if c = nan then univ else
    univ.pi ![c.r.approx, c.g.approx, c.b.approx, c.a.approx]

/-- Roughly what `Color` a `Color32` corresponds to -/
noncomputable def Color32.val (c : Color32) : Color :=
  ![c.r.color, c.g.color, c.b.color, c.a.color]
