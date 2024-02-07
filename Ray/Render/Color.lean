import Ray.Approx.Interval.Basic

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

lemma Color32.ext_iff (x y : Color32) : x = y ↔ x.r = y.r ∧ x.g = y.g ∧ x.b = y.b ∧ x.a = y.a := by
  induction x; induction y; simp only [mk.injEq]

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

/-- `c[i]` for `i < 4` -/
instance : GetElem Color32 (Fin 4) UInt8 (fun _ _ ↦ True) where
  getElem c i _ := match i with
  | 0 => c.r
  | 1 => c.g
  | 2 => c.b
  | 3 => c.a

-- `c[i]` simplification lemmas
@[simp] lemma Color32.get_0 (c : Color32) : c[(0 : Fin 4)] = c.r := rfl
@[simp] lemma Color32.get_1 (c : Color32) : c[(1 : Fin 4)] = c.g := rfl
@[simp] lemma Color32.get_2 (c : Color32) : c[(2 : Fin 4)] = c.b := rfl
@[simp] lemma Color32.get_3 (c : Color32) : c[(3 : Fin 4)] = c.a := rfl
