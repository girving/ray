import Interval.Box.Exp
import Interval.Interval.Division
import Ray.Render.Potential

/-!
## Bounds on the Mandelbrot potential function via interval arithmetic
-/

open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

variable {α β γ δ : Type}

def rough_circle (r : Interval) (n : ℕ) : Array Box :=
  let a := Interval.pi * (.ofRat (2 / n))
  (Array.range n).map fun k : ℕ ↦ r • Interval.cis (a * k)

def linspace (x0 x1 : Interval) (n : ℕ) : Array Interval :=
  let dx := (x1 - x0) / Interval.ofNat (n + 1)
  (Array.range (n + 2)).map fun k : ℕ ↦ x0 + dx * k

def Array.fold1 (f : α → α → α) (xs : Array α) (h : xs.size ≠ 0) : α :=
  loop xs[0] 1 where
  loop (y : α) (k : ℕ) : α :=
    if h : k < xs.size then loop (f y xs[k]) (k + 1) else y

def Array.union_map (f : α → β) (xs : Array α) [Union β] [Nan β] : β :=
  if h : xs.size = 0 then nan else
  (xs.map f).fold1 Union.union (by simp only [size_map]; omega)

def rough_potential_circle (r : Interval) (n : ℕ) : Interval :=
  let ring := rough_circle r n
  ring.union_map fun c ↦ ring.union_map fun z ↦
  (Box.potential c z 100 1000).1

#eval (rough_potential_circle 4 30).lo
