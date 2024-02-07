import Ray.Render.PNG

/-!
## Test image writing
-/

def gradient (_ : Unit) : Image :=
  let w := 162
  let h := 100
  let i (c : ℚ) : UInt8 := (c * 255).floor
  Image.ofFn w h (fun x y ↦
    let x := (x : ℚ) / w
    let y := (y : ℚ) / h
    let r := i x
    let g := i 0
    let b := i y
    let a := i (if x + y < 1 then 1 else 2 - x - y)
    ⟨r,g,b,a⟩)

def main : IO Unit := do
  Image.write_png "gradient.png" (gradient ())
