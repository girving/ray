import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Nat.Basic

/-!
## Progress meter in the IO monad
-/

/-- A progress meter that counts up to a given `ℕ` -/
structure Progress where
  /-- Total work to do -/
  total : ℕ
  /-- (finished work, last printed percent) -/
  state : IO.Ref (ℕ × ℕ)

namespace Progress

/-- Create a new progress meter with a given total -/
def start (total : ℕ) : IO Progress := do
  let state ← IO.mkRef (0, 0)
  return { total := total, state := state }

/-- Mark some work as finished -/
def add (p : Progress) (n : ℕ) : IO Unit := do
  let print : Option ℕ ← p.state.modifyGet (fun (done, percent) ↦
    let done' := done + n
    let percent' := 100 * done' / p.total
    (if percent < percent' then some percent' else none, done'))
  match print with
  | none => return ()
  | some p =>
    if p < 100 then IO.print f!" {p}%"
    else IO.println " 100%"
