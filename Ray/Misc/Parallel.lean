import Lake.Util.Task
import Mathlib.Init.Control.Lawful
import Mathlib.Order.SetNotation
import Std.Classes.LawfulMonad

/-!
## Parallelism monads

We define a type class for parallel computations, with instantiations for either

1. Parallelism with printing, via `TaskIO α = BaseIO (Task (Except IO.Error α))`.
2. Pure parallelism without printing, via `Task`.
-/

universe u v

class ParM (m : Type u → Type v) [Monad m] where
  /-- Lift a pure computation into the monad lazily -/
  spawn : {α : Type u} → (Unit → α) → m α
  /-- Do two tasks in parallel -/
  par : {α β : Type u} → m α → m β → m (α × β)
  /-- Diagnostic printing -/
  putStr : String → m PUnit

export ParM (spawn par)

/-- `ParM` instance for `Task`, which prints nothing -/
instance : ParM Task where
  spawn := Task.spawn
  par x y := do return (← x, ← y)
  putStr _ := return ()

/-- `IO` parallelizes via `IO.asTask` -/
instance : ParM IO where
  spawn := IO.lazyPure
  par x y := do
    let x ← IO.asTask x
    let y ← y
    let x ← IO.ofExcept x.get
    return (x, y)
  putStr s := IO.print s

/-!
### Convenience routines for parallelism
-/

variable {α β : Type}
variable {m : Type → Type} [Monad m] [ParM m]

def print [ToString α] (x : α) : m Unit :=
  ParM.putStr (toString x)

def println [ToString α] (x : α) : m Unit :=
  ParM.putStr ((toString x).push '\n')

def Array.par (xs : Array (m α)) : m (Array α) := do
  let mut out := #[]
  for x in xs do
    out := out.push (← x)
  return out

def Array.parMap (xs : Array α) (f : α → m β) : m (Array β) :=
  (xs.map f).par
