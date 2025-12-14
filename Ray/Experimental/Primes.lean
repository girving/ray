module
import Mathlib.Algebra.Order.Floor.Div

/-!
## Try to do trial division for primes in parallel
-/

def slow_prime_loop (n : ℕ) : ℕ → Bool
| 0 => True
| 1 => True
| k+1 => n % (k+1) != 0 && slow_prime_loop n k

def slow_prime (n : ℕ) : Bool :=
  1 < n && slow_prime_loop n n.sqrt

def count_range (lo hi : ℕ) : ℕ :=
  (hi - lo).fold (fun n _ t ↦ t + if slow_prime (lo + n) then 1 else 0) 0

-- set_option trace.compiler.ir.result true in
def count (n : ℕ) (chunk : ℕ) : ℕ :=
  let tasks := (Array.range (n ⌊/⌋ chunk)).map (fun c ↦ Task.spawn (fun _ ↦
    count_range (c * chunk) ((c+1) * chunk)))
  tasks.foldl (fun n t ↦ n + t.get) 0

-- set_option trace.compiler.ir.result true in
def BaseIO.lazyPure {α : Type} (f : Unit → α) : BaseIO α := do
  pure (f ())

def countIO (n : ℕ) (chunk : ℕ) : IO ℕ :=
  let tasks := (Array.range (n ⌊/⌋ chunk)).map (fun c ↦
    BaseIO.asTask (BaseIO.lazyPure (fun _ ↦ count_range (c * chunk) ((c+1) * chunk))))
  tasks.foldlM (fun n (t : BaseIO (Task ℕ)) ↦ do pure (n + (←t).get)) 0

def main : IO Unit := do
  let n := 1000 * 1000 * 1000
  IO.println ("n = " ++ repr n)
  let t ← countIO n 1000000
  IO.println ("π(n) = " ++ repr t)
  --IO.println ("π(n) = " ++ repr (count n 1000))
