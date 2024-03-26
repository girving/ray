import Cli
import Mathlib.Data.Nat.Basic
import Ray.Misc.Parallel
import Std.Data.Nat.Basic

open Cli

/-!
## Try to do trial division for primes in parallel
-/

variable {α : Type}
variable {m : Type → Type} [Monad m] [ParM m]

def slow_prime_loop (n : ℕ) : ℕ → Bool
| 0 => True
| 1 => True
| k+1 => n % (k+1) != 0 && slow_prime_loop n k

def slow_prime (n : ℕ) : Bool :=
  1 < n && slow_prime_loop n n.sqrt

def count (lo hi : ℕ) : ℕ :=
  (hi - lo).fold (fun n t ↦ t + if slow_prime (lo + n) then 1 else 0) 0

@[noinline] def countM (n : ℕ) : m ℕ := do
  let ns := Array.range n
  let ts ← ns.parMap' (fun i ↦ count i (i+1))
  return ts.foldl (· + ·) 0

def primesRun (p : Parsed) : IO UInt32 := do
  let n := p.flag! "number" |>.as! Nat
  IO.println s!"n = {n}"
  let t ← IO.wait (countM n)
  IO.println s!"π(n) = {t}"
  return 0

def primesCmd : Cmd := `[Cli|
  primes VIA primesRun;
  "Count primes up to a value."

  FLAGS:
    n, number : ℕ;              "Count primes below `n`."

  EXTENSIONS:
    defaultValues! #[("number", "10000000")]
]

def main (args : List String): IO UInt32 := do
  primesCmd.validate args
