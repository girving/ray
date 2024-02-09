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
  (hi - lo).fold (fun n t ↦ t + if slow_prime (lo + n) then 1 else 0) 0

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

/-
def map_lambda (x_1 : @& obj) (x_2 : @& obj) (x_3 : @& obj) : obj :=
  let x_4 : obj := Nat.mul x_1 x_2;
  let x_5 : obj := 1;
  let x_6 : obj := Nat.add x_1 x_5;
  let x_7 : obj := Nat.mul x_6 x_2;
  dec x_6;
  let x_8 : obj := count_range x_4 x_7;
  dec x_4;
  ret x_8

def map_lambda_boxed (x_1 : obj) (x_2 : obj) (x_3 : obj) : obj :=
  let x_4 : obj := map_lambda x_1 x_2 x_3;
  dec x_3;
  dec x_2;
  dec x_1;
  ret x_4

def map_count (x_1 : obj) (x_2 : usize) (x_3 : usize) (x_4 : obj) : obj :=
  let x_5 : u8 := USize.decLt x_3 x_2;
  case x_5 : u8 of
  Bool.false →
    dec x_1;
    ret x_4
  Bool.true →
    let x_6 : obj := Array.uget ◾ x_4 x_3 ◾;
    let x_7 : obj := 0;
    let x_8 : obj := Array.uset ◾ x_4 x_3 x_7 ◾;
    inc x_1;
    let x_9 : obj := pap map_lambda_boxed x_6 x_1;
    let x_10 : obj := Task.Priority.default;
    let x_11 : obj := Task.spawn ◾ x_9 x_10;
    let x_12 : usize := 1;
    let x_13 : usize := USize.add x_3 x_12;
    let x_14 : obj := Array.uset ◾ x_8 x_3 x_11 ◾;
    let x_15 : obj := map_count x_1 x_2 x_13 x_14;
    ret x_15

def count_foldl (x_1 : @& obj) (x_2 : usize) (x_3 : usize) (x_4 : obj) : obj :=
  let x_5 : u8 := USize.decEq x_2 x_3;
  case x_5 : u8 of
  Bool.false →
    let x_6 : obj := Array.uget ◾ x_1 x_2 ◾;
    let x_7 : obj := Task.get ◾ x_6;
    let x_8 : obj := Nat.add x_4 x_7;
    dec x_7;
    dec x_4;
    let x_9 : usize := 1;
    let x_10 : usize := USize.add x_2 x_9;
    let x_11 : obj := count_foldl x_1 x_10 x_3 x_8;
    ret x_11
  Bool.true →
    ret x_4

def count (x_1 : obj) (x_2 : obj) : obj :=
  let x_3 : obj := Nat.div x_1 x_2;
  dec x_1;
  let x_4 : obj := Array.range x_3;
  let x_5 : obj := Array.size ◾ x_4;
  let x_6 : usize := USize.ofNat x_5;
  dec x_5;
  let x_7 : usize := 0;
  let x_8 : obj := map_count x_2 x_6 x_7 x_4;
  let x_9 : obj := Array.size ◾ x_8;
  let x_10 : obj := 0;
  let x_11 : u8 := Nat.decLt x_10 x_9;
  case x_11 : u8 of
  Bool.false →
    dec x_9;
    dec x_8;
    let x_12 : obj := 0;
    ret x_12
  Bool.true →
    let x_13 : u8 := Nat.decLe x_9 x_9;
    case x_13 : u8 of
    Bool.false →
      dec x_9;
      dec x_8;
      let x_14 : obj := 0;
      ret x_14
    Bool.true →
      let x_15 : usize := USize.ofNat x_9;
      dec x_9;
      let x_16 : obj := count_foldl x_8 x_7 x_15 x_10;
      dec x_8;
      ret x_16
-/
