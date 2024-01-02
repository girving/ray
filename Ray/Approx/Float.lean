import Mathlib.Data.Real.Basic

/-!
## `Float` extras
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set
open scoped Real

def Float.nan : Float := (0 : Float) / (0 : Float)
