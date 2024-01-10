import Mathlib.Data.Real.Basic

/-!
## `Float` extras
-/

open Set
open scoped Real

def Float.nan : Float := (0 : Float) / (0 : Float)
