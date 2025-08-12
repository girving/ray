import Lake
open Lake DSL

package ray where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`linter.docPrime, false⟩,
    ⟨`autoImplicit, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib Ray
