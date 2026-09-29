import Lake
open Lake DSL

package ray where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`linter.docPrime, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`experimental.module, true⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.34.1"

@[default_target]
lean_lib Ray
