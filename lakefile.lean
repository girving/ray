import Lake
open Lake DSL

package ray where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`weak.linter.docPrime, false⟩, -- `weak.` so libs that don't import Mathlib (which defines this linter) don't error
    ⟨`autoImplicit, false⟩,
    ⟨`experimental.module, true⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.33.0"

require trustless from ".." / "trustless"

-- `Ray.Mandelbrot`'s `trustless import` needs the bridge olean and the
-- lean4export binary, edges Lake cannot see; build them first.
@[default_target]
lean_lib Ray where
  extraDepTargets := #[`RayMandelbrotBridge, `lean4exportBin]

-- The lean4export exe as a package-local target (`extraDepTargets` cannot name
-- targets of other packages).
target lean4exportBin _pkg : System.FilePath := do
  let some l4e := (← getWorkspace).packages.find? (·.name == `lean4export)
    | error "lean4export package not found in workspace"
  let some exe := l4e.findLeanExe? `lean4export
    | error "lean4export executable target not found"
  exe.exe.fetch

-- The untrusted bridge, kept out of `Ray`'s import closure.
lean_lib RayMandelbrotBridge where
  roots := #[`Ray.MandelbrotBridge]
