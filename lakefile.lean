import Lake
open Lake DSL

package ray where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`weak.linter.docPrime, false⟩, -- `weak.`: defined by Mathlib, absent in libs that don't import it
    ⟨`autoImplicit, false⟩,
    ⟨`experimental.module, true⟩,
  ]

require "leanprover-community" / "mathlib" @ git "v4.33.0"

require trustless from ".." / "trustless"

@[default_target]
lean_lib Ray where
  roots := #[`Ray, `Mandelbrot, `Mandelbrot2]
  -- The fills read the sources' oleans, an edge Lake cannot see; build them first.
  extraDepTargets := #[`RayMandelbrotSource]

-- The untrusted proofs, kept out of `Ray`'s import closure.
lean_lib RayMandelbrotSource where
  roots := #[`Ray.Mandelbrot, `Ray.Mandelbrot2]
