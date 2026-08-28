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

-- The trusted `Mandelbrot`'s `const import` reads `Ray.Mandelbrot`'s olean, an
-- edge Lake cannot see; build it first. (`extraDepTargets` is best-effort
-- ordering; a cold build may need `lake build RayMandelbrotSource` first.)
@[default_target]
lean_lib Ray where
  -- `Mandelbrot` (the trusted file) lives at the package root, outside the `Ray`
  -- namespace, so it must be named as a root for Lake to build it.
  roots := #[`Ray, `Mandelbrot, `Mandelbrot2]
  extraDepTargets := #[`RayMandelbrotSource]

-- The untrusted proof (`Ray.Mandelbrot`), kept out of `Ray`'s import closure so
-- its results arrive only through the trusted `Mandelbrot`'s `const import`,
-- never as a second copy.
lean_lib RayMandelbrotSource where
  roots := #[`Ray.Mandelbrot, `Ray.Mandelbrot2]
