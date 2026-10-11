# CLAUDE.md

## What this is

Lean 4 formalization of the Mandelbrot set (Böttcher map, connectedness, Grönwall area bounds) on Mathlib.  See
README.md for the main results.

## Building

    lake exe cache get   # Mathlib's prebuilt oleans
    lake build

Lean and Mathlib versions move together: `lean-toolchain` and the mathlib tag in `lakefile.lean`.

## Conventions

- Files use the module system (`module`, `public import`, `public` declarations, `@[expose]` on definitions that
  public proofs unfold); `autoImplicit` is off.
- Each file opens with a `/-! ... -/` docstring summarising its results.
- Changes go through pull requests for review.
