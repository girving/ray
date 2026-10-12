module
import Trustless
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
## The Mandelbrot set and its complement are connected (trustless)

A verifier of `IsConnected mandelbrot` and `IsConnected mandelbrotᶜ` that does not
trust what the Ray library does while constructing a proof.
It does trust Mathlib and Trustless.

const_fill: reads the named theorem's proof term and its dependency closure straight out of
`Ray.Mandelbrot`'s compiled olean, re-checks every constant through the kernel, and closes the
goal with the transplanted term, activating none of the library's elaboration (notation,
macros, instances).
trustless_fill: The same as above except the constants are extracted from lean4export, run in a
sandbox.
-/

open Filter (Tendsto atTop)
open Set
section

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c`. -/
@[expose] public def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}

/-- The Mandelbrot set is connected. -/
public theorem isConnected_mandelbrot : IsConnected mandelbrot :=
  trustless_fill Ray.Mandelbrot

/-- The complement of the Mandelbrot set is connected. -/
public theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ :=
  trustless_fill Ray.Mandelbrot

/-!
Appendix:
  The meaning of the above theorems depends on `IsConnected` and the topology on ℂ is given by
  an instance of `[TopologicalSpace ℂ]`. We prove they both have the usual meaning.
-/

/-- The topology on ℂ being used is the open ball topology -/
example (u : Set ℂ) : IsOpen u ↔ ∀ z ∈ u, ∃ ε > 0, ∀ w : ℂ, ‖w - z‖ < ε → w ∈ u := by
  simp only [Metric.isOpen_iff, subset_def, Metric.mem_ball, Complex.dist_eq]

/-- `‖·‖` above is the ordinary modulus on `ℂ` -/
example (z : ℂ) : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := Complex.norm_eq_sqrt_sq_add_sq z

/-- IsConnected s means: s is non-empty, and if two open sets cover s
  and each have nontrivial intersection with s, then so does their intersection.
 -/
example {α} [TopologicalSpace α] (s : Set α) :
    IsConnected s ↔
      s.Nonempty ∧
        ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v →
          (s ∩ u).Nonempty → (s ∩ v).Nonempty → (s ∩ (u ∩ v)).Nonempty :=
  Iff.rfl
