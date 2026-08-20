module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Ray.Multibrot.Defs
import Ray.Misc.Cobounded
import Ray.Multibrot.Basic
import Ray.Multibrot.Connected

/-!
# Untrusted bridge: `mandelbrot` ⟶ Mathlib's `multibrot`

Repeats the trusted `mandelbrot` definition (`Ray.Mandelbrot` does not import
this file), proves it equals `multibrot 2`, and transports Mathlib's
`isConnected_multibrot` across. `Ray.Mandelbrot` kernel-re-checks everything it
imports from here, so nothing in this file is trusted.
-/

open Filter (Tendsto atTop)
open RiemannSphere
open Set
open scoped Topology Real
noncomputable section

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c`. -/
@[expose] public def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}

-- Namespaced so the canonical names stay free for `Ray.Mandelbrot`.
namespace MandelbrotBridge

/-- The trusted Mandelbrot set is the `d = 2` Multibrot set. -/
public theorem mandelbrot_eq_multibrot : mandelbrot = multibrot 2 := by
  ext c
  simp only [mandelbrot, mem_ofPred_eq, multibrot, f_f'_iter, tendsto_inf_iff_tendsto_cobounded,
    tendsto_cobounded_iff_norm_tendsto_atTop]
  rfl

/-- The Mandelbrot set is connected. -/
public theorem isConnected_mandelbrot : IsConnected mandelbrot := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_multibrot 2

/-- The complement of the Mandelbrot set is connected. -/
public theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_compl_multibrot 2

end MandelbrotBridge
