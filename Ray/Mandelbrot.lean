module
public import Ray.Multibrot.Defs
import Ray.Misc.Cobounded
import Ray.Multibrot.Basic
import Ray.Multibrot.Connected

/-!
## The Mandelbrot set and its complement are connected

The rest of our proof works via manifolds and other machinery.  Here we strip that away:

1. We define the Mandebrot set directly
2. We show it is equal to `multibrot 2`
3. Thus, the Mandelbrot set and its complement are connected
-/

open Filter (Tendsto atTop)
open RiemannSphere
open Set
open scoped Topology Real
noncomputable section

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c` -/
@[expose] public def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}

/-- The Mandelbrot set is the `d = 2` Multibrot set -/
public theorem mandelbrot_eq_multibrot : mandelbrot = multibrot 2 := by
  ext c
  simp only [mandelbrot, mem_setOf_eq, multibrot, f_f'_iter, tendsto_inf_iff_tendsto_cobounded,
    tendsto_cobounded_iff_norm_tendsto_atTop]
  rfl

/-- The Mandelbrot set is connected -/
public theorem isConnected_mandelbrot : IsConnected mandelbrot := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_multibrot 2

/-- The complement of the Mandelbrot set is connected -/
public theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_compl_multibrot 2
