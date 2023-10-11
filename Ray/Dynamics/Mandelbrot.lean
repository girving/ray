import Ray.Dynamics.Multibrot
import Ray.Dynamics.MultibrotConnected

/-!
## The Mandelbrot set and its complement are connected

The rest of our proof works via `AnalyticManifold`s and other machinery.  Here we strip that away:

1. We define the Mandebrot set directly
2. We show it is equal to `multibrot 2`
3. Thus, the Mandelbrot set and its complement are connected
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Complex (abs)
open Filter (Tendsto atTop)
open RiemannSphere
open Set
open scoped Topology Real
noncomputable section

local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c` -/
def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ abs ((fun z ↦ z^2 + c)^[n] c)) atTop atTop}

/-- The Mandelbrot set is the `d = 2` Multibrot set -/
theorem mandelbrot_eq_multibrot : mandelbrot = multibrot 2 := by
  apply Set.ext; intro c
  simp only [mandelbrot, multibrot, mem_setOf, f_f'_iter, tendsto_inf_iff_tendsto_atInf,
    tendsto_atInf_iff_norm_tendsto_atTop, Complex.norm_eq_abs, f']

/-- The Mandelbrot set is connected -/
theorem isConnected_mandelbrot : IsConnected mandelbrot := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_multibrot 2

/-- The complement of the Mandelbrot set is connected -/
theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ := by
  rw [mandelbrot_eq_multibrot]; exact isConnected_compl_multibrot 2
