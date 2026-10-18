module
import Trustless
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
const import pulls in constants without triggering elaboration (it also replays them into the
Kernel.Environment so they get rechecked again).
Use `trustless import` for a version that extracts a the constants from lean4export
running in a sandbox.

Ray.Mandelbrot2 declares everything inside the `Ray` namespace, so that it doesn't collide with
our mandelbrot, isConnected_mandelbrot and isConnected_compl_mandelbrot.
-/
const import Ray.Mandelbrot2

open Filter (Tendsto atTop)
open Set
section

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c`. -/
@[expose] public def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}

-- The Mandelbrot set is connected.
public theorem isConnected_mandelbrot : IsConnected mandelbrot := Ray.isConnected_mandelbrot

-- The complement of the Mandelbrot set is connected.
public theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ := Ray.isConnected_compl_mandelbrot
