module
import Trustless
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Mandelbrot set and its complement are connected

`mandelbrot` is defined here, and the proofs arrive via `trustless import` from
`Ray.MandelbrotBridge`: kernel-re-checked against this file's definitions, with
none of the bridge's notation, instances, or other elaborator surface active,
and without mapping its olean into this process. The bridge repeats the
definition; the re-check fails unless the copies agree.
-/

open Filter (Tendsto atTop)
open Set
noncomputable section

/-- The Mandelbrot set: all points that do not escape to `∞` under `z ↦ z^2 + c`. -/
@[expose] public def mandelbrot : Set ℂ :=
  {c | ¬Tendsto (fun n ↦ ‖(fun z ↦ z^2 + c)^[n] c‖) atTop atTop}

trustless import Ray.MandelbrotBridge
  (MandelbrotBridge.isConnected_mandelbrot MandelbrotBridge.isConnected_compl_mandelbrot)

/-- The Mandelbrot set is connected. -/
public theorem isConnected_mandelbrot : IsConnected mandelbrot :=
  MandelbrotBridge.isConnected_mandelbrot

/-- The complement of the Mandelbrot set is connected. -/
public theorem isConnected_compl_mandelbrot : IsConnected mandelbrotᶜ :=
  MandelbrotBridge.isConnected_compl_mandelbrot
