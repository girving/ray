-- The Mandelbrot set and its complement are connected

import multibrot
import multibrot_connected

open complex (abs)
open filter (tendsto at_top)
open riemann_sphere
open set
open_locale alexandroff riemann_sphere topology real
noncomputable theory

-- The Mandelbrot set: all points that do not escape to infinity under z² + c → z
def mandelbrot : set ℂ := {c | ¬tendsto (λ n, abs ((λ z, z^2 + c)^[n] c)) at_top at_top}

-- The Mandelbrot set is a multibrot set
lemma mandelbrot_eq_multibrot : mandelbrot = multibrot 2 := begin
  apply set.ext, intro c,
  simp only [mandelbrot, multibrot, mem_set_of, f_f'_iter, tendsto_inf_iff_tendsto_at_inf,
    tendsto_at_inf_iff_norm_tendsto_at_top, complex.norm_eq_abs],
  refl,
end

-- The Mandelbrot set is connected
theorem is_connected.mandelbrot : is_connected mandelbrot := begin
  rw mandelbrot_eq_multibrot, exact is_connected.multibrot 2,
end

-- The complement of the Mandelbrot set is connected
theorem is_connected.compl_mandelbrot : is_connected mandelbrotᶜ := begin
  rw mandelbrot_eq_multibrot, exact is_connected.compl_multibrot 2,
end