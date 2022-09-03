Mandelbrot set formalization
============================

The main goal of this repo is to prove that the Mandelbrot set is simply
connected via Bottcher coordinates.  But I'm also using it to learn Lean
generally, which means various detours along the way.  So far, we have
two results:

**[Hartog's theorem](https://en.wikipedia.org/wiki/Hartogs%27s_theorem_on_separate_holomorphicity):**
Let $E$ be a separable Banach space, and $f : \mathbb{C}^2 \to E$
a function which is analytic along each axis at each point in an open set $S \subset \mathbb{C}^2$.
Then $f$ is jointly analytic in $S$.

**[Bottcher's theorem](https://en.wikipedia.org/wiki/B%C3%B6ttcher%27s_equation):** 
Let $f : \mathbb{C} \to \mathbb{C}$ be analytic with a monic superattracting fixpoint at 0,
so that $f(z) = z^d + O(z^{d+1})$.  Then there is an analytic $b : \mathbb{C} \to \mathbb{C}$
near 0 s.t. $b(f(z)) = b(z)^d$.  If $f(z) = f_p(z)$ is also analytic in a parameter $p$, then
$b(z) = b_p(z)$ is also analytic in $p$.

## Building

Run

    brew install lean mathlibtools
    cd ray
    leanproject get-mathlib-cache
    leanproject build
