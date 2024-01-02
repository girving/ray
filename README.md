The Mandelbrot set is connected
===============================

The goal of this repository is to formalize standard results about the
Mandelbrot set in Lean. The main result is that [the Mandelbrot set and its
complement are connected](http://github.com/girving/ray/blob/main/Ray/Dynamics/Mandelbrot.lean#L37), by exhibiting the
analytic Böttcher homeomorphism from the exterior of the Mandelbrot set to the
exterior of the closed unit disk. But I'm also using it to learn Lean
generally, which means detours along the way. The main results are

* **[Hartogs's theorem](https://en.wikipedia.org/wiki/Hartogs%27s_theorem_on_separate_holomorphicity)** -
  [Hartogs.lean](http://github.com/girving/ray/blob/main/Ray/Hartogs/Hartogs.lean):
  Let $E$ be a separable Banach space, and $f : \mathbb{C}^2 \to E$
  a function which is analytic along each axis at each point in an open set $S \subset \mathbb{C}^2$.
  Then $f$ is jointly analytic in $S$.

* **[Bottcher's theorem](https://en.wikipedia.org/wiki/B%C3%B6ttcher%27s_equation)** -
  [BottcherNear.lean](http://github.com/girving/ray/blob/main/Ray/Dynamics/BottcherNear.lean):
  Let $f : \mathbb{C} \to \mathbb{C}$ be analytic with a monic superattracting fixpoint at 0,
  so that $f(z) = z^d + O(z^{d+1})$.  Then there is an analytic $b : \mathbb{C} \to \mathbb{C}$ near 0 s.t.
  $b(f(z)) = b(z)^d$.  If $f(z) = f_c(z)$ is also analytic in a parameter $c$, then $b(z) = b_c(z)$ is also analytic in $c$.

* **Analytic continuation of the Böttcher map up to the critical value** -
  [Bottcher.lean](http://github.com/girving/ray/blob/main/Ray/Dynamics/Bottcher.lean),
  [Ray.lean](http://github.com/girving/ray/blob/main/Ray/Dynamics/Ray.lean):
  Let $S$ be a compact, 1D complex
  manifold, $f : S \to S$ a holomorphic map with a fixpoint $f(a) = a$, and assume $f$ has no
  other preimages of $a$.  Starting with the local Böttcher map $b(z)$ defined in a neighborhood of
  $a$, we get a continuous potential map $\phi : S \to [0,1]$ s.t. $\phi(z) = |b(z)|$ near $a$ and
  $\phi(f(z)) = \phi(z)^d$ everywhere.  Let $\phi^\ast = \min~\\{\phi(z) | f'(z) = 0, z \ne a\\}$ be the
  critical potential.  Then $b(z)$ can be analytically continued throughout the postcritical region
  $P = \\{z | \phi(z) < \phi^\ast\\}$, and gives an analytic homeomorphism from $P$ to the open disk
  $D_{\phi^\ast}(0) \subset \mathbb{C}$.  If $f(z) = f_c(z)$ is also analytic in a parameter
  $c \in \mathbb{C}$, then $b_c(z)$ can be analytically continued throughout
  $P = \\{(c,z) | \phi_c(z) < \phi^\ast_c\\}$.

* **Böttcher map for the Multibrot set** - [Multibrot.lean](http://github.com/girving/ray/blob/main/Ray/Dynamics/Multibrot.lean):
  Let $M_d \subset \mathbb{S}$ be the [Multibrot set](https://en.wikipedia.org/wiki/Multibrot_set) for the
  family $f_c(z) = z^d + c$, viewed as a subset of the Riemann sphere $\mathbb{S}$.  Then $(c,c)$ is
  postcritical for each $c \in \mathbb{S} - M_d$, so the diagonal $b_c(c)$ of the Böttcher map is
  holomorphic throughout $\mathbb{S} - M_d$, and defines an analytic bijection from $\mathbb{S} - M_d$
  to the open unit disk $D_1(0)$.

* **Multibrot connectness** -
  [MultibrotConnected.lean](http://github.com/girving/ray/blob/main/Ray/Dynamics/MultibrotConnected.lean#L76),
  [Mandelbrot.lean](http://github.com/girving/ray/blob/main/Ray/Dynamics/Mandelbrot.lean#L37):
  Each Multibrot set $M_d$ and its complement $\mathbb{S} - M_d$
  are corrected, including the Mandelbrot set $M = M_2$.

## References

1. [Adrien Douady, John Hubbard (1984-5). Exploring the Mandelbrot set.  The Orsay Notes](https://pi.math.cornell.edu/~hubbard/OrsayEnglish.pdf)
2. [John Milnor (1990), Dynamics in one complex variable](https://arxiv.org/abs/math/9201272)
3. [Dierk Schleicher (1998), Rational parameter rays of the Mandelbrot set](https://arxiv.org/abs/math/9711213)
4. [Paul Garrett (2005), Hartogs’ Theorem: separate analyticity implies joint](https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf)
5. [Hartog's theorem](https://en.wikipedia.org/wiki/Hartogs%27s_theorem_on_separate_holomorphicity)
6. [Böttcher's theorem](https://en.wikipedia.org/wiki/B%C3%B6ttcher%27s_equation)

## Building

1. Install [`elan`](https://github.com/leanprover/elan) (`brew install elan-init` on Mac)
2. `lake build`
