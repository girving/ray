-- Infinite products of analytic functions

import analysis.analytic.basic
import analysis.analytic.composition
import data.complex.basic
import data.real.basic
import data.real.ennreal
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import data.stream.defs
import data.stream.init
import topology.metric_space.basic
import topology.uniform_space.uniform_convergence
import topology.algebra.infinite_sum

import analytic
import bounds
import finset
import holomorphic
import series
import simple
import tactics

open complex (abs exp log)
open filter (at_top)
open metric (ball closed_ball sphere)
open_locale classical real nnreal ennreal topological_space

noncomputable theory

-- Equivalents of has_sum and has_sum_on
def has_prod (f : ℕ → ℂ) (g : ℂ) := filter.tendsto (λ N : finset ℕ, N.prod (λ n, f n)) at_top (𝓝 g)
def has_prod_on (f : ℕ → ℂ → ℂ) (g : ℂ → ℂ) (s : set ℂ) := ∀ z, z ∈ s → has_prod (λ n, f n z) (g z)
def prod_exists (f : ℕ → ℂ) : Prop := ∃ g, has_prod f g
noncomputable def tprod (f : ℕ → ℂ) := if h : prod_exists f then classical.some h else 0
noncomputable def tprod_on (f : ℕ → ℂ → ℂ) := λ z, tprod (λ n, f n z)
def prod_exists_on (f : ℕ → ℂ → ℂ) (s : set ℂ) := ∀ z, z ∈ s → prod_exists (λ n, f n z)

-- Products are unique
lemma has_prod.unique {f : ℕ → ℂ} {a b : ℂ} : has_prod f a → has_prod f b → a = b := tendsto_nhds_unique
lemma has_prod.prod_exists {f : ℕ → ℂ} {g : ℂ} (h : has_prod f g) : prod_exists f := ⟨g,h⟩

-- tprod is the product if it exists
lemma has_prod.tprod_eq {f : ℕ → ℂ} {g : ℂ} : has_prod f g → tprod f = g := begin
  intro h, rw tprod, simp [h.prod_exists],
  have s := classical.some_spec (h.prod_exists),
  exact s.unique h
end

-- tprod_on is the product on s if it exists on s
lemma has_prod_on.tprod_on_eq {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {s : set ℂ}
    : has_prod_on f g s → ∀ z, z ∈ s → tprod_on f z = g z := begin
  intros h z zs, exact (h z zs).tprod_eq
end

-- The product of ones is one
theorem prod_ones : has_prod (λ _, (1 : ℂ)) 1 := by { rw has_prod, simp, exact tendsto_const_nhds }

-- The product of ones is one (tprod version)
theorem prod_ones' : tprod (λ _, (1 : ℂ)) = 1 := has_prod.tprod_eq prod_ones

-- Analytic products that converge exponentially converge to analytic functions.
-- For now, we require the constant to be ≤ 1/2 so that we can take logs without care.
theorem fast_products_converge {f : ℕ → ℂ → ℂ} {s : set ℂ} {a c : ℝ}
    (o : is_open s) (c12 : c ≤ 1/2) (a0 : a ≥ 0) (a1 : a < 1)
    (h : ∀ n, analytic_on ℂ (f n) s) (hf : ∀ n z, z ∈ s → abs (f n z - 1) ≤ c * a^n)
    : ∃ (g : ℂ → ℂ), has_prod_on f g s ∧ analytic_on ℂ g s := begin
  set fl := λ n z, log (f n z),
  have near1 : ∀ n z, z ∈ s → abs (f n z - 1) ≤ 1/2, {
    intros n z zs,
    calc abs (f n z - 1) ≤ c * a^n : hf n z zs
    ... ≤ (1/2 : ℝ) * 1^n : by bound
    ... = 1/2 : by norm_num
  },
  have near1' : ∀ n z, z ∈ s → abs (f n z - 1) < 1 := λ n z zs, lt_of_le_of_lt (near1 n z zs) (by bound),
  have expfl : ∀ n z, z ∈ s → exp (fl n z) = f n z, {
    intros n z zs, refine complex.exp_log _,
    exact near_one_avoids_zero (near1' n z zs)
  },
  have hl : ∀ n, analytic_on ℂ (fl n) s := λ n, log_analytic_near_one o (h n) (near1' n),
  set c2 := 2 * c,
  have hfl : ∀ n z, z ∈ s → abs (fl n z) ≤ c2 * a^n, {
    intros n z zs,
    calc abs (fl n z) = abs (log (f n z)) : rfl
    ... ≤ 2 * abs (f n z - 1) : log_small (near1 n z zs)
    ... ≤ 2 * (c * a^n) : by bound [hf n z zs]
    ... = 2 * c * a^n : by ring
    ... = c2 * a^n : rfl
  },
  rcases fast_series_converge o a0 a1 hl hfl with ⟨gl,gla,us⟩,
  set g := λ z, exp (gl z),
  existsi g,
  constructor, {
    intros z zs,
    specialize us z zs, simp at us,
    have comp : filter.tendsto (exp ∘ λ N : finset ℕ, N.sum (λ n, fl n z)) at_top (𝓝 (exp (gl z)))
      := filter.tendsto.comp (continuous.tendsto complex.continuous_exp _) us,
    have expsum0 : (exp ∘ λ N : finset ℕ, N.sum (λ n, fl n z)) = λ N : finset ℕ, N.prod (λ n, f n z), {
      apply funext, intro N, simp, rw complex.exp_sum, simp_rw expfl _ z zs,
    },
    rw expsum0 at comp, assumption
  }, {
    intros z zs,
    exact analytic_at.comp (entire.exp _) (gla z zs)
  }
end

-- Same as above, but converge to tprod_on
theorem fast_products_converge' {f : ℕ → ℂ → ℂ} {s : set ℂ} {c a : ℝ}
    (o : is_open s) (c12 : c ≤ 1/2) (a0 : 0 ≤ a) (a1 : a < 1) 
    (h : ∀ n, analytic_on ℂ (f n) s) (hf : ∀ n z, z ∈ s → abs (f n z - 1) ≤ c * a^n)
    : prod_exists_on f s ∧ analytic_on ℂ (tprod_on f) s := begin
  rcases fast_products_converge o c12 a0 a1 h hf with ⟨g,gp,ga⟩,
  constructor, {
    intros z zs, existsi g z, exact gp z zs
  }, {
    rwa ←analytic_on_congr o (λ z zs, (gp.tprod_on_eq z zs).symm),
  }
end

-- Powers commute with products
theorem product_pow {f : ℕ → ℂ} {g : ℂ} (p : ℕ) (h : has_prod f g) : has_prod (λ n, f n ^ p) (g ^ p) := begin
  rw has_prod, simp_rw finset.prod_pow,
  exact filter.tendsto.comp (continuous.tendsto (continuous_pow p) g) h
end

-- Powers commute with products (tprod version)
theorem product_pow' {f : ℕ → ℂ} {p : ℕ} (h : prod_exists f) : (tprod f) ^ p = tprod (λ n, f n ^ p) := begin
  rcases h with ⟨g,h⟩, rw has_prod.tprod_eq h, rw has_prod.tprod_eq _, exact product_pow p h
end

-- Adding one more term to a product multiplies by it
theorem product_cons {a g : ℂ} {f : ℕ → ℂ} (h : has_prod f g) : has_prod (a :: f) (a * g) := begin
  rw has_prod at ⊢ h,
  have ha := filter.tendsto.comp (continuous.tendsto (continuous_mul_left a) g) h,
  have s : (λ z, a * z) ∘ (λ N : finset ℕ, N.prod f) = (λ N : finset ℕ, N.prod (a::f)) ∘ push, {
    apply funext, intro N, simp, exact push_prod
  },
  rw s at ha,
  exact tendsto_comp_push.mp ha
end

-- Adding one more term to a product multiplies by it (tprod version)
theorem product_cons' {a : ℂ} {f : ℕ → ℂ} (h : prod_exists f) : tprod (a :: f) = a * tprod f := begin
  rcases h with ⟨g,h⟩, rw has_prod.tprod_eq h, rw has_prod.tprod_eq _, exact product_cons h
end

-- Dropping a nonzero term divides by it
theorem product_drop {f : ℕ → ℂ} {g : ℂ} (f0 : f 0 ≠ 0) (h : has_prod f g) : has_prod (λ n, f (n+1)) (g / f 0) := begin
  have c := @product_cons (f 0)⁻¹ _ _ h,
  rw has_prod,
  rw [inv_mul_eq_div, has_prod, ←tendsto_comp_push, ←tendsto_comp_push] at c,
  have s : ((λ N : finset ℕ, N.prod (λ n, ((f 0)⁻¹::f) n)) ∘ push) ∘ push = λ N : finset ℕ, N.prod (λ n, f (n+1)), {
    clear c h g, apply funext, intro N, simp,
    nth_rewrite 1 ←stream.eta f,
    rw [←push_prod, ←push_prod, stream.head, stream.tail],
    field_simp, ring
  },
  rw s at c, assumption
end

-- Dropping a nonzero term divides by it (tprod version)
theorem product_drop' {f : ℕ → ℂ} (f0 : f 0 ≠ 0) (h : prod_exists f) : tprod (λ n, f (n+1)) = tprod f / f 0 := begin
  rcases h with ⟨g,h⟩, rw has_prod.tprod_eq h, rw has_prod.tprod_eq _, exact product_drop f0 h 
end

-- Products that start with zero are zero
lemma product_head_zero {f : ℕ → ℂ} (f0 : f 0 = 0) : has_prod f 0 := begin
  rw has_prod, rw metric.tendsto_at_top, intros e ep,
  existsi (finset.range 1), intros N N1,
  simp at N1, rw finset.prod_eq_zero N1 f0, simpa
end

-- Separate out head and tail in a product
theorem product_split {f : ℕ → ℂ} (h : prod_exists f) : tprod f = f 0 * tprod (λ n, f (n+1)) := begin
  by_cases f0 : f 0 = 0, { rw [f0, (product_head_zero f0).tprod_eq], simp },
  rw [product_drop' f0 h], field_simp, exact mul_comm _ _
end

-- The zero product
theorem has_prod.zero : has_prod (λ _, 0) 0 := begin apply product_head_zero, refl end