-- Julia sets

import data.real.basic
import data.complex.basic
import tactic.linarith.frontend
import tactics
import simple
open tactic.interactive (nlinarith)
open complex (abs has_zero)
open nat (iterate)
open simple

-- Evaluation of polynomials
def eval (p : polynomial ℂ) (z : ℂ) : ℂ := p.sum (λ n c, c * z^n)

-- Iteration of polynomials
noncomputable def iter (p : polynomial ℂ) : ℕ → polynomial ℂ
| 0 := 1
| (n+1) := polynomial.comp p (iter n)

-- Sequences that escape to infinity
def escape (s : ℕ → ℂ) := ∀ r, ∃ n, abs (s n) ≥ r

-- The filled Julia set: points that remain bounded
def K (p : polynomial ℂ) (z : ℂ) := ∃ r, ∀ n, abs (eval (iter p n) z) ≤ r

-- The complement of the filled Julia set: points that escape to infinity
def Kc (p : polynomial ℂ) (z : ℂ) := escape (λ n, eval (iter p n) z)