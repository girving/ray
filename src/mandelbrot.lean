-- Mandelbrot set

import data.real.basic
import data.complex.basic
import tactic.linarith.frontend
import tactics
import simple
open tactic.interactive (nlinarith)
open complex (abs has_zero)
open simple

def f (c : ℂ) : ℕ → ℂ
| 0 := 0
| (n+1) := let z := f n in z^2+c

def escape (s : ℕ → ℂ) := ∀ r : ℝ, ∃ n : ℕ, abs (s n) ≥ r

def M (c : ℂ) := ∀ n : ℕ, abs (f c n) ≤ 2
def Mc (c : ℂ) := escape (f c)

lemma f_zero (n : ℕ) : f 0 n = 0 := begin
  induction n,
  exact rfl,
  rw f, simp, exact n_ih
end

lemma f_one (c : ℂ) : f c 1 = c := begin
  rw f, simp, rw f
end

theorem M_zero : M 0 := begin
  rw M, intros, rw f_zero, simp,
end

theorem M_disk (c : ℂ) (h : M c) : abs c ≤ 2 := begin
  specialize h 1, rw f_one at h, exact h
end

def Mr (r : ℝ) (c : ℂ) := ∀ n : ℕ, abs (f c n) ≤ r

theorem Mr2 (c : ℂ) : M c ↔ Mr 2 c := by apply iff.refl

lemma f_sub_ge {z c : ℂ} : abs (z^2 + c) ≥ (abs z)^2 - abs c := begin
  calc abs (z^2 + c) ≥ abs (z^2) - abs c : abs_sub_ge _ _
   ... = (abs z)^2 - abs c : by rw complex.abs_pow
end

lemma large_escape_helper {c : ℂ} {s : ℝ} (h1 : s ≥ 0) (h2 : 2 + s ≤ abs c) (n : ℕ)
  : abs (f c (n+1)) ≥ (abs c)*(1 + n*s) :=
begin
   induction n with n,
   simp, rw f_one,
   rw f, simp,
   let hs : n.succ = n + 1 := rfl,
   rw hs, clear hs,
   set z := f c (n + 1),
   flip_ineq,
   calc abs (z^2 + c) ≥ (abs z)^2 - abs c : f_sub_ge
   ... ≥ (abs c * (1 + n*s))^2 - abs c : by bound
   ... = abs c * (abs c * (1 + n*s)^2 - 1) : by ring
   ... ≥ abs c * ((2 + s) * (1 + n*s)^2 - 1) : by bound
   ... ≥ abs c * ((2 + s) * (1 + 2*n*s) - 1) : begin
     have h := sq_bound (n*s), rw ←mul_assoc at h, bound end
   ... = abs c * (2 + 4*n*s + s + 2*n*s^2 - 1) : by ring
   ... ≥ abs c * (2 + 1*n*s + s + 0 - 1) : by bound
   ... = abs c * (1 + (n+1)*s) : by ring
end

lemma small_escape_helper {c : ℂ} {s : ℝ} {n : ℕ} (h1 : s ≥ 0) (hs : abs c ≤ 2)
  (e : abs (f c n) ≥ 2 + s) (m : ℕ) : abs (f c (n+m)) ≥ 2 + (1+m)*s :=
begin
  induction m with m,
  simp, bound,
  have su : n + m.succ = (n + m).succ := rfl,
  rw [su, f], simp, flip_ineq,
  set z := f c (n + m),
  calc abs (z ^ 2 + c) ≥ abs z^2 - abs c : f_sub_ge
  ... ≥ (2 + (1 + ↑m) * s)^2 - 2 : by bound
  ... = 2 + (4 + 4*↑m) * s + ((1 + m) * s)^2 : by ring
  ... ≥ 2 + (2 + 1*↑m) * s + (0 : ℝ)^2 : by bound
  ... = 2 + (2 + ↑m) * s : by ring
  ... = 2 + (1 + (↑m + 1)) * s : by ring
end

theorem large_escape {c : ℂ} (h : abs c > 2) : Mc c := begin
  rcases gap h with ⟨s, sp, sc⟩,
  intro,
  cases large_div_nat (abs c * s) r (by nlinarith) with k hk,
  existsi (k + 1),
  calc abs (f c (k + 1)) ≥ abs c * (1 + ↑k * s) :
    large_escape_helper (le_of_lt sp) sc k
  ... = abs c + abs c * s * ↑k : by ring
  ... ≥ abs c * s * ↑k : by linarith
  ... ≥ r : by bound
end

theorem small_escape {c : ℂ} (hs : abs c ≤ 2) {n : ℕ} (e : abs (f c n) > 2)
    : Mc c := begin
  rcases gap e with ⟨s, _, sc⟩,
  intro,
  cases large_div_nat s r (by linarith) with m hm,
  existsi (n + m),
  have snn : s ≥ 0 := by linarith,
  calc abs (f c (n + m)) ≥ 2 + (1+m)*s : small_escape_helper (by linarith) hs sc m
  ... ≥ 0 + (0+m)*s : by bound
  ... = m*s : by ring
  ... ≥ r : by linarith
end

theorem M_escape {c : ℂ} : M c ↔ ¬Mc c := begin
  apply iff.intro, {
    intro h,
    by_contradiction e,
    rw M at h,
    rw [Mc, escape] at e,
    cases e 3 with n,
    have hn := h n,
    linarith
  }, {
    intro e,
    cases le_or_gt (abs c) 2 with hs hl, {
      by_contradiction h,
      rw M at h,
      cases not_all h with n h,
      revert h, simp,
      by_contradiction q,
      have se := small_escape hs q,
      trivial
    }, {
      have he := large_escape hl,
      trivial
    }
  }
end

-- If abs c ≥ 4, the iteration escapes exponentially fast
theorem fast_escape {c : ℂ} {h : abs c ≥ 4} {n : ℕ}
  : abs (f c (n+1)) ≥ 2^n * abs c :=
begin
  induction n with n,
  simp, rw f_one,
  have su : n.succ + 1 = (n+1).succ := rfl,
  rw [su, f], simp,
  set z := f c (n+1),
  flip_ineq,
  calc abs (z ^ 2 + c) ≥ abs z^2 - abs c : f_sub_ge
  ... ≥ (2^n * abs c)^2 - abs c : by bound
  ... = 2^n * 2^n * abs c * abs c - abs c : by ring
  ... ≥ 2^n * 2^n * abs c * 4 - abs c : by bound
  ... = (4*2^n*2^n-1) * abs c : by ring
  ... ≥ 2^(n+1) * abs c : mul_le_mul_of_nonneg_right _ (complex.abs_nonneg _),
  clear n_ih z su h c,
  rw pow_succ,
  simp,
  set p : ℝ := 2^n,
  have ph : p ≥ 1 := coe_pow_ge_one,
  nlinarith
end