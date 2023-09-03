-- Facts about pow

import analysis.special_functions.pow.complex

-- (z ^ a) ^ n = z ^ (a * n)
lemma pow_mul_nat {z w : ℂ} {n : ℕ} : (z ^ w) ^ n = z ^ (w * n) := begin
  by_cases z0 : z = 0, {
    rw z0,
    by_cases w0 : w = 0, { rw w0, simp },
    by_cases n0 : n = 0, { rw n0, simp },
    have wn0 : w * n ≠ 0 := mul_ne_zero w0 (nat.cast_ne_zero.mpr n0),
    rw complex.zero_cpow w0,
    rw complex.zero_cpow wn0,
    exact zero_pow' n n0,
  },
  simp only [complex.cpow_def_of_ne_zero z0, ←complex.exp_nat_mul],
  ring_nf,
end
