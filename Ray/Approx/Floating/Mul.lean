import Ray.Approx.Floating.Abs
import Ray.Approx.Floating.Neg
import Ray.Approx.Floating.Standardization

open Pointwise

/-!
## Floating point multiplication

For floating point, multiplication is easier than addition, as the exponent adds.
If `z = x * y`, we have

  `z.n * 2^(z.s - 2^63) = x.n * y.n * 2^(x.s + y.s - 2^63 - 2^63)`
-/

open Set
open scoped Real
namespace Floating

/-!
### Auxiliary lemmas
-/

/-- The limit for our 64 bit → 128 bit multiplication -/
def mul_n_max : ℕ := (2^63 - 1) ^ 2

/-- Our `64 → 128` bit integer multiplication doesn't get too big -/
lemma mul_n_le {x y : Floating} (x0 : 0 ≤ x.val) (y0 : 0 ≤ y.val) :
    (mul128 x.n.n y.n.n).toNat ≤ mul_n_max := by
  rw [toNat_mul128, mul_n_max, pow_two]
  have hx := n_lt_of_nonneg x0
  have hy := n_lt_of_nonneg y0
  exact Nat.mul_le_mul (by omega) (by omega)

/-!
### The definition of multiplication
-/

/-- Normalize a 128-bit `n` into a 64-bit one, rounding and shifting as necessary.
    We also return how much we shifted left by. -/
@[irreducible, inline] def mul_norm (n : UInt128) (up : Bool) : UInt64 × UInt64 :=
  let t := n.log2
  let s := 126 - t
  -- Shift left to normalize
  let z : UInt128 := n <<< s
  -- Round to a single word
  let r : UInt64 := z.hi + bif z.lo != 0 && up then 1 else 0
  -- If we round up too much, shift down by one
  bif r == 2^63 then (2^62, s - 1) else (r, s)

/-- `mul_norm` returns a normalized value -/
lemma mul_norm_norm (n : UInt128) (up : Bool) (n0 : n ≠ 0) (lo : n.toNat ≤ mul_n_max) :
    (mul_norm n up).1.toNat ∈ Ico (2^62) (2^63) := by
  rw [mul_norm]
  generalize ht : n.log2 = t
  generalize hs : 126 - t = s
  generalize hz : n <<< s = z
  generalize hb : (bif z.lo != 0 && up then (1 : UInt64) else 0) = b
  generalize hr : z.hi + b = r
  generalize hp : (bif r == 2^63 then (2^62, s - 1) else (r, s)) = p
  simp only [hz, Bool.and_eq_true, bne_iff_ne, ne_eq, hr, mem_Ico, hb, hs, hp]
  simp only [UInt64.eq_iff_toNat_eq, UInt128.toNat_log2, UInt128.eq_iff_toNat_eq,
    UInt128.toNat_shiftLeft', UInt64.toNat_add, UInt64.size_eq_pow, bif_eq_if,
    apply_ite (f := fun x : UInt64 ↦ x.toNat), UInt64.toNat_zero,
    UInt64.toNat_one, beq_iff_eq, up63] at ht hz hb hr hs hp
  rw [UInt128.ne_zero_iff] at n0
  have t_le : t.toNat ≤ 126 := by
    rw [←ht, ←Nat.lt_succ_iff, Nat.log2_lt n0]; exact lt_of_le_of_lt lo (by norm_num [mul_n_max])
  have t_le' : t ≤ 126 := by simp only [UInt64.le_iff_toNat_le, u126, t_le]
  simp only [UInt64.toNat_sub t_le', u126] at hs
  have s_lt : s.toNat < 128 := by rw [←hs]; omega
  have nt' : n.toNat * 2^s.toNat < 2^127 := by
    refine lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (by positivity)) ?_
    simp only [ht, ← pow_add, ←hs]
    exact pow_le_pow_right (by norm_num) (by omega)
  have nt : n.toNat * 2^s.toNat < 2^128 := lt_trans nt' (by norm_num)
  have b1 : b.toNat ≤ 1 := by rw [←hb]; split_ifs; repeat norm_num
  simp only [UInt64.toNat_sub t_le', u126, Nat.mod_eq_of_lt s_lt, Nat.mod_eq_of_lt nt] at hz
  have z_lt : z.toNat < 2^127 := by rwa [←hz]
  have r_le : z.hi.toNat + b.toNat ≤ 2^63 := by
    rw [UInt128.toNat_def] at z_lt
    contrapose z_lt; simp only [not_le, not_lt] at z_lt ⊢
    have zh63 : 2^63 ≤ z.hi.toNat := by omega
    exact le_trans (le_trans (by norm_num) (Nat.mul_le_mul_right _ zh63)) (Nat.le_add_right _ _)
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt r_le (by norm_num))] at hr
  rw [hr] at r_le
  have le_z : 2^126 ≤ z.toNat := by
    rw [←hz, ←hs, ←ht]
    refine le_trans ?_ (Nat.mul_le_mul_right _ (Nat.log2_self_le n0))
    rw [←pow_add]
    exact pow_le_pow_right (by norm_num) (by omega)
  have le_r : 2^62 ≤ r.toNat := by
    rw [←hr]
    refine le_trans ?_ (Nat.le_add_right _ _)
    rw [UInt128.toNat_def] at le_z
    have zl := z.lo.toNat_lt
    norm_num only at le_z zl ⊢
    omega
  rw [←hp]
  split_ifs with r_eq
  · rw [up62]; decide
  · simp only [ite_false, le_r, r_le.lt_of_ne r_eq, and_self]

/-- Build a `Floating` with value `n * 2^s`, rounding if necessary -/
@[irreducible, inline] def mul_finish (n : UInt64) (s : UInt128) (up : Bool)
    (norm : n.toNat ∈ Ico (2^62) (2^63)) : Floating :=
  bif s.hi == 0 then { -- Exponent is already 64 bits, so not much to do
    n := ⟨n⟩
    s := s.lo
    zero_same := by
      intro n0
      simp only [Int64.ext_iff, Int64.n_zero] at n0
      simp only [n0, UInt64.toNat_zero, mem_Ico, nonpos_iff_eq_zero, gt_iff_lt, zero_lt_two,
        pow_pos, and_true] at norm
    nan_same := by
      intro nm
      simp only [Int64.ext_iff, Int64.n_min] at nm
      simp only [nm, UInt64.toNat_2_pow_63, mem_Ico, lt_self_iff_false, and_false] at norm
    norm := by
      intro _ _ _
      simp only [mem_Ico] at norm
      rw [Int64.abs_eq_self']
      · simp only [UInt64.le_iff_toNat_le, up62, norm.1]
      · simp only [Int64.isNeg_eq_le, decide_eq_false_iff_not, not_le, norm.2] }
  else bif s.hi < 1 <<< 63 then nan -- Overflow, exponent too big
  else bif up then min_norm else 0  -- Flush denormals for now

/-- Twos complement, 128-bit exponent `e = xs + ys + t - 126 - 2^64` -/
@[irreducible, inline] def mul_exponent (xs ys t : UInt64) : UInt128 :=
  let xs : UInt128 := ⟨xs,0⟩
  let ys : UInt128 := ⟨ys,0⟩
  let t : UInt128 := ⟨t,0⟩
  let c : UInt128 := ⟨62,1⟩
  xs + ys + t - c

/-- Multiply two positive, non-nan `Floating`s -/
@[irreducible, inline] def mul_of_pos (x y : Floating) (up : Bool)
    (x0 : 0 ≤ x.val) (y0 : 0 ≤ y.val) : Floating :=
  let z := mul128 x.n.n y.n.n  -- `z * 2^(x.s + y.s - 2^64)`.
  if z0 : z = 0 then 0 else
  let n := mul_norm z up  -- `n.1 * 2^(x.s + y.s + n.2 - 62 - 2^64)`
  let e := mul_exponent x.s y.s n.2  -- `n.1 * 2^e`
  mul_finish n.1 e up (mul_norm_norm z up z0 (mul_n_le x0 y0))

/-- Floating point multiply -/
@[irreducible] def mul (x y : Floating) (up : Bool) : Floating :=
  if n : x = nan ∨ y = nan then nan else
  bif x == 0 || y == 0 then 0 else
  let p := x.n.isNeg != y.n.isNeg
  let z := mul_of_pos x.abs y.abs (up.xor p)
    (abs_nonneg (not_or.mp n).1) (abs_nonneg (not_or.mp n).2)
  bif p then -z else z
