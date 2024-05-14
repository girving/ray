import Ray.Approx.Floating.Mul
import Ray.Approx.Interval.Basic
import Ray.Approx.Interval.Preinterval

open Classical
open Pointwise

/-!
## Interval arithmetic multiplication
-/

open Set
open scoped Real
namespace Interval

/-!
### Definition, without correctness proof
-/

/-- Multiply two intervals, producing a not necessarily correct interval.
    We define this, prove it correct, then wrap it in `Mul Interval` below. -/
@[irreducible, inline, pp_dot] def premul (x : Interval) (y : Interval) : Preinterval :=
  bif x.lo.n.isNeg != x.hi.n.isNeg && y.lo.n.isNeg != x.hi.n.isNeg then  -- x,y have mixed sign
    ⟨min (x.lo.mul y.hi false) (x.hi.mul y.lo false),
     (x.lo.mul y.lo true).max (x.hi.mul y.hi true)⟩
  else -- At least one of x,y has constant sign, so we can save multiplications
    let (a,b,c,d) := match (x.lo.n.isNeg, x.hi.n.isNeg, y.lo.n.isNeg, y.hi.n.isNeg) with
      | (false, _, false, _)    => (x.lo, x.hi, y.lo, y.hi)  -- 0 ≤ x, 0 ≤ y
      | (false, _, true, false) => (x.hi, x.hi, y.lo, y.hi)  -- 0 ≤ x, 0 ∈ y
      | (false, _, _, true)     => (x.hi, x.lo, y.lo, y.hi)  -- 0 ≤ x, y ≤ 0
      | (true, false, false, _) => (x.lo, x.hi, y.hi, y.hi)  -- 0 ∈ x, 0 ≤ y
      | (true, false, _, _)     => (x.hi, x.lo, y.lo, y.lo)  -- 0 ∈ x, y ≤ 0 (0 ∈ y is impossible)
      | (_, true, false, _)     => (x.lo, x.hi, y.hi, y.lo)  -- x ≤ 0, 0 ≤ y
      | (_, true, true, false)  => (x.lo, x.lo, y.hi, y.lo)  -- x ≤ 0, 0 ∈ y
      | (_, true, _, true)      => (x.hi, x.lo, y.hi, y.lo)  -- x ≤ 0, y ≤ 0
    ⟨a.mul c false, b.mul d true⟩

/-!
### Correctness proof
-/

/-- `premul` propagates `x = nan` -/
@[simp] lemma nan_premul {y : Interval} : (nan : Interval).premul y = nan := by
  rw [premul]
  simp only [lo_nan, Floating.n_nan, Int64.isNeg_min, hi_nan, bne_self_eq_false, Floating.isNeg_iff,
    Bool.xor_true, Bool.false_and, Floating.nan_mul, min_self, max_self, bif_eq_if, ite_false]
  rcases y.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals try simp only [not_lt.mpr ls]
  all_goals try simp only [not_lt.mpr hs]
  all_goals simp only [ls, hs, decide_true_eq_true, decide_false_eq_false, Floating.mul_nan,
    Floating.nan_mul, Preinterval.approx_nan_lo, Preinterval.approx_nan_hi, subset_univ,
    ←Preinterval.nan_def]

/-- `premul` propagates `y = nan` -/
@[simp] lemma premul_nan {x : Interval} : x.premul nan = nan := by
  rw [premul]
  simp only [Floating.isNeg_iff, lo_nan, Floating.n_nan, Int64.isNeg_min, Bool.true_xor, hi_nan,
    Floating.mul_nan, min_self, max_self, bif_eq_if, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_decide, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  rcases x.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals try simp only [not_lt.mpr ls]
  all_goals try simp only [not_lt.mpr hs]
  all_goals simp only [ls, hs, decide_true_eq_true, decide_false_eq_false, Floating.mul_nan,
    Floating.nan_mul, Preinterval.approx_nan_lo, Preinterval.approx_nan_hi, subset_univ, not_true,
    bne_self_eq_false, Bool.and_self, ite_self, Preinterval.approx_nan_hi, ←Preinterval.nan_def,
    false_and, if_false, true_iff, not_false_iff, true_and, if_true, Floating.max_nan]

set_option maxHeartbeats 10000000 in
/-- `mul` respects `approx` -/
lemma approx_premul (x : Interval) (y : Interval) : approx x * approx y ⊆ approx (x.premul y) := by
  -- Discard nans
  by_cases n : x = nan ∨ y = nan
  · rcases n with n | n
    all_goals simp only [n, nan_premul, premul_nan, Preinterval.approx_nan, subset_univ]
  rcases not_or.mp n with ⟨xn,yn⟩; clear n
  rw [premul]
  simp only [image2_mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq, Floating.isNeg_iff,
    Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_decide]
  -- Record Floating.mul bounds
  generalize mll0 : x.lo.mul y.lo false = ll0
  generalize mlh0 : x.lo.mul y.hi false = lh0
  generalize mhl0 : x.hi.mul y.lo false = hl0
  generalize mhh0 : x.hi.mul y.hi false = hh0
  generalize mll1 : x.lo.mul y.lo true = ll1
  generalize mlh1 : x.lo.mul y.hi true = lh1
  generalize mhl1 : x.hi.mul y.lo true = hl1
  generalize mhh1 : x.hi.mul y.hi true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * y.lo.val := by rw [←mll0]; exact Floating.mul_le
  have ilh0 : lh0 ≠ nan → lh0.val ≤ x.lo.val * y.hi.val := by rw [←mlh0]; exact Floating.mul_le
  have ihl0 : hl0 ≠ nan → hl0.val ≤ x.hi.val * y.lo.val := by rw [←mhl0]; exact Floating.mul_le
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * y.hi.val := by rw [←mhh0]; exact Floating.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * y.lo.val ≤ ll1.val := by rw [←mll1]; exact Floating.le_mul
  have ilh1 : lh1 ≠ nan → x.lo.val * y.hi.val ≤ lh1.val := by rw [←mlh1]; exact Floating.le_mul
  have ihl1 : hl1 ≠ nan → x.hi.val * y.lo.val ≤ hl1.val := by rw [←mhl1]; exact Floating.le_mul
  have ihh1 : hh1 ≠ nan → x.hi.val * y.hi.val ≤ hh1.val := by rw [←mhh1]; exact Floating.le_mul
  have xle := x.le
  have yle := y.le
  -- Split on signs
  rcases x.sign_cases with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals try simp only [not_lt.mpr xls]
  all_goals try simp only [not_lt.mpr xhs]
  all_goals rcases y.sign_cases with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
  all_goals try simp only [not_lt.mpr yls]
  all_goals try simp only [not_lt.mpr yhs]
  all_goals simp only [xls, xhs, yls, yhs, not_true, false_and, if_false, decide_true_eq_true,
    decide_false_eq_false, true_iff, not_false_iff, true_and, if_true, mll0, mlh0, mhl0, mhh0, mll1,
    mlh1, mhl1, mhh1]
  all_goals clear mll0 mlh0 mhl0 mhh0 mll1 mlh1 mhl1 mhh1
  all_goals simp only [approx, xn, yn, x.lo_ne_nan xn, x.hi_ne_nan xn, y.lo_ne_nan yn,
    y.hi_ne_nan yn, if_false, subset_if_univ_iff, not_or, and_imp, Icc_mul_Icc_subset_Icc xle yle,
    Floating.min_eq_nan, Floating.max_eq_nan, Floating.val_min, min_le_iff]
  -- Dispatch everything with nlinarith
  · intro m0 m1; specialize ihh0 m0; specialize ill1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ilh0 m0; specialize ihl1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ilh0 m0; specialize ill1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ihl0 m0; specialize ilh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ill0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1; specialize ihl0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1 m2 m3
    specialize ilh0 m0; specialize ihl0 m1; specialize ill1 m2; specialize ihh1 m3
    simp only [Floating.val_max m2 m3, le_max_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
  · intro m0 m1; specialize ilh0 m0; specialize ihh1 m1
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith,
            by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · intro m0 m1 m2 m3
    specialize ilh0 m0; specialize ihl0 m1; specialize ill1 m2; specialize ihh1 m3
    simp only [Floating.val_max m2 m3, le_max_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith

/-!
### Final definition
-/

/-- Multiply two intervals -/
@[irreducible, pp_dot] def mul (x : Interval) (y : Interval) : Interval :=
  (x.premul y).mix' (approx_premul x y (mul_mem_mul x.lo_mem y.lo_mem))

/-- `* = mul` -/
instance : Mul Interval where
  mul (x y : Interval) := x.mul y

/-- `*` definition -/
lemma mul_def {x y : Interval} : x * y = x.mul y := rfl

/-- `Interval` multiplication approximates `ℝ` -/
instance : ApproxMul Interval ℝ where
  approx_mul x y := by
    rw [mul_def, mul, Preinterval.approx_mix']
    apply approx_premul

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing Interval ℝ where

/-- `approx_mul` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul {a b : Set ℝ} {x : Interval} {y : Interval}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) : a * b ⊆ approx (x * y) :=
  subset_trans (mul_subset_mul as bs) (approx_mul x y)

/-- `approx_mul` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul {a b : ℝ} {x : Interval} {y : Interval}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (x * y) :=
  subset_approx_mul (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `mul` propagates `x = nan` -/
@[simp] lemma nan_mul {y : Interval} : nan * y = nan := by
  rw [mul_def, mul]; simp only [nan_premul, lo_nan, Preinterval.mix_nan']

/-- `mul` propagates `y = nan` -/
@[simp] lemma mul_nan {x : Interval} : x * nan = nan := by
  rw [mul_def, mul]; simp only [premul_nan, lo_nan, Preinterval.mix_nan']

/-- `mul` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_mul {x : Interval} {y : Interval} (n : x * y ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n
  all_goals simp only [n, nan_mul, mul_nan]

/-!
### `Floating * Floating`, but conservative
-/

/-- Multiply two `Floating`s, producing an `Interval -/
@[irreducible] def float_mul_float (x : Floating) (y : Floating) : Interval :=
  mix (x.mul y false) (x.mul y true)
    (fun n0 n1 ↦ le_trans (Floating.mul_le n0) (Floating.le_mul n1))

/-- `float_mul_float` respects `approx` -/
lemma approx_float_mul_float (x : Floating) (y : Floating) :
    approx x * approx y ⊆ approx (float_mul_float x y) := by
  intro a m
  simp only [mem_mul, exists_and_left] at m
  rcases m with ⟨b,bm,c,cm,bc⟩
  rw [float_mul_float]
  simp only [approx, mem_ite_univ_left, mem_singleton_iff, mem_Icc] at bm cm ⊢
  by_cases n : x = nan ∨ y = nan ∨ Floating.mul x y false = nan ∨ Floating.mul x y true = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, Ne] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  intro nm
  simp only [n0, not_false_eq_true, forall_true_left, n1, lo_eq_nan] at bm cm nm
  simp only [n2, n3, or_self, not_false_eq_true, ← bc, bm, cm, forall_true_left, lo_mix nm,
    hi_mix nm]
  exact ⟨Floating.mul_le n2, Floating.le_mul n3⟩

/-- `approx_float_mul_float` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_float_mul_float {a b : Set ℝ} {x : Floating} {y : Floating}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (float_mul_float x y) :=
  subset_trans (mul_subset_mul as bs) (approx_float_mul_float x y)

/-- `approx_float_mul_float` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_float_mul_float {a b : ℝ} {x : Floating} {y : Floating}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (float_mul_float x y) :=
  subset_approx_float_mul_float (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `float_mul_float _ nan _ = nan` -/
@[simp] lemma float_mul_float_nan_right {x : Floating} :
    float_mul_float x (nan : Floating) = nan := by
  simp only [float_mul_float, Floating.mul_nan, mix_self, coe_nan]

/-- `float_mul_float nan _ _ = nan` -/
@[simp] lemma float_mul_float_nan_left {x : Floating} :
    float_mul_float (nan : Floating) x = nan := by
  simp only [float_mul_float, Floating.nan_mul, mix_self, coe_nan]

/-- `float_mul_float` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_float_mul_float {x : Floating} {y : Floating}
    (n : (float_mul_float x y).lo ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp [n]

/-!
### `Interval * Floating`
-/

/-- Multiply times a `Floating` -/
@[irreducible, pp_dot] def mul_float (x : Interval) (y : Floating) : Interval :=
  let t := bif y.n.isNeg then (x.hi, x.lo) else (x.lo, x.hi)
  mix (t.1.mul y false) (t.2.mul y true) (by
    intro n0 n1
    refine le_trans (Floating.mul_le n0) (le_trans ?_ (Floating.le_mul n1))
    clear n0 n1
    simp only [t, bif_eq_if, Floating.isNeg_iff, decide_eq_true_eq]
    by_cases y0 : y.val < 0
    · simp only [y0, ite_true, mul_le_mul_right_of_neg, le]
    · simp only [y0, ite_false]; exact mul_le_mul_of_nonneg_right x.le (not_lt.mp y0))

/-- `mul_float` respects `approx` -/
lemma approx_mul_float (x : Interval) (y : Floating) :
    approx x * approx y ⊆ approx (x.mul_float y) := by
  -- Handle special cases
  rw [mul_float]
  simp only [Floating.isNeg_iff, bif_eq_if, decide_eq_true_eq]
  by_cases n : x = nan ∨ y = nan
  · rcases n with n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1⟩
  have xle : x.lo.val ≤ x.hi.val := x.le
  -- Record Floating.mul bounds
  generalize ml0 : x.lo.mul y false = l0
  generalize mh0 : x.hi.mul y false = h0
  generalize ml1 : x.lo.mul y true = l1
  generalize mh1 : x.hi.mul y true = h1
  have il0 : l0 ≠ nan → l0.val ≤ x.lo.val * y.val := by rw [←ml0]; exact Floating.mul_le
  have ih0 : h0 ≠ nan → h0.val ≤ x.hi.val * y.val := by rw [←mh0]; exact Floating.mul_le
  have il1 : l1 ≠ nan → x.lo.val * y.val ≤ l1.val := by rw [←ml1]; exact Floating.le_mul
  have ih1 : h1 ≠ nan → x.hi.val * y.val ≤ h1.val := by rw [←mh1]; exact Floating.le_mul
  -- Split on signs
  by_cases ys : y.val < 0
  all_goals simp only [ys, n0, n1, ite_true, ite_false, approx, false_or, subset_if_univ_iff,
    not_or, and_imp, ml0, mh0, ml1, mh1, mul_singleton, x.lo_ne_nan n0]
  all_goals intro m
  all_goals simp only [lo_eq_nan] at m
  all_goals simp only [lo_mix m, hi_mix m]
  all_goals simp only [mix_eq_nan, not_or, Ne] at m
  -- Handle each case
  · have le : x.hi.val * y.val ≤ x.lo.val * y.val := by nlinarith
    simp only [image_mul_right_Icc_of_neg ys, Icc_subset_Icc_iff le]
    exact ⟨ih0 m.1, il1 m.2⟩
  · have le : x.lo.val * y.val ≤ x.hi.val * y.val := by nlinarith
    simp only [image_mul_right_Icc xle (not_lt.mp ys), Icc_subset_Icc_iff le]
    exact ⟨il0 m.1, ih1 m.2⟩

/-- `approx_mul_float` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul_float {a b : Set ℝ} {x : Interval} {y : Floating}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) : a * b ⊆ approx (mul_float x y) :=
  subset_trans (mul_subset_mul as bs) (approx_mul_float x y)

/-- `approx_mul_float` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul_float {a b : ℝ} {x : Interval} {y : Floating}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (mul_float x y) :=
  subset_approx_mul_float (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-!
### Interval squaring
-/

/-- Tighter than `mul x x` -/
@[pp_dot] def sqr (x : Interval) : Interval :=
  if m : x.lo.n.isNeg != x.hi.n.isNeg then  -- x has mixed sign
    mix 0 ((x.lo.mul x.lo true).max (x.hi.mul x.hi true)) (by
      intro _ n
      simp only [ne_eq, Floating.max_eq_nan, not_or] at n
      simp only [Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide] at m
      simp only [Floating.val_zero, Floating.val_max n.1 n.2, le_max_iff]
      by_cases x0 : x.lo.val < 0
      · left; exact le_trans (by nlinarith) (Floating.le_mul n.1)
      · right; exact le_trans (by nlinarith) (Floating.le_mul n.2))
  else if x0 : x.lo.n.isNeg then
    mix (x.hi.mul x.hi false) (x.lo.mul x.lo true) (by
      intro n0 n1
      simp only [Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide, not_not,
        decide_eq_true_eq] at m x0
      have le := x.le
      have h0 := m.mp x0
      exact le_trans (Floating.mul_le n0) (le_trans (by nlinarith) (Floating.le_mul n1)))
  else
    mix (x.lo.mul x.lo false) (x.hi.mul x.hi true) (by
      intro n0 n1
      simp only [Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide, not_not,
        decide_eq_true_eq] at m x0
      have le := x.le
      exact le_trans (Floating.mul_le n0) (le_trans (by nlinarith) (Floating.le_mul n1)))

/-- `sqr` respects `approx` -/
@[mono] lemma approx_sqr (x : Interval) : (fun x ↦ x^2) '' approx x ⊆ approx x.sqr := by
  -- Record Floating.mul bounds
  generalize mll0 : x.lo.mul x.lo false = ll0
  generalize mll1 : x.lo.mul x.lo true = ll1
  generalize mhh0 : x.hi.mul x.hi false = hh0
  generalize mhh1 : x.hi.mul x.hi true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * x.lo.val := by rw [←mll0]; exact Floating.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * x.lo.val ≤ ll1.val := by rw [←mll1]; exact Floating.le_mul
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * x.hi.val := by rw [←mhh0]; exact Floating.mul_le
  have ihh1 : hh1 ≠ nan → x.hi.val * x.hi.val ≤ hh1.val := by rw [←mhh1]; exact Floating.le_mul
  -- Handle special cases
  simp only [sqr, Floating.isNeg_iff, bne_iff_ne, ne_eq, decide_eq_decide, decide_eq_true_eq,
    dite_not]
  by_cases n : x = nan
  · simp only [n, approx_nan, lo_nan, Floating.val_nan_lt_zero, hi_nan, Floating.mul_nan, mix_self,
      coe_nan, dite_eq_ite, ite_self, le_refl, Floating.max_nan, mix_nan, preimage_univ,
      subset_univ]
  -- Split on signs
  rcases x.sign_cases with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals try simp only [not_lt.mpr xls]
  all_goals try simp only [not_lt.mpr xhs]
  all_goals simp only [xls, xhs, bne_self_eq_false, Bool.false_and, if_false, not_or, dite_false,
    Bool.xor_false, Bool.and_self, dite_true, Bool.and_false, ite_false, approx, false_or,
    Floating.max_eq_nan, subset_if_univ_iff, and_imp, mll0, mhh0, mll1, mhh1, sqr_Icc_subset_Icc,
    x.lo_ne_nan n, x.hi_ne_nan n, lo_eq_nan, n, true_iff]
  all_goals intro m
  all_goals simp only [lo_mix m, hi_mix m]
  all_goals simp only [mix_eq_nan, true_iff, not_lt, not_or, Floating.max_eq_nan] at m
  -- Dispatch everything with nlinarith
  · intro u lu uh
    specialize ihh0 m.1; specialize ill1 m.2
    exact ⟨by nlinarith, by nlinarith⟩
  · intro u lu uh
    specialize ill0 m.1; specialize ihh1 m.2
    exact ⟨by nlinarith, by nlinarith⟩
  · intro u lu uh
    specialize ill1 m.2.1; specialize ihh1 m.2.2
    simp only [Floating.val_zero, Floating.val_max m.2.1 m.2.2, le_max_iff]
    constructor
    · nlinarith
    · by_cases us : u < 0
      · left; nlinarith
      · right; nlinarith

/-- `sqr` respects `approx`, `∈` version -/
@[mono] lemma mem_approx_sqr (a : ℝ) (x : Interval) (ax : a ∈ approx x) : a^2 ∈ approx x.sqr := by
  apply approx_sqr; use a
