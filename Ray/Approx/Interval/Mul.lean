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

/-- Multiply, changing `s` -/
@[irreducible, inline, pp_dot] def premul (x : Interval) (y : Interval) : Preinterval :=
  bif x.lo.n.isNeg != x.hi.n.isNeg && y.lo.n.isNeg != x.hi.n.isNeg then  -- x,y have mixed sign
    ⟨min (x.lo.mul y.hi false) (x.hi.mul y.lo false),
     max (x.lo.mul y.lo true) (x.hi.mul y.hi true)⟩
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
lemma nan_premul {y : Interval} : (nan : Interval).premul y = nan := by
  rw [premul]
  simp only [image2_mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  simp only [approx_nan, lo_nan, Floating.n_nan, Int64.isNeg_min, hi_nan, bne_self_eq_false,
    Floating.isNeg_iff, Bool.xor_true, Bool.false_and, Floating.nan_mul, min_self, max_self,
    ite_false]
  rcases y.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
  all_goals try simp only [not_lt.mpr ls]
  all_goals try simp only [not_lt.mpr hs]
  all_goals simp only [ls, hs, decide_true_eq_true, decide_false_eq_false, Floating.mul_nan,
    Floating.nan_mul, Preinterval.approx_nan_lo, Preinterval.approx_nan_hi, subset_univ]

set_option maxHeartbeats 10000000 in
/-- `mul` respects `approx` -/
lemma approx_mul (x : Interval) (y : Interval) : approx x * approx y ⊆ approx (x.premul y) := by
  -- Handle special cases
  rw [premul]
  simp only [image2_mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  -- Discard nans
  by_cases xn : x = nan
  · simp only [xn, approx_nan, lo_nan, Floating.n_nan, Int64.isNeg_min, hi_nan, bne_self_eq_false,
      Floating.isNeg_iff, Bool.xor_true, Bool.false_and, Floating.nan_mul, min_self, max_self,
      ite_false]
    rcases y.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
    all_goals try simp only [not_lt.mpr ls]
    all_goals try simp only [not_lt.mpr hs]
    all_goals simp only [ls, hs, decide_true_eq_true, decide_false_eq_false, Floating.mul_nan,
      Floating.nan_mul, Preinterval.approx_nan_lo, Preinterval.approx_nan_hi, subset_univ]
  by_cases yn : y = nan
  · simp only [yn, approx_nan, lo_nan, Floating.n_nan, Int64.isNeg_min, hi_nan, bne_self_eq_false,
      Floating.isNeg_iff, Bool.xor_true, Bool.false_and, Floating.mul_nan, min_self, max_self,
      ite_false]
    rcases x.sign_cases with ⟨ls,hs⟩ | ⟨ls,hs⟩ | ⟨ls,hs⟩
    all_goals try simp only [not_lt.mpr ls]
    all_goals try simp only [not_lt.mpr hs]
    all_goals simp only [ls, hs, decide_true_eq_true, decide_false_eq_false, Floating.mul_nan,
      Floating.nan_mul, Preinterval.approx_nan_lo, Preinterval.approx_nan_hi, subset_univ,
      bne_self_eq_false, Bool.and_self, ite_self, Preinterval.approx_nan_hi]
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
  all_goals rcases y.sign_cases with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
  all_goals simp only [xls, xhs, yls, yhs, bne_self_eq_false, Bool.false_and,
    if_false, Bool.xor_false, Bool.and_self, ite_true, Bool.and_false, ite_false, approx,
    Ici_inter_Iic, Floating.min_eq_nan, false_or, Floating.max_eq_nan, subset_if_univ_iff, not_or,
    and_imp, mll0, mlh0, mhl0, mhh0, mll1, mlh1, mhl1, mhh1, Icc_mul_Icc_subset_Icc x.le y.le,
    Floating.val_min, min_le_iff, Floating.isNeg_iff, decide_true_eq_true, x.lo_ne_nan xn,
    x.hi_ne_nan xn, y.lo_ne_nan yn, y.hi_ne_nan yn]
  all_goals clear mll0 mlh0 mhl0 mhh0 mll1 mlh1 mhl1 mhh1
  -- Dispatch everything with nlinarith
  · intro m0 m1; specialize ihh0 m0; specialize ill1 m1
    exact ⟨by nlinarith?, by nlinarith, by nlinarith, by nlinarith,
           by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  stop
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

#exit

/-!
### Final definition
-/

/-- `* = mul` -/
instance : Mul Interval where
  mul (x y : Interval) := x.mul y s

/-- `Interval` multiplication approximates `ℝ` -/
instance : ApproxMul Interval ℝ where
  approx_mul _ _ := approx_mul _ _ _

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing Interval ℝ where

/-- `approx_mul` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul {a b : Set ℝ} {x : Interval} {y : Interval}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) : a * b ⊆ approx (x.mul y) :=
  subset_trans (mul_subset_mul as bs) (approx_mul x y _)

/-- `approx_mul` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul {a b : ℝ} {x : Interval} {y : Interval}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (x.mul y) :=
  subset_approx_mul (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `mul` propagates `lo = nan` -/
@[simp] lemma mul_nan_lo {x : Interval} {y : Interval} (yn : y.lo = nan) :
    x.mul y = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Floating.isNeg_nan, Bool.true_xor,
    Floating.mul_nan, cond_true]

/-- `mul` propagates `hi = nan` -/
@[simp] lemma mul_nan_hi {x : Interval} {y : Interval} (yn : y.hi = nan) :
    x.mul y = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Floating.isNeg_nan, Bool.true_xor,
    Floating.mul_nan, cond_true]

/-- `mul` propagates `lo = nan` -/
@[simp] lemma nan_mul_lo {x : Interval} {y : Interval} (xn : x.lo = nan) :
    x.mul y = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Floating.isNeg_nan, Bool.true_xor,
    Floating.mul_nan, cond_true]

/-- `mul` propagates `hi = nan` -/
@[simp] lemma nan_mul_hi {x : Interval} {y : Interval} (xn : x.hi = nan) :
    x.mul y = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Floating.isNeg_nan, Bool.true_xor,
    Floating.mul_nan, cond_true]

/-- `mul` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_mul {x : Interval} {y : Interval}
    (n : (x.mul y).lo ≠ nan) : x.lo ≠ nan ∧ x.hi ≠ nan ∧ y.lo ≠ nan ∧ y.hi ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n | n | n
  · rwa [nan_mul_lo, nan_def]
  · rwa [nan_mul_hi, nan_def]
  · rwa [mul_nan_lo, nan_def]
  · rwa [mul_nan_hi, nan_def]

/-!
### `Floating * Floating`, but conservative
-/

/-- Multiply two `Floating`s, producing an `Interval -/
def fixed_mul_fixed (x : Floating s) (y : Floating t) : Interval :=
  ⟨x.mul y false, x.mul y true⟩

/-- `fixed_mul_fixed` respects `approx` -/
lemma approx_fixed_mul_fixed (x : Floating s) (y : Floating t) :
    approx x * approx y ⊆ approx (fixed_mul_fixed x y) := by
  intro a m
  simp only [mem_mul, exists_and_left] at m
  rcases m with ⟨b,bm,c,cm,bc⟩
  simp only [approx, mem_ite_univ_left, mem_singleton_iff, mem_Icc,
    fixed_mul_fixed] at bm cm ⊢
  by_cases n : x = nan ∨ y = nan ∨ Floating.mul x y false = nan ∨ Floating.mul x y true = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←Ne.def] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, not_false_eq_true, forall_true_left, n1] at bm cm
  simp only [n2, n3, or_self, not_false_eq_true, ← bc, bm, cm, forall_true_left]
  exact ⟨Floating.mul_le n2, Floating.le_mul n3⟩

/-- `approx_fixed_mul_fixed` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_fixed_mul_fixed {a b : Set ℝ} {x : Floating s} {y : Floating t}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (fixed_mul_fixed x y) :=
  subset_trans (mul_subset_mul as bs) (approx_fixed_mul_fixed x y _)

/-- `approx_fixed_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_fixed_mul_fixed {a b : ℝ} {x : Floating s} {y : Floating t}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (fixed_mul_fixed x y) :=
  subset_approx_fixed_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `fixed_mul_fixed _ nan _ = nan` -/
@[simp] lemma fixed_mul_fixed_nan_right {x : Floating s} :
    fixed_mul_fixed x (nan : Floating t) = nan := by
  simp only [fixed_mul_fixed, Floating.mul_nan, nan_def]

/-- `fixed_mul_fixed nan _ _ = nan` -/
@[simp] lemma fixed_mul_fixed_nan_left {x : Floating t} :
    fixed_mul_fixed (nan : Floating s) x = nan := by
  simp only [fixed_mul_fixed, Floating.nan_mul, nan_def]

/-- `fixed_mul_fixed` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_fixed_mul_fixed {x : Floating s} {y : Floating t}
    (n : (fixed_mul_fixed x y).lo ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp [n]

/-!
### `Interval * Floating`
-/

/-- Multiply times a `Floating`, changing `s` -/
@[pp_dot] def mul_fixed (x : Interval) (y : Floating t) : Interval :=
  bif x.lo == nan || x.hi == nan || y == nan then nan else
  let (a,b) := bif y.n.isNeg then (x.hi, x.lo) else (x.lo, x.hi)
  ⟨a.mul y false, b.mul y true⟩

/-- Diagonal comparison to 0 -/
@[simp] lemma diagonal_eq_zero (x : Floating s) : ((⟨x,x⟩ : Interval) = 0) ↔ x == 0 := by
  simp only [ext_iff, lo_zero, hi_zero, and_self, beq_iff_eq]

/-- `mul_fixed` respects `approx` -/
lemma approx_mul_fixed (x : Interval) (y : Floating t) :
    approx x * approx y ⊆ approx (x.mul_fixed y) := by
  -- Handle special cases
  simp only [image2_mul, mul_fixed, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y = nan ∨ approx x = ∅
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,n2,nx⟩
  have xi : x.lo.val ≤ x.hi.val := by
    simpa only [approx, n0, n1, or_self, ite_false, nonempty_Icc] using nx
  simp only [n0, n1, n2, or_self, ite_false]
  -- Record Floating.mul bounds
  generalize ml0 : Floating.mul x.lo y false = l0
  generalize mh0 : Floating.mul x.hi y false = h0
  generalize ml1 : Floating.mul x.lo y true = l1
  generalize mh1 : Floating.mul x.hi y true = h1
  have il0 : l0 ≠ nan → l0.val ≤ x.lo.val * y.val := by rw [←ml0]; exact Floating.mul_le
  have ih0 : h0 ≠ nan → h0.val ≤ x.hi.val * y.val := by rw [←mh0]; exact Floating.mul_le
  have il1 : l1 ≠ nan → x.lo.val * y.val ≤ l1.val := by rw [←ml1]; exact Floating.le_mul
  have ih1 : h1 ≠ nan → x.hi.val * y.val ≤ h1.val := by rw [←mh1]; exact Floating.le_mul
  -- Split on signs
  by_cases ys : y.n.isNeg
  all_goals simp only [ys, n0, n1, n2, ite_true, ite_false, approx, false_or, subset_if_univ_iff,
    not_or, and_imp, ml0, mh0, ml1, mh1, mul_singleton]
  all_goals simp only [←Floating.val_lt_zero, ←Floating.val_nonneg, not_lt] at ys
  -- Handle each case
  · intro mh0 ml1
    have le : x.hi.val * y.val ≤ x.lo.val * y.val := by nlinarith
    simp only [image_mul_right_Icc_of_neg ys, Icc_subset_Icc_iff le]
    exact ⟨ih0 mh0, il1 ml1⟩
  · intro ml0 mh1
    have le : x.lo.val * y.val ≤ x.hi.val * y.val := by nlinarith
    simp only [image_mul_right_Icc xi ys, Icc_subset_Icc_iff le]
    exact ⟨il0 ml0, ih1 mh1⟩

/-- `approx_mul_fixed` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul_fixed {a b : Set ℝ} {x : Interval} {y : Floating t}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (mul_fixed x y) :=
  subset_trans (mul_subset_mul as bs) (approx_mul_fixed x y _)

/-- `approx_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul_fixed {a b : ℝ} {x : Interval} {y : Floating t}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (mul_fixed x y) :=
  subset_approx_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-!
### Interval squaring
-/

/-- Tighter than `mul x x` -/
@[pp_dot] def sqr (x : Interval) : Interval :=
  bif x == 0 then 0
  else bif x.lo == nan || x.hi == nan then nan
  else bif x.lo.n.isNeg != x.hi.n.isNeg then  -- x has mixed sign
    ⟨0, max (x.lo.mul x.lo true) (x.hi.mul x.hi true)⟩
  else bif x.lo.n.isNeg then ⟨x.hi.mul x.hi false, x.lo.mul x.lo true⟩
  else ⟨x.lo.mul x.lo false, x.hi.mul x.hi true⟩

/-- `sqr` respects `approx` -/
lemma approx_sqr (x : Interval) :
    (fun x ↦ x^2) '' approx x ⊆ approx x.sqr := by
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
  simp only [sqr, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases x0 : x = 0; · simp [x0]
  simp only [x0, or_self, ite_false]
  clear x0
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ approx x = ∅
  · rcases n with n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,nx⟩
  simp only [n0, n1, or_self, ite_false]
  -- Split on signs
  rcases sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals simp only [xls, xhs, n0, n1, bne_self_eq_false, Bool.false_and, if_false, not_or,
    Bool.xor_false, Bool.and_self, ite_true, Bool.and_false, ite_false, approx, false_or,
    Floating.max_eq_nan, subset_if_univ_iff, and_imp, mll0, mhh0, mll1, mhh1, sqr_Icc_subset_Icc]
  all_goals simp only [←Floating.val_lt_zero, ←Floating.val_nonneg] at xls xhs
  all_goals clear mll0 mhh0 mll1 mhh1 nx
  -- Dispatch everything with nlinarith
  · intro nhh0 nll1 u lu uh
    specialize ihh0 nhh0; specialize ill1 nll1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro nll0 nhh1 u lu uh
    specialize ill0 nll0; specialize ihh1 nhh1
    exact ⟨by nlinarith, by nlinarith⟩
  · intro _ nll1 nhh1 u lu uh
    specialize ill1 nll1; specialize ihh1 nhh1
    simp only [Floating.val_zero, Floating.val_max nll1 nhh1, le_max_iff]
    constructor
    · nlinarith
    · by_cases us : u < 0
      · left; nlinarith
      · right; nlinarith
