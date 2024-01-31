import Ray.Approx.Interval.Basic

open Classical
open Pointwise

/-!
## Interval arithmetic multiplication
-/

open Set
open scoped Real

/-- Multiply, changing `s` -/
@[pp_dot] def mul (x : Interval) (y : Interval) (u : Int64) : Interval u :=
  bif x.lo == nan || x.hi == nan || y.lo == nan || y.hi == nan then nan
  else bif x.lo.n.isNeg != x.hi.n.isNeg && y.lo.n.isNeg != x.hi.n.isNeg then  -- x,y have mixed sign
    ⟨min (x.lo.mul y.hi u false) (x.hi.mul y.lo u false),
     max (x.lo.mul y.lo u true) (x.hi.mul y.hi u true)⟩
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
    ⟨a.mul c u false, b.mul d u true⟩

/-- By default, multiplying intervals preserves `s` -/
instance : Mul Interval where
  mul (x y : Interval) := x.mul y s

set_option maxHeartbeats 10000000 in
/-- Rewrite `Icc * Icc ⊆ Icc` in terms of inequalities -/
lemma Icc_mul_Icc_subset_Icc {a b c d x y : ℝ} (ab : a ≤ b) (cd : c ≤ d) :
    Icc a b * Icc c d ⊆ Icc x y ↔
      x ≤ a * c ∧ x ≤ a * d ∧ x ≤ b * c ∧ x ≤ b * d ∧
      a * c ≤ y ∧ a * d ≤ y ∧ b * c ≤ y ∧ b * d ≤ y := by
  have am : a ∈ Icc a b := left_mem_Icc.mpr ab
  have bm : b ∈ Icc a b := right_mem_Icc.mpr ab
  have cm : c ∈ Icc c d := left_mem_Icc.mpr cd
  have dm : d ∈ Icc c d := right_mem_Icc.mpr cd
  simp only [←image2_mul, image2_subset_iff]
  constructor
  · intro h
    simp only [mem_Icc (a := x)] at h
    exact ⟨(h _ am _ cm).1, (h _ am _ dm).1, (h _ bm _ cm).1, (h _ bm _ dm).1,
           (h _ am _ cm).2, (h _ am _ dm).2, (h _ bm _ cm).2, (h _ bm _ dm).2⟩
  · simp only [mem_Icc]
    rintro ⟨xac,xad,xbc,xbd,acy,ady,bcy,bdy⟩ u ⟨au,ub⟩ v ⟨cv,vd⟩
    all_goals cases nonpos_or_nonneg c
    all_goals cases nonpos_or_nonneg d
    all_goals cases nonpos_or_nonneg u
    all_goals cases nonpos_or_nonneg v
    all_goals exact ⟨by nlinarith, by nlinarith⟩

set_option maxHeartbeats 10000000 in
/-- `mul` respects `approx` -/
lemma approx_mul (x : Interval) (y : Interval) (u : Int64) :
    approx x * approx y ⊆ approx (x.mul y u) := by
  -- Handle special cases
  simp only [image2_mul, mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan ∨ approx x = ∅ ∨ approx y = ∅
  · rcases n with n | n | n | n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,n2,n3,nx,ny⟩
  have xi : x.lo.val ≤ x.hi.val := by
    simpa only [approx, n0, n1, or_self, ite_false, nonempty_Icc] using nx
  have yi : y.lo.val ≤ y.hi.val := by
    simpa only [approx, n2, n3, or_self, ite_false, nonempty_Icc] using ny
  simp only [n0, n1, n2, n3, or_self, ite_false]
  -- Record Fixed.mul bounds
  generalize mll0 : Fixed.mul x.lo y.lo u false = ll0
  generalize mlh0 : Fixed.mul x.lo y.hi u false = lh0
  generalize mhl0 : Fixed.mul x.hi y.lo u false = hl0
  generalize mhh0 : Fixed.mul x.hi y.hi u false = hh0
  generalize mll1 : Fixed.mul x.lo y.lo u true = ll1
  generalize mlh1 : Fixed.mul x.lo y.hi u true = lh1
  generalize mhl1 : Fixed.mul x.hi y.lo u true = hl1
  generalize mhh1 : Fixed.mul x.hi y.hi u true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * y.lo.val := by rw [←mll0]; exact Fixed.mul_le
  have ilh0 : lh0 ≠ nan → lh0.val ≤ x.lo.val * y.hi.val := by rw [←mlh0]; exact Fixed.mul_le
  have ihl0 : hl0 ≠ nan → hl0.val ≤ x.hi.val * y.lo.val := by rw [←mhl0]; exact Fixed.mul_le
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * y.hi.val := by rw [←mhh0]; exact Fixed.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * y.lo.val ≤ ll1.val := by rw [←mll1]; exact Fixed.le_mul
  have ilh1 : lh1 ≠ nan → x.lo.val * y.hi.val ≤ lh1.val := by rw [←mlh1]; exact Fixed.le_mul
  have ihl1 : hl1 ≠ nan → x.hi.val * y.lo.val ≤ hl1.val := by rw [←mhl1]; exact Fixed.le_mul
  have ihh1 : hh1 ≠ nan → x.hi.val * y.hi.val ≤ hh1.val := by rw [←mhh1]; exact Fixed.le_mul
  -- Split on signs
  rcases sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals rcases sign_cases ny n3 with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
  all_goals simp only [xls, xhs, yls, yhs, n0, n1, n2, n3, bne_self_eq_false, Bool.false_and,
    if_false, Bool.xor_false, Bool.and_self, ite_true, Bool.and_false, ite_false, approx,
    Ici_inter_Iic, Fixed.min_eq_nan, false_or, Fixed.max_eq_nan, subset_if_univ_iff, not_or,
    and_imp, mll0, mlh0, mhl0, mhh0, mll1, mlh1, mhl1, mhh1, Icc_mul_Icc_subset_Icc xi yi,
    Fixed.val_min, min_le_iff]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg] at xls xhs yls yhs
  all_goals clear mll0 mlh0 mhl0 mhh0 mll1 mlh1 mhl1 mhh1 nx ny
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
    simp only [Fixed.val_max m2 m3, le_max_iff]
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
    simp only [Fixed.val_max m2 m3, le_max_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith
    · right; nlinarith
    · left; nlinarith
    · left; nlinarith
    · left; nlinarith
    · right; nlinarith

/-- `Interval` multiplication approximates `ℝ` -/
instance : ApproxMul Interval ℝ where
  approx_mul _ _ := approx_mul _ _ _

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing Interval ℝ where

/-- `approx_mul` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_mul {a b : Set ℝ} {x : Interval} {y : Interval} {u : Int64}
    (as : a ⊆ approx x) (bs : b ⊆ approx y) : a * b ⊆ approx (x.mul y u) :=
  subset_trans (mul_subset_mul as bs) (approx_mul x y _)

/-- `approx_mul` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul {a b : ℝ} {x : Interval} {y : Interval} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (x.mul y u) :=
  subset_approx_mul (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `mul` propagates `lo = nan` -/
@[simp] lemma mul_nan_lo {x : Interval} {y : Interval} {u : Int64} (yn : y.lo = nan) :
    x.mul y u = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` propagates `hi = nan` -/
@[simp] lemma mul_nan_hi {x : Interval} {y : Interval} {u : Int64} (yn : y.hi = nan) :
    x.mul y u = nan := by
  simp only [mul, yn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` propagates `lo = nan` -/
@[simp] lemma nan_mul_lo {x : Interval} {y : Interval} {u : Int64} (xn : x.lo = nan) :
    x.mul y u = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` propagates `hi = nan` -/
@[simp] lemma nan_mul_hi {x : Interval} {y : Interval} {u : Int64} (xn : x.hi = nan) :
    x.mul y u = nan := by
  simp only [mul, xn, beq_self_eq_true, Bool.or_true, Bool.true_or, Fixed.isNeg_nan, Bool.true_xor,
    Fixed.mul_nan, cond_true]

/-- `mul` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_mul {x : Interval} {y : Interval} {u : Int64}
    (n : (x.mul y u).lo ≠ nan) : x.lo ≠ nan ∧ x.hi ≠ nan ∧ y.lo ≠ nan ∧ y.hi ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n | n | n
  · rwa [nan_mul_lo, nan_def]
  · rwa [nan_mul_hi, nan_def]
  · rwa [mul_nan_lo, nan_def]
  · rwa [mul_nan_hi, nan_def]

/-!
### `Fixed * Fixed`, but conservative
-/

/-- Multiply two `Fixed`s, producing an `Interval -/
def fixed_mul_fixed (x : Fixed s) (y : Fixed t) (u : Int64) : Interval u :=
  ⟨x.mul y u false, x.mul y u true⟩

/-- `fixed_mul_fixed` respects `approx` -/
lemma approx_fixed_mul_fixed (x : Fixed s) (y : Fixed t) (u : Int64) :
    approx x * approx y ⊆ approx (fixed_mul_fixed x y u) := by
  intro a m
  simp only [mem_mul, exists_and_left] at m
  rcases m with ⟨b,bm,c,cm,bc⟩
  simp only [approx, mem_ite_univ_left, mem_singleton_iff, mem_Icc,
    fixed_mul_fixed] at bm cm ⊢
  by_cases n : x = nan ∨ y = nan ∨ Fixed.mul x y u false = nan ∨ Fixed.mul x y u true = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←Ne.def] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, not_false_eq_true, forall_true_left, n1] at bm cm
  simp only [n2, n3, or_self, not_false_eq_true, ← bc, bm, cm, forall_true_left]
  exact ⟨Fixed.mul_le n2, Fixed.le_mul n3⟩

/-- `approx_fixed_mul_fixed` in `mono` form, `⊆` version -/
@[mono] lemma subset_approx_fixed_mul_fixed {a b : Set ℝ} {x : Fixed s} {y : Fixed t}
    {u : Int64} (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (fixed_mul_fixed x y u) :=
  subset_trans (mul_subset_mul as bs) (approx_fixed_mul_fixed x y _)

/-- `approx_fixed_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_fixed_mul_fixed {a b : ℝ} {x : Fixed s} {y : Fixed t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (fixed_mul_fixed x y u) :=
  subset_approx_fixed_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-- `fixed_mul_fixed _ nan _ = nan` -/
@[simp] lemma fixed_mul_fixed_nan_right {x : Fixed s} {u : Int64} :
    fixed_mul_fixed x (nan : Fixed t) u = nan := by
  simp only [fixed_mul_fixed, Fixed.mul_nan, nan_def]

/-- `fixed_mul_fixed nan _ _ = nan` -/
@[simp] lemma fixed_mul_fixed_nan_left {x : Fixed t} {u : Int64} :
    fixed_mul_fixed (nan : Fixed s) x u = nan := by
  simp only [fixed_mul_fixed, Fixed.nan_mul, nan_def]

/-- `fixed_mul_fixed` arguments are `≠ nan` if the result is -/
lemma ne_nan_of_fixed_mul_fixed {x : Fixed s} {y : Fixed t} {u : Int64}
    (n : (fixed_mul_fixed x y u).lo ≠ nan) : x ≠ nan ∧ y ≠ nan := by
  contrapose n
  simp only [not_and_or, not_not] at n ⊢
  rcases n with n | n; repeat simp [n]

/-!
### `Interval * Fixed`
-/

/-- Multiply times a `Fixed`, changing `s` -/
@[pp_dot] def mul_fixed (x : Interval) (y : Fixed t) (u : Int64) : Interval u :=
  bif x.lo == nan || x.hi == nan || y == nan then nan else
  let (a,b) := bif y.n.isNeg then (x.hi, x.lo) else (x.lo, x.hi)
  ⟨a.mul y u false, b.mul y u true⟩

/-- Diagonal comparison to 0 -/
@[simp] lemma diagonal_eq_zero (x : Fixed s) : ((⟨x,x⟩ : Interval) = 0) ↔ x == 0 := by
  simp only [ext_iff, lo_zero, hi_zero, and_self, beq_iff_eq]

/-- `mul_fixed` respects `approx` -/
lemma approx_mul_fixed (x : Interval) (y : Fixed t) (u : Int64) :
    approx x * approx y ⊆ approx (x.mul_fixed y u) := by
  -- Handle special cases
  simp only [image2_mul, mul_fixed, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y = nan ∨ approx x = ∅
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,n2,nx⟩
  have xi : x.lo.val ≤ x.hi.val := by
    simpa only [approx, n0, n1, or_self, ite_false, nonempty_Icc] using nx
  simp only [n0, n1, n2, or_self, ite_false]
  -- Record Fixed.mul bounds
  generalize ml0 : Fixed.mul x.lo y u false = l0
  generalize mh0 : Fixed.mul x.hi y u false = h0
  generalize ml1 : Fixed.mul x.lo y u true = l1
  generalize mh1 : Fixed.mul x.hi y u true = h1
  have il0 : l0 ≠ nan → l0.val ≤ x.lo.val * y.val := by rw [←ml0]; exact Fixed.mul_le
  have ih0 : h0 ≠ nan → h0.val ≤ x.hi.val * y.val := by rw [←mh0]; exact Fixed.mul_le
  have il1 : l1 ≠ nan → x.lo.val * y.val ≤ l1.val := by rw [←ml1]; exact Fixed.le_mul
  have ih1 : h1 ≠ nan → x.hi.val * y.val ≤ h1.val := by rw [←mh1]; exact Fixed.le_mul
  -- Split on signs
  by_cases ys : y.n.isNeg
  all_goals simp only [ys, n0, n1, n2, ite_true, ite_false, approx, false_or, subset_if_univ_iff,
    not_or, and_imp, ml0, mh0, ml1, mh1, mul_singleton]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg, not_lt] at ys
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
@[mono] lemma subset_approx_mul_fixed {a b : Set ℝ} {x : Interval} {y : Fixed t}
    {u : Int64} (as : a ⊆ approx x) (bs : b ⊆ approx y) :
    a * b ⊆ approx (mul_fixed x y u) :=
  subset_trans (mul_subset_mul as bs) (approx_mul_fixed x y _)

/-- `approx_mul_fixed` in `mono` form, `∈` version -/
@[mono] lemma mem_approx_mul_fixed {a b : ℝ} {x : Interval} {y : Fixed t} {u : Int64}
    (am : a ∈ approx x) (bm : b ∈ approx y) : a * b ∈ approx (mul_fixed x y u) :=
  subset_approx_mul_fixed (singleton_subset_iff.mpr am) (singleton_subset_iff.mpr bm)
    (mul_mem_mul rfl rfl)

/-!
### Interval squaring
-/

/-- Tighter than `mul x x u` -/
@[pp_dot] def sqr (x : Interval) (u : Int64 := s) : Interval u :=
  bif x == 0 then 0
  else bif x.lo == nan || x.hi == nan then nan
  else bif x.lo.n.isNeg != x.hi.n.isNeg then  -- x has mixed sign
    ⟨0, max (x.lo.mul x.lo u true) (x.hi.mul x.hi u true)⟩
  else bif x.lo.n.isNeg then ⟨x.hi.mul x.hi u false, x.lo.mul x.lo u true⟩
  else ⟨x.lo.mul x.lo u false, x.hi.mul x.hi u true⟩

/-- Rewrite `Icc^2 ⊆ Icc` in terms of inequalities -/
lemma sqr_Icc_subset_Icc {a b x y : ℝ} :
    (fun x ↦ x^2) '' Icc a b ⊆ Icc x y ↔ ∀ u, a ≤ u → u ≤ b → x ≤ u^2 ∧ u^2 ≤ y := by
  simp only [subset_def, mem_image, mem_Icc, forall_exists_index, and_imp]
  constructor
  · intro h u au ub; exact h _ u au ub rfl
  · intro h u v av vb vu; rw [←vu]; exact h v av vb

/-- `sqr` respects `approx` -/
lemma approx_sqr (x : Interval) (u : Int64) :
    (fun x ↦ x^2) '' approx x ⊆ approx (x.sqr u) := by
  -- Record Fixed.mul bounds
  generalize mll0 : x.lo.mul x.lo u false = ll0
  generalize mll1 : x.lo.mul x.lo u true = ll1
  generalize mhh0 : x.hi.mul x.hi u false = hh0
  generalize mhh1 : x.hi.mul x.hi u true = hh1
  have ill0 : ll0 ≠ nan → ll0.val ≤ x.lo.val * x.lo.val := by rw [←mll0]; exact Fixed.mul_le
  have ill1 : ll1 ≠ nan → x.lo.val * x.lo.val ≤ ll1.val := by rw [←mll1]; exact Fixed.le_mul
  have ihh0 : hh0 ≠ nan → hh0.val ≤ x.hi.val * x.hi.val := by rw [←mhh0]; exact Fixed.mul_le
  have ihh1 : hh1 ≠ nan → x.hi.val * x.hi.val ≤ hh1.val := by rw [←mhh1]; exact Fixed.le_mul
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
    Fixed.max_eq_nan, subset_if_univ_iff, and_imp, mll0, mhh0, mll1, mhh1, sqr_Icc_subset_Icc]
  all_goals simp only [←Fixed.val_lt_zero, ←Fixed.val_nonneg] at xls xhs
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
    simp only [Fixed.val_zero, Fixed.val_max nll1 nhh1, le_max_iff]
    constructor
    · nlinarith
    · by_cases us : u < 0
      · left; nlinarith
      · right; nlinarith
