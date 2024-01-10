import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Data.Set.Pointwise.Interval
import Ray.Approx.Fixed

open Classical
open Pointwise

/-!
## 64-bit fixed point interval arithmetic
-/

open Set
open scoped Real

variable {s t : Int64}

/-- 64-bit fixed point intervals -/
structure Interval (s : Int64) where
  lo : Fixed s
  hi : Fixed s
  deriving DecidableEq, BEq

/-- `Interval` has nice equality -/
instance : LawfulBEq (Interval s) where
  eq_of_beq {x y} e := by
    induction' x with xlo xhi; induction' y with ylo yhi
    have g : ((xlo == ylo && xhi == yhi) = true) := e
    simp only [Bool.and_eq_true, beq_iff_eq] at g
    simp only [g.1, g.2]
  rfl {x} := by
    have e : (x == x) = (x.lo == x.lo && x.hi == x.hi) := rfl
    simp only [e, beq_self_eq_true, Bool.and_self]

/-- `Interval` approximates `ℝ` -/
instance : Approx (Interval s) ℝ where
  approx x := if x.lo = nan ∨ x.hi = nan then univ else Icc x.lo.val x.hi.val

/-- Interval zero -/
instance : Zero (Interval s) where
  zero := ⟨0,0⟩

/-- Interval negation -/
instance : Neg (Interval s) where
  neg x := ⟨-x.hi, -x.lo⟩

/-- Interval addition -/
instance : Add (Interval s) where
  add x y := ⟨x.lo + y.lo, x.hi + y.hi⟩

/-- Interval subtraction -/
instance : Sub (Interval s) where
  sub x y := ⟨x.lo - y.hi, x.hi - y.lo⟩

/-- Interval intersection -/
instance : Inter (Interval s) where
  inter x y := ⟨max x.lo y.lo, min x.hi y.hi⟩

-- Bounds properties of interval arithmetic
lemma Interval.add_def {x y : Interval s} : x + y = ⟨x.lo + y.lo, x.hi + y.hi⟩ := rfl
lemma Interval.sub_def {x y : Interval s} : x - y = ⟨x.lo - y.hi, x.hi - y.lo⟩ := rfl
@[simp] lemma Interval.lo_neg {x : Interval s} : (-x).lo = -x.hi := rfl
@[simp] lemma Interval.hi_neg {x : Interval s} : (-x).hi = -x.lo := rfl
@[simp] lemma Interval.lo_zero : (0 : Interval s).lo = 0 := rfl
@[simp] lemma Interval.hi_zero : (0 : Interval s).hi = 0 := rfl
@[simp] lemma Interval.approx_zero : approx (0 : Interval s) = {0} := by
  simp only [approx, lo_zero, Fixed.val_zero, ite_false, hi_zero, Ici_inter_Iic, Icc_self,
    Fixed.zero_ne_nan, false_or]
@[simp] lemma Interval.approx_nan : approx ({lo := nan, hi := nan} : Interval s) = univ := by
  simp only [approx, ite_true, inter_self, true_or]

/-- `x - y = x + (-y)` -/
lemma Interval.sub_eq_add_neg (x y : Interval s) : x - y = x + (-y) := by
  simp only [sub_def, Fixed.sub_eq_add_neg, add_def, lo_neg, hi_neg]

/-- `Interval.neg` respects `approx` -/
instance : ApproxNeg (Interval s) ℝ where
  approx_neg x := by
    by_cases n : x.lo = nan ∨ x.hi = nan
    · rcases n with n | n; repeat simp [n, approx]
    simp only [not_or] at n
    simp only [approx, Interval.lo_neg, Interval.hi_neg, Set.inter_neg, n.1, n.2, false_or,
      if_false, Fixed.neg_eq_nan, preimage_neg_Icc, Fixed.val_neg n.1, Fixed.val_neg n.2,
      subset_refl]

/-- `Interval.add` respects `approx` -/
instance : ApproxAdd (Interval s) ℝ where
  approx_add x y := by
    simp only [approx]
    by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan
    · rcases n with n | n | n | n; repeat simp [n, Set.univ_add, Interval.add_def]
    simp only [not_or] at n
    rcases n with ⟨n0,n1,n2,n3⟩
    simp only [n0, n1, or_self, ite_false, n2, n3, Interval.add_def]
    split_ifs with h
    · rcases h with h | h; repeat simp only [h, subset_univ]
    simp only [not_or] at h
    simp only [Fixed.val_add_of_ne_nan h.1, Fixed.val_add_of_ne_nan h.2]
    apply Set.Icc_add_Icc_subset

/-- `Interval.sub` respects `approx` -/
instance : ApproxSub (Interval s) ℝ where
  approx_sub x y := by
    simp only [Interval.sub_eq_add_neg, sub_eq_add_neg]
    refine subset_trans ?_ (approx_add x (-y))
    refine subset_trans ?_ (image2_subset_left (approx_neg _))
    simp only [←Set.image2_sub, ←Set.image_neg, image2_image_right, ←image2_add, image2_image_right,
      ←sub_eq_add_neg, subset_refl]

/-- `Interval` approximates `ℝ` as an additive group -/
instance : ApproxAddGroup (Interval s) ℝ where

/-- `Interval.inter` respects `approx` -/
lemma Interval.approx_inter {x y : Interval s} : approx x ∩ approx y ⊆ approx (x ∩ y) := by
  intro a ⟨ax,ay⟩
  simp only [approx, mem_ite_univ_left, mem_Icc, Inter.inter, Fixed.max_eq_nan, Fixed.min_eq_nan,
    Fixed.val_min, le_min_iff] at ax ay ⊢
  by_cases n : x.lo = nan ∨ x.hi = nan ∨ y.lo = nan ∨ y.hi = nan
  · rcases n with n | n | n | n; repeat simp [n]
  simp only [not_or] at n
  rcases n with ⟨n0,n1,n2,n3⟩
  simp only [n0, n1, or_self, not_false_eq_true, forall_true_left, n2, n3, Fixed.val_max n0 n2,
    max_le_iff] at ax ay ⊢
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  repeat linarith

/-!
### Interval multiplication
-/

/-- Multiply, changing `s` -/
def Interval.mul (x : Interval s) (y : Interval t) (u : Int64) : Interval u :=
  bif x == 0 || y == 0 then 0
  else bif x.lo == nan || x.hi == nan || y.lo == nan || y.hi == nan then ⟨nan,nan⟩
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
instance : Mul (Interval s) where
  mul (x y : Interval s) := x.mul y s

/-- Either `approx = ∅` or `x.lo ≤ x.hi` (if we're not nan) -/
lemma Interval.sign_cases {x : Interval s} (a : (approx x).Nonempty) (hn : x.hi ≠ nan) :
    (x.lo.n.isNeg ∧ x.hi.n.isNeg) ∨ (x.lo.n.isNeg = false ∧ x.hi.n.isNeg = false) ∨
    (x.lo.n.isNeg ∧ x.hi.n.isNeg = false) := by
  by_cases ln : x.lo = nan
  · simp only [ln, Fixed.isNeg_nan, true_and, false_and, false_or, Bool.eq_false_or_eq_true]
  · rcases a with ⟨a,h⟩
    simp only [approx, ln, ite_false, hn, mem_inter_iff, mem_Ici, mem_Iic] at h
    replace h := le_trans h.1 h.2
    simp only [Fixed.val, mul_le_mul_right (zpow_pos_of_pos (by norm_num : 0 < (2 : ℝ)) _),
      Int.cast_le, Int64.coe_le_coe] at h
    simp only [Int64.isNeg_eq, decide_eq_true_eq, decide_eq_false_iff_not, not_lt]
    by_cases ls : x.lo.n < 0
    all_goals by_cases hs : x.hi.n < 0
    all_goals simp_all
    have h := lt_of_le_of_lt (le_trans ls h) hs
    simp only [lt_self_iff_false] at h

/-- Simplify to case assuming not `nan` -/
lemma subset_if_univ_iff {t u : Set ℝ} {p : Prop} {dp : Decidable p} :
    t ⊆ @ite _ p dp univ u ↔ ¬p → t ⊆ u := by
  by_cases n : p
  repeat simp only [n, ite_true, ite_false, subset_univ, not_true_eq_false, IsEmpty.forall_iff,
    not_false_eq_true, forall_true_left]

/-- Reals are either `≤ 0` or `≥ 0` -/
lemma nonpos_or_nonneg (x : ℝ) : x ≤ 0 ∨ 0 ≤ x := by
  by_cases p : 0 ≤ x
  · right; assumption
  · left; linarith

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
/-- `Interval.mul` respects `approx` -/
lemma Interval.approx_mul (x : Interval s) (y : Interval t) (u : Int64) :
    approx x * approx y ⊆ approx (x.mul y u) := by
  -- Handle special cases
  simp only [image2_mul, mul, bif_eq_if, Bool.or_eq_true, beq_iff_eq]
  by_cases x0 : x = 0; · simp [x0]
  by_cases y0 : y = 0; · simp [y0]
  simp only [x0, y0, or_self, ite_false]
  clear x0 y0
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
  rcases Interval.sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
  all_goals rcases Interval.sign_cases ny n3 with ⟨yls,yhs⟩ | ⟨yls,yhs⟩ | ⟨yls,yhs⟩
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
instance : ApproxMul (Interval s) ℝ where
  approx_mul _ _ := Interval.approx_mul _ _ _

/-- `Interval` approximates `ℝ` as a ring -/
instance : ApproxRing (Interval s) ℝ where

/-!
### Interval squaring
-/

/-- Tighter than `Interval.mul x x u` -/
def Interval.sqr (x : Interval s) (u : Int64 := s) : Interval u :=
  bif x == 0 then 0
  else bif x.lo == nan || x.hi == nan then ⟨nan,nan⟩
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

/-- `Interval.sqr` respects `approx` -/
lemma Interval.approx_sqr (x : Interval s) (u : Int64) :
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
  rcases Interval.sign_cases nx n1 with ⟨xls,xhs⟩ | ⟨xls,xhs⟩ | ⟨xls,xhs⟩
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
