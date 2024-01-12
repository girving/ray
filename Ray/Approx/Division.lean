import Ray.Approx.Box
import Ray.Approx.Floating
import Ray.Approx.Interval

open Pointwise

/-!
## `Interval` and `Box` inv and division

Given `x : Interval s`, we want `1 / x` (division will follow immediately).  If `0 ∈ x`, then
`1 / x = nan`.  Otherwise, `x` is reliably positive or negative.

Given a smooth function `f : ℝ → ℝ` and its extension `f : Interval → Interval`.  At each step,
we can choose any `c ∈ approx x`.  Newton's method applied to intervals is

  `step f x c = c - f c / deriv f x`
  `newton f x c = x ∩ step f x c`

Does this work for `inv`, using `f x = 1/x - a`?  We have

  `deriv f x = -1 / x^2`
  `step f x c = c - f c / (-1 / x^2) = c + (1/c - a) / (1 / x^2)`
  `           = c + x^2/c - a x^2 = c + x^2 (1/c - a)`
  `           = c + x^2/c (1 - a c)`

Happily, we can cancel `x/c` to get `step f x c = c + x (1 - a c)`.  Let `c = 1/a + d`.  Then

  `step f x c = 1/a + d + x (1 - a (1/a + d)) = 1/a + d (1 - a x)`

If `1/a ∈ x`, the two endpoints of `x` will produce opposite sign for `1 - a x`, which regardless of
the sign of `d` will produce opposite signs for `d (1 - a x)`, and will bracket `1/a`.
-/

open Set
open scoped Real

variable {s t : Int64}

/-!
## `Interval` reciprocal
-/

/-- Approximate the reciprocal of a number in `[1/2,1)` using 64-bit integer division -/
def inv_guess (x : Fixed s) {t : Int64} : Fixed t :=
  -- Our guess is `y = 2^63 / (x.n.n / 2^a) * 2^b`, and we want
  --   `y * 2^t = 1 / (x.n.n * 2^s)`
  --   `2^63 / (x.n.n / 2^a) * 2^b * 2^t = 1 / (x.n.n * 2^s)`
  --   `2^63 * 2^a * 2^b * 2^t = 2^-s`
  --   `a + b ~ -s - t - 63`
  -- `a` and `b` both correspond to lost precision, so we'll balance them.
  let n := -63 - s - t
  bif n.isNeg then nan else
  let b := n.n / 2
  ⟨⟨(((1 : UInt64) <<< 63) / (x.n.n >>> (n.n - b))) <<< b⟩⟩

/-- Conservative region that includes `x⁻¹` -/
@[irreducible] def inv_region (x : Fixed s) : Interval t :=
  let n := x.log2
  ⟨.two_pow (-1-n) false, .two_pow (-n) true⟩

/-- One step of Newton's method for the reciprocal.
    We trust that `1/x ∈ r`, but do not trust the guess `c`. -/
@[irreducible] def inv_step (x : Fixed s) (r : Interval t) (c : Fixed t) : Interval t :=
  -- `r ∩ (c + r (1 - x c))`, where `x ∈ [1/2,1]`, `r,c ∈ [1,2]`
  r ∩ (c + r.mul (1 - Interval.fixed_mul_fixed x c t) t)

/-- Floating point interval reciprocal using Newton's method.
    We assume `x⁻¹ ∈ approx r`. -/
@[irreducible, pp_dot] def Fixed.inv_pos (x : Fixed s) : Interval t :=
  -- Three steps of Newton's method to produce a tight, conservative interval.
  -- Probably two is enough, but I'm lazy.
  let r1 := inv_step x (inv_region x) (inv_guess x)
  let r2 := inv_step x r1 r1.lo
  inv_step x r2 r2.lo

/-- `Interval` reciprocal of a positive interval -/
@[irreducible, pp_dot] def Interval.inv_pos (x : Interval s) : FloatingInterval :=
  -- If `2^n ≤ x.lo < 2^(n+1)`, then `2^(-n-1) < y = x.lo⁻¹ ≤ 2^-n`
  -- A good output precision is `-62 - n` so that
  --   `y.n = y / 2^(-62 - n) ≤ 2^-n / 2^(-62 - n) = 2^62`.
  let k := -62 - x.lo.log2
  bif k == nan then nan else
  ⟨k.n, x.hi.inv_pos ∪ x.lo.inv_pos⟩

/-- `Interval` reciprocal using Newton's method. -/
@[irreducible, pp_dot] def Interval.inv (x : Interval s) : FloatingInterval :=
  bif x.lo == 0 || x.hi == 0 || x.lo == nan || x.hi == nan || x.lo.n.isNeg != x.hi.n.isNeg then
    nan else
  let r := |x|.inv_pos
  bif x.lo.n.isNeg then -r else r

/-- The exact precision reason why `inv_step` is conservative -/
lemma approx_inv_step_reason {x c rl rh ml mh : ℝ} (x0 : 0 < x) (xr : rl ≤ x⁻¹ ∧ x⁻¹ ≤ rh)
    (mm : (fun z ↦ z * (1 - x * c)) '' Icc rl rh ⊆ Icc ml mh)
    : c + ml ≤ x⁻¹ ∧ x⁻¹ ≤ c + mh := by
  generalize he : 1/x - c = e
  replace he : c = 1/x - e := by linarith
  simp only [he, one_div, mul_sub, mul_inv_cancel x0.ne', sub_sub_cancel, add_comm_sub,
    add_le_iff_nonpos_right, tsub_le_iff_right, zero_add, le_add_iff_nonneg_right,
    sub_nonneg] at mm ⊢
  by_cases e0 : 0 ≤ e
  · have xe : 0 ≤ x * e := mul_nonneg x0.le e0
    simp only [image_mul_right_Icc (le_trans xr.1 xr.2) xe] at mm
    rw [Set.Icc_subset_Icc_iff (by nlinarith)] at mm
    constructor
    · refine le_trans mm.1 (le_trans (mul_le_mul_of_nonneg_right xr.1 xe) ?_)
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]
    · refine le_trans (le_trans ?_ (mul_le_mul_of_nonneg_right xr.2 xe)) mm.2
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]
  · simp only [not_le] at e0
    have xe : x * e < 0 := mul_neg_of_pos_of_neg x0 e0
    simp only [image_mul_right_Icc_of_neg xe] at mm
    rw [Set.Icc_subset_Icc_iff (by nlinarith)] at mm
    constructor
    · refine le_trans mm.1 (le_trans (mul_le_mul_of_nonpos_right xr.2 xe.le) ?_)
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]
    · refine le_trans (le_trans ?_ (mul_le_mul_of_nonpos_right xr.1 xe.le)) mm.2
      simp only [← mul_assoc, inv_mul_cancel x0.ne', one_mul, le_refl]

/-- `inv_step` is conservative -/
@[mono] lemma approx_inv_step {x : Fixed s} {r : Interval t} (c : Fixed t) (x0 : 0 < x.val)
    (xr : (approx x)⁻¹ ⊆ approx r) : (approx x)⁻¹ ⊆ approx (inv_step x r c) := by
  -- Preliminiaries
  rw [inv_step]
  apply Interval.subset_approx_inter xr
  intro a ax
  simp only [approx, Interval.add_def, Interval.lo_fixed, Interval.hi_fixed, mem_ite_univ_left,
    mem_Icc]
  -- Assemble `≠ nan` hypotheses
  intro n
  simp only [not_or] at n
  rcases Fixed.ne_nan_of_add n.1 with ⟨cn, raln⟩
  have rahn := (Fixed.ne_nan_of_add n.2).2
  rcases Interval.ne_nan_of_mul raln with ⟨rln,rhn,sln,shn⟩
  simp only [Fixed.val_add n.1, Fixed.val_add n.2]
  have xn := (Interval.ne_nan_of_fixed_mul_fixed (Fixed.ne_nan_of_sub shn).2).1
  clear sln shn n
  -- Reduce to a statement over `ℝ`
  simp only [approx, xn, ite_false, inv_singleton, mem_singleton_iff, rln, rhn, or_self,
    singleton_subset_iff, mem_Icc] at ax xr
  simp only [ax]; clear ax a
  have mm : approx r * ({1} - approx x * approx c) ⊆
      approx (r.mul (1 - Interval.fixed_mul_fixed x c t) t) := by mono
  generalize hmul : r.mul (1 - Interval.fixed_mul_fixed x c t) t = mul at raln rahn
  simp only [approx, rln, rhn, or_self, ite_false, mul_singleton, hmul, raln, rahn, xn, cn,
    image_singleton, sub_singleton] at mm
  clear cn rln rhn raln rahn hmul xn
  exact approx_inv_step_reason x0 xr mm

/-- `inv_step` propagates `r = nan` -/
@[simp] lemma inv_step_nan {x : Fixed s} {c : Fixed t} : inv_step x nan c = nan := by
  rw [inv_step]
  simp only [Interval.nan_mul_lo, Interval.add_def, Interval.lo_fixed, Fixed.add_nan,
    Interval.hi_fixed, Interval.inter_def, Interval.mk.injEq, Fixed.max_eq_nan, or_self,
    Fixed.min_eq_nan, and_self, Interval.lo_nan, Interval.hi_nan, Interval.nan_def]

/-- `inv_region` is conservative -/
@[mono] lemma approx_inv_region {x : Fixed s} :
    (approx x)⁻¹ ⊆ approx (inv_region x : Interval t) := by
  rw [inv_region]
  by_cases x0 : x.val ≤ 0
  · simp only [x0, Fixed.log2_eq_nan_of_nonpos, Fixed.sub_nan, Fixed.two_pow_nan, Fixed.neg_nan,
      Interval.approx_of_lo_nan, subset_univ]
  simp only [not_le] at x0
  by_cases xn : x = nan
  · simp [xn]
  · simp only [Fixed.approx_eq_singleton xn, inv_singleton, singleton_subset_iff]
    simp only [approx, mem_ite_univ_left, not_or, mem_Icc, and_imp]
    intro n0 n1
    have nn := Fixed.ne_nan_of_two_pow n1
    have ns := Fixed.ne_nan_of_two_pow n0
    have nl := Fixed.ne_nan_of_neg nn
    have m := Fixed.val_mem_log2 nl
    simp only [mem_Ico] at m
    constructor
    · refine le_trans (Fixed.two_pow_le n0) ?_
      rw [le_inv two_zpow_pos x0, ←zpow_neg]
      have v1 : ((-1 : Fixed 0).n : ℤ) = -1 := by native_decide
      have v := Fixed.val_sub ns
      simp only [Fixed.val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_sub, Int.cast_inj,
        v1] at v
      simp only [v, neg_sub, sub_neg_eq_add, m.2.le]
    · refine le_trans ?_ (Fixed.le_two_pow n1)
      rw [inv_le x0 two_zpow_pos, ←zpow_neg]
      have v := Fixed.val_neg nl
      simp only [Fixed.val, Int64.coe_zero, zpow_zero, mul_one, ←Int.cast_neg, Int.cast_inj] at v
      simp only [v, neg_neg, m.1]

/-- `inv_region` propagates `nan` -/
@[simp] lemma inv_region_nan : (inv_region (nan : Fixed s) : Interval t) = nan := by
  rw [inv_region]
  simp only [Fixed.log2_nan, Fixed.sub_nan, Fixed.two_pow_nan, Fixed.neg_nan, Interval.nan_def]

/-- `Fixed.inv_pos` is conservative -/
lemma Fixed.approx_inv_pos {x : Fixed s} (x0 : 0 < x.val) :
    (approx x)⁻¹ ⊆ approx (x.inv_pos : Interval t) := by
  rw [Fixed.inv_pos]; mono

/-- `inv_pos` propagates `nan` -/
@[simp] lemma Fixed.imv_pos_nan : ((nan : Fixed s).inv_pos : Interval t) = nan := by
  rw [Fixed.inv_pos]; simp only [inv_region_nan, inv_step_nan]

/-- `Fixed.inv_pos'` is conservative -/
@[mono] lemma Fixed.approx_inv_pos' {x : Fixed s} (p : 0 < x.val) :
    x.val⁻¹ ∈ approx (x.inv_pos : Interval t) :=
  Fixed.approx_inv_pos p (by mono)

/-- `Interval.inv_pos` is conservative -/
@[mono] lemma Interval.approx_inv_pos {x : Interval s} (p : 0 < x.lo.val) :
    (approx x)⁻¹ ⊆ approx x.inv_pos := by
  rw [inv_pos]
  simp only [bif_eq_if, beq_iff_eq]
  generalize -62 - x.lo.log2 = k
  by_cases n : k = nan ∨ x.lo = nan ∨ x.hi = nan ∨ approx x = ∅
  · rcases n with n | n | n | n
    repeat simp [n, apply_ite (fun x : FloatingInterval ↦ univ ⊆ approx x)]
  simp only [not_or, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨kn,ln,hn,ax⟩
  simp only [kn, ite_false, FloatingInterval.approx_def]
  have p' := lt_of_lt_of_le p (Interval.le_of_nonempty ax hn)
  have ie : (approx x)⁻¹ = Icc x.hi.val⁻¹ x.lo.val⁻¹ := by
    simp only [approx, ln, hn, or_self, ite_false, inv_Icc p p']
  simp only [ln, hn, or_self, ite_false, ie]
  apply Icc_subset_approx
  · exact Interval.approx_union_left (Fixed.approx_inv_pos' p')
  · exact Interval.approx_union_right (Fixed.approx_inv_pos' p)

/-- `Interval.inv` is conservative -/
@[mono] lemma Interval.approx_inv {x : Interval s} : (approx x)⁻¹ ⊆ approx x.inv := by
  rw [inv]
  simp only [bif_eq_if, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  by_cases n : x.lo = 0 ∨ x.hi = 0 ∨ x.lo = nan ∨ x.hi = nan ∨ approx x = ∅ ∨
      x.lo.n.isNeg ≠ x.hi.n.isNeg
  · rcases n with n | n | n | n | n | n; repeat simp [n]
  simp only [not_or, not_not, ←nonempty_iff_ne_empty] at n
  rcases n with ⟨n0,n1,ln,hn,an,se⟩
  simp only [n0, n1, or_self, se, not_true_eq_false, ite_false]
  simp only [Fixed.isNeg_eq, decide_eq_decide, decide_eq_true_eq, ln, hn, or_false,
    if_false] at se ⊢
  have a0 : 0 < |x|.lo.val := Interval.abs_pos ln hn n0 n1 se
  by_cases l0 : x.lo.val < 0
  · rw [se] at l0
    replace ax : approx x = -approx |x| := by simp only [Interval.abs_of_nonpos l0.le an, neg_neg]
    simp only [ax, Set.inv_neg, l0, ite_true]
    mono
  · replace ax : approx x = approx |x| := by simp only [Interval.abs_of_nonneg (not_lt.mp l0) an]
    simp only [ax, ite_false, ←se, l0]
    mono

/-- `Interval.inv` is conservative, `mono ⊆` version -/
@[mono] lemma Interval.subset_approx_inv {p : Set ℝ} {x : Interval s}
    (px : p ⊆ approx x) : p⁻¹ ⊆ approx x.inv :=
  subset_trans (inv_subset_inv.mpr px) Interval.approx_inv

/-- `Interval.inv` is conservative, `mono ∈` version -/
@[mono] lemma Interval.mem_approx_inv {p : ℝ} {x : Interval s}
    (px : p ∈ approx x) : p⁻¹ ∈ approx x.inv :=
  Interval.approx_inv (inv_mem_inv.mpr px)

/-!
## `Interval` and `Box` division
-/

/-- `Interval` division via reciproval multiplication -/
@[irreducible] def Interval.div (x : Interval s) (y : Interval t) (u : Int64) : Interval u :=
  y.inv.x.mul x u

/-- `Box / Interval` via reciproval multiplication -/
@[irreducible] def Box.div_scalar (z : Box s) (x : Interval t) (u : Int64) : Box u :=
  x.inv.x.mul_box z u

/-- `Interval.div` is conservative -/
@[mono] lemma Interval.approx_div {x : Interval s} {y : Interval t} {u : Int64} :
    approx x / approx y ⊆ approx (x.div y u) := by
  rw [Interval.div, div_eq_inv_mul]; mono

/-- `Box / Interval` is conservative -/
@[mono] lemma Box.approx_div_scalar {z : Box s} {x : Interval t} {u : Int64} :
    approx z / Complex.ofReal '' approx x ⊆ approx (z.div_scalar x u) := by
  rw [Box.div_scalar, div_eq_inv_mul]
  refine subset_trans (mul_subset_mul ?_ subset_rfl) (Interval.approx_mul_box _ _ _)
  intro a
  simp only [Complex.ofReal_eq_coe, mem_inv, mem_image, forall_exists_index, and_imp]
  intro b m e
  use b⁻¹
  constructor
  · simp only [FloatingInterval.approx_x]; mono
  · rw [Complex.ofReal_inv, e, inv_inv]

/-!
### Unit tests
-/

/-- We're don't verify anything about `inv_guess`, but we do need some tests -/
def guess_test (x : Float) (s t : Int64) (e : Float := 1e-9) : Bool :=
  ((inv_guess (.ofFloat x : Fixed s) : Fixed t).toFloat - 1 / x).abs < e
lemma guess_test1 : guess_test 0.5 (-63) (-61) := by native_decide
lemma guess_test2 : guess_test 0.67862 (-63) (-61) := by native_decide
lemma guess_test3 : guess_test 0.999 (-63) (-61) := by native_decide
lemma guess_test4 : guess_test 0.67862 (-60) (-57) := by native_decide
lemma guess_test5 : guess_test 1e-4 (-76) (-49) := by native_decide

/-- `Interval.inv` is provably conservative, but we need to test that it's accurate -/
def inv_test (l h : Float) (s : Int64) (e : Float := 1e-15) : Bool :=
  let x : Interval s := ⟨.ofFloat l, .ofFloat h⟩
  let r := x.inv
  (r.x.lo.toFloat * h - 1).abs < e && (r.x.hi.toFloat * l - 1).abs < e
lemma inv_test1p : inv_test 0.4 0.6 (-60) := by native_decide
lemma inv_test2p : inv_test 0.4871231 17.87341 (-52) := by native_decide
lemma inv_test3p : inv_test 0.001871 17.87341 (-52) (1e-13) := by native_decide
lemma inv_test1n : inv_test (-0.6) (-0.4) (-60) := by native_decide
lemma inv_test2n : inv_test (-17.87341) (-0.4871231) (-52) := by native_decide
lemma inv_test3n : inv_test (-17.87341) (-0.001871) (-52) (1e-13) := by native_decide
