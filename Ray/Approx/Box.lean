import Mathlib.Data.Complex.Basic
import Ray.Approx.Interval.Basic
import Ray.Approx.Interval.Conversion
import Ray.Approx.Interval.Mul
import Ray.Approx.Interval.Scale

open Classical
open Pointwise

/-!
## Complex interval arithmic (on top of 64-bit fixed point intervals)
-/

open Set
open scoped Real ComplexConjugate

/-- Rectangular boxes of complex numbers -/
@[unbox] structure Box where
  re : Interval
  im : Interval
  deriving DecidableEq, BEq

namespace Box

/-- `Box` has nice equality -/
instance : LawfulBEq Box where
  eq_of_beq {x y} e := by
    induction' x with xlo xhi; induction' y with ylo yhi
    have g : ((xlo == ylo && xhi == yhi) = true) := e
    simp only [Bool.and_eq_true, beq_iff_eq] at g
    simp only [g.1, g.2]
  rfl {x} := by
    have e : (x == x) = (x.re == x.re && x.im == x.im) := rfl
    simp only [e, beq_self_eq_true, Bool.and_self]

/-- Reduce `Box s` equality to `Interval` equality -/
lemma ext_iff (z w : Box) : z = w ↔ z.re = w.re ∧ z.im = w.im := by
  induction z; induction w; simp only [mk.injEq]

instance : Repr Box where
  reprPrec z _ := "(" ++ repr z.re ++ " + " ++ repr z.im ++ "i⟩"

/-- Simplification of `∈ image2` for `Box` -/
@[simp] lemma mem_image2_iff {z : ℂ} {s t : Set ℝ} :
    z ∈ image2 (fun r i ↦ (⟨r,i⟩ : ℂ)) s t ↔ z.re ∈ s ∧ z.im ∈ t := by
  simp only [image2, Complex.ext_iff, exists_and_left, exists_eq_right_right, mem_setOf_eq]

/-- `Box` approximates `ℂ` -/
instance instApprox : Approx Box ℂ where
  approx z := image2 (fun r i ↦ ⟨r,i⟩) (approx z.re) (approx z.im)

/-- `Box` zero -/
instance : Zero Box where
  zero := ⟨0,0⟩

/-- `Box` negation -/
instance : Neg Box where
  neg x := ⟨-x.re, -x.im⟩

/-- `Box` addition -/
instance : Add Box where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

/-- `Box` subtraction -/
instance : Sub Box where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

/-- Complex conjugation -/
instance : Star Box where
  star x := ⟨x.re, -x.im⟩

/-- `Box` multiplication -/
instance : Mul Box where
  mul z w := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- `Interval * Box` -/
def _root_.Interval.mul_box (x : Interval) (z : Box) : Box :=
  ⟨x * z.re, x * z.im⟩

/-- `Box` squaring (tighter than `z * z`) -/
def sqr (z : Box) : Box :=
  let w := z.re * z.im
  ⟨z.re.sqr - z.im.sqr, w.scaleB 1⟩

-- Definition lemmas
lemma neg_def {z : Box} : -z = ⟨-z.re, -z.im⟩ := rfl
lemma add_def {z w : Box} : z + w = ⟨z.re + w.re, z.im + w.im⟩ := rfl
lemma sub_def {z w : Box} : z - w = ⟨z.re - w.re, z.im - w.im⟩ := rfl
lemma mul_def {z w : Box} : z * w = ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩ := rfl
@[simp] lemma re_conj {z : Box} : (star z).re = z.re := rfl
@[simp] lemma im_conj {z : Box} : (star z).im = -z.im := rfl

-- Bounds properties of `Box` arithmetic
@[simp] lemma re_zero : (0 : Box).re = 0 := rfl
@[simp] lemma im_zero : (0 : Box).im = 0 := rfl
@[simp] lemma approx_zero : approx (0 : Box) = {0} := by
  simp only [instApprox, re_zero, Interval.approx_zero, im_zero, image2_singleton_right,
    image_singleton, singleton_eq_singleton_iff, Complex.ext_iff, Complex.zero_re, Complex.zero_im,
    and_self]

/-- Prove `re ∈` via full `∈` -/
@[mono] lemma mem_approx_re {z : ℂ} {w : Box} (zw : z ∈ approx w) : z.re ∈ approx w.re := by
  simp only [approx, mem_image2_iff] at zw; exact zw.1

/-- Prove `im ∈` via full `∈` -/
@[mono] lemma mem_approx_im {z : ℂ} {w : Box} (zw : z ∈ approx w) : z.im ∈ approx w.im := by
  simp only [approx, mem_image2_iff] at zw; exact zw.2

/-- `star` is conservative -/
instance : ApproxStar Box ℂ where
  approx_star z := by
    simp only [IsROrC.star_def, instApprox, image_image2, re_conj, im_conj, Interval.approx_neg,
      image2_subset_iff, mem_image2, mem_neg]
    intro r rz i iz
    exact ⟨r, rz, -i, by simpa only [neg_neg], rfl⟩

/-- `Box.neg` respects `approx` -/
instance : ApproxNeg Box ℂ where
  approx_neg z := by
    simp only [Box.instApprox, ← image_neg, image_image2, image2_subset_iff, mem_image2,
      exists_and_left]
    intro r rz i iz
    refine ⟨-r, ?_, -i, ?_, rfl⟩
    repeat { apply approx_neg; simpa only [mem_neg, neg_neg] }

/-- `Box.add` respects `approx` -/
instance : ApproxAdd Box ℂ where
  approx_add z w := by
    simp only [Box.instApprox, add_subset_iff, Box.mem_image2_iff, and_imp, Complex.add_re,
      Complex.add_im, Box.add_def]
    intro a ar ai b br bi
    exact ⟨approx_add _ _ (add_mem_add ar br), approx_add _ _ (add_mem_add ai bi)⟩

/-- `Box.sub` respects `approx` -/
instance : ApproxSub Box ℂ where
  approx_sub x y := by
    simp only [Box.instApprox, sub_subset_iff, Box.mem_image2_iff, and_imp, Complex.sub_re,
      Complex.sub_im, Box.sub_def]
    intro a ar ai b br bi
    exact ⟨approx_sub _ _ (sub_mem_sub ar br), approx_sub _ _ (sub_mem_sub ai bi)⟩

/-- `Box` approximates `ℂ` as an additive group -/
noncomputable instance : ApproxAddGroup Box ℂ where

/-- `Box` multiplication approximates `ℂ` -/
instance : ApproxMul Box ℂ where
  approx_mul z w := by
    simp only [Box.instApprox, mul_subset_iff, Box.mem_image2_iff, and_imp, Complex.mul_re,
      Complex.mul_im, Box.mul_def]
    intro a ar ai b br bi
    exact ⟨by mono, by mono⟩

/-- `Interval * Box` multiplication approximates `ℂ` -/
@[mono] lemma _root_.Interval.approx_mul_box (x : Interval) (z : Box) :
    (Complex.ofReal '' approx x) * approx z ⊆ approx (x.mul_box z) := by
  simp only [Box.instApprox, mul_subset_iff, Box.mem_image2_iff, and_imp, Complex.mul_re,
    Complex.mul_im, Interval.mul_box]
  intro a ⟨t,tx,ta⟩ b br bi
  simp only [← ta, Complex.ofReal_eq_coe, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  exact ⟨by mono, by mono⟩

/-- `mono` friendly version of `Interval.approx_mul_box` -/
@[mono] lemma _root_.Interval.subset_approx_mul_box {p : Set ℝ} {q : Set ℂ} {x : Interval} {z : Box}
    (px : p ⊆ approx x) (qz : q ⊆ approx z) :
    (Complex.ofReal '' p) * q ⊆ approx (x.mul_box z) :=
  subset_trans (mul_subset_mul (image_mono px) qz) (Interval.approx_mul_box _ _)

/-- `Box` approximates `ℂ` as a ring -/
noncomputable instance : ApproxRing Box ℂ where

/-- `Box` squaring approximates `ℂ` -/
@[mono] lemma approx_sqr (z : Box) : (fun z ↦ z^2) '' approx z ⊆ approx z.sqr := by
  simp only [instApprox, image_image2, Box.mem_image2_iff, subset_def, Box.sqr, mem_image2]
  rintro w ⟨r,rz,i,iz,e⟩
  refine ⟨r^2 - i^2, ?_, 2*r*i, ?_, ?_⟩
  · apply approx_sub
    rw [Set.mem_sub]
    exact ⟨r^2, Interval.approx_sqr _ (mem_image_of_mem _ rz),
           i^2, Interval.approx_sqr _ (mem_image_of_mem _ iz), rfl⟩
  · have e : (2 : ℝ) = 2^(1 : ℤ) := by norm_num
    rw [mul_assoc, mul_comm, e]
    exact Interval.mem_approx_scaleB (mem_approx_mul rz iz)
  · simpa only [Complex.ext_iff, pow_two, Complex.mul_re, Complex.mul_im, two_mul, add_mul,
      mul_comm _ r] using e

/-- `Box` squaring approximates `ℂ`, `∈` version -/
@[mono] lemma mem_approx_sqr {z' : ℂ} {z : Box} (m : z' ∈ approx z) : z'^2 ∈ approx z.sqr := by
  apply approx_sqr; use z'

/-!
### Square magnitude
-/

/-- `Box` square magnitude -/
def normSq (z : Box) : Interval :=
  z.re.sqr + z.im.sqr

/-- `normSq` is conservative -/
@[mono] lemma mem_approx_normSq {z' : ℂ} {z : Box} (m : z' ∈ approx z) :
    Complex.abs z' ^ 2 ∈ approx z.normSq := by
  rw [normSq]
  simp only [Complex.sq_abs, Complex.normSq, ←pow_two, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  mono

/-- `normSq` is conservative -/
@[mono] lemma mem_approx_normSq' {z' : ℂ} {z : Box} (m : z' ∈ approx z) :
    Complex.normSq z' ∈ approx z.normSq := by
  simp only [Complex.normSq_eq_abs]
  exact mem_approx_normSq m

/-- Lower bounds on `normSq` produce lower bounds on contained radii -/
lemma sqrt_normSq_le_abs {z' : ℂ} {z : Box} (m : z' ∈ approx z) (n : z.normSq ≠ nan) :
    Real.sqrt z.normSq.lo.val ≤ Complex.abs z' := by
  simp only [Real.sqrt_le_iff, apply_nonneg, true_and]
  apply Interval.lo_le n
  mono

/-- Upper bounds on `normSq` produce upper bounds on contained radii -/
lemma abs_le_sqrt_normSq {z' : ℂ} {z : Box} (m : z' ∈ approx z) (n : z.normSq ≠ nan) :
    Complex.abs z' ≤ Real.sqrt z.normSq.hi.val := by
  apply Real.le_sqrt_of_sq_le
  apply Interval.le_hi n
  mono

/-!
### Conversion
-/

@[coe] def _root_.Complex.ofRat (z : ℚ × ℚ) : ℂ := ⟨z.1, z.2⟩

noncomputable instance : Coe (ℚ × ℚ) ℂ where
  coe z := Complex.ofRat z

def ofRat (z : ℚ × ℚ) : Box :=
  ⟨.ofRat z.1, .ofRat z.2⟩

@[mono] lemma approx_ofRat (z : ℚ × ℚ) : ↑z ∈ approx (ofRat z) := by
  simp only [instApprox, ofRat, mem_image2, Complex.mk.injEq, exists_eq_right_right,
    Interval.approx_ofRat, true_and, exists_eq_right, Complex.ofRat]
