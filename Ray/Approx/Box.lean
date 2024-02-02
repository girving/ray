import Mathlib.Data.Complex.Basic
import Ray.Approx.Interval.Basic

open Classical
open Pointwise

/-!
## Complex interval arithmic (on top of 64-bit fixed point intervals)
-/

open Set
open scoped Real

variable {s t : Int64}

/-- Rectangular boxes of complex numbers -/
structure Box (s : Int64) where
  re : Interval s
  im : Interval s
  deriving DecidableEq, BEq

/-- `Box` has nice equality -/
instance : LawfulBEq (Box s) where
  eq_of_beq {x y} e := by
    induction' x with xlo xhi; induction' y with ylo yhi
    have g : ((xlo == ylo && xhi == yhi) = true) := e
    simp only [Bool.and_eq_true, beq_iff_eq] at g
    simp only [g.1, g.2]
  rfl {x} := by
    have e : (x == x) = (x.re == x.re && x.im == x.im) := rfl
    simp only [e, beq_self_eq_true, Bool.and_self]

/-- Reduce `Box s` equality to `Interval` equality -/
lemma Box.ext_iff (z w : Box s) : z = w ↔ z.re = w.re ∧ z.im = w.im := by
  induction z; induction w; simp only [mk.injEq]

/-- Simplification of `∈ image2` for `Box` -/
@[simp] lemma Box.mem_image2_iff {z : ℂ} {s t : Set ℝ} :
    z ∈ image2 (fun r i ↦ (⟨r,i⟩ : ℂ)) s t ↔ z.re ∈ s ∧ z.im ∈ t := by
  simp only [image2, Complex.ext_iff, exists_and_left, exists_eq_right_right, mem_setOf_eq]

/-- `Box` approximates `ℂ` -/
instance Box.instApprox : Approx (Box s) ℂ where
  approx z := image2 (fun r i ↦ ⟨r,i⟩) (approx z.re) (approx z.im)

/-- `Box` zero -/
instance : Zero (Box s) where
  zero := ⟨0,0⟩

/-- `Box` negation -/
instance : Neg (Box s) where
  neg x := ⟨-x.re, -x.im⟩

/-- `Box` addition -/
instance : Add (Box s) where
  add x y := ⟨x.re + y.re, x.im + y.im⟩

/-- `Box` subtraction -/
instance : Sub (Box s) where
  sub x y := ⟨x.re - y.re, x.im - y.im⟩

/-- Complex conjugation -/
def Box.conj (z : Box s) : Box s := ⟨z.re, -z.im⟩

/-- `Box` inhomogenous multiplication -/
def Box.mul (z : Box s) (w : Box t) (u : Int64) : Box u :=
  ⟨z.re.mul w.re u - z.im.mul w.im u, z.re.mul w.im u + z.im.mul w.re u⟩

/-- `Interval * Box` -/
def Interval.mul_box (x : Interval s) (z : Box t) (u : Int64) : Box u :=
  ⟨x.mul z.re u, x.mul z.im u⟩

/-- `Box` homogenous multiplication -/
instance : Mul (Box s) where
  mul z w := z.mul w s

/-- `Box` squaring (tighter than `z.mul z`) -/
def Box.sqr (z : Box s) (u : Int64 := s) : Box u :=
  let w := z.re.mul z.im u
  ⟨z.re.sqr u - z.im.sqr u, w + w⟩

/-- `Box` square magnitude -/
def Box.sqr_mag (z : Box s) (u : Int64) : Interval u :=
  z.re.sqr u + z.im.sqr u

-- Bounds properties of `Box` arithmetic
lemma Box.neg_def {z : Box s} : -z = ⟨-z.re, -z.im⟩ := rfl
lemma Box.add_def {z w : Box s} : z + w = ⟨z.re + w.re, z.im + w.im⟩ := rfl
lemma Box.sub_def {z w : Box s} : z - w = ⟨z.re - w.re, z.im - w.im⟩ := rfl
@[simp] lemma Box.re_zero : (0 : Box s).re = 0 := rfl
@[simp] lemma Box.im_zero : (0 : Box s).im = 0 := rfl
@[simp] lemma Box.approx_zero : approx (0 : Box s) = {0} := by
  simp only [instApprox, re_zero, Interval.approx_zero, im_zero, image2_singleton_right,
    image_singleton, singleton_eq_singleton_iff, Complex.ext_iff, Complex.zero_re, Complex.zero_im,
    and_self]

/-- `Box.neg` respects `approx` -/
instance : ApproxNeg (Box s) ℂ where
  approx_neg z := by
    simp only [Box.instApprox, ← image_neg, image_image2, image2_subset_iff, mem_image2,
      exists_and_left]
    intro r rz i iz
    refine ⟨-r, ?_, -i, ?_, rfl⟩
    repeat { apply approx_neg; simpa only [mem_neg, neg_neg] }

/-- `Box.add` respects `approx` -/
instance : ApproxAdd (Box s) ℂ where
  approx_add z w := by
    simp only [Box.instApprox, add_subset_iff, Box.mem_image2_iff, and_imp, Complex.add_re,
      Complex.add_im, Box.add_def]
    intro a ar ai b br bi
    exact ⟨approx_add _ _ (add_mem_add ar br), approx_add _ _ (add_mem_add ai bi)⟩

/-- `Box.sub` respects `approx` -/
instance : ApproxSub (Box s) ℂ where
  approx_sub x y := by
    simp only [Box.instApprox, sub_subset_iff, Box.mem_image2_iff, and_imp, Complex.sub_re,
      Complex.sub_im, Box.sub_def]
    intro a ar ai b br bi
    exact ⟨approx_sub _ _ (sub_mem_sub ar br), approx_sub _ _ (sub_mem_sub ai bi)⟩

/-- `Box` approximates `ℂ` as an additive group -/
noncomputable instance : ApproxAddGroup (Box s) ℂ where

/-- `Box` multiplication approximates `ℂ` (inhomogenous case) -/
@[mono] lemma Box.approx_mul (z : Box s) (w : Box t) (u : Int64) :
    approx z * approx w ⊆ approx (z.mul w u) := by
  simp only [Box.instApprox, mul_subset_iff, Box.mem_image2_iff, and_imp, Complex.mul_re,
    Complex.mul_im, Box.mul]
  intro a ar ai b br bi
  exact ⟨by mono, by mono⟩

/-- `Interval * Box` multiplication approximates `ℂ` (inhomogenous case) -/
@[mono] lemma Interval.approx_mul_box (x : Interval s) (z : Box t) (u : Int64) :
    (Complex.ofReal '' approx x) * approx z ⊆ approx (x.mul_box z u) := by
  simp only [Box.instApprox, mul_subset_iff, Box.mem_image2_iff, and_imp, Complex.mul_re,
    Complex.mul_im, Interval.mul_box]
  intro a ⟨t,tx,ta⟩ b br bi
  simp only [← ta, Complex.ofReal_eq_coe, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero]
  exact ⟨by mono, by mono⟩

/-- `mono` friendly version of `Interval.approx_mul_box` -/
@[mono] lemma Interval.subset_approx_mul_box {p : Set ℝ} {q : Set ℂ} {x : Interval s} {z : Box t}
    {u : Int64} (px : p ⊆ approx x) (qz : q ⊆ approx z) :
    (Complex.ofReal '' p) * q ⊆ approx (x.mul_box z u) :=
  subset_trans (mul_subset_mul (image_mono px) qz) (Interval.approx_mul_box _ _ _)

/-- `Box` multiplication approximates `ℂ` (homogenous case) -/
instance : ApproxMul (Box s) ℂ where
  approx_mul _ _ := Box.approx_mul _ _ _

/-- `Box` approximates `ℂ` as a ring -/
noncomputable instance : ApproxRing (Box s) ℂ where

/-- `Box` squaring approximates `ℂ` -/
@[mono] lemma Box.approx_sqr (z : Box s) (u : Int64 := s) :
    (fun z ↦ z^2) '' approx z ⊆ approx (z.sqr u) := by
  simp only [Box.instApprox, image_image2, Box.mem_image2_iff, subset_def, Box.sqr, mem_image2]
  rintro w ⟨r,rz,i,iz,e⟩
  refine ⟨r^2 - i^2, ?_, 2*r*i, ?_, ?_⟩
  · apply approx_sub
    rw [Set.mem_sub]
    exact ⟨r^2, Interval.approx_sqr _ _ (mem_image_of_mem _ rz),
           i^2, Interval.approx_sqr _ _ (mem_image_of_mem _ iz), rfl⟩
  · rw [mul_assoc, two_mul]
    apply approx_add
    rw [Set.mem_add]
    have ri := Interval.approx_mul _ _ u (mem_image2_of_mem rz iz)
    exact ⟨r*i, ri, r*i, ri, rfl⟩
  · simpa only [Complex.ext_iff, pow_two, Complex.mul_re, Complex.mul_im, two_mul, add_mul,
      mul_comm _ r] using e
