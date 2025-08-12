import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
## `Circle` facts
-/

open Classical
open Complex (arg slitPlane)
open Set
open scoped Real
noncomputable section

variable {X : Type} [TopologicalSpace X]

instance : Neg Circle where
  neg z := Circle.exp π * z

lemma Circle.neg_def (z : Circle) : -z = Circle.exp π * z := rfl

instance : InvolutiveNeg Circle where
  neg_neg z := by
    have e : π + π = 2 * π := by ring
    simp only [Circle.neg_def, ← mul_assoc, ← Circle.exp_add, mul_eq_right, e, Circle.exp_two_pi]

instance : HasDistribNeg Circle where
  neg_mul z w := by simp only [Circle.neg_def, mul_assoc]
  mul_neg z w := by simp only [Circle.neg_def, ← mul_assoc, mul_comm _ (Circle.exp _)]

@[simp] lemma Circle.neg_ne (z : Circle) : -z ≠ z := by
  simp only [neg_def, ne_eq, mul_eq_right, exp_eq_one, ← mul_assoc, eq_comm (a := π), not_exists]
  simp only [ne_eq, Real.pi_ne_zero, not_false_eq_true, mul_eq_right₀,
    (by norm_num : (2 : ℝ) = (2 : ℤ)), ← Int.cast_one (R := ℝ), ← Int.cast_mul, Int.cast_inj]
  omega

@[simp] lemma Circle.coe_neg (z : Circle) : (-z).val = -z.val := by
  simp only [neg_def, coe_mul, coe_exp, Complex.exp_pi_mul_I, neg_mul, one_mul]

lemma Circle.arg_neg_one : arg (-1 : Circle).val = π := by
  simp only [neg_def, mul_one, coe_exp, Complex.exp_pi_mul_I, Complex.arg_neg_one]

@[simp] lemma Circle.mem_slitPlane (z : Circle) : z.val ∈ slitPlane ↔ z ≠ -1 := by
  simp only [Complex.mem_slitPlane_iff_arg, ne_eq, Circle.ext_iff, Complex.ext_norm_arg_iff,
    norm_zero, Complex.arg_zero, Circle.norm_coe, true_and, one_ne_zero, false_and, not_false_iff,
    and_true, coe_neg, norm_neg, OneMemClass.coe_one, Complex.arg_neg_one, norm_one]

@[fun_prop] lemma Continuous.circle_exp {f : X → ℝ} (fc : Continuous f) :
    Continuous (fun x ↦ Circle.exp (f x)) := by fun_prop

instance : Inhabited Circle where
  default := 1

instance : Nonempty Circle := by infer_instance

instance : Infinite Circle := by
  rw [Circle.argEquiv.infinite_iff]
  apply Set.Infinite.to_subtype
  exact Ioc_infinite (by linarith [Real.pi_pos])

lemma Circle.connected_compl_singleton (s : Circle) : IsConnected {s}ᶜ := by
  have e : {s}ᶜ = (fun t ↦ -s * Circle.exp t) '' Ioo (-π) π := by
    ext z
    simp only [mem_compl_iff, mem_singleton_iff, neg_mul, mem_image, mem_Ioo]
    constructor
    · intro zs
      refine ⟨(z / -s).val.arg, ?_⟩
      simp only [Complex.neg_pi_lt_arg, true_and, (Complex.arg_le_pi _).lt_iff_ne,
        Circle.exp_arg]
      simp only [← Circle.arg_neg_one, ne_eq, Circle.arg_eq_arg]
      simpa only [div_neg, neg_inj, mul_neg, mul_div_cancel, neg_neg, and_true, div_eq_one]
    · intro ⟨t,⟨lo,hi⟩,e⟩
      simp only [← e, neg_mul_eq_mul_neg, mul_eq_left]
      simp only [neg_eq_iff_eq_neg, Circle.ext_iff, coe_exp, coe_neg, OneMemClass.coe_one, ne_eq]
      rw [← Complex.exp_pi_mul_I]
      by_contra h
      replace h := Complex.exp_inj_of_neg_pi_lt_of_le_pi ?_ ?_ ?_ ?_ h
      · simp only [mul_eq_mul_right_iff, Complex.ofReal_inj, Complex.I_ne_zero, or_false] at h
        simp only [h, lt_self_iff_false] at hi
      · simp [lo]
      · simp [hi.le]
      · simp [Real.pi_pos]
      · simp
  rw [e]
  apply IsConnected.image
  · exact isConnected_Ioo (by linarith [Real.pi_pos])
  · fun_prop

lemma Circle.not_continuous_or_not_injective {f : Circle → ℝ} (cont : Continuous f)
    (inj : f.Injective) : False := by
  obtain ⟨a,_,lo⟩ := isCompact_univ.exists_isMinOn univ_nonempty cont.continuousOn
  obtain ⟨b,_,hi⟩ := isCompact_univ.exists_isMaxOn univ_nonempty cont.continuousOn
  simp only [isMinOn_iff, mem_univ, forall_const, isMaxOn_iff] at lo hi
  by_cases ab : f a = f b
  · have e : ∀ x y, f x = f y := by intro x y; linarith [lo x, hi x, lo y, hi y]
    specialize e (-1) 1
    simp only [inj.eq_iff, neg_ne] at e
  · replace ab : f a < f b := Ne.lt_of_le ab (lo b)
    obtain ⟨x,m⟩ := Infinite.exists_notMem_finset {a, b}
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← ne_eq] at m
    have ax : f a < f x := (inj.ne_iff.mpr m.1).symm.lt_of_le (lo x)
    have xb : f x < f b := (inj.ne_iff.mpr m.2).lt_of_le (hi x)
    have connect : (f '' {x}ᶜ).OrdConnected :=
      ((Circle.connected_compl_singleton x).image _ cont.continuousOn).isPreconnected.ordConnected
    have mem := connect.out (x := f a) (y := f b) (by aesop) (by aesop) ⟨ax.le, xb.le⟩
    simp only [mem_image, mem_compl_iff, mem_singleton_iff, inj.eq_iff, not_and_self,
      exists_const] at mem
