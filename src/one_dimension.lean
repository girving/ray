-- Conveniences for 1D complex manifolds

import complex_manifold
import geometry.manifold.mfderiv
open filter (eventually_of_forall tendsto)
open function (uncurry)
open set
open_locale manifold topology
noncomputable theory

namespace one_dimension

notation `I` := model_with_corners_self ℂ ℂ
notation `II` := model_with_corners.prod I I

end one_dimension
open one_dimension

variables {S : Type} [topological_space S] [complex_manifold I S]
variables {T : Type} [topological_space T] [complex_manifold I T]
variables {U : Type} [topological_space U] [complex_manifold I U]

-- 1D tangent spaces are nontrivial
instance one_dimension_tangent_space_nontrivial (z : S) : nontrivial (tangent_space I z) :=
  by simp only [tangent_space, complex.nontrivial]

-- tangent spaces are normed_spaces
instance one_dimension_tangent_space_normed_add_comm_group (z : S) : normed_add_comm_group (tangent_space I z) :=
  complex.normed_add_comm_group
instance one_dimension_tangent_space_normed_space (z : S) : normed_space ℂ (tangent_space I z) :=
  @normed_field.to_normed_space _ complex.normed_field

-- The tangent space norm is just abs
lemma tangent_space_norm_eq_complex_norm (z : S) (x : tangent_space I z) : ‖x‖ = complex.abs x :=
  by rw ←complex.norm_eq_abs

-- 1D tangent space maps are (noncanonically!) equivalent to ℂ 
def mderiv_to_scalar' (z : S) (w : T) : (tangent_space I z →L[ℂ] tangent_space I w) ≃ₗ[ℂ] ℂ := {
  to_fun := begin intro x, have y : ℂ →L[ℂ] ℂ := x, exact y 1, end,
  inv_fun := begin intro x, have y : ℂ →L[ℂ] ℂ := x • continuous_linear_map.id ℂ ℂ, exact y, end,
  map_add' := λ x y, continuous_linear_map.add_apply _ _ _,
  map_smul' := λ s x, continuous_linear_map.smul_apply _ _ _,
  left_inv := begin
    intro x, simp only, apply continuous_linear_map.ext, intro s,
    simp only [continuous_linear_map.smul_apply, continuous_linear_map.id_apply, smul_eq_mul],
    rw [mul_comm, ←smul_eq_mul, ←continuous_linear_map.map_smul, smul_eq_mul, mul_one],
  end,
  right_inv := begin
    intro x, simp only [continuous_linear_map.smul_apply, continuous_linear_map.id_apply, smul_eq_mul, mul_one],
  end,
}
def mderiv_to_scalar (z : S) (w : T) : (tangent_space I z →L[ℂ] tangent_space I w) ≃L[ℂ] ℂ := {
  to_linear_equiv := mderiv_to_scalar' z w,
  continuous_to_fun := begin
    simp only [mderiv_to_scalar'],
    rw metric.continuous_iff, intros x e ep, use [e/2, half_pos ep], intros y xy,
    simp only [dist_eq_norm, ←continuous_linear_map.sub_apply y x (1 : ℂ)] at xy ⊢,
    have b := continuous_linear_map.le_of_op_norm_le _ (le_of_lt xy) (1 : ℂ),
    simp only [tangent_space_norm_eq_complex_norm, complex.abs.map_one, mul_one] at b ⊢,
    exact lt_of_le_of_lt b (half_lt_self ep),
  end,
  continuous_inv_fun := begin
    simp only [mderiv_to_scalar'],
    rw metric.continuous_iff, intros x e ep, use [e/2, half_pos ep], intros y xy,
    simp only [dist_eq_norm, complex.norm_eq_abs] at xy ⊢, refine lt_of_le_of_lt _ (half_lt_self ep),
    apply continuous_linear_map.op_norm_le_bound' _ (le_of_lt (half_pos ep)), intros s sp,
    simp only [continuous_linear_map.sub_apply, continuous_linear_map.smul_apply, continuous_linear_map.id_apply],
    simp only [tangent_space_norm_eq_complex_norm, smul_eq_mul, ←mul_sub_right_distrib,
      complex.abs.map_mul] at xy ⊢,
    bound,
  end,
}

-- Given nonzero u, a tangent space map x is 0 iff x u = 0
lemma mderiv_eq_zero_iff {z : S} {w : T} (f : tangent_space I z →L[ℂ] tangent_space I w) (u : tangent_space I z)
    : f u = 0 ↔ f = 0 ∨ u = 0 := begin
  constructor, {
    rw or_iff_not_imp_right, intros f0 u0,
    apply continuous_linear_map.ext, intro v,
    have uu : complex.has_mul.mul (complex.has_inv.inv u) u = 1 := inv_mul_cancel u0,
    have e : v = (complex.has_mul.mul v (complex.has_inv.inv u)) • u :=
      by rw [smul_eq_mul, mul_assoc, uu, mul_one],
    rw [continuous_linear_map.zero_apply, e, f.map_smul, f0, smul_zero],
  }, {
    intro h, cases h,
    simp only [h, continuous_linear_map.zero_apply],
    simp only [h, continuous_linear_map.map_zero],
  },
end
lemma mderiv_eq_zero_iff' {z : S} {w : T} {f : tangent_space I z →L[ℂ] tangent_space I w}
    {u : tangent_space I z} (u0 : u ≠ 0) : f u = 0 ↔ f = 0 := by simp only [mderiv_eq_zero_iff, u0, or_false]

-- ne_zero versions of mderiv_eq_zero_iff
lemma mderiv_ne_zero_iff {z : S} {w : T} (f : tangent_space I z →L[ℂ] tangent_space I w) (u : tangent_space I z)
    : f u ≠ 0 ↔ f ≠ 0 ∧ u ≠ 0 := begin
  simp only [←not_or_distrib], exact iff.not (mderiv_eq_zero_iff _ _),
end
lemma mderiv_ne_zero_iff' {z : S} {w : T} {f : tangent_space I z →L[ℂ] tangent_space I w}
    {u : tangent_space I z} (u0 : u ≠ 0) : f u ≠ 0 ↔ f ≠ 0 :=
  by simp only [mderiv_ne_zero_iff, u0, eq_true_iff.mpr u0, and_true]

-- comp is zero iff either side is
lemma mderiv_comp_eq_zero_iff {x : S} {y : T} {z : U} (f : tangent_space I y →L[ℂ] tangent_space I z)
   (g : tangent_space I x →L[ℂ] tangent_space I y) : f.comp g = 0 ↔ f = 0 ∨ g = 0 := begin
  rcases exists_ne (0 : tangent_space I x) with ⟨t,t0⟩,
  constructor, {
    intro h, simp only [←mderiv_eq_zero_iff' t0, continuous_linear_map.comp_apply] at h,
    by_cases g0 : g t = 0,
    right, rw mderiv_eq_zero_iff' t0 at g0, exact g0,
    left, rwa ←mderiv_eq_zero_iff' g0,
  }, {
    intro h, cases h, simp only [h, g.zero_comp], simp only [h, f.comp_zero],
  },
end
lemma mderiv_comp_ne_zero {x : S} {y : T} {z : U} (f : tangent_space I y →L[ℂ] tangent_space I z)
   (g : tangent_space I x →L[ℂ] tangent_space I y) : f ≠ 0 → g ≠ 0 → f.comp g ≠ 0 := begin
  intros f0 g0, simp only [ne.def, mderiv_comp_eq_zero_iff, f0, g0, or_self, not_false_iff],
end
lemma has_mfderiv_at_of_mderiv_ne_zero {f : S → T} {x : S} (d0 : mfderiv I I f x ≠ 0)
    : mdifferentiable_at I I f x := begin
  contrapose d0, simp only [mfderiv, d0, if_false, ne.def, eq_self_iff_true, not_true, not_false_iff],
end
lemma mderiv_comp_ne_zero' {f : T → U} {g : S → T} {x : S}
    : mfderiv I I f (g x) ≠ 0 → mfderiv I I g x ≠ 0 → mfderiv I I (λ x, f (g x)) x ≠ 0 := begin
  intros df dg,
  rw mfderiv_comp x (has_mfderiv_at_of_mderiv_ne_zero df) (has_mfderiv_at_of_mderiv_ne_zero dg),
  exact mderiv_comp_ne_zero _ _ df dg,
end 
 
-- Nonzero 1D derivatives are invertible
def mderiv_equiv {z : S} {w : T} (f : tangent_space I z →L[ℂ] tangent_space I w) (f0 : f ≠ 0)
    : tangent_space I z ≃L[ℂ] tangent_space I w := {
  to_fun := f,
  map_add' := f.map_add', 
  map_smul' := f.map_smul',
  inv_fun := begin intro x, have f' : ℂ →L[ℂ] ℂ := f,  exact complex.has_mul.mul (f' 1)⁻¹ x end,
  left_inv := begin
    intro x, simp only,
    have e : f x = complex.has_mul.mul (f (1 : ℂ)) x :=
      by rw [mul_comm, ←smul_eq_mul, ←f.map_smul, smul_eq_mul, mul_one],
    rw [e, ←mul_assoc, inv_mul_cancel, one_mul], contrapose f0,
    simp only [not_not] at f0 ⊢, exact (mderiv_eq_zero_iff' (by norm_num)).mp f0,
  end,
  right_inv := begin
    intro x, simp only,
    have e : ∀ y : ℂ, f y = complex.has_mul.mul (f (1 : ℂ)) y :=
      λ y, by rw [mul_comm, ←smul_eq_mul, ←f.map_smul, smul_eq_mul, mul_one],
    rw [e ((f (1 : ℂ))⁻¹ * x), ←mul_assoc, mul_inv_cancel, one_mul],
    contrapose f0, simp only [not_not] at f0 ⊢, exact (mderiv_eq_zero_iff' (by norm_num)).mp f0,
  end,
  continuous_to_fun := f.cont,
  continuous_inv_fun := begin
    simp only, exact continuous.mul continuous_const continuous_id,
  end,
}
lemma mderiv_equiv_apply {z : S} {w : T} {f : tangent_space I z →L[ℂ] tangent_space I w} (f0 : f ≠ 0)
    (x : tangent_space I z) : mderiv_equiv f f0 x = f x := rfl
lemma mderiv_equiv_eq {z : S} {w : T} (f : tangent_space I z →L[ℂ] tangent_space I w) (f0 : f ≠ 0)
    : ↑(mderiv_equiv f f0) = f := begin
  apply continuous_linear_map.ext, intro x, refl,
end

-- Chart derivatives are nonzero
lemma ext_chart_at_mderiv_ne_zero' {z w : S} (m : w ∈ (ext_chart_at I z).source)
    : mfderiv I I (ext_chart_at I z) w ≠ 0 := begin
  rcases exists_ne (0 : tangent_space I z) with ⟨t,t0⟩,
  rw ←mderiv_ne_zero_iff' t0, contrapose t0, simp only [not_not] at ⊢ t0,
  have h := continuous_linear_map.ext_iff.mp (ext_chart_at_mderiv_left_inverse m) t,
  simp only [t0, continuous_linear_map.comp_apply, continuous_linear_map.map_zero,
    continuous_linear_map.id_apply] at h, exact h.symm,
end
lemma ext_chart_at_symm_mderiv_ne_zero' {z : S} {w : ℂ} (m : w ∈ (ext_chart_at I z).target)
    : mfderiv I I (ext_chart_at I z).symm w ≠ 0 := begin
  rcases exists_ne (0 : tangent_space I (ext_chart_at I z z)) with ⟨t,t0⟩,
  rw ←mderiv_ne_zero_iff' t0, contrapose t0, simp only [not_not] at ⊢ t0,
  have h := continuous_linear_map.ext_iff.mp (ext_chart_at_mderiv_right_inverse m) t,
  simp only [t0, continuous_linear_map.comp_apply, continuous_linear_map.map_zero,
    continuous_linear_map.id_apply] at h, exact h.symm,
end
lemma ext_chart_at_mderiv_ne_zero (z : S) : mfderiv I I (ext_chart_at I z) z ≠ 0 :=
  ext_chart_at_mderiv_ne_zero' (mem_ext_chart_source I z)
lemma ext_chart_at_symm_mderiv_ne_zero (z : S) : mfderiv I I (ext_chart_at I z).symm (ext_chart_at I z z) ≠ 0 :=
  ext_chart_at_symm_mderiv_ne_zero' (mem_ext_chart_target I z)

-- Identity derivatives are nonzero
lemma id_mderiv_ne_zero {z : S} : mfderiv I I (λ z, z) z ≠ 0 := begin
  have d : mdifferentiable_at I I (λ z, z) z := mdifferentiable_at_id I,
  simp only [mfderiv, d, if_true, written_in_ext_chart_at, function.comp,
    model_with_corners.boundaryless.range_eq_univ, fderiv_within_univ],
  have e : (λ w, ext_chart_at I z ((ext_chart_at I z).symm w)) =ᶠ[𝓝 (ext_chart_at I z z)] id, {
    apply ((ext_chart_at_open_target I z).eventually_mem (mem_ext_chart_target I z)).mp,
    refine eventually_of_forall (λ w m, _),
    simp only [id, local_equiv.right_inv _ m],
  },
  simp only [e.fderiv_eq, fderiv_id, ne.def, continuous_linear_map.ext_iff, not_forall,
    continuous_linear_map.zero_apply, continuous_linear_map.id_apply], use [1, one_ne_zero],
end 

-- Nonzeroness of mfderiv reduces to nonzeroness of deriv
lemma mfderiv_eq_zero_iff_deriv_eq_zero {f : ℂ → ℂ} {z : ℂ} : mfderiv I I f z = 0 ↔ deriv f z = 0 := begin
  by_cases d : differentiable_at ℂ f z, {
    constructor, {
      have h := d.mdifferentiable_at.has_mfderiv_at, intro e, rw e at h,
      have p := h.has_fderiv_at.has_deriv_at,
      simp only [continuous_linear_map.zero_apply] at p, exact p.deriv, 
    }, {
      have h := d.has_deriv_at, intro e, rw e at h,
      have s0 : (1 : ℂ →L[ℂ] ℂ).smul_right (0 : ℂ) = 0, {
        apply continuous_linear_map.ext, simp only [continuous_linear_map.smul_right_apply, algebra.id.smul_eq_mul,
          mul_zero, continuous_linear_map.zero_apply, forall_const],
      },
      have p := h.has_fderiv_at.has_mfderiv_at, rw s0 at p, exact p.mfderiv,
    },
  }, {
    have d' : ¬mdifferentiable_at I I f z, {
      contrapose d, simp only [not_not] at ⊢ d, exact d.differentiable_at,
    },
    simp only [deriv_zero_of_not_differentiable_at d, mfderiv_zero_of_not_mdifferentiable_at d', eq_self_iff_true],
  },
end 
lemma mfderiv_ne_zero_iff_deriv_ne_zero {f : ℂ → ℂ} {z : ℂ} : mfderiv I I f z ≠ 0 ↔ deriv f z ≠ 0 :=
  by rw [not_iff_not, mfderiv_eq_zero_iff_deriv_eq_zero]

-- A critical point is where the derivative of f vanishes
def critical (f : S → T) (z : S) := mfderiv I I f z = 0

-- A precritical point is an iterated preimage of a critical point
def precritical (f : S → S) (z : S) := ∃ n, critical f (f^[n] z)

-- Critical points of iterations are precritical points
lemma critical_iter {f : S → S} {n : ℕ} {z : S} (fa : holomorphic I I f)
    (c : critical (f^[n]) z) : precritical f z := begin
  induction n with n h, {
    simp only [function.iterate_zero, critical, mfderiv_id, ←continuous_linear_map.op_norm_zero_iff,
      continuous_linear_map.norm_id] at c,
    contrapose c, norm_num,
  }, {
    simp only [function.iterate_succ', critical, function.comp,
      mfderiv_comp z (fa _).mdifferentiable_at (fa.iter _ _).mdifferentiable_at, mderiv_comp_eq_zero_iff] at c,
    cases c, use [n,c], exact h c,
  },
end

-- Next we prove some facts about mfderiv.  These would ideally follow from continuity and holomorphicity
-- of mfderiv, but we can't express that directly as mfderiv lives in a different type at each point.
-- Rather than detour into the necessary theory, I'm going to express what I need in coordinates for now.

-- A curried function in coordinates
def in_chart (f : ℂ → S → T) (c : ℂ) (z : S) : ℂ → ℂ → ℂ :=
  λ e w, ext_chart_at I (f c z) (f e ((ext_chart_at I z).symm w))

-- in_chart is analytic
lemma holomorphic_at.in_chart {f : ℂ → S → T} {c : ℂ} {z : S} (fa : holomorphic_at II I (uncurry f) (c,z))
    : analytic_at ℂ (uncurry (in_chart f c z)) (c, ext_chart_at I z z) := begin
  apply holomorphic_at.analytic_at II I,
  apply (holomorphic_at.ext_chart_at (mem_ext_chart_source I (f c z))).comp_of_eq,
  apply fa.curry_comp_of_eq holomorphic_at_fst,
  apply (holomorphic_at.ext_chart_at_symm (mem_ext_chart_target I z)).comp_of_eq holomorphic_at_snd,
  repeat { simp only [local_equiv.left_inv _ (mem_ext_chart_source I z)] },
end

-- in_chart preserves critical points locally
lemma in_chart_critical {f : ℂ → S → T} {c : ℂ} {z : S} (fa : holomorphic_at II I (uncurry f) (c,z))
    : ∀ᶠ p : ℂ × S in 𝓝 (c,z), mfderiv I I (f p.1) (p.2) = 0 ↔
        deriv (in_chart f c z p.1) (ext_chart_at I z p.2) = 0 := begin
  apply (fa.continuous_at.eventually_mem (is_open_ext_chart_at_source I (f c z))
    (mem_ext_chart_source I (f c z))).mp,
  apply ((is_open_ext_chart_at_source II (c,z)).eventually_mem (mem_ext_chart_source _ _)).mp,
  refine fa.eventually.mp (eventually_of_forall _), rintros ⟨e,w⟩ fa m fm,
  simp only [ext_chart_at_prod, local_equiv.prod_source, ext_chart_at_eq_refl, local_equiv.refl_source,
    mem_prod, mem_univ, true_and] at m,
  simp only [uncurry] at fm,
  have m' := local_equiv.map_source _ m,
  rw in_chart, simp only [←mfderiv_eq_zero_iff_deriv_eq_zero],
  have e0 := local_equiv.left_inv _ m,
  rw [mfderiv_comp (ext_chart_at I z w), mderiv_comp_eq_zero_iff, e0],
  rw [mfderiv_comp (ext_chart_at I z w), mderiv_comp_eq_zero_iff, e0],
  simp only [ext_chart_at_mderiv_ne_zero' fm, false_or, ext_chart_at_symm_mderiv_ne_zero' m', or_false],
  rw e0, exact fa.in2.mdifferentiable_at,
  exact (holomorphic_at.ext_chart_at_symm m').mdifferentiable_at,
  rw e0, exact (holomorphic_at.ext_chart_at fm).mdifferentiable_at,
  apply mdifferentiable_at.comp (ext_chart_at I z w),
  rw e0, exact fa.in2.mdifferentiable_at,
  exact (holomorphic_at.ext_chart_at_symm m').mdifferentiable_at,
  repeat { apply_instance },
end
 
-- mfderiv is nonzero near where it is nonzero
lemma mfderiv_ne_zero_eventually' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : holomorphic_at II I (uncurry f) (c,z)) (f0 : mfderiv I I (f c) z ≠ 0)
    : ∀ᶠ p : ℂ × S in 𝓝 (c,z), mfderiv I I (f p.1) p.2 ≠ 0 := begin
  set g := in_chart f c z,
  have g0 := in_chart_critical fa,
  have g0n : ∀ᶠ p : ℂ × S in 𝓝 (c,z), deriv (g p.1) (ext_chart_at I z p.2) ≠ 0, {
    refine continuous_at.eventually_ne _ _, {
      have e : (λ p : ℂ × S, deriv (g p.1) (ext_chart_at I z p.2)) = (λ p : ℂ × ℂ, deriv (g p.1) p.2) ∘
        (λ p : ℂ × S, (p.1, ext_chart_at I z p.2)) := rfl,
      rw e, exact fa.in_chart.deriv2.continuous_at.comp_of_eq
        (continuous_at_fst.prod ((continuous_at_ext_chart_at I z).comp_of_eq continuous_at_snd rfl)) rfl,
    }, {
      contrapose f0, simp only [not_not, function.comp] at ⊢ f0, simp only [g0.self], exact f0,
    },
  },
  refine g0.mp (g0n.mp (eventually_of_forall (λ w g0 e, _))),
  rw [ne.def, e], exact g0,
end
lemma mfderiv_ne_zero_eventually {f : S → T} {z : S} (fa : holomorphic_at I I f z) (f0 : mfderiv I I f z ≠ 0)
    : ∀ᶠ w in 𝓝 z, mfderiv I I f w ≠ 0 := begin
  set c : ℂ := 0, 
  set g : ℂ → S → T := λ c z, f z, 
  have ga : holomorphic_at II I (uncurry g) (c,z), {
    have e : uncurry g = f ∘ (λ p, p.2) := rfl, rw e,
    apply holomorphic_at.comp_of_eq fa holomorphic_at_snd, simp only,
  },
  have pc : tendsto (λ z, (c,z)) (𝓝 z) (𝓝 (c,z)) := continuous_at_const.prod continuous_at_id,
  exact pc.eventually (mfderiv_ne_zero_eventually' ga f0),
end

-- The set of noncritical points is open (resp. critical → closed)
lemma is_open_noncritical {f : ℂ → S → T} (fa : holomorphic II I (uncurry f))
    : is_open {p : ℂ × S | ¬critical (f p.1) p.2} := begin
  rw is_open_iff_eventually, rintros ⟨c,z⟩ m, exact mfderiv_ne_zero_eventually' (fa _) m,
end
lemma is_closed_critical {f : ℂ → S → T} (fa : holomorphic II I (uncurry f))
    : is_closed {p : ℂ × S | critical (f p.1) p.2} := begin
  have c := (is_open_noncritical fa).is_closed_compl,
  simp only [compl_set_of, not_not] at c, exact c,
end

-- Osgood's theorem on manifolds
lemma osgood_manifold {f : S × T → U} (fc : continuous f)
    (f0 : ∀ x y, holomorphic_at I I (λ x, f (x,y)) x)
    (f1 : ∀ x y, holomorphic_at I I (λ y, f (x,y)) y)
    : holomorphic II I f := begin
  rw holomorphic_iff, use fc, intro p, apply osgood_at',
  have fm : ∀ᶠ q in 𝓝 (ext_chart_at II p p), f ((ext_chart_at II p).symm q) ∈ (ext_chart_at I (f p)).source, {
    refine continuous_at.eventually_mem (fc.continuous_at.comp (continuous_at_ext_chart_at_symm II p))
      (is_open_ext_chart_at_source I (f p)) _,
    rw (ext_chart_at II p).left_inv (mem_ext_chart_source _ _), apply mem_ext_chart_source,
  },
  apply ((ext_chart_at_open_target II p).eventually_mem (mem_ext_chart_target II p)).mp,
  refine fm.mp (eventually_of_forall (λ q fm m, ⟨_,_,_⟩)), {
    exact (continuous_at_ext_chart_at' I _ fm).comp_of_eq (fc.continuous_at.comp
      (continuous_at_ext_chart_at_symm'' _ _ m)) rfl,
  }, {
    apply holomorphic_at.analytic_at I I,
    refine (holomorphic_at.ext_chart_at fm).comp_of_eq _ rfl,
    rw ext_chart_at_prod at m,
    simp only [function.comp, ext_chart_at_prod, local_equiv.prod_symm, local_equiv.prod_coe,
      local_equiv.prod_target, mem_prod_eq] at ⊢ m,
    exact (f0 _ _).comp (holomorphic_at.ext_chart_at_symm m.1),
  }, {
    apply holomorphic_at.analytic_at I I,
    refine (holomorphic_at.ext_chart_at fm).comp_of_eq _ rfl,
    rw ext_chart_at_prod at m,
    simp only [function.comp, ext_chart_at_prod, local_equiv.prod_symm, local_equiv.prod_coe,
      local_equiv.prod_target, mem_prod_eq] at ⊢ m,
    exact (f1 _ _).comp (holomorphic_at.ext_chart_at_symm m.2),
  },
end