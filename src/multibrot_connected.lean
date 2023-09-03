-- The multibrot set and its complement are connected

import connected
import multibrot

open complex (abs has_zero)
open filter (eventually_of_forall tendsto at_top)
open function (uncurry)
open metric (ball sphere closed_ball is_open_ball mem_ball_self mem_ball mem_closed_ball mem_closed_ball_self mem_sphere)
open real (exp log)
open riemann_sphere
open set
open_locale alexandroff riemann_sphere topology real
noncomputable theory

variables {c : ℂ}

-- Fix d ≥ 2
variables {d : ℕ} [fact (2 ≤ d)]

-- multibrot_ext is path connected
theorem is_path_connected.multibrot_ext (d : ℕ) [fact (2 ≤ d)] : is_path_connected (multibrot_ext d) := begin
  rw ←ray_surj d, apply is_path_connected.image_of_continuous_on,
  exact (convex_ball _ _).is_path_connected (metric.nonempty_ball.mpr one_pos),
  exact (ray_holomorphic d).continuous_on,
end

-- Levelsets of potential are connected
lemma is_path_connected.potential_levelset (p : ℝ) (p0 : 0 ≤ p) (p1 : p < 1)
    : is_path_connected (potential d ⁻¹' {p}) := begin
  have e : potential d ⁻¹' {p} = ray d '' sphere 0 p, {
    apply set.ext, intros c,
    simp only [mem_preimage, mem_singleton_iff, ←abs_bottcher, mem_image, mem_sphere, complex.dist_eq, sub_zero],
    constructor, {
      intros h, use bottcher d c, use h, rw ray_bottcher, rw [←potential_lt_one, ←abs_bottcher, h], exact p1,
    }, {
      rintros ⟨e,ep,ec⟩, rw [←ec, bottcher_ray], exact ep,
      simp only [mem_ball, complex.dist_eq, sub_zero, ep, p1],
    },
  },
  rw e, apply (is_path_connected_sphere p0).image_of_continuous_on,
  exact (ray_holomorphic d).continuous_on.mono (metric.sphere_subset_ball p1),
end

-- multibrot_extᶜ is connected.
-- Proof: It is the downward intersection of the connected sets potential d ⁻¹' (Ici p)
theorem is_connected.compl_multibrot_ext (d : ℕ) [fact (2 ≤ d)] : is_connected (multibrot_ext d)ᶜ := begin
  use ((0:ℂ):𝕊), simp only [mem_compl_iff, multibrot_ext_coe, not_not, multibrot_zero],
  have e : (multibrot_ext d)ᶜ = ⋂ (p : Ico 0 (1:ℝ)), potential d ⁻¹' (Ici p), {
    apply set.ext, intros z,
    simp only [mem_compl_iff, ←potential_lt_one, mem_Inter, mem_preimage, not_lt, mem_Ici],
    constructor, rintros p1 ⟨q,m⟩, simp only [subtype.coe_mk, mem_Ico] at ⊢ m, linarith,
    intros h, contrapose h, simp only [not_le, not_forall] at h ⊢,
    rcases exists_between h with ⟨y,py,y1⟩, refine ⟨⟨y,⟨trans potential_nonneg (le_of_lt py),y1⟩⟩,py⟩,
  },
  rw e, apply is_preconnected.directed_Inter, {
    rintros ⟨a,a0,a1⟩ ⟨b,b0,b1⟩, refine ⟨⟨max a b, mem_Ico.mpr ⟨le_max_of_le_left a0,max_lt a1 b1⟩⟩, _, _⟩,
    intros z h, simp only [mem_preimage, mem_Ici, subtype.coe_mk, max_le_iff] at h ⊢, exact h.1,
    intros z h, simp only [mem_preimage, mem_Ici, subtype.coe_mk, max_le_iff] at h ⊢, exact h.2,
  }, {
    rintros ⟨p,m⟩, simp only [subtype.coe_mk],
    refine is_connected.is_preconnected (is_path_connected.is_connected _),
    apply is_path_connected.of_frontier, {
      rw frontier_Ici, exact is_path_connected.potential_levelset _ m.1 m.2,
    }, {
      exact potential_continuous,
    }, {
      exact is_closed_Ici,
    },
  }, {
    rintros ⟨p,m⟩, exact (is_closed_Ici.preimage potential_continuous).is_compact,
  },
end

-- multibrot is connected
theorem is_connected.multibrot (d : ℕ) [fact (2 ≤ d)] : is_connected (multibrot d) := begin
  have e : multibrot d = (λ z : 𝕊, z.to_complex) '' (multibrot_ext d)ᶜ, {
    apply set.ext, intro z, simp only [mem_image, mem_compl_iff], constructor,
    intro m, use z, simp only [multibrot_ext_coe, not_not, m, to_complex_coe, true_and, eq_self_iff_true],
    rintros ⟨w,m,wz⟩, induction w using riemann_sphere.rec,
    simp only [multibrot_ext_coe, not_not, to_complex_coe] at m wz, rwa ←wz,
    contrapose m, simp only [not_not, multibrot_ext_inf],
  },
  rw e, apply (is_connected.compl_multibrot_ext d).image,
  refine continuous_on_to_complex.mono _, intros z m,
  contrapose m, simp only [mem_compl_iff, mem_singleton_iff, not_not] at m,
  simp only [m, not_mem_compl_iff, multibrot_ext_inf],
end

-- multibrotᶜ is connected
theorem is_connected.compl_multibrot (d : ℕ) [fact (2 ≤ d)] : is_connected (multibrot d)ᶜ := begin
  have dc : is_connected (multibrot_ext d \ {∞}), {
    use (((3:ℝ):ℂ):𝕊), constructor,
    simp only [multibrot_ext_coe, mem_compl_iff], apply multibrot_two_lt,
    rw [complex.abs_of_real, abs_of_pos], norm_num, norm_num,
    simp only [mem_singleton_iff, coe_ne_inf, not_false_iff],
    exact (is_path_connected.multibrot_ext d).is_connected.is_preconnected.open_diff_singleton is_open_multibrot_ext _,
  },
  have e : (multibrot d)ᶜ = (λ z : 𝕊, z.to_complex) '' (multibrot_ext d \ {∞}), {
    apply set.ext, intro z, simp only [mem_compl_iff, mem_image], constructor,
    intro m, use z, simp only [multibrot_ext_coe, m, true_and, to_complex_coe, not_false_iff, true_and, mem_diff,
      eq_self_iff_true, and_true, mem_singleton_iff, coe_ne_inf],
    rintros ⟨w,⟨m,wi⟩,wz⟩, induction w using riemann_sphere.rec,
    simp only [multibrot_ext_coe, to_complex_coe, mem_diff] at m wz, rwa ←wz,
    contrapose wi, simp only [mem_singleton_iff, not_not],
  },
  rw e, apply dc.image,
  refine continuous_on_to_complex.mono _, rintros z ⟨m,i⟩,
  simp only [mem_singleton_iff, mem_compl_iff] at ⊢ i, exact i,
end