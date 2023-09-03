-- at_inf filter for convergence to infinity

import analysis.normed.field.basic
import analysis.normed.group.basic
import order.filter.basic
import topology.metric_space.basic

import topology

open filter (tendsto at_top)
open metric (ball closed_ball)
open set
open_locale topology

-- at_inf represents the limit → ∞ on a normed commutative group
def at_inf {X : Type} [has_norm X] : filter X := ⨅ r : ℝ, filter.principal {x | r < ‖x‖}

-- A basis for at_inf 
lemma at_inf_basis {X : Type} [has_norm X]
    : (@at_inf X _).has_basis (λ r : ℝ, true) (λ r, {x | r < ‖x‖}) := begin
  apply filter.has_basis_infi_principal, apply directed_of_sup,
  intros a b ab, simp only [ge_iff_le, le_eq_subset, set_of_subset_set_of], intros x h, linarith,
end

instance at_inf_ne_bot : (@at_inf ℂ _).ne_bot := begin
  rw at_inf_basis.ne_bot_iff, intros r, simp only [true_implies_iff],
  rcases exists_nat_gt r, use w, simp only [mem_set_of, complex.norm_eq_abs, complex.abs_of_nat], exact h,
end

-- Characterization of → at_inf convergence
lemma tendsto_at_inf {X Y : Type} [has_norm Y] {f : X → Y} {l : filter X}
    : tendsto f l at_inf ↔ ∀ r, ∀ᶠ x in l, r < ‖f x‖ := begin
  rw at_inf_basis.tendsto_right_iff, simp only [true_implies_iff, mem_set_of],
end

-- Characterization of at_top → at_inf convergence
lemma tendsto_at_top_at_inf {X : Type} [has_norm X] {f : ℕ → X}
    : tendsto f at_top at_inf ↔ ∀ r, ∃ N, ∀ n, N ≤ n → r < ‖f n‖ := begin
  have h := @filter.has_basis.tendsto_iff _ _ _ _ _ _ _ _ _ _ f filter.at_top_basis at_inf_basis,
  simp only [mem_Ici, ge_iff_le, mem_set_of_eq, exists_true_left, forall_true_left] at h, exact h,
end

-- at_inf convergence in terms of norm convergence
lemma tendsto_at_inf_iff_norm_tendsto_at_top {X Y : Type} [has_norm Y] {f : filter X} {g : X → Y}
    : tendsto (λ x, g x) f at_inf ↔ tendsto (λ x, ‖g x‖) f at_top := begin
  rw filter.at_top_basis_Ioi.tendsto_right_iff,
  simp only [at_inf_basis.tendsto_right_iff, true_implies_iff, mem_set_of, mem_Ioi],
  apply_instance, apply_instance,
end

-- Characterization of s ∈ at_inf 
lemma mem_at_inf_iff {X : Type} [has_norm X] {s : set X} : s ∈ @at_inf X _ ↔ ∃ r, {x | ‖x‖ > r} ⊆ s :=
  by simp only [filter.has_basis_iff.mp at_inf_basis s, exists_true_left]

-- Eventually at_inf the norm is as large as desired
lemma eventually_at_inf {X : Type} [has_norm X] (r : ℝ) : ∀ᶠ x : X in at_inf, ‖x‖ > r := begin
  rw [filter.eventually_iff, mem_at_inf_iff], use r,
end

-- Convergence at_inf is the same as convergence at 0 for the reciprocal function
lemma tendsto_at_inf_iff_tendsto_nhds_zero {𝕜 X : Type} [nontrivially_normed_field 𝕜] {l : filter X} {f : 𝕜 → X}
    : tendsto f at_inf l ↔ tendsto (λ x, f x⁻¹) (𝓝[{0}ᶜ] 0) l := begin
  rw [filter.has_basis.tendsto_left_iff at_inf_basis, metric.nhds_within_basis_ball.tendsto_left_iff],
  constructor, {
    intros h t tl, rcases h t tl with ⟨r,rt,m⟩,
    by_cases rp : 0 < r, {
      use r⁻¹, simp only [rp, inv_pos, true_and], intros x xs, refine m _,
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs,
      simp only [←lt_inv (norm_pos_iff.mpr xs.2) rp, xs.1, mem_set_of_eq, norm_inv],
    }, {
      use 1, simp only [zero_lt_one, true_and], intros x xs, refine m _,
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs,
      simp only [mem_set_of_eq, norm_inv], simp only [not_lt] at rp,
      exact lt_of_le_of_lt rp (inv_pos.mpr (norm_pos_iff.mpr xs.2)),
    },
  }, {
    intros h t tl, rcases h t tl with ⟨r,rp,m⟩, use r⁻¹, simp only [true_and],
    intros x xs, simp only [mem_set_of_eq] at xs,
    have m := @m x⁻¹ _, { simp only [inv_inv] at m, exact m },
    simp only [mem_inter_iff, mem_ball_zero_iff, norm_inv, mem_compl_iff, mem_singleton_iff, inv_eq_zero],
    have np : 0 < ‖x‖ := trans (inv_pos.mpr rp) xs,
    simp [inv_lt np rp, xs, norm_pos_iff.mp np],
  },
end

-- Convergence to at_inf implies cocompact convergence
lemma at_inf_le_cocompact {X : Type} [normed_add_comm_group X] : @at_inf X _ ≤ filter.cocompact X := begin
  rw filter.le_def, intros s m,
  rcases filter.mem_cocompact.mp m with ⟨t,tc,ts⟩,
  rcases continuous_on_id.bounded_norm tc with ⟨r,rp,rh⟩,
  rw mem_at_inf_iff, use r,
  intros x m, apply ts, contrapose m,
  simp only [mem_compl_iff, not_not_mem] at m,
  simp only [mem_set_of_eq, not_lt],
  exact rh _ m,
end

-- On proper spaces, at_inf = cocompact
lemma at_inf_eq_cocompact {X : Type} [normed_add_comm_group X] [proper_space X]
    : @at_inf X _ = filter.cocompact X := begin
  apply le_antisymm at_inf_le_cocompact, rw filter.le_def, intros s m,
  rcases mem_at_inf_iff.mp m with ⟨r,h⟩,
  rw filter.mem_cocompact, use [closed_ball 0 r, is_compact_closed_ball _ _],
  refine trans _ h, intros x xs,
  simp only [mem_compl_iff, mem_closed_ball_zero_iff, not_le] at xs, exact xs,
end

-- ⁻¹ tendsto at_inf near 0, and vice versa
lemma inv_tendsto_at_inf {𝕜 : Type} [nontrivially_normed_field 𝕜]
    : tendsto (λ x : 𝕜, x⁻¹) (𝓝[{(0 : 𝕜)}ᶜ] 0) at_inf := begin
  rw ←@tendsto_at_inf_iff_tendsto_nhds_zero _ _ _ _ (λ x : 𝕜, x), exact filter.tendsto_id,
end
lemma inv_tendsto_at_inf' {𝕜 : Type} [nontrivially_normed_field 𝕜]
    : tendsto (λ x : 𝕜, x⁻¹) at_inf (𝓝 0) := begin
  simp only [tendsto_at_inf_iff_tendsto_nhds_zero, inv_inv],
  exact filter.tendsto_id.mono_left nhds_within_le_nhds,
end