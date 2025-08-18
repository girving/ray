-- at_inf filter for convergence to infinity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Basic
import Ray.Misc.Topology

/-!
## `atInf` filter for convergence to infinity

For proper spaces this is just `Filter.cocompact`, so I should probably remove this.
-/

open Filter (Tendsto atTop)
open Metric (ball closedBall)
open Set
open scoped Topology

variable {α : Type}

/-- `atInf` represents the limit `→ ∞` on a normed commutative group -/
def atInf {X : Type} [Norm X] : Filter X :=
  ⨅ r : ℝ, Filter.principal {x | r < ‖x‖}

/-- A basis for `atInf` -/
theorem atInf_basis {X : Type} [Norm X] :
    (@atInf X _).HasBasis (fun _ : ℝ ↦ True) fun r ↦ {x | r < ‖x‖} := by
  apply Filter.hasBasis_iInf_principal; apply directed_of_isDirected_le
  intro a b ab; simp only [ge_iff_le, le_eq_subset, setOf_subset_setOf]; intro x h; linarith

instance atInf_neBot : (@atInf ℂ _).NeBot := by
  rw [atInf_basis.neBot_iff]; intro r; simp only [true_imp_iff]
  rcases exists_nat_gt r with ⟨w,h⟩; refine ⟨w,?_⟩
  simpa only [mem_setOf_eq, Complex.norm_natCast]

/-- Characterization of `→ atInf` convergence -/
theorem tendsto_atInf {X Y : Type} [Norm Y] {f : X → Y} {l : Filter X} :
    Tendsto f l atInf ↔ ∀ r, ∀ᶠ x in l, r < ‖f x‖ := by
  rw [atInf_basis.tendsto_right_iff]; simp only [true_imp_iff, mem_setOf]

/-- Characterization of `atTop → atInf` convergence -/
theorem tendsto_atTop_atInf {X : Type} [Norm X] {f : ℕ → X} :
    Tendsto f atTop atInf ↔ ∀ r, ∃ N, ∀ n, N ≤ n → r < ‖f n‖ := by
  have h := Filter.HasBasis.tendsto_iff (f := f) Filter.atTop_basis atInf_basis
  simpa only [mem_Ici, ge_iff_le, mem_setOf_eq, exists_true_left, forall_true_left, true_and]
    using h

/-- `atInf` convergence in terms of norm convergence -/
theorem tendsto_atInf_iff_norm_tendsto_atTop {X Y : Type} [Norm Y] {f : Filter X} {g : X → Y} :
    Tendsto (fun x ↦ g x) f atInf ↔ Tendsto (fun x ↦ ‖g x‖) f atTop := by
  rw [Filter.atTop_basis_Ioi.tendsto_right_iff]
  simp only [atInf_basis.tendsto_right_iff, true_imp_iff, mem_setOf, mem_Ioi]

/-- Characterization of `s ∈ atInf` -/
theorem mem_atInf_iff {X : Type} [Norm X] {s : Set X} :
    s ∈ @atInf X _ ↔ ∃ r, {x | r < ‖x‖} ⊆ s := by
  simp only [Filter.hasBasis_iff.mp atInf_basis s, true_and]

/-- Eventually `atInf` the norm is as large as desired -/
theorem eventually_atInf {X : Type} [Norm X] (r : ℝ) : ∀ᶠ x : X in atInf, r < ‖x‖ := by
  rw [Filter.eventually_iff, mem_atInf_iff]; use r

/-- Eventually `atInf` is the same as eventually `𝓝[≠] 0` for `x⁻¹` -/
theorem eventually_atInf_iff_nhds_zero {𝕜 : Type} [NontriviallyNormedField 𝕜] {p : 𝕜 → Prop} :
    (∀ᶠ x in atInf, p x) ↔ ∀ᶠ x in 𝓝[≠] 0, p x⁻¹ := by
  rw [atInf_basis.eventually_iff, Metric.nhdsWithin_basis_ball.eventually_iff]
  constructor
  · intro ⟨r,_,h⟩
    refine ⟨(max r 1)⁻¹, by bound, fun x ⟨m,x0⟩ ↦ ?_⟩
    refine @h x⁻¹ ?_
    simp only [Metric.mem_ball, dist_zero_right, mem_compl_iff, mem_singleton_iff, mem_setOf_eq,
      norm_inv] at m x0 ⊢
    rw [← lt_inv_comm₀ (by bound) (by simpa)] at m
    exact lt_of_le_of_lt (le_max_left _ _) m
  · intro ⟨i,i0,h⟩
    refine ⟨i⁻¹, trivial, fun x m ↦ ?_⟩
    refine inv_inv x ▸ @h x⁻¹ ?_
    simp only [mem_setOf_eq, mem_inter_iff, Metric.mem_ball, dist_zero_right, norm_inv,
      mem_compl_iff, mem_singleton_iff, inv_eq_zero] at m ⊢
    have x0 : x ≠ 0 := by have : 0 < ‖x‖ := lt_trans (by bound) m; simpa
    rw [← inv_lt_comm₀ i0 (by simpa)]
    exact ⟨m, x0⟩

/-- Convergence `atInf` is the same as convergence at `0` for the reciprocal function -/
theorem tendsto_atInf_iff_tendsto_nhds_zero {𝕜 X : Type} [NontriviallyNormedField 𝕜] {l : Filter X}
    {f : 𝕜 → X} : Tendsto f atInf l ↔ Tendsto (fun x ↦ f x⁻¹) (𝓝[{0}ᶜ] 0) l := by
  rw [Filter.HasBasis.tendsto_left_iff atInf_basis, Metric.nhdsWithin_basis_ball.tendsto_left_iff]
  constructor
  · intro h t tl; rcases h t tl with ⟨r, _, m⟩
    by_cases rp : 0 < r
    · use r⁻¹; simp only [rp, inv_pos, true_and]; intro x xs; refine m ?_
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs
      simp only [← lt_inv_comm₀ (norm_pos_iff.mpr xs.2) rp, xs.1, mem_setOf_eq, norm_inv]
    · use 1; simp only [zero_lt_one, true_and]; intro x xs; refine m ?_
      simp only [mem_inter_iff, mem_ball_zero_iff, mem_compl_iff, mem_singleton_iff] at xs
      simp only [mem_setOf_eq, norm_inv]; simp only [not_lt] at rp
      exact lt_of_le_of_lt rp (inv_pos.mpr (norm_pos_iff.mpr xs.2))
  · intro h t tl; rcases h t tl with ⟨r, rp, m⟩; use r⁻¹; simp only [true_and]
    intro x xs; simp only [mem_setOf_eq] at xs
    have m := @m x⁻¹ ?_; · simp only [inv_inv] at m; exact m
    simp only [mem_inter_iff, mem_ball_zero_iff, norm_inv, mem_compl_iff, mem_singleton_iff,
      inv_eq_zero]
    have np : 0 < ‖x‖ := _root_.trans (inv_pos.mpr rp) xs
    simp [inv_lt_comm₀ np rp, xs, norm_pos_iff.mp np]

/-- Convergence to `atInf` implies `cocompact` convergence -/
theorem atInf_le_cocompact {X : Type} [NormedAddCommGroup X] : @atInf X _ ≤ Filter.cocompact X := by
  rw [Filter.le_def]; intro s m
  rcases Filter.mem_cocompact.mp m with ⟨t, tc, ts⟩
  rcases tc.bddAbove_image continuousOn_id.norm with ⟨r, rh⟩
  simp only [id_eq, mem_upperBounds, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at rh
  rw [mem_atInf_iff]; use r
  intro x m; apply ts; contrapose m
  simp only [mem_compl_iff, not_notMem] at m
  simp only [mem_setOf_eq, not_lt]
  exact rh _ m

/-- On proper spaces, `atInf = cocompact` -/
theorem atInf_eq_cocompact {X : Type} [NormedAddCommGroup X] [ProperSpace X] :
    @atInf X _ = Filter.cocompact X := by
  apply le_antisymm atInf_le_cocompact; rw [Filter.le_def]; intro s m
  rcases mem_atInf_iff.mp m with ⟨r, h⟩
  rw [Filter.mem_cocompact]; use closedBall 0 r, isCompact_closedBall _ _
  refine _root_.trans ?_ h; intro x xs
  simp only [mem_compl_iff, mem_closedBall_zero_iff, not_le] at xs; exact xs

/-- `⁻¹` tendsto `atInf` near `0` -/
theorem inv_tendsto_atInf {𝕜 : Type} [NontriviallyNormedField 𝕜] :
    Tendsto (fun x : 𝕜 ↦ x⁻¹) (𝓝[{(0 : 𝕜)}ᶜ] 0) atInf := by
  rw [←tendsto_atInf_iff_tendsto_nhds_zero (f := fun x : 𝕜 ↦ x)]; exact Filter.tendsto_id

/-- `⁻¹` tendsto `0` near `atInf` -/
theorem inv_tendsto_atInf' {𝕜 : Type} [NontriviallyNormedField 𝕜] :
    Tendsto (fun x : 𝕜 ↦ x⁻¹) atInf (𝓝 0) := by
  simp only [tendsto_atInf_iff_tendsto_nhds_zero, inv_inv]
  exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds

/-- We either tend to infinity or have a cluster point -/
lemma tendsto_atInf_or_mapClusterPt (f : α → ℂ) (l : Filter α) :
    Tendsto f l atInf ∨ ∃ z, MapClusterPt z l f := by
  by_cases t : Tendsto f l atInf
  · exact .inl t
  · simp only [t, false_or]
    simp only [tendsto_atInf, not_forall, Filter.not_eventually, not_lt,
      ← add_mem_closedBall_iff_norm (a := (0 : ℂ)), zero_add] at t
    obtain ⟨r,t⟩ := t
    have t := IsCompact.exists_mapClusterPt_of_frequently (isCompact_closedBall _ _) t
    obtain ⟨z,m,c⟩ := t
    exact ⟨z,c⟩

