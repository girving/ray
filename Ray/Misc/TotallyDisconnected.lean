import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
## Countable sets and space are totally disconnected
-/

open Classical
open Function (uncurry)
open Metric (ball closedBall mem_ball mem_closedBall isOpen_ball isClosed_ball mem_ball_self)
open Set
open scoped Topology
noncomputable section

/-- A left inverse to subtype coe -/
def Set.Nonempty.invCoe {X : Type} {s : Set X} (ne : s.Nonempty) : X → s := fun x ↦
  if m : x ∈ s then (⟨x, m⟩ : s) else (⟨ne.some, ne.some_mem⟩ : s)

theorem Set.Nonempty.left_invCoe {X : Type} {s : Set X} (ne : s.Nonempty) :
    ∀ x : s, ne.invCoe x = x := by
  intro ⟨x, m⟩; simp only [Set.Nonempty.invCoe, Subtype.coe_mk, m, dif_pos]

theorem Set.Nonempty.right_invCoe {X : Type} {s : Set X} (ne : s.Nonempty) :
    ∀ x, x ∈ s → ↑(ne.invCoe x) = x := by
  intro x m; simp only [Set.Nonempty.invCoe, m, dif_pos, Subtype.coe_mk]

theorem Set.Nonempty.continuousOn_invCoe {X : Type} {s : Set X} (ne : s.Nonempty)
    [TopologicalSpace X] : ContinuousOn ne.invCoe s := by
  rw [embedding_subtype_val.continuousOn_iff]; apply continuousOn_id.congr; intro x m
  simp only [Function.comp, ne.right_invCoe _ m, id]

/-- `IsTotallyDisconnected` is the same as `TotallyDisconnectedSpace` on the subtype -/
theorem isTotallyDisconnected_iff_totally_disconnected_subtype {X : Type} [TopologicalSpace X]
    {s : Set X} : TotallyDisconnectedSpace s ↔ IsTotallyDisconnected s := by
  constructor
  · intro h
    by_cases ne : s.Nonempty
    · intro t ts tc
      set t' := ne.invCoe '' t
      have tc' : IsPreconnected t' := tc.image _ (ne.continuousOn_invCoe.mono ts)
      have q := h.isTotallyDisconnected_univ _ (subset_univ _) tc'
      have e : t = (fun x : s ↦ x.val) '' t' := by
        apply Set.ext; intro x; simp only [mem_image]; constructor
        · intro xt; use ⟨x, ts xt⟩; refine ⟨⟨x,xt,?_⟩,?_⟩
          simp only [Subtype.ext_iff, Subtype.coe_mk, ne.right_invCoe _ (ts xt)]
          rw [Subtype.coe_mk]
        · intro ⟨⟨y, ys⟩, ⟨z, zt, zy⟩, yx⟩
          simp only [Subtype.coe_mk, Subtype.ext_iff, ne.right_invCoe _ (ts zt)] at yx zy
          rw [← yx, ← zy]; exact zt
      rw [e]; exact q.image _
    · simp only [not_nonempty_iff_eq_empty] at ne; rw [ne]; exact isTotallyDisconnected_empty
  · intro h; refine ⟨?_⟩; apply embedding_subtype_val.isTotallyDisconnected
    rw [Subtype.coe_image_univ]; exact h

/-- `Ioo` on the reals is not countable if it is nonempty -/
theorem not_countable_Ioo {a b : ℝ} (h : a < b) : ¬(Ioo a b).Countable := by
  rw [← Cardinal.le_aleph0_iff_set_countable, not_le, Cardinal.mk_Ioo_real h]; apply Cardinal.cantor

/-- Countable metric spaces are totally disconnected -/
theorem Countable.totallyDisconnectedSpace {X : Type} [MetricSpace X] [Countable X] :
    TotallyDisconnectedSpace X := by
  set R := {r | ∃ x y : X, dist x y = r}
  have rc : R.Countable := by
    have e : R = range (uncurry dist) := by
      apply Set.ext; intro r; simp only [mem_setOf, mem_range, Prod.exists, uncurry]; rfl
    rw [e]; exact countable_range _
  refine ⟨?_⟩; apply isTotallyDisconnected_of_isClopen_set; intro x y xy
  rw [← dist_pos] at xy
  have h : ¬Ioo 0 (dist x y) ⊆ R := by by_contra h; exact not_countable_Ioo xy (rc.mono h)
  simp only [not_subset, mem_Ioo] at h; rcases h with ⟨r, ⟨rp, rxy⟩, rr⟩
  have e : ball x r = closedBall x r := by
    apply Set.ext; intro z; simp only [mem_ball, mem_closedBall]
    simp only [mem_setOf, not_exists] at rr; simp only [Ne.le_iff_lt (rr z x)]
  refine ⟨ball x r, ⟨?_, isOpen_ball⟩, ?_⟩
  rw [e]; exact isClosed_ball; use mem_ball_self rp
  simp only [mem_ball, not_lt]; rw [dist_comm]; exact rxy.le

/-- Countable sets are totally disconnected -/
theorem IsCountable.isTotallyDisconnected {X : Type} [MetricSpace X] {s : Set X} (h : s.Countable) :
    IsTotallyDisconnected s := by
  rw [← isTotallyDisconnected_iff_totally_disconnected_subtype]
  exact @Countable.totallyDisconnectedSpace _ _ (countable_coe_iff.mpr h)
