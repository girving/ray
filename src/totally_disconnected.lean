-- Totally disconnected set facts

import data.real.basic
import data.real.cardinality
import set_theory.cardinal.basic
import topology.connected
import topology.metric_space.basic

open function (uncurry)
open metric (ball closed_ball mem_ball mem_closed_ball is_open_ball is_closed_ball mem_ball_self)
open set
open_locale topology
noncomputable theory

-- A left inverse to subtype coe
def set.nonempty.inv_coe {X : Type} {s : set X} (ne : s.nonempty) : X → s :=
  λ x, @dite _ (x ∈ s) (classical.dec _)
    (λ m, (⟨x,m⟩ : s)) (λ _, (⟨ne.some, ne.some_mem⟩ : s))
lemma set.nonempty.left_inv_coe {X : Type} {s : set X} (ne : s.nonempty) : ∀ x : s, ne.inv_coe x = x := begin
  rintros ⟨x,m⟩, simp only [set.nonempty.inv_coe, subtype.coe_mk, m, dif_pos],
end
lemma set.nonempty.right_inv_coe {X : Type} {s : set X} (ne : s.nonempty)
    : ∀ x, x ∈ s → ↑(ne.inv_coe x) = x := begin
  intros x m, simp only [set.nonempty.inv_coe, m, dif_pos, subtype.coe_mk],
end
lemma set.nonempty.continuous_on_inv_coe {X : Type} {s : set X} (ne : s.nonempty) [topological_space X]
    : continuous_on ne.inv_coe s := begin
  rw embedding_subtype_coe.continuous_on_iff, apply continuous_on_id.congr, intros x m,
  simp only [function.comp, ne.right_inv_coe _ m, id],
end

-- is_totally_disconnected is the same as totally_disconnected_space on the subtype
lemma is_totally_disconnected_iff_totally_disconnected_subtype {X : Type} [topological_space X] {s : set X}
    : totally_disconnected_space s ↔ is_totally_disconnected s := begin
  constructor, {
    intro h,
    by_cases ne : s.nonempty, {
      intros t ts tc,
      set t' := ne.inv_coe '' t,
      have tc' : is_preconnected t' := tc.image _ (ne.continuous_on_inv_coe.mono ts),
      have q := h.is_totally_disconnected_univ _ (subset_univ _) tc',
      have e : t = coe '' t', {
        apply set.ext, intros x, simp only [mem_image], constructor, {
          intro xt, use [⟨x,ts xt⟩, x, xt],
          simp only [subtype.ext_iff, subtype.coe_mk, ne.right_inv_coe _ (ts xt)], rw subtype.coe_mk,
        }, {
          rintros ⟨⟨y,ys⟩,⟨z,zt,zy⟩,yx⟩,
          simp only [subtype.coe_mk, subtype.ext_iff, ne.right_inv_coe _ (ts zt)] at yx zy,
          rw [←yx, ←zy], exact zt,
        },
      },
      rw e, exact q.image _,
    }, {
      simp only [not_nonempty_iff_eq_empty] at ne, rw ne, exact is_totally_disconnected_empty,
    }
  }, {
    intro h, refine ⟨_⟩, apply embedding_subtype_coe.is_totally_disconnected,
    rw subtype.coe_image_univ, exact h,
  },
end

-- Ioo is not countable if it is nonempty
lemma not_countable_Ioo {a b : ℝ} (h : a < b) : ¬(Ioo a b).countable := begin
  rw [←cardinal.le_aleph_0_iff_set_countable, not_le, cardinal.mk_Ioo_real h], apply cardinal.cantor,
end

-- Countable metric spaces are totally disconnected
lemma countable.totally_disconnected_space {X : Type} [metric_space X] [countable X]
    : totally_disconnected_space X := begin
  set R := {r | ∃ x y : X, dist x y = r},
  have rc : R.countable, {
    have e : R = range (uncurry dist), {
      apply set.ext, intro r, simp only [mem_set_of, mem_range, prod.exists, uncurry],
    },
    rw e, exact countable_range _,
  },
  refine ⟨_⟩, apply is_totally_disconnected_of_clopen_set, intros x y xy,
  rw [←dist_pos] at xy,
  have h : ¬Ioo 0 (dist x y) ⊆ R, { by_contradiction h, exact not_countable_Ioo xy (rc.mono h) }, 
  simp only [not_subset, mem_Ioo] at h, rcases h with ⟨r,⟨rp,rxy⟩,rr⟩,
  have e : ball x r = closed_ball x r, {
    apply set.ext, intros z, simp only [mem_ball, mem_closed_ball],
    simp only [mem_set_of, not_exists] at rr, simp only [ne.le_iff_lt (rr z x)],
  },
  use [ball x r, is_open_ball],
  rw e, exact is_closed_ball, use mem_ball_self rp,
  simp only [mem_ball, not_lt], rw dist_comm, exact le_of_lt rxy,
end

-- Countable sets are totally disconnected
lemma is_countable.is_totally_disconnected {X : Type} [metric_space X] {s : set X} (h : s.countable)
    : is_totally_disconnected s := begin
  rw ←is_totally_disconnected_iff_totally_disconnected_subtype,
  exact @countable.totally_disconnected_space _ _ (countable_coe_iff.mpr h),
end