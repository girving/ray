-- finset ℕ machinery for use in sums and products

import data.complex.basic
import data.finset.basic
import data.stream.defs
import order.filter.at_top_bot

open complex (abs)
open filter (at_top)
open_locale topology

-- Insert 0, adding 1 to existing elements
def push (N : finset ℕ) := insert 0 (finset.image (λ n, n + 1) N)

-- Subtract 1 from everything, discarding zero (left inverse of push)
def pop (N : finset ℕ) := finset.image (λ n, n - 1) (finset.erase N 0)

-- push almost cancels pop
lemma push_pop {N : finset ℕ} : push (pop N) = insert 0 N := begin
  rw [push, pop], apply finset.ext, simp,
  intro n, by_cases n0 : n = 0, { rw n0, simp },
  simp_rw or_iff_right n0,
  constructor, {
    intro h, rcases h with ⟨x,hx⟩,
    have c := nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr hx.left.left),
    rw c at hx, finish
  }, {
    intro h, existsi n,
    rw nat.sub_add_cancel (nat.one_le_iff_ne_zero.mpr n0),
    finish
  }
end

-- push is monotone
lemma push_le_push {A B : finset ℕ} : push A ≤ push B ↔ A ≤ B := begin
  simp, rw push, rw push, 
  constructor, {
    intro AB, rw finset.subset_iff at ⊢ AB, intros x xA,
    have h : x+1 ∈ insert 0 (finset.image (λ (n : ℕ), n + 1) A) := by simpa,
    specialize AB h, simp at AB, assumption
  }, {
    intro AB, apply finset.insert_subset_insert, apply finset.image_mono, assumption
  }
end

-- push and products interact nicely
lemma push_prod {a : ℂ} {f : ℕ → ℂ} {N : finset ℕ} : a * N.prod f = (push N).prod (a::f) :=
  by { rw push, simp, refl }

-- The range of push is finsets containing 0
lemma push_range : set.range push = {N : finset ℕ | 0 ∈ N} := begin
  rw set.range, apply set.ext, simp, intro N, constructor, {
    intro h, rcases h with ⟨M,H⟩, rw push at H, rw ←H, exact finset.mem_insert_self 0 _
  }, {
    intro N0, existsi pop N, rw push_pop, exact finset.insert_eq_of_mem N0
  }
end

lemma push_comap_at_top : filter.comap push at_top = at_top := begin
  apply filter.comap_embedding_at_top,
  exact @push_le_push,
  intro N, existsi pop N, rw push_pop, simp, exact finset.subset_insert _ _
end

-- f ∘ push converges at_top iff f does
lemma tendsto_comp_push {A : Type} {f : finset ℕ → A} {l : filter A}
    : filter.tendsto (f ∘ push) at_top l ↔ filter.tendsto f at_top l := begin
  nth_rewrite 0 ←push_comap_at_top, apply filter.tendsto_comap'_iff,
  rw push_range,
  have h : {N : finset ℕ | 0 ∈ N} = {N : finset ℕ | {0} ≤ N} := by simp,
  rw h, exact filter.mem_at_top _
end

lemma finset_complex_abs_sum_le (N : finset ℕ) (f : ℕ → ℂ)
    : abs (N.sum (λ n, f n)) ≤ N.sum (λ n, abs (f n)) :=
begin
  induction N using finset.induction with n N Nn h, {
    simp
  }, {
    rw finset.sum_insert Nn,
    rw finset.sum_insert Nn,
    transitivity abs (f n) + abs (N.sum (λ n, f n)), {
      exact complex.abs.add_le _ _
    }, {
      apply add_le_add_left, assumption
    }
  }
end

lemma subset_union_sdiff (A B : finset ℕ) : B ⊆ A ∪ B \ A := begin
  rw finset.subset_iff, intros x Bx,
  rw [finset.mem_union, finset.mem_sdiff],
  finish
end
