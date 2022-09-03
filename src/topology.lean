-- Topology facts about ℂ

import data.complex.basic
import data.real.basic
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import topology.metric_space.basic

import simple
import tactics

open metric (ball closed_ball)
open filter (at_top)
open_locale real nnreal topological_space

noncomputable theory

lemma open_has_cball {s : set ℂ} (o : is_open s) (z ∈ s) : ∃ r : ℝ≥0, r > 0 ∧ closed_ball z r ⊆ s := begin
  rw metric.is_open_iff at o,
  have oz := o z H,
  rcases oz with ⟨t,ht,bs⟩,
  set r : ℝ≥0 := (t / 2).to_nnreal,
  existsi r,
  split,
  refine real.to_nnreal_pos.mp _,
  simp, linarith,
  calc closed_ball z r ⊆ ball z t : metric.closed_ball_subset_ball _
  ... ⊆ s : bs,
  calc ↑r = t/2 : real.coe_to_nnreal (t/2) (by linarith)
  ... < t : by bound
end

lemma nhd_has_ball {z : ℂ} {s : set ℂ} (h : s ∈ 𝓝 z) : ∃ r, r > 0 ∧ metric.ball z r ⊆ s := begin
  rcases mem_nhds_iff.mp h with ⟨so,os,iso,zso⟩,
  rcases metric.is_open_iff.mp iso z zso with ⟨r,rp,rb⟩,
  existsi r, constructor, assumption,
  transitivity so, assumption, assumption
end

-- If something is true near c, it is true at c
lemma filter.eventually.self {A : Type} [topological_space A] {p : A → Prop} {x : A}
    (h : ∀ᶠ y in nhds x, p y) : p x := begin
  rcases eventually_nhds_iff.mp h with ⟨s,ps,_,xs⟩,
  exact ps x xs,
end

-- Continuous functions achieve their supremum on compact sets
lemma continuous_on.compact_max {A B : Type} [topological_space A] [topological_space B]
    [conditionally_complete_linear_order B] [order_topology B]
    {f : A → B} {s : set A} (fc : continuous_on f s) (cs : is_compact s) (sn : s.nonempty)
    : ∃ x, x ∈ s ∧ is_max_on f s x := begin
  have ic := is_compact.image_of_continuous_on cs fc,
  have ss := is_compact.Sup_mem ic (set.nonempty_image_iff.mpr sn),
  rcases (set.mem_image _ _ _).mp ss with ⟨x,xs,xm⟩,
  existsi [x, xs],
  rw is_max_on_iff, intros y ys, rw xm,
  exact le_cSup ic.bdd_above ((set.mem_image _ _ _).mpr ⟨y,ys,rfl⟩),
end

-- Continuous functions on compact sets are bounded
lemma continuous_on.bounded {X : Type} [topological_space X]
    {f : X → ℝ} {s : set X} (fc : continuous_on f s) (sc : is_compact s)
    : ∃ b : ℝ, b ≥ 0 ∧ ∀ x, x ∈ s → f x ≤ b := begin
  by_cases n : s.nonempty, {
    rcases fc.compact_max sc n with ⟨x,xs,xm⟩,
    use [max 0 (f x), by bound], intros y ys, exact trans (xm ys) (by bound),
  }, {
    rw set.not_nonempty_iff_eq_empty at n,
    existsi [(0 : ℝ), le_refl _], simp [n],
  },
end  

-- Continuous functions on compact sets have bounded norm
lemma continuous_on.bounded_norm {X Y : Type} [topological_space X] [normed_add_comm_group Y]
    {f : X → Y} {s : set X} (fc : continuous_on f s) (sc : is_compact s)
    : ∃ b : ℝ, b ≥ 0 ∧ ∀ x, x ∈ s → ∥f x∥ ≤ b := begin
  by_cases n : s.nonempty, {
    have nc : continuous_on (λ x, ∥f x∥) s := continuous_norm.comp_continuous_on fc,
    rcases nc.compact_max sc n with ⟨x,xs,xm⟩,
    existsi [∥f x∥, norm_nonneg _], intros y ys, exact xm ys,
  }, {
    rw set.not_nonempty_iff_eq_empty at n,
    existsi [(0 : ℝ), le_refl _], simp [n],
  }
end  

-- Uniform cauchy sequences are cauchy sequences at points
lemma uniform_cauchy_seq_on.cauchy_seq {X Y : Type} [topological_space X] [metric_space Y]
    {f : ℕ → X → Y} {s : set X} (u : uniform_cauchy_seq_on f at_top s)
    : ∀ x, x ∈ s → cauchy_seq (λ n, f n x) := begin
  intros x xs,
  rw metric.cauchy_seq_iff,
  rw metric.uniform_cauchy_seq_on_iff at u,
  intros e ep, rcases u e ep with ⟨N,H⟩,
  existsi N, intros a aN b bN,
  exact H a aN b bN x xs,
end

-- Uniform cauchy sequences on compact sets are uniformly bounded
lemma uniform_cauchy_seq_on.bounded {X Y : Type} [topological_space X] [normed_add_comm_group Y]
    {f : ℕ → X → Y} {s : set X} (u : uniform_cauchy_seq_on f at_top s) (fc : ∀ n, continuous_on (f n) s) (sc : is_compact s)
    : ∃ b : ℝ, b ≥ 0 ∧ ∀ n x, x ∈ s → ∥f n x∥ ≤ b := begin
  set c := λ n, classical.some ((fc n).bounded_norm sc),
  have cs : ∀ n, 0 ≤ c n ∧ ∀ x, x ∈ s → ∥f n x∥ ≤ c n := λ n, classical.some_spec ((fc n).bounded_norm sc),
  rw metric.uniform_cauchy_seq_on_iff at u,
  rcases u 1 (by norm_num) with ⟨N,H⟩, clear u,
  set bs := finset.image c (finset.range (N+1)),
  have c0 : c 0 ∈ bs, { simp, existsi 0, simp },
  set b := 1 + bs.max' ⟨_,c0⟩,
  existsi b, constructor, {
    bound [trans (cs 0).1 (finset.le_max' _ _ c0)],
  }, {
    intros n x xs,
    by_cases nN : n ≤ N, {
      have cn : c n ∈ bs, { simp, existsi n, simp [nat.lt_add_one_iff.mpr nN] },
      exact trans ((cs n).2 x xs) (trans (finset.le_max' _ _ cn) (by bound)),
    }, {
      simp at nN,
      specialize H N (by bound) n (by bound) x xs,
      have cN : c N ∈ bs, { simp, existsi N, simp },
      have bN := trans ((cs N).2 x xs) (finset.le_max' _ _ cN),
      rw dist_eq_norm at H,
      calc ∥f n x∥ = ∥f N x - (f N x - f n x)∥ : by abel
      ... ≤ ∥f N x∥ + ∥f N x - f n x∥ : by bound
      ... ≤ bs.max' _ + 1 : by bound
      ... = 1 + bs.max' _ : by abel
      ... = b : rfl,
    }
  },
end

-- Functions from empty spaces are continuous
lemma is_empty.continuous {A B : Type} [topological_space A] [topological_space B]
    [is_empty A] (f : A → B) : continuous f := begin
  rw continuous_def, intros s o,
  have e : f ⁻¹' s = ∅, { apply set.subset_eq_empty (set.subset_univ _), simp, apply_instance },
  simp [e],
end