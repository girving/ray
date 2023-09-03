-- Topology facts

import data.complex.basic
import data.real.basic
import data.real.nnreal
import data.real.pi.bounds
import data.set.basic
import topology.metric_space.basic
import topology.semicontinuous

import tactics

open metric (ball closed_ball sphere mem_sphere mem_ball)
open filter (at_top tendsto eventually_of_forall)
open function (uncurry)
open order_dual (of_dual to_dual)
open set
open_locale real nnreal topology
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
    (h : ∀ᶠ y in 𝓝 x, p y) : p x := begin
  rcases eventually_nhds_iff.mp h with ⟨s,ps,_,xs⟩, exact ps x xs,
end

-- If something is true near a set, it is true on the set
lemma filter.eventually.self_set {A : Type} [topological_space A] {p : A → Prop} {s : set A}
    (h : ∀ᶠ y in 𝓝ˢ s, p y) : ∀ y, y ∈ s → p y := begin
  rcases mem_nhds_set_iff_exists.mp h with ⟨t,ot,st,tp⟩, exact λ _ m, tp (st m),
end

-- is_open s → s ∈ 𝓝ˢ s
lemma mem_nhds_set_self {X : Type} [topological_space X] {s : set X} (o : is_open s) : s ∈ 𝓝ˢ s :=
  o.mem_nhds_set.mpr (subset_refl _) 

-- Turn s ⊆ set_of_p back into a clean forall
lemma subset_set_of {X : Type} {p : X → Prop} {s : set X} : s ⊆ set_of p ↔ ∀ x, x ∈ s → p x := begin
  constructor, intros sub x m, exact sub m, intros sub x m, simp only [mem_set_of], exact sub _ m,
end

-- 𝓝ˢ members must include the set 
lemma subset_of_nhds_set {X : Type} [topological_space X] {s t : set X} (m : s ∈ 𝓝ˢ t) : t ⊆ s :=
  λ x n, mem_of_mem_nhds (nhds_le_nhds_set n m)

-- 𝓝ˢ equivalents of eventually_nhds_iff
lemma eventually_nhds_set_iff {X : Type} [topological_space X] {s : set X} {p : X → Prop}
    : (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∃ t, is_open t ∧ s ⊆ t ∧ ∀ x, x ∈ t → p x :=
  by simp only [filter.eventually_iff, mem_nhds_set_iff_exists, subset_set_of]
lemma eventually_nhds_set_iff_forall {X : Type} [topological_space X] {s : set X} {p : X → Prop}
    : (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, p y :=
  by simp only [filter.eventually_iff, mem_nhds_set_iff_forall, subset_set_of]

-- 𝓝ˢ factors for compact sets
lemma nhds_set_prod {X Y : Type} [topological_space X] [topological_space Y] {s : set X} {t : set Y}
    (sc : is_compact s) (tc : is_compact t) : 𝓝ˢ (s ×ˢ t) = (𝓝ˢ s).prod (𝓝ˢ t) := begin
  apply le_antisymm, {
    intros u m, rw mem_nhds_set_iff_forall, rintros ⟨x,y⟩ ⟨xs,yt⟩,
    simp only [nhds_prod_eq], exact filter.prod_mono (nhds_le_nhds_set xs) (nhds_le_nhds_set yt) m,
  }, {
    intros u m, rw mem_nhds_set_iff_forall at m,
    apply sc.induction_on, {
      simp only [nhds_set_empty, filter.bot_prod],
    }, {
      intros s0 s1 sub m, exact filter.prod_mono_left _ (nhds_set_mono sub) m,
    }, {
      intros s0 s1 m0 m1, simp only [nhds_set_union, filter.sup_prod], exact filter.mem_sup.mpr ⟨m0,m1⟩,
    }, {
      intros x xs, apply tc.induction_on, {
        use [univ, filter.univ_mem], simp only [nhds_set_empty, filter.prod_bot],
      }, {
        rintros t0 t1 sub ⟨s,n,m⟩, use [s, n, filter.prod_mono_right _ (nhds_set_mono sub) m],
      }, {
        rintros t0 t1 ⟨s0,n0,m0⟩ ⟨s1,n1,m1⟩, use [s0 ∩ s1, filter.inter_mem n0 n1],
        simp only [nhds_set_union, filter.prod_sup], refine filter.mem_sup.mpr ⟨_,_⟩, 
        exact filter.prod_mono_left _ (nhds_set_mono (inter_subset_left _ _)) m0,
        exact filter.prod_mono_left _ (nhds_set_mono (inter_subset_right _ _)) m1,
      }, {
        intros y yt, specialize m ⟨x,y⟩ ⟨xs,yt⟩,
        rcases mem_nhds_prod_iff'.mp m with ⟨p,q,po,xp,qo,yq,sub⟩,
        use [q, nhds_within_le_nhds (qo.mem_nhds yq), p, nhds_within_le_nhds (po.mem_nhds xp),
          filter.mem_of_superset (filter.prod_mem_prod (mem_nhds_set_self po) (mem_nhds_set_self qo)) sub],
      },
    }
  }
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

-- Continuous functions achieve their infimum on compact sets
lemma continuous_on.compact_min {A B : Type} [topological_space A] [topological_space B]
    [conditionally_complete_linear_order B] [order_topology B]
    {f : A → B} {s : set A} (fc : continuous_on f s) (cs : is_compact s) (sn : s.nonempty)
    : ∃ x, x ∈ s ∧ is_min_on f s x := begin
  set g : A → Bᵒᵈ := λ x, f x,
  have gc : continuous_on g s := fc,
  exact gc.compact_max cs sn,
end

-- Continuous functions on compact sets are bounded above
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
    : ∃ b : ℝ, b ≥ 0 ∧ ∀ x, x ∈ s → ‖f x‖ ≤ b := begin
  by_cases n : s.nonempty, {
    have nc : continuous_on (λ x, ‖f x‖) s := continuous_norm.comp_continuous_on fc,
    rcases nc.compact_max sc n with ⟨x,xs,xm⟩,
    existsi [‖f x‖, norm_nonneg _], intros y ys, exact xm ys,
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
    : ∃ b : ℝ, b ≥ 0 ∧ ∀ n x, x ∈ s → ‖f n x‖ ≤ b := begin
  set c := λ n, classical.some ((fc n).bounded_norm sc),
  have cs : ∀ n, 0 ≤ c n ∧ ∀ x, x ∈ s → ‖f n x‖ ≤ c n := λ n, classical.some_spec ((fc n).bounded_norm sc),
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
      calc ‖f n x‖ = ‖f N x - (f N x - f n x)‖ : by abel
      ... ≤ ‖f N x‖ + ‖f N x - f n x‖ : by bound
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

-- {b | (a,b) ∈ s} is open if s is open
lemma is_open.snd_preimage {A B : Type} [topological_space A] [topological_space B] {s : set (A × B)}
    (o : is_open s) (a : A) : is_open {b | (a,b) ∈ s} := begin
  rw is_open_iff_mem_nhds, intros b m, simp only [set.mem_set_of_eq] at m,
  rcases mem_nhds_prod_iff.mp (o.mem_nhds m) with ⟨u,un,v,vn,uv⟩,
  apply filter.mem_of_superset vn,
  intros b bv, apply uv, simp only [mem_of_mem_nhds un, bv, set.prod_mk_mem_set_prod_eq, and_self],
end

-- {b | (a,b) ∈ s} is closed if s is closed
lemma is_closed.snd_preimage {A B : Type} [topological_space A] [topological_space B] {s : set (A × B)}
    (c : is_closed s) (a : A) : is_closed {b | (a,b) ∈ s} := begin
  simp only [←is_open_compl_iff, compl_set_of] at c ⊢, exact c.snd_preimage _,
end

-- Rewriting for tendsto and ⁻¹
lemma tendsto_iff_tendsto_inv {A B : Type} [topological_space A] [nontrivially_normed_field B]
    {l : filter A} {f : A → B} {a : B} (a0 : a ≠ 0) : tendsto (λ x, (f x)⁻¹) l (𝓝 a⁻¹) ↔ tendsto f l (𝓝 a) := begin
  refine ⟨λ h, _, λ h, h.inv₀ a0⟩,
  have h := h.inv₀ (inv_ne_zero a0),
  field_simp [a0] at h, exact h,
end

-- continuous_at in terms of 𝓝[{x}ᶜ] x
lemma continuous_at_iff_tendsto_nhds_within {A B : Type} [topological_space A] [topological_space B]
    {f : A → B} {x : A} : continuous_at f x ↔ tendsto f (𝓝[{x}ᶜ] x) (𝓝 (f x)) := begin
  rw continuous_at, constructor,
  exact λ t, t.mono_left nhds_within_le_nhds,
  intro t, rw ←nhds_within_compl_singleton_sup_pure,
  exact filter.tendsto.sup t (tendsto_pure_nhds _ _),
end

-- Analogue of continuous_at.prod for continuous
theorem continuous.prod {A B C : Type} [topological_space A] [topological_space B] [topological_space C]
    {f : A → B} {g : A → C} (fc : continuous f) (gc : continuous g) : continuous (λ x, (f x, g x)) :=
  continuous_id.comp₂ fc gc

-- Similar to is_open.eventually_mem, but assuming only continuous_at
theorem continuous_at.eventually_mem {A B : Type} [topological_space A] [topological_space B]
    {f : A → B} {x : A} (fc : continuous_at f x) {s : set B} (o : is_open s) (m : f x ∈ s)
    : ∀ᶠ y in 𝓝 x, f y ∈ s := begin
  rw [continuous_at, ←is_open.nhds_within_eq o m] at fc,
  exact eventually_mem_of_tendsto_nhds_within fc,
end

-- Similar to continuous_at.eventually_mem, but assuming s ∈ 𝓝 (f x), not is_open s
theorem continuous_at.eventually_mem_nhd {A B : Type} [topological_space A] [topological_space B]
    {f : A → B} {x : A} (fc : continuous_at f x) {s : set B} (m : s ∈ 𝓝 (f x))
    : ∀ᶠ y in 𝓝 x, f y ∈ s := begin
  rw ←mem_interior_iff_mem_nhds at m,
  exact (fc.eventually_mem is_open_interior m).mp (eventually_of_forall (λ y i, @interior_subset _ _ s _ i)),
end

-- continuous_at.comp and comp_of_eq for curried functions
theorem continuous_at.curry_comp {A B C D : Type} [topological_space A] [topological_space B]
    [topological_space C] [topological_space D] {f : B → C → D} {g : A → B} {h : A → C} {x : A}
    (fc : continuous_at (uncurry f) (g x, h x)) (gc : continuous_at g x) (hc : continuous_at h x)
    : continuous_at (λ x, f (g x) (h x)) x := begin
  have e : (λ x, f (g x) (h x)) = uncurry f ∘ (λ x, (g x, h x)) := rfl,
  rw e, exact continuous_at.comp fc (gc.prod hc),
end
theorem continuous_at.curry_comp_of_eq {A B C D : Type} [topological_space A] [topological_space B]
    [topological_space C] [topological_space D] {f : B → C → D} {g : A → B} {h : A → C} {x : A} {y : B × C}
    (fc : continuous_at (uncurry f) y) (gc : continuous_at g x) (hc : continuous_at h x) (e : (g x, h x) = y)
    : continuous_at (λ x, f (g x) (h x)) x := begin
  rw ←e at fc, exact fc.curry_comp gc hc,
end

-- The above, but composing with continuous_within_at
theorem continuous_at.curry_comp_continuous_within_at {A B C D : Type} [topological_space A] [topological_space B]
    [topological_space C] [topological_space D] {f : B → C → D} {g : A → B} {h : A → C} {x : A} {s : set A}
    (fc : continuous_at (uncurry f) (g x, h x)) (gc : continuous_within_at g s x) (hc : continuous_within_at h s x)
    : continuous_within_at (λ x, f (g x) (h x)) s x := begin
  have e : (λ x, f (g x) (h x)) = uncurry f ∘ (λ x, (g x, h x)) := rfl,
  rw e, exact continuous_at.comp_continuous_within_at fc (gc.prod hc),
end
theorem continuous_at.curry_comp_continuous_within_at_of_eq {A B C D : Type}
    [topological_space A] [topological_space B] [topological_space C] [topological_space D]
    {f : B → C → D} {g : A → B} {h : A → C} {x : A} {s : set A} {y : B × C}
    (fc : continuous_at (uncurry f) y) (gc : continuous_within_at g s x) (hc : continuous_within_at h s x)
    (e : (g x, h x) = y)
    : continuous_within_at (λ x, f (g x) (h x)) s x := begin
  rw ←e at fc, exact fc.curry_comp_continuous_within_at gc hc,
end

-- continuous.comp for curried functions
theorem continuous.curry_comp {A B C D : Type} [topological_space A] [topological_space B]
    [topological_space C] [topological_space D] {f : B → C → D} {g : A → B} {h : A → C}
    (fc : continuous (uncurry f)) (gc : continuous g) (hc : continuous h) : continuous (λ x, f (g x) (h x)) := begin
  have e : (λ x, f (g x) (h x)) = uncurry f ∘ (λ x, (g x, h x)) := rfl,
  rw e, exact fc.comp (gc.prod hc),
end

-- Curried continuous functions are continuous in each argument
theorem continuous.in1 {A B C : Type} [topological_space A] [topological_space B] [topological_space C]
    {f : A → B → C} (fc : continuous (uncurry f)) {b : B} : continuous (λ a, f a b) :=
  fc.comp (continuous_id.prod continuous_const)
theorem continuous.in2 {A B C : Type} [topological_space A] [topological_space B] [topological_space C]
    {f : A → B → C} (fc : continuous (uncurry f)) {a : A} : continuous (λ b, f a b) :=
  fc.comp (continuous_const.prod continuous_id)

-- In a compact space, exactly one limit point implies tendsto
lemma le_nhds_of_cluster_pt_unique {A : Type} [topological_space A] [compact_space A]
    {l : filter A} [l.ne_bot] {y : A} (u : ∀ x, cluster_pt x l → x = y) : l ≤ 𝓝 y := begin
  contrapose u, simp only [not_forall, exists_prop],
  rcases filter.not_tendsto_iff_exists_frequently_nmem.mp u with ⟨s,sl,h⟩, clear u,
  rcases mem_nhds_iff.mp sl with ⟨t,ts,ot,yt⟩, clear sl,
  have ne : (l ⊓ filter.principal tᶜ).ne_bot, {
    rw filter.inf_principal_ne_bot_iff, intros u ul,
    rcases filter.frequently_iff.mp h ul with ⟨x,xu,xs⟩,
    use x, rw [set.mem_inter_iff, set.mem_compl_iff], use [xu, set.not_mem_subset ts xs],
  },
  rcases @cluster_point_of_compact _ _ _ _ ne with ⟨x,⟨cp⟩⟩,
  simp only [cluster_pt, filter.ne_bot_iff, ←bot_lt_iff_ne_bot, ←inf_assoc] at cp ⊢,
  use [x, lt_of_lt_of_le cp inf_le_left],
  simp only [@inf_comm _ _ _ l, inf_assoc] at cp,
  have xt := lt_of_lt_of_le cp inf_le_right,
  simp only [bot_lt_iff_ne_bot, ←mem_closure_iff_nhds_ne_bot, ot.is_closed_compl.closure_eq] at xt,
  contrapose xt, simp only [not_not] at xt, simp only [set.not_mem_compl_iff, xt, yt],
end
lemma tendsto_of_cluster_pt_unique {A B : Type} [topological_space A] [topological_space B] [compact_space B]
    {l : filter A} [ln : l.ne_bot] {f : A → B}  {y : B} (u : ∀ x, map_cluster_pt x l f → x = y)
    : tendsto f l (𝓝 y) := le_nhds_of_cluster_pt_unique u

-- Continuous images of compact closures are closures of images
lemma continuous.image_compact_closure {A B : Type} [topological_space A] [topological_space B] [t2_space B]
    {f : A → B} {s : set A} (fc : continuous f) (sc : is_compact (closure s))
    : f '' closure s = closure (f '' s) := begin
  apply subset_antisymm (image_closure_subset_closure_image fc),
  rw ←(sc.image fc).is_closed.closure_eq, exact closure_mono (set.image_subset _ (subset_closure)),
end

-- The reverse direction of is_closed.Icc_subset_of_forall_mem_nhds_within
lemma is_closed.Icc_subset_of_forall_mem_nhds_within' {X : Type} [conditionally_complete_linear_order X]
    [topological_space X] [order_topology X] [densely_ordered X] {a b : X} {s : set X}
    (sc : is_closed (s ∩ Icc a b)) (sb : b ∈ s) (so : ∀ x, x ∈ s ∩ Ioc a b → s ∈ 𝓝[Iio x] x) :
    Icc a b ⊆ s := begin
  set s' := of_dual ⁻¹' s,
  have rev : Icc (to_dual b) (to_dual a) ⊆ s', {
    apply is_closed.Icc_subset_of_forall_mem_nhds_within, {
      have e : s' ∩ Icc (to_dual b) (to_dual a) = of_dual ⁻¹' (s ∩ Icc a b), {
        apply set.ext, intro x, simp only [set.dual_Icc, set.preimage_inter],
      },
      rw e, exact is_closed.preimage continuous_of_dual sc,
    }, {
      simp only [set.mem_preimage, order_dual.of_dual_to_dual, sb],
    }, {
      intros x m,
      simp only [set.mem_preimage, set.mem_inter_iff, set.mem_Ico,
        order_dual.to_dual_le, order_dual.lt_to_dual] at m,
      simp only [mem_nhds_within_iff_eventually, eventually_nhds_iff, set.mem_inter_iff, set.mem_Ioc] at ⊢ so,
      rcases so (of_dual x) ⟨m.1, m.2.2, m.2.1⟩ with ⟨n,h,o,nx⟩,
      use of_dual ⁻¹' n,
      refine ⟨_, o.preimage continuous_of_dual, set.mem_preimage.mpr nx⟩,
      intros y m xy, simp only [set.mem_Ioi] at xy, simp only [set.mem_preimage],
      simp only [set.mem_Iio, set.mem_preimage, order_dual.of_dual_lt_of_dual] at h,
      exact h _ m xy,
    },
  },
  intros x m, simp only [set.mem_Icc] at m, specialize @rev (to_dual x),
  simp only [set.dual_Icc, set.mem_preimage, set.mem_Icc, and_imp, order_dual.of_dual_to_dual] at rev,
  exact rev m.1 m.2,
end

-- fst is a closed map if B is compact
lemma is_closed_map.fst {A B : Type} [topological_space A] [topological_space B] [compact_space B]
    : is_closed_map (λ p : A × B, p.1) := begin
  intros s h, simp only [←is_open_compl_iff, is_open_iff_eventually] at h ⊢, intros x m,
  simp only [mem_compl_iff, mem_image, prod.exists, exists_and_distrib_right, exists_eq_right, not_exists] at m ⊢,
  generalize hp : (λ t : set B, ∀ᶠ x' in 𝓝 x, ∀ y, y ∈ t → (x',y) ∉ s) = p,
  suffices q : p univ, rw ←hp at q, exact q.mp (eventually_of_forall (λ x' i y, i y (mem_univ y))),
  refine is_compact_univ.induction_on _ _ _ _, {
    simp_rw [←hp, not_mem_empty, false_implies_iff, implies_true_iff, filter.eventually_true],
  }, {
    intros u v uv pv, rw ←hp at pv ⊢, exact pv.mp (eventually_of_forall (λ x' pv y yu, pv y (uv yu))),
  }, {
    intros u v pu pv, rw ←hp at pu pv ⊢, refine pu.mp (pv.mp (eventually_of_forall (λ x' pv pu y yuv, _))),
    cases (mem_union _ _ _).mp yuv with yu yv, exact pu y yu, exact pv y yv,
  }, {
    intros y yu, specialize h (x,y) (m y),
    rcases (filter.has_basis.prod_nhds (nhds_basis_opens x) (nhds_basis_opens y)).eventually_iff.mp h
      with ⟨⟨ta,tb⟩,⟨⟨xta,ota⟩,⟨ytb,otb⟩⟩,h⟩,
    simp only [nhds_within_univ, ←hp, eventually_nhds_iff],
    refine ⟨tb, otb.mem_nhds ytb, ta, _, ota, xta⟩,
    intros x' xta' y' ytb', exact h (mk_mem_prod xta' ytb'),
  },
end

-- Open connected sets form a basis for 𝓝ˢ t in any locally connected space, if t is connected
lemma local_connected_nhds_set {X : Type} [topological_space X] [lc : locally_connected_space X]
    {s t : set X} (tc : is_connected t) (st : s ∈ 𝓝ˢ t)
    : ∃ c, is_open c ∧ t ⊆ c ∧ c ⊆ s ∧ is_connected c := begin
  have h' : ∀ x : t, ∃ c, is_open c ∧ x.val ∈ c ∧ c ⊆ s ∧ is_connected c, {
    rintros ⟨x,m⟩,
    rcases locally_connected_space_iff_open_connected_subsets.mp lc x s (mem_nhds_set_iff_forall.mp st _ m)
      with ⟨c,cs,oc,xc,cc⟩,
    use [c, oc, xc, cs, cc],
  },
  generalize hc : (λ x : t, classical.some (h' x)) = c,
  have h : ∀ x : t, is_open (c x) ∧ x.val ∈ c x ∧ c x ⊆ s ∧ is_connected (c x), {
    rw ←hc, intro x, exact classical.some_spec (h' x),
  },
  clear hc h',
  rcases tc.nonempty with ⟨b,bt⟩,
  use ⋃ x, c x, refine ⟨_,_,_,_,_⟩, {
    exact is_open_Union (λ x, (h x).1),
  }, {
    exact λ x m, mem_Union.mpr ⟨⟨x,m⟩,(h ⟨x,m⟩).2.1⟩,
  }, {
    exact Union_subset (λ x, (h x).2.2.1),
  }, {
    use [b, mem_Union_of_mem ⟨b,bt⟩ (h ⟨b,bt⟩).2.1],
  }, {
    have e : (⋃ x, c x) = (⋃ x, c x ∪ t), {
      apply le_antisymm, exact Union_mono (λ x, subset_union_left _ _),
      intros x m, simp only [Union_coe_set, mem_Union, mem_union] at m,
      rcases m with ⟨y,m,xt|xc⟩,
      exact mem_Union_of_mem ⟨y,m⟩ xt,
      exact mem_Union_of_mem _ (h ⟨_,xc⟩).2.1,
    },
    rw e,
    apply is_preconnected_Union, rw set.nonempty_Inter, use [b, λ x, subset_union_right _ _ bt],
    refine λ x, is_preconnected.union x.val (h x).2.1 x.property (h x).2.2.2.is_preconnected tc.is_preconnected,
  },
end

-- Open preconnected sets form a basis for 𝓝ˢ t in any locally connected space, if t is preconnected
lemma local_preconnected_nhds_set {X : Type} [topological_space X] [lc : locally_connected_space X]
    {s t : set X} (tc : is_preconnected t) (st : s ∈ 𝓝ˢ t)
    : ∃ c, is_open c ∧ t ⊆ c ∧ c ⊆ s ∧ is_preconnected c := begin
  by_cases h : t.nonempty, {
    rcases local_connected_nhds_set ⟨h,tc⟩ st with ⟨c,co,tc,cs,cc⟩,
    use [c,co,tc,cs,cc.is_preconnected],
  }, {
    simp only [not_nonempty_iff_eq_empty] at h, use ∅,
    simp only [h, is_open_empty, empty_subset, true_and, is_preconnected_empty],
  },
end

-- Lower semicontinuity composes with continuity
lemma lower_semicontinuous_at.comp {X Y Z : Type} [topological_space X] [topological_space Y]
    [linear_order Z] [topological_space Z] [order_topology Z] {f : Y → Z} {g : X → Y} {x : X}
    (fc : lower_semicontinuous_at f (g x)) (gc : continuous_at g x)
    : lower_semicontinuous_at (λ x, f (g x)) x :=
  λ z lt, gc.eventually (fc _ lt)
lemma lower_semicontinuous.comp {X Y Z : Type} [topological_space X] [topological_space Y]
    [linear_order Z] [topological_space Z] [order_topology Z] {f : Y → Z} {g : X → Y}
    (fc : lower_semicontinuous f) (gc : continuous g)
    : lower_semicontinuous (λ x, f (g x)) :=
  λ x, (fc (g x)).comp gc.continuous_at

-- Continuous functions locally injective near a compact set are injective on a neighborhood
theorem locally_injective_on_compact {X Y : Type} [topological_space X] [topological_space Y] [t2_space Y]
    {f : X → Y} {s : set X} (fc : ∀ x, x ∈ s → continuous_at f x) (sc : is_compact s)
    (inj : inj_on f s) (loc : ∀ x, x ∈ s → ∃ u, u ∈ 𝓝 x ∧ inj_on f u)
    : ∃ t, is_open t ∧ s ⊆ t ∧ inj_on f t := begin
  -- We work by two-level compact induction on injectivity.  For the outer level, we ask that a
  -- neighborhood of a subset of s is distinct from a neighborhood of all of s.
  generalize hh : (λ u : set X, ∃ t, is_open t ∧ u ⊆ t ∧ ∀ᶠ x in 𝓝ˢ s, ∀ y, y ∈ t → f x = f y → x = y) = h,
  suffices hs : h s, {
    rw ←hh at hs, rcases hs with ⟨t0,o0,st0,h⟩,
    simp only [filter.eventually_iff, mem_nhds_set_iff_exists] at h,
    rcases h with ⟨t1,o1,st1,h⟩,
    use [t0 ∩ t1, o0.inter o1, subset_inter st0 st1],
    intros x xm y ym,
    exact h (inter_subset_right _ _ xm) y (inter_subset_left _ _ ym),
  },
  apply is_compact.induction_on sc, {
    rw ←hh, use ∅,
    simp only [empty_subset, and_true, is_open_empty, mem_empty_iff_false, is_empty.forall_iff,
      implies_true_iff, filter.eventually_true],
  }, {
    rw ←hh, intros u0 u1 u01 h, rcases h with ⟨t,o,ut,h⟩, use [t, o, trans u01 ut, h],
  }, {
    rw ←hh, intros u0 u1 h0 h1, rcases h0 with ⟨t0,o0,ut0,h0⟩, rcases h1 with ⟨t1,o1,ut1,h1⟩,
    use [t0 ∪ t1, o0.union o1, union_subset_union ut0 ut1],
    refine h0.mp (h1.mp (eventually_of_forall (λ x h1 h0 y m, _))),
    cases m, exact h0 _ m, exact h1 _ m,
  },
  -- For the inner level, we build up the set of points w.r.t. some neighborhood of x is injective
  rw ←hh, clear hh, intros x m, simp only,
  generalize hg : (λ u : set X, ∃ t : set X, is_open t ∧ x ∈ t ∧
    ∀ᶠ x in 𝓝ˢ u, ∀ y, y ∈ t → f x = f y → x = y) = g,
  suffices gs : g s, {
    rw ←hg at gs, rcases gs with ⟨t,o,m,g⟩,
    use [t, nhds_within_le_nhds (o.mem_nhds m), t, o, subset_refl _, g],
  },
  apply is_compact.induction_on sc, {
    rw ←hg, use univ, simp only [is_open_univ, mem_univ, nhds_set_empty, filter.eventually_bot, and_self],
  }, {
    rw ←hg, clear hg, simp only, intros s0 s1 s01 g, rcases g with ⟨t,o,m,g⟩,
    use [t,o,m, filter.eventually.filter_mono (nhds_set_mono s01) g],
  }, {
    rw ←hg, clear hg, simp only, intros s0 s1 g0 g1,
    rcases g0 with ⟨t0,o0,m0,g0⟩, rcases g1 with ⟨t1,o1,m1,g1⟩,
    use [t0 ∩ t1, o0.inter o1, mem_inter m0 m1],
    simp only [nhds_set_union, filter.eventually_sup], constructor,
    exact g0.mp (eventually_of_forall (λ x i y m, i _ (inter_subset_left _ _ m))),
    exact g1.mp (eventually_of_forall (λ x i y m, i _ (inter_subset_right _ _ m))),
  }, {
    rw ←hg, clear hg, simp only, intros y ym,
    by_cases xy : x = y, {
      -- We're injective near (x,x) by loc, which ensures an injective neighborhood of each x
      rw ←xy, rcases loc x m with ⟨u,un,ui⟩,
      rcases mem_nhds_iff.mp un with ⟨v,vu,vo,xv⟩,
      use [v, nhds_within_le_nhds (vo.mem_nhds xv), v, vo, xv],
      apply filter.eventually_of_mem (vo.mem_nhds_set.mpr (subset_refl _)),
      exact ui.mono vu,
    }, {
      -- We're injective near (x,y) for x ≠ y by continuity and injectivity on s
      rcases t2_separation (inj.ne m ym xy) with ⟨ux,uy,uxo,uyo,xu,yu,uxy⟩,
      rcases mem_nhds_iff.mp (tendsto_nhds.mp (fc _ m) ux uxo xu) with ⟨tx,xf,xo,xt⟩,
      rcases mem_nhds_iff.mp (tendsto_nhds.mp (fc _ ym) uy uyo yu) with ⟨ty,yf,yo,yt⟩,
      use [ty, nhds_within_le_nhds (yo.mem_nhds yt), tx, xo, xt],
      apply filter.eventually_of_mem (yo.mem_nhds_set.mpr (subset_refl _)),
      intros y ym x xm e, contrapose e,
      replace xf := xf xm,
      replace yf := yf ym,
      simp only [mem_preimage] at xf yf,
      exact (disjoint_iff_forall_ne.mp uxy _ xf _ yf).symm,
    },
  },
end  

-- p and q occur frequently along two filters iff p ∧ q occurs frequently in the product filter
lemma prod.frequently {A B : Type} {f : filter A} {g : filter B} {p : A → Prop} {q : B → Prop}
    : (∃ᶠ x : A × B in f.prod g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ (∃ᶠ b in g, q b) := begin
  constructor, {
    intro h, contrapose h, simp only [filter.not_frequently, not_and_distrib] at h ⊢, cases h with h h,
    exact (h.prod_inl g).mp (eventually_of_forall (by tauto)),
    exact (h.prod_inr f).mp (eventually_of_forall (by tauto)),
  }, {
    rintros ⟨u,v⟩, simp only [filter.frequently_iff] at u v ⊢, intros s m,
    rcases filter.mem_prod_iff.mp m with ⟨s0,m0,s1,m1,sub⟩, 
    rcases u m0 with ⟨a,am,ap⟩,
    rcases v m1 with ⟨b,bm,bq⟩,
    exact ⟨⟨a,b⟩,sub (mk_mem_prod am bm),ap,bq⟩,
  },
end

-- Product of map_cluster_pt with tendsto
lemma map_cluster_pt.prod {A B C : Type} [topological_space A] [topological_space B] [topological_space C]
    {f : A → B} {g : A → C} {a : filter A} {b : B} {c : C}
    (fa : map_cluster_pt b a f) (ga : tendsto g a (𝓝 c)) : map_cluster_pt (b,c) a (λ x, (f x, g x)) := begin
  rw map_cluster_pt_iff at ⊢ fa, intros s n,
  rcases mem_nhds_prod_iff.mp n with ⟨u,un,v,vn,sub⟩,
  apply (fa _ un).mp,
  apply (filter.tendsto_iff_forall_eventually_mem.mp ga v vn).mp,
  exact eventually_of_forall (λ x gv fu, sub (mk_mem_prod fu gv)),
end

-- If we converge to g, we're eventually greater than anything less than g
lemma filter.tendsto.exists_lt {X : Type} [linear_order X] [topological_space X] [order_closed_topology X]
    {f : ℕ → X} {g : X} (tend : tendsto f at_top (𝓝 g)) : ∀ {x}, x < g → ∃ n, x < f n := begin
  intros x h, contrapose h, simp only [not_lt, not_exists] at ⊢ h, exact le_of_tendsto' tend h,
end 

-- ≠ → eventual ≠
lemma ne.eventually_ne {X : Type} [topological_space X] [t2_space X] {x y : X} (h : x ≠ y)
    : ∀ᶠ q : X × X in 𝓝 (x,y), q.1 ≠ q.2 := begin
  contrapose h, simp only [not_not, filter.not_eventually] at h ⊢,
  refine tendsto_nhds_unique_of_frequently_eq _ _ h, exact continuous_at_fst, exact continuous_at_snd,
end

-- sphere ⊆ ball
lemma metric.sphere_subset_ball {z : ℂ} {a b : ℝ} (ab : a < b) : sphere z a ⊆ ball z b := begin
  intros x m, simp only [mem_sphere, mem_ball, complex.dist_eq] at m ⊢, rwa m,
end 

-- There are nearby smaller and larger real numbers
lemma real.frequently_smaller (x : ℝ) : ∃ᶠ y in 𝓝 x, y < x := begin
  rw (nhds_basis_Ioo x).frequently_iff,
  rintros ⟨a,b⟩ ⟨ax,xb⟩, use (a+x)/2, simp only [mem_Ioo],
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩,
end
lemma real.frequently_larger (x : ℝ) : ∃ᶠ y in 𝓝 x, x < y := begin
  rw (nhds_basis_Ioo x).frequently_iff,
  rintros ⟨a,b⟩ ⟨ax,xb⟩, use (x+b)/2, simp only [mem_Ioo],
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩,
end
