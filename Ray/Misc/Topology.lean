module
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
## Various topology lemmas
-/

open Classical
open Metric (ball closedBall sphere mem_sphere mem_ball)
open Filter
open OrderDual (ofDual toDual)
open Set
open scoped Real NNReal Topology Filter ENNReal
noncomputable section

/-- Uniform cauchy sequences on compact sets are uniformly bounded -/
public theorem UniformCauchySeqOn.bounded {X Y : Type} [TopologicalSpace X] [NormedAddCommGroup Y]
    {f : ℕ → X → Y} {s : Set X} (u : UniformCauchySeqOn f atTop s) (fc : ∀ n, ContinuousOn (f n) s)
    (sc : IsCompact s) : ∃ b : ℝ, 0 ≤ b ∧ ∀ n x, x ∈ s → ‖f n x‖ ≤ b := by
  generalize hc : (fun n ↦ Classical.choose ((sc.bddAbove_image (fc n).norm).exists_ge 0)) = c
  have cs : ∀ n, 0 ≤ c n ∧ ∀ x, x ∈ s → ‖f n x‖ ≤ c n := fun n ↦ by
    simpa only [← hc, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using
      Classical.choose_spec ((sc.bddAbove_image (fc n).norm).exists_ge 0)
  rw [Metric.uniformCauchySeqOn_iff] at u
  rcases u 1 (by norm_num) with ⟨N, H⟩; clear u
  generalize hbs : Finset.image c (Finset.range (N + 1)) = bs
  have c0 : c 0 ∈ bs := by simp [← hbs]; exists 0; simp
  generalize hb : 1 + bs.max' ⟨_, c0⟩ = b
  exists b; constructor
  · rw [← hb]; exact add_nonneg (by norm_num) (_root_.trans (cs 0).1 (Finset.le_max' _ _ c0))
  · intro n x xs
    by_cases nN : n ≤ N
    · have cn : c n ∈ bs := by simp [← hbs]; exists n; simp [Nat.lt_add_one_iff.mpr nN]
      exact _root_.trans ((cs n).2 x xs) (_root_.trans (Finset.le_max' _ _ cn)
        (by simp only [le_add_iff_nonneg_left, zero_le_one, ← hb]))
    · simp at nN
      specialize H N le_rfl n nN.le x xs
      have cN : c N ∈ bs := by simp [← hbs]; exists N; simp
      have bN := _root_.trans ((cs N).2 x xs) (Finset.le_max' _ _ cN)
      rw [dist_eq_norm] at H
      calc ‖f n x‖ = ‖f N x - (f N x - f n x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖f N x‖ + ‖f N x - f n x‖ := norm_sub_le _ _
        _ ≤ bs.max' _ + 1 := add_le_add bN H.le
        _ = 1 + bs.max' _ := by ring
        _ = b := by simp only [hb]

/-- `{b | (a,b) ∈ s}` is open if `s` is open -/
public theorem IsOpen.snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {s : Set (A × B)} (o : IsOpen s) (a : A) : IsOpen {b | (a, b) ∈ s} :=
  o.preimage (Continuous.prodMk_right a)

/-- `{b | (a,b) ∈ s}` is closed if `s` is closed -/
public theorem IsClosed.snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {s : Set (A × B)} (c : IsClosed s) (a : A) : IsClosed {b | (a, b) ∈ s} :=
  c.preimage (Continuous.prodMk_right a)

/-- Tendsto commutes with ⁻¹ away from zero -/
theorem tendsto_inv_iff_tendsto {A B : Type} [NontriviallyNormedField B]
    {l : Filter A} {f : A → B} {a : B} (a0 : a ≠ 0) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto f l (𝓝 a) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.inv₀ a0⟩
  have h := h.inv₀ (inv_ne_zero a0)
  field_simp [a0] at h; exact h

/-- If `f x ∈ s` for `s ∈ 𝓝 (f x)` and `f` continuous at `z`, `∈` holds locally -/
public theorem ContinuousAt.eventually_mem_nhd {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] {f : A → B} {x : A} (fc : ContinuousAt f x) {s : Set B} (m : s ∈ 𝓝 (f x)) :
    ∀ᶠ y in 𝓝 x, f y ∈ s :=
  (eventually_mem_nhds_iff.2 (fc m)).mono fun _x hx ↦ mem_preimage.1 (mem_of_mem_nhds hx)

/-- The reverse direction of `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` -/
theorem IsClosed.Icc_subset_of_forall_mem_nhds_within' {X : Type}
    [ConditionallyCompleteLinearOrder X] [TopologicalSpace X] [OrderTopology X] [DenselyOrdered X]
    {a b : X} {s : Set X} (sc : IsClosed (s ∩ Icc a b)) (sb : b ∈ s)
    (so : ∀ x, x ∈ s ∩ Ioc a b → s ∈ 𝓝[Iio x] x) : Icc a b ⊆ s := by
  generalize hs' : ofDual ⁻¹' s = s'
  have rev : Icc (toDual b) (toDual a) ⊆ s' := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · have e : s' ∩ Icc (toDual b) (toDual a) = ofDual ⁻¹' (s ∩ Icc a b) := by
        apply Set.ext; intro x; simp only [Set.Icc_toDual, Set.preimage_inter, ← hs']
      rw [e]; exact IsClosed.preimage continuous_ofDual sc
    · simp only [Set.mem_preimage, OrderDual.ofDual_toDual, sb, ← hs']
    · intro x m
      simp only [Set.mem_inter_iff, Set.mem_Ico, OrderDual.toDual_le, OrderDual.lt_toDual] at m
      simp only [mem_nhdsWithin_iff_eventually, eventually_nhds_iff, Set.mem_inter_iff,
        Set.mem_Ioc, ← hs'] at so m ⊢
      rcases so (ofDual x) ⟨m.1, m.2.2, m.2.1⟩ with ⟨n, h, o, nx⟩
      use ofDual ⁻¹' n
      refine ⟨?_, o.preimage continuous_ofDual, mem_preimage.mpr nx⟩
      intro y m xy; simp only [Set.mem_Ioi] at xy; simp only [Set.mem_preimage]
      simp only [Set.mem_Iio] at h
      exact h _ m xy
  intro x m; simp only [Set.mem_Icc] at m; specialize @rev (toDual x)
  simp only [Set.Icc_toDual, Set.mem_preimage, Set.mem_Icc, and_imp, OrderDual.ofDual_toDual,
    ← hs'] at rev
  exact rev m.1 m.2

lemma IsPreconnected.sUnion_of_pairwise_exists_isPreconnected {X : Type*} [TopologicalSpace X]
    {S : Set (Set X)} (hSc : ∀ s ∈ S, IsPreconnected s)
    (h : S.Pairwise fun s t ↦ s.Nonempty → t.Nonempty →
      ∃ u, u ⊆ ⋃₀ S ∧ (s ∩ u).Nonempty ∧ (u ∩ t).Nonempty ∧ IsPreconnected u) :
    IsPreconnected (⋃₀ S) := by
  refine isPreconnected_of_forall_pair fun x hx y hy ↦ ?_
  rcases mem_sUnion.1 hx with ⟨s, hs, hxs⟩
  rcases mem_sUnion.1 hy with ⟨t, ht, hyt⟩
  rcases eq_or_ne s t with rfl | hst
  · exact ⟨s, subset_sUnion_of_mem hs, hxs, hyt, hSc s hs⟩
  · rcases h hs ht hst ⟨x, hxs⟩ ⟨y, hyt⟩ with ⟨u, huS, hsu, hut, hu⟩
    refine ⟨s ∪ u ∪ t, ?_, ?_, ?_, ?_⟩
    · simp [*, subset_sUnion_of_mem]
    · simp [*]
    · simp [*]
    · refine ((hSc s hs).union' hsu hu).union' (hut.mono ?_) (hSc t ht)
      exact inter_subset_inter_left _ subset_union_right

lemma IsPreconnected.iUnion_of_pairwise_exists_isPreconnected {ι X : Type*} [TopologicalSpace X]
    {s : ι → Set X} (hsc : ∀ i, IsPreconnected (s i))
    (h : Pairwise fun i j ↦ (s i).Nonempty → (s j).Nonempty →
      ∃ u, u ⊆ ⋃ i, s i ∧ (s i ∩ u).Nonempty ∧ (u ∩ s j).Nonempty ∧ IsPreconnected u) :
    IsPreconnected (⋃ i, s i) := by
  apply IsPreconnected.sUnion_of_pairwise_exists_isPreconnected (forall_mem_range.2 hsc)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact h (ne_of_apply_ne s hij)

/-- Open preconnected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is preconnected -/
public theorem local_preconnected_nhdsSet {X : Type} [TopologicalSpace X]
    [lc : LocallyConnectedSpace X] {s t : Set X} (tc : IsPreconnected t) (st : s ∈ 𝓝ˢ t) :
    ∃ c, IsOpen c ∧ t ⊆ c ∧ c ⊆ s ∧ IsPreconnected c := by
  rw [← subset_interior_iff_mem_nhdsSet] at st
  have hsub : t ⊆ ⋃ x : t, connectedComponentIn (interior s) x := fun x hx ↦
    mem_iUnion.2 ⟨⟨x, hx⟩, mem_connectedComponentIn (st hx)⟩
  refine ⟨_, isOpen_iUnion fun _ ↦ isOpen_interior.connectedComponentIn, hsub,
    iUnion_subset fun x ↦ ?_, ?_⟩
  · exact (connectedComponentIn_subset _ _).trans interior_subset
  · apply IsPreconnected.iUnion_of_pairwise_exists_isPreconnected
    · exact fun _ ↦ isPreconnected_connectedComponentIn
    · exact fun x y _ _ _ ↦ ⟨t, hsub, ⟨x, mem_connectedComponentIn (st x.2), x.2⟩,
        ⟨y, y.2, mem_connectedComponentIn (st y.2)⟩, tc⟩

/-- Open connected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is connected -/
theorem local_connected_nhdsSet {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    {s t : Set X} (tc : IsConnected t) (st : s ∈ 𝓝ˢ t) :
    ∃ c, IsOpen c ∧ t ⊆ c ∧ c ⊆ s ∧ IsConnected c :=
  let ⟨c, hco, htc, hcs, hc⟩ := local_preconnected_nhdsSet tc.2 st
  ⟨c, hco, htc, hcs, tc.1.mono htc, hc⟩

open Filter in
/-- `p` and `q` occur frequently along two filters iff `p ∧ q` occurs frequently in the product
    filter -/
public theorem Prod.frequently {A B : Type} {f : Filter A} {g : Filter B} {p : A → Prop}
    {q : B → Prop} :
    (∃ᶠ x : A × B in f ×ˢ g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ ∃ᶠ b in g, q b := by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

/-- The product of `MapClusterPt` and `Tendsto` is `MapClusterPt` -/
public theorem MapClusterPt.prod {A B C : Type} [TopologicalSpace B] [TopologicalSpace C]
    {f : A → B} {g : A → C} {a : Filter A} {b : B} {c : C}
    (fa : MapClusterPt b a f) (ga : Tendsto g a (𝓝 c)) :
    MapClusterPt (b, c) a fun x ↦ (f x, g x) := by
  rw [mapClusterPt_iff_frequently] at fa ⊢; intro s n
  rcases mem_nhds_prod_iff.mp n with ⟨u, un, v, vn, sub⟩
  apply (fa _ un).mp
  apply (Filter.tendsto_iff_forall_eventually_mem.mp ga v vn).mp
  exact .of_forall fun x gv fu ↦ sub (mk_mem_prod fu gv)

/-- If we converge to `g`, we're eventually greater than anything less than `g` -/
public theorem Filter.Tendsto.exists_lt {X : Type} [LinearOrder X] [TopologicalSpace X]
    [OrderClosedTopology X] {f : ℕ → X} {g : X} (tend : Tendsto f atTop (𝓝 g)) :
    ∀ {x}, x < g → ∃ n, x < f n := fun hx ↦
  (tend.eventually (eventually_gt_nhds hx)).exists

/-- `≠ → eventual ≠` -/
public theorem Ne.eventually_ne {X : Type} [TopologicalSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∀ᶠ q : X × X in 𝓝 (x, y), q.1 ≠ q.2 :=
  (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds h

/-- The `⊥` filter has no cluster_pts -/
public lemma ClusterPt.bot {X : Type} [TopologicalSpace X] {x : X} : ¬ClusterPt x ⊥ := fun h ↦
  (h.neBot.mono inf_le_right).ne rfl

/-- Version of `nhdsWithin_eq_iff_eventuallyEq` that doesn't misuse eventual equality -/
lemma nhdsWithin_eq_iff_eventuallyEq' {X : Type} [TopologicalSpace X] {s t : Set X} {x : X} :
    𝓝[s] x = 𝓝[t] x ↔ (· ∈ s) =ᶠ[𝓝 x] (· ∈ t) :=
  nhdsWithin_eq_iff_eventuallyEq

/-- `ContinuousWithinAt` depends only locally on the set -/
lemma ContinuousWithinAt.congr_set'' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {s t : Set X} {x : X} (fc : ContinuousWithinAt f s x)
    (hst : (· ∈ s) =ᶠ[𝓝 x] (· ∈ t)) : ContinuousWithinAt f t x := by
  simpa only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq'.mpr hst] using fc

/-- Turn eventual equality into an intersection into eventual equality w.r.t. `𝓝[s] x` -/
lemma eventuallyEq_inter {X : Type} [TopologicalSpace X] {s t u : Set X} {x : X} :
    (· ∈ t ∩ s) =ᶠ[𝓝 x] (· ∈ u ∩ s) ↔ (· ∈ t) =ᶠ[𝓝[s] x] (· ∈ u) := by
  rw [Filter.EventuallyEq, eventuallyEq_nhdsWithin_iff]
  simp only [mem_inter_iff, eq_iff_iff, and_congr_left_iff]

/-- Given a closed ball in an open set, we can expand the ball to a larger open ball -/
public lemma exists_ball_superset {X : Type} [MetricSpace X] [ProperSpace X] {s : Set X} {x : X}
    {r : ℝ} (sub : closedBall x r ⊆ s) (o : IsOpen s) : ∃ t, r < t ∧ ball x t ⊆ s := by
  by_cases n : closedBall x (r + 1) \ s = ∅
  · simp only [diff_eq_empty] at n
    exact ⟨r + 1, by linarith, subset_trans Metric.ball_subset_closedBall n⟩
  simp only [← nonempty_iff_ne_empty] at n
  have c : IsCompact (closedBall x (r + 1) \ s) := (isCompact_closedBall x (r + 1)).diff o
  have d : Continuous fun y ↦ dist x y := continuous_const.dist continuous_id
  obtain ⟨y, ⟨yr, ys⟩, h⟩ := c.exists_isMinOn n d.continuousOn
  refine ⟨dist x y, ?_, ?_⟩
  · contrapose ys
    simp only [not_lt] at ys ⊢
    apply sub
    simpa only [Metric.mem_closedBall, dist_comm]
  · intro z m
    by_contra zs
    simp only [isMinOn_iff, mem_diff, Metric.mem_closedBall, dist_comm, and_imp, mem_ball] at h m yr
    specialize h z (le_trans m.le yr) zs
    linarith

/-- Eventually in terms of radii -/
lemma eventually_nhdsGT_zero_ball_iff_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop} :
    (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ ball c r, p x) ↔ ∀ᶠ x in 𝓝 c, p x := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff, Metric.nhds_basis_ball.eventually_iff]
  constructor
  · intro ⟨r,r0,h⟩
    exact ⟨r/2, by bound, fun x m ↦ @h (r/2) (by simpa) _ m⟩
  · intro ⟨r,r0,h⟩
    refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
    simp only [Metric.mem_ball, mem_Ioo] at m sr ⊢
    linarith

/-- Eventually in terms of radii and closed balls -/
lemma eventually_nhdsGT_zero_closedBall_iff_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop} :
    (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ closedBall c r, p x) ↔ ∀ᶠ x in 𝓝 c, p x := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff, Metric.nhds_basis_closedBall.eventually_iff]
  constructor
  · intro ⟨r,r0,h⟩
    exact ⟨r/2, by bound, fun x m ↦ @h (r/2) (by simpa) _ m⟩
  · intro ⟨r,r0,h⟩
    refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
    simp only [Metric.mem_closedBall, mem_Ioo] at m sr ⊢
    linarith

/-- Eventually in terms of radii and spheres -/
public lemma eventually_nhdsGT_zero_sphere_of_nhds {X : Type} [MetricSpace X] {c : X} {p : X → Prop}
    (h : ∀ᶠ x in 𝓝 c, p x) : (∀ᶠ r in 𝓝[>] 0, ∀ x ∈ sphere c r, p x) := by
  simp only [(nhdsGT_basis (0 : ℝ)).eventually_iff,
    Metric.nhds_basis_closedBall.eventually_iff] at h ⊢
  obtain ⟨r,r0,h⟩ := h
  refine ⟨r, by bound, fun s sr x m ↦ @h _ ?_⟩
  simp only [Metric.mem_sphere, mem_Ioo, Metric.mem_closedBall] at m sr ⊢
  rw [← m] at sr
  exact sr.2.le

/-- Flip `atTop` to `𝓝[>] 0` -/
public lemma eventually_atTop_iff_nhdsGT_zero {p : ℝ → Prop} :
    (∀ᶠ r in atTop, p r) ↔ ∀ᶠ r in 𝓝[>] 0, p r⁻¹ := by
  simp only [Filter.eventually_atTop, (nhdsGT_basis (0 : ℝ)).eventually_iff]
  constructor
  · intro ⟨r,h⟩
    refine ⟨(max 1 r)⁻¹, by bound, fun s m ↦ h _ ?_⟩
    rw [mem_Ioo, lt_inv_comm₀, max_lt_iff] at m
    all_goals bound
  · intro ⟨r,r0,h⟩
    refine ⟨2 * r⁻¹, fun s m ↦ ?_⟩
    refine inv_inv s ▸ @h s⁻¹ ?_
    simp only [mem_Ioo, inv_pos]
    have s0 : 0 < s := lt_of_lt_of_le (by bound) m
    refine ⟨s0, ?_⟩
    rw [inv_lt_comm₀ s0 r0]
    exact lt_of_lt_of_le (lt_mul_of_one_lt_left (by bound) (by norm_num)) m

/-- Pull an `∃` out of an `∃ᶠ` via Skolemization -/
public lemma frequently_skolem {X Y : Type} [TopologicalSpace X] [n : Nonempty Y] {p : X → Y → Prop}
    (f : Filter X) : (∃ᶠ x in f, ∃ y, p x y) ↔ ∃ s : X → Y, ∃ᶠ x in f, p x (s x) := by
  constructor
  · intro h
    set s : X → Y := fun x ↦ if q : ∃ y, p x y then Classical.choose q else Classical.choice n
    use s
    refine h.mp (.of_forall fun x e ↦ ?_)
    simp only [e, ↓reduceDIte, choose_spec, s]
  · intro ⟨s,h⟩
    refine h.mp (.of_forall fun x e ↦ ?_)
    use s x

public lemma ENNReal.continuousAt_toNNReal {x : ℝ≥0∞} (h : x ≠ ⊤) :
    ContinuousAt (fun x ↦ x.toNNReal) x := by
  apply ENNReal.continuousOn_toNNReal.continuousAt
  apply ENNReal.isOpen_ne_top.mem_nhds
  simpa only [ne_eq, Set.mem_setOf_eq]
