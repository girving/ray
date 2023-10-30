import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Semicontinuous
import Ray.Tactic.Bound

/-!
## Various topology lemmas
-/

open Metric (ball closedBall sphere mem_sphere mem_ball)
open Filter (atTop Tendsto eventually_of_forall)
open OrderDual (ofDual toDual)
open Set
open scoped Real NNReal Topology Filter
noncomputable section

/-- Turn `s ⊆ setOf p` back into a clean forall -/
theorem subset_setOf {X : Type} {p : X → Prop} {s : Set X} : s ⊆ setOf p ↔ ∀ x, x ∈ s → p x :=
  Iff.rfl

/-- Continuous functions on compact sets are bounded above -/
theorem ContinuousOn.bounded {X : Type} [TopologicalSpace X] {f : X → ℝ} {s : Set X}
    (fc : ContinuousOn f s) (sc : IsCompact s) : ∃ b : ℝ, b ≥ 0 ∧ ∀ x, x ∈ s → f x ≤ b := by
  simpa using (sc.bddAbove_image fc).exists_ge 0

/-- Uniform cauchy sequences are cauchy sequences at points -/
theorem UniformCauchySeqOn.cauchySeq {X Y : Type} [MetricSpace Y]
    {f : ℕ → X → Y} {s : Set X} (u : UniformCauchySeqOn f atTop s) :
    ∀ x, x ∈ s → CauchySeq fun n ↦ f n x := by
  intro x xs
  rw [Metric.cauchySeq_iff]
  rw [Metric.uniformCauchySeqOn_iff] at u
  intro e ep; rcases u e ep with ⟨N, H⟩
  exists N; intro a aN b bN
  exact H a aN b bN x xs

/-- Uniform cauchy sequences on compact sets are uniformly bounded -/
theorem UniformCauchySeqOn.bounded {X Y : Type} [TopologicalSpace X] [NormedAddCommGroup Y]
    {f : ℕ → X → Y} {s : Set X} (u : UniformCauchySeqOn f atTop s) (fc : ∀ n, ContinuousOn (f n) s)
    (sc : IsCompact s) : ∃ b : ℝ, b ≥ 0 ∧ ∀ n x, x ∈ s → ‖f n x‖ ≤ b := by
  set c := fun n ↦ Classical.choose ((fc n).norm.bounded sc)
  have cs : ∀ n, 0 ≤ c n ∧ ∀ x, x ∈ s → ‖f n x‖ ≤ c n := fun n ↦
    Classical.choose_spec ((fc n).norm.bounded sc)
  rw [Metric.uniformCauchySeqOn_iff] at u
  rcases u 1 (by norm_num) with ⟨N, H⟩; clear u
  set bs := Finset.image c (Finset.range (N + 1))
  have c0 : c 0 ∈ bs := by simp; exists 0; simp
  set b := 1 + bs.max' ⟨_, c0⟩
  exists b; constructor
  · exact add_nonneg (by norm_num) (_root_.trans (cs 0).1 (Finset.le_max' _ _ c0))
  · intro n x xs
    by_cases nN : n ≤ N
    · have cn : c n ∈ bs := by simp; exists n; simp [Nat.lt_add_one_iff.mpr nN]
      exact _root_.trans ((cs n).2 x xs) (_root_.trans (Finset.le_max' _ _ cn) (by bound))
    · simp at nN
      specialize H N le_rfl n (by bound) x xs
      have cN : c N ∈ bs := by simp; exists N; simp
      have bN := _root_.trans ((cs N).2 x xs) (Finset.le_max' _ _ cN)
      rw [dist_eq_norm] at H
      calc ‖f n x‖ = ‖f N x - (f N x - f n x)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖f N x‖ + ‖f N x - f n x‖ := norm_sub_le _ _
        _ ≤ bs.max' _ + 1 := add_le_add bN H.le
        _ = 1 + bs.max' _ := by ring
        _ = b := rfl

/-- `{b | (a,b) ∈ s}` is open if `s` is open -/
theorem IsOpen.snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B] {s : Set (A × B)}
    (o : IsOpen s) (a : A) : IsOpen {b | (a, b) ∈ s} :=
  o.preimage (Continuous.Prod.mk a)

/-- `{b | (a,b) ∈ s}` is closed if `s` is closed -/
theorem IsClosed.snd_preimage {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {s : Set (A × B)} (c : IsClosed s) (a : A) : IsClosed {b | (a, b) ∈ s} :=
  c.preimage (Continuous.Prod.mk a)

/-- Tendsto commutes with ⁻¹ away from zero -/
theorem tendsto_iff_tendsto_inv {A B : Type} [NontriviallyNormedField B]
    {l : Filter A} {f : A → B} {a : B} (a0 : a ≠ 0) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto f l (𝓝 a) := by
  refine' ⟨fun h ↦ _, fun h ↦ h.inv₀ a0⟩
  have h := h.inv₀ (inv_ne_zero a0)
  field_simp [a0] at h; exact h

/-- `ContinuousAt` in terms of `𝓝[{x}ᶜ] x` (useful when `f x` is a special case) -/
theorem continuousAt_iff_tendsto_nhdsWithin {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} {x : A} : ContinuousAt f x ↔ Tendsto f (𝓝[{x}ᶜ] x) (𝓝 (f x)) := by
  rw [ContinuousAt]; constructor
  exact fun t ↦ t.mono_left nhdsWithin_le_nhds
  intro t; rw [← nhdsWithin_compl_singleton_sup_pure]
  exact Filter.Tendsto.sup t (tendsto_pure_nhds _ _)

/-- If `f x ∈ s` for `s` open and `f` continuous at `z`, `∈` holds locally.
    This is `IsOpen.eventually_mem`, but assuming only `ContinuousAt`. -/
theorem ContinuousAt.eventually_mem {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} {x : A} (fc : ContinuousAt f x) {s : Set B} (o : IsOpen s) (m : f x ∈ s) :
    ∀ᶠ y in 𝓝 x, f y ∈ s := by
  exact fc (o.mem_nhds m)

/-- If `f x ∈ s` for `s ∈ 𝓝 (f x)` and `f` continuous at `z`, `∈` holds locally -/
theorem ContinuousAt.eventually_mem_nhd {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} {x : A} (fc : ContinuousAt f x) {s : Set B} (m : s ∈ 𝓝 (f x)) :
    ∀ᶠ y in 𝓝 x, f y ∈ s :=
  (eventually_mem_nhds.2 (fc m)).mono fun _x hx ↦ mem_preimage.1 (mem_of_mem_nhds hx)

/-- `ContinuousAt.comp` for curried functions -/
theorem ContinuousAt.comp₂ {A B C D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] {f : B × C → D} {g : A → B} {h : A → C} {x : A}
    (fc : ContinuousAt f (g x, h x)) (gc : ContinuousAt g x) (hc : ContinuousAt h x) :
    ContinuousAt (fun x ↦ f (g x, h x)) x :=
  ContinuousAt.comp fc (gc.prod hc)

/-- `ContinuousAt.comp_of_eq` for curried functions -/
theorem ContinuousAt.comp₂_of_eq {A B C D : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] {f : B × C → D} {g : A → B} {h : A → C} {x : A}
    {y : B × C} (fc : ContinuousAt f y) (gc : ContinuousAt g x) (hc : ContinuousAt h x)
    (e : (g x, h x) = y) : ContinuousAt (fun x ↦ f (g x, h x)) x := by
  rw [←e] at fc; exact fc.comp₂ gc hc

/-- `ContinuousAt.comp` for curried functions and `ContinuousWithinAt` -/
theorem ContinuousAt.comp₂_continuousWithinAt {A B C D : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] {f : B × C → D} {g : A → B}
    {h : A → C} {x : A} {s : Set A} (fc : ContinuousAt f (g x, h x))
    (gc : ContinuousWithinAt g s x) (hc : ContinuousWithinAt h s x) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x :=
  ContinuousAt.comp_continuousWithinAt fc (gc.prod hc)

/-- `ContinuousAt.comp_of_eq` for curried functions and `ContinuousWithinAt` -/
theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {A B C D : Type} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] {f : B × C → D} {g : A → B}
    {h : A → C} {x : A} {s : Set A} {y : B × C} (fc : ContinuousAt f y)
    (gc : ContinuousWithinAt g s x) (hc : ContinuousWithinAt h s x) (e : (g x, h x) = y) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x := by
  rw [← e] at fc; exact fc.comp₂_continuousWithinAt gc hc

/-- Curried continuous functions are continuous in the first argument -/
theorem Continuous.along_fst {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {f : A × B → C} (fc : Continuous f) {b : B} : Continuous fun a ↦ f (a, b) :=
  fc.comp (continuous_id.prod_mk continuous_const)

/-- Curried continuous functions are continuous in the second argument -/
theorem Continuous.along_snd {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {f : A × B → C} (fc : Continuous f) {a : A} : Continuous fun b ↦ f (a, b) :=
  fc.comp (continuous_const.prod_mk continuous_id)

/-- The reverse direction of `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` -/
theorem IsClosed.Icc_subset_of_forall_mem_nhds_within' {X : Type}
    [ConditionallyCompleteLinearOrder X] [TopologicalSpace X] [OrderTopology X] [DenselyOrdered X]
    {a b : X} {s : Set X} (sc : IsClosed (s ∩ Icc a b)) (sb : b ∈ s)
    (so : ∀ x, x ∈ s ∩ Ioc a b → s ∈ 𝓝[Iio x] x) : Icc a b ⊆ s := by
  set s' := ofDual ⁻¹' s
  have rev : Icc (toDual b) (toDual a) ⊆ s' := by
    apply IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    · have e : s' ∩ Icc (toDual b) (toDual a) = ofDual ⁻¹' (s ∩ Icc a b) := by
        apply Set.ext; intro x; simp only [Set.dual_Icc, Set.preimage_inter]
      rw [e]; exact IsClosed.preimage continuous_ofDual sc
    · simp only [Set.mem_preimage, OrderDual.ofDual_toDual, sb]
    · intro x m
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_Ico, OrderDual.toDual_le,
        OrderDual.lt_toDual] at m
      simp only [mem_nhdsWithin_iff_eventually, eventually_nhds_iff, Set.mem_inter_iff,
        Set.mem_Ioc] at so ⊢
      rcases so (ofDual x) ⟨m.1, m.2.2, m.2.1⟩ with ⟨n, h, o, nx⟩
      use ofDual ⁻¹' n
      refine' ⟨_, o.preimage continuous_ofDual, mem_preimage.mpr nx⟩
      intro y m xy; simp only [Set.mem_Ioi] at xy; simp only [Set.mem_preimage]
      simp only [Set.mem_Iio, Set.mem_preimage, OrderDual.ofDual_lt_ofDual] at h
      exact h _ m xy
  intro x m; simp only [Set.mem_Icc] at m; specialize @rev (toDual x)
  simp only [Set.dual_Icc, Set.mem_preimage, Set.mem_Icc, and_imp, OrderDual.ofDual_toDual] at rev
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
      exact inter_subset_inter_left _ (subset_union_right _ _)

lemma IsPreconnected.iUnion_of_pairwise_exists_isPreconnected {ι X : Type*} [TopologicalSpace X]
    {s : ι → Set X} (hsc : ∀ i, IsPreconnected (s i))
    (h : Pairwise fun i j ↦ (s i).Nonempty → (s j).Nonempty →
      ∃ u, u ⊆ ⋃ i, s i ∧ (s i ∩ u).Nonempty ∧ (u ∩ s j).Nonempty ∧ IsPreconnected u) :
    IsPreconnected (⋃ i, s i) := by
  apply IsPreconnected.sUnion_of_pairwise_exists_isPreconnected (forall_range_iff.2 hsc)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact h (ne_of_apply_ne s hij)

/-- Open preconnected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is preconnected -/
theorem local_preconnected_nhdsSet {X : Type} [TopologicalSpace X] [lc : LocallyConnectedSpace X]
    {s t : Set X} (tc : IsPreconnected t) (st : s ∈ 𝓝ˢ t) :
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

/-- Lower semicontinuity composes with continuity -/
theorem LowerSemicontinuousAt.comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Z] {f : Y → Z} {g : X → Y} {x : X}
    (fc : LowerSemicontinuousAt f (g x)) (gc : ContinuousAt g x) :
    LowerSemicontinuousAt (fun x ↦ f (g x)) x :=
  fun _ lt ↦ gc.eventually (fc _ lt)

/-- Lower semicontinuity composes with continuity -/
theorem LowerSemicontinuous.comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Z] {f : Y → Z} {g : X → Y}
    (fc : LowerSemicontinuous f) (gc : Continuous g) : LowerSemicontinuous fun x ↦ f (g x) :=
  fun x ↦ (fc (g x)).comp gc.continuousAt

open Filter in
/-- `p` and `q` occur frequently along two filters iff `p ∧ q` occurs frequently in the product
    filter -/
theorem Prod.frequently {A B : Type} {f : Filter A} {g : Filter B} {p : A → Prop} {q : B → Prop} :
    (∃ᶠ x : A × B in f ×ˢ g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ ∃ᶠ b in g, q b := by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

/-- The product of `MapClusterPt` and `Tendsto` is `MapClusterPt` -/
theorem MapClusterPt.prod {A B C : Type} [TopologicalSpace B] [TopologicalSpace C]
    {f : A → B} {g : A → C} {a : Filter A} {b : B} {c : C}
    (fa : MapClusterPt b a f) (ga : Tendsto g a (𝓝 c)) :
    MapClusterPt (b, c) a fun x ↦ (f x, g x) := by
  rw [mapClusterPt_iff] at fa ⊢; intro s n
  rcases mem_nhds_prod_iff.mp n with ⟨u, un, v, vn, sub⟩
  apply (fa _ un).mp
  apply (Filter.tendsto_iff_forall_eventually_mem.mp ga v vn).mp
  exact eventually_of_forall fun x gv fu ↦ sub (mk_mem_prod fu gv)

/-- If we converge to `g`, we're eventually greater than anything less than `g` -/
theorem Filter.Tendsto.exists_lt {X : Type} [LinearOrder X] [TopologicalSpace X]
    [OrderClosedTopology X] {f : ℕ → X} {g : X} (tend : Tendsto f atTop (𝓝 g)) :
    ∀ {x}, x < g → ∃ n, x < f n := fun hx ↦
  (tend.eventually (eventually_gt_nhds hx)).exists

/-- `≠ → eventual ≠` -/
theorem Ne.eventually_ne {X : Type} [TopologicalSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∀ᶠ q : X × X in 𝓝 (x, y), q.1 ≠ q.2 :=
  (isOpen_ne_fun continuous_fst continuous_snd).mem_nhds h

/-- The `⊥` filter has no cluster_pts -/
theorem ClusterPt.bot {X : Type} [TopologicalSpace X] {x : X} : ¬ClusterPt x ⊥ := fun h ↦
  (h.neBot.mono inf_le_right).ne rfl
