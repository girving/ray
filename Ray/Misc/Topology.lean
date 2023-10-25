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
open scoped Real NNReal Topology
noncomputable section

/-- `IsOpen s → s ∈ 𝓝ˢ s` -/
theorem IsOpen.mem_nhdsSet_self {X : Type*} [TopologicalSpace X] {s : Set X} (o : IsOpen s) :
    s ∈ 𝓝ˢ s :=
  o.mem_nhdsSet.mpr Subset.rfl

/-- Turn `s ⊆ setOf p` back into a clean forall -/
theorem subset_setOf {X : Type} {p : X → Prop} {s : Set X} : s ⊆ setOf p ↔ ∀ x, x ∈ s → p x :=
  Iff.rfl

/-- A proposition is true `∀ᶠ in 𝓝ˢ` if it is true on a larger open set -/
theorem eventually_nhdsSet_iff {X : Type} [TopologicalSpace X] {s : Set X} {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∃ t, IsOpen t ∧ s ⊆ t ∧ ∀ x, x ∈ t → p x := by
  simp only [Filter.eventually_iff, mem_nhdsSet_iff_exists, subset_setOf]

/-- A proposition is true `∀ᶠ in 𝓝ˢ` if it is eventually true near each point in the set -/
theorem eventually_nhdsSet_iff_forall {X : Type} [TopologicalSpace X] {s : Set X} {p : X → Prop} :
    (∀ᶠ x in 𝓝ˢ s, p x) ↔ ∀ x, x ∈ s → ∀ᶠ y in 𝓝 x, p y := by
  simp only [Filter.eventually_iff, mem_nhdsSet_iff_forall, subset_setOf]

/-- Continuous functions on compact sets are bounded above -/
theorem ContinuousOn.bounded {X : Type} [TopologicalSpace X] {f : X → ℝ} {s : Set X}
    (fc : ContinuousOn f s) (sc : IsCompact s) : ∃ b : ℝ, b ≥ 0 ∧ ∀ x, x ∈ s → f x ≤ b := by
  simpa using (sc.bddAbove_image fc).exists_ge 0

/-- Continuous functions on compact sets have bounded norm -/
theorem ContinuousOn.bounded_norm {X Y : Type} [TopologicalSpace X] [NormedAddCommGroup Y]
    {f : X → Y} {s : Set X} (fc : ContinuousOn f s) (sc : IsCompact s) :
    ∃ b : ℝ, b ≥ 0 ∧ ∀ x, x ∈ s → ‖f x‖ ≤ b :=
  fc.norm.bounded sc

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
  set c := fun n ↦ Classical.choose ((fc n).bounded_norm sc)
  have cs : ∀ n, 0 ≤ c n ∧ ∀ x, x ∈ s → ‖f n x‖ ≤ c n := fun n ↦
    Classical.choose_spec ((fc n).bounded_norm sc)
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
    ∀ᶠ y in 𝓝 x, f y ∈ s :=
  fc (o.mem_nhds m)

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
theorem Continuous.in1 {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {f : A × B → C} (fc : Continuous f) {b : B} : Continuous fun a ↦ f (a, b) :=
  fc.comp (continuous_id.prod_mk continuous_const)

/-- Curried continuous functions are continuous in the second argument -/
theorem Continuous.in2 {A B C : Type} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {f : A × B → C} (fc : Continuous f) {a : A} : Continuous fun b ↦ f (a, b) :=
  fc.comp (continuous_const.prod_mk continuous_id)

/-- In a compact space, uniqueness of limit points implies convergence -/
theorem le_nhds_of_clusterPt_unique {A : Type} [TopologicalSpace A] [CompactSpace A] {l : Filter A}
    {y : A} (u : ∀ x, ClusterPt x l → x = y) : l ≤ 𝓝 y := by
  contrapose u; simp only [not_forall, exists_prop]
  rcases Filter.not_tendsto_iff_exists_frequently_nmem.mp u with ⟨s, sl, h⟩; clear u
  rcases mem_nhds_iff.mp sl with ⟨t, ts, ot, yt⟩; clear sl
  have ne : (l ⊓ Filter.principal (tᶜ)).NeBot := by
    rw [Filter.inf_principal_neBot_iff]; intro u ul
    rcases Filter.frequently_iff.mp h ul with ⟨x, xu, xs⟩
    use x; rw [Set.mem_inter_iff, Set.mem_compl_iff]; use xu, Set.not_mem_subset ts xs
  rcases@cluster_point_of_compact _ _ _ _ ne with ⟨x, ⟨cp⟩⟩
  simp only [ClusterPt, Filter.neBot_iff, ← bot_lt_iff_ne_bot, ← inf_assoc] at cp ⊢
  use x, lt_of_lt_of_le cp inf_le_left
  simp only [@inf_comm _ _ _ l, inf_assoc] at cp
  have xt := lt_of_lt_of_le cp inf_le_right
  simp only [bot_lt_iff_ne_bot, ← mem_closure_iff_nhds_neBot, ot.isClosed_compl.closure_eq] at xt
  contrapose xt; simp only [not_not] at xt; simp only [Set.not_mem_compl_iff, xt, yt]

/-- In a compact space, uniqueness of limit points implies convergence -/
theorem tendsto_of_cluster_pt_unique {A B : Type} [TopologicalSpace B]
    [CompactSpace B] {l : Filter A} {f : A → B} {y : B}
    (u : ∀ x, MapClusterPt x l f → x = y) : Tendsto f l (𝓝 y) :=
  le_nhds_of_clusterPt_unique u

/-- Continuous images of compact closures are closures of images -/
theorem Continuous.image_compact_closure {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [T2Space B] {f : A → B} {s : Set A} (fc : Continuous f) (sc : IsCompact (closure s)) :
    f '' closure s = closure (f '' s) :=
  image_closure_of_isCompact sc fc.continuousOn

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

/-- `fst` is a closed map if `B` is compact -/
theorem IsClosedMap.fst {A B : Type} [TopologicalSpace A] [TopologicalSpace B] [CompactSpace B] :
    IsClosedMap fun p : A × B ↦ p.1 := by
  intro s h; simp only [← isOpen_compl_iff, isOpen_iff_eventually] at h ⊢; intro x m
  simp only [mem_compl_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right,
    not_exists] at m ⊢
  generalize hp : (fun t : Set B ↦ ∀ᶠ x' in 𝓝 x, ∀ y, y ∈ t → (x', y) ∉ s) = p
  suffices q : p univ; rw [←hp] at q
  exact q.mp (eventually_of_forall fun x' i y ↦ i y (mem_univ y))
  refine' isCompact_univ.induction_on _ _ _ _
  · simp_rw [← hp, not_mem_empty, false_imp_iff, imp_true_iff, Filter.eventually_true]
  · intro u v uv pv; rw [← hp] at pv ⊢
    exact pv.mp (eventually_of_forall fun x' pv y yu ↦ pv y (uv yu))
  · intro u v pu pv; rw [← hp] at pu pv ⊢
    refine' pu.mp (pv.mp (eventually_of_forall fun x' pv pu y yuv ↦ _))
    cases' (mem_union _ _ _).mp yuv with yu yv; exact pu y yu; exact pv y yv
  · intro y _; specialize h (x, y) (m y)
    rcases(Filter.HasBasis.prod_nhds (nhds_basis_opens x) (nhds_basis_opens y)).eventually_iff.mp
        h with
      ⟨⟨ta, tb⟩, ⟨⟨xta, ota⟩, ⟨ytb, otb⟩⟩, h⟩
    simp only [nhdsWithin_univ, ← hp, eventually_nhds_iff]
    refine' ⟨tb, otb.mem_nhds ytb, ta, _, ota, xta⟩
    intro x' xta' y' ytb'; exact h (mk_mem_prod xta' ytb')

/-- Open connected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is connected -/
theorem local_connected_nhdsSet {X : Type} [TopologicalSpace X] [lc : LocallyConnectedSpace X]
    {s t : Set X} (tc : IsConnected t) (st : s ∈ 𝓝ˢ t) :
    ∃ c, IsOpen c ∧ t ⊆ c ∧ c ⊆ s ∧ IsConnected c := by
  have h' : ∀ x : t, ∃ c, IsOpen c ∧ x.val ∈ c ∧ c ⊆ s ∧ IsConnected c := by
    intro ⟨x, m⟩
    rcases locallyConnectedSpace_iff_open_connected_subsets.mp lc x s
        (mem_nhdsSet_iff_forall.mp st _ m) with
      ⟨c, cs, oc, xc, cc⟩
    use c
  generalize hc : (fun x : t ↦ Classical.choose (h' x)) = c
  have h : ∀ x : t, IsOpen (c x) ∧ x.val ∈ c x ∧ c x ⊆ s ∧ IsConnected (c x) := by
    rw [←hc]; intro x; exact Classical.choose_spec (h' x)
  clear hc h'
  rcases tc.nonempty with ⟨b, bt⟩
  use⋃ x, c x; refine' ⟨_, _, _, _, _⟩; · exact isOpen_iUnion fun x ↦ (h x).1
  · exact fun x m ↦ mem_iUnion.mpr ⟨⟨x, m⟩, (h ⟨x, m⟩).2.1⟩
  · exact iUnion_subset fun x ↦ (h x).2.2.1
  · use b; exact mem_iUnion_of_mem ⟨b, bt⟩ (h ⟨b, bt⟩).2.1
  · have e : (⋃ x, c x) = ⋃ x, c x ∪ t := by
      apply le_antisymm; exact iUnion_mono fun x ↦ subset_union_left _ _
      intro x m; simp only [iUnion_coe_set, mem_iUnion, mem_union] at m
      rcases m with ⟨y, m, xt | xc⟩
      exact mem_iUnion_of_mem ⟨y, m⟩ xt
      exact mem_iUnion_of_mem _ (h ⟨_, xc⟩).2.1
    rw [e]
    apply isPreconnected_iUnion; rw [Set.nonempty_iInter]; use b, fun x ↦ subset_union_right _ _ bt
    refine' fun x ↦
      IsPreconnected.union x.val (h x).2.1 x.property (h x).2.2.2.isPreconnected tc.isPreconnected

/-- Open preconnected sets form a basis for `𝓝ˢ t` in any locally connected space,
    if `t` is preconnected -/
theorem local_preconnected_nhdsSet {X : Type} [TopologicalSpace X] [lc : LocallyConnectedSpace X]
    {s t : Set X} (tc : IsPreconnected t) (st : s ∈ 𝓝ˢ t) :
    ∃ c, IsOpen c ∧ t ⊆ c ∧ c ⊆ s ∧ IsPreconnected c := by
  by_cases h : t.Nonempty
  · rcases local_connected_nhdsSet ⟨h, tc⟩ st with ⟨c, co, tc, cs, cc⟩
    use c, co, tc, cs, cc.isPreconnected
  · simp only [not_nonempty_iff_eq_empty] at h; use∅
    simp only [h, isOpen_empty, empty_subset, true_and_iff, isPreconnected_empty]

/-- Lower semicontinuity composes with continuity -/
theorem LowerSemicontinuousAt.comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Z] {f : Y → Z} {g : X → Y} {x : X}
    (fc : LowerSemicontinuousAt f (g x)) (gc : ContinuousAt g x) :
    LowerSemicontinuousAt (fun x ↦ f (g x)) x := fun _ lt ↦ gc.eventually (fc _ lt)

/-- Lower semicontinuity composes with continuity -/
theorem LowerSemicontinuous.comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Z] {f : Y → Z} {g : X → Y}
    (fc : LowerSemicontinuous f) (gc : Continuous g) : LowerSemicontinuous fun x ↦ f (g x) :=
  fun x ↦ (fc (g x)).comp gc.continuousAt

/-- Continuous functions locally injective near a compact set are injective on a neighborhood -/
theorem locally_injective_on_compact {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} {s : Set X} (fc : ∀ x, x ∈ s → ContinuousAt f x) (sc : IsCompact s)
    (inj : InjOn f s) (loc : ∀ x, x ∈ s → ∃ u, u ∈ 𝓝 x ∧ InjOn f u) :
    ∃ t, IsOpen t ∧ s ⊆ t ∧ InjOn f t := by
  -- We work by two-level compact induction on injectivity.  For the outer level, we ask that a
  -- neighborhood of a subset of s is distinct from a neighborhood of all of s.
  generalize hh : (fun u : Set X ↦ ∃ t,
    IsOpen t ∧ u ⊆ t ∧ ∀ᶠ x in 𝓝ˢ s, ∀ y, y ∈ t → f x = f y → x = y) = h
  suffices hs : h s
  · rw [← hh] at hs; rcases hs with ⟨t0, o0, st0, h⟩
    simp only [Filter.eventually_iff, mem_nhdsSet_iff_exists] at h
    rcases h with ⟨t1, o1, st1, h⟩
    use t0 ∩ t1, o0.inter o1, subset_inter st0 st1
    intro x xm y ym
    exact h (inter_subset_right _ _ xm) y (inter_subset_left _ _ ym)
  apply @IsCompact.induction_on _ _ _ sc h
  · rw [←hh]; use ∅
    simp only [empty_subset, and_true_iff, isOpen_empty, mem_empty_iff_false, IsEmpty.forall_iff,
      imp_true_iff, Filter.eventually_true, true_and_iff]
  · rw [← hh]; intro u0 u1 u01 h; rcases h with ⟨t, o, ut, h⟩; use t, o, _root_.trans u01 ut, h
  · rw [← hh]; intro u0 u1 h0 h1; rcases h0 with ⟨t0, o0, ut0, h0⟩; rcases h1 with ⟨t1, o1, ut1, h1⟩
    use t0 ∪ t1, o0.union o1, union_subset_union ut0 ut1
    refine' h0.mp (h1.mp (eventually_of_forall fun x h1 h0 y m ↦ _))
    cases' m with m m; exact h0 _ m; exact h1 _ m
  -- For the inner level, we build up the set of points w.r.t. some neighborhood of x is injective
  rw [← hh]
  clear hh; intro x m; simp only
  generalize hg : (fun u : Set X ↦
    ∃ t : Set X, IsOpen t ∧ x ∈ t ∧ ∀ᶠ x in 𝓝ˢ u, ∀ y, y ∈ t → f x = f y → x = y) = g
  suffices gs : g s
  · rw [← hg] at gs; rcases gs with ⟨t, o, m, g⟩
    use t, nhdsWithin_le_nhds (o.mem_nhds m), t, o, subset_refl _, g
  apply @IsCompact.induction_on _ _ _ sc g
  · rw [← hg]; use univ
    simp only [isOpen_univ, mem_univ, nhdsSet_empty, Filter.eventually_bot, and_self_iff]
  · rw [← hg]; clear hg; simp only; intro s0 s1 s01 g; rcases g with ⟨t, o, m, g⟩
    use t, o, m, Filter.Eventually.filter_mono (nhdsSet_mono s01) g
  · rw [← hg]; clear hg; simp only; intro s0 s1 g0 g1
    rcases g0 with ⟨t0, o0, m0, g0⟩; rcases g1 with ⟨t1, o1, m1, g1⟩
    use t0 ∩ t1, o0.inter o1, mem_inter m0 m1
    simp only [nhdsSet_union, Filter.eventually_sup]; constructor
    exact g0.mp (eventually_of_forall fun x i y m ↦ i _ (inter_subset_left _ _ m))
    exact g1.mp (eventually_of_forall fun x i y m ↦ i _ (inter_subset_right _ _ m))
  · rw [← hg]; clear hg; simp only; intro y ym
    by_cases xy : x = y
    · -- We're injective near (x,x) by loc, which ensures an injective neighborhood of each x
      rw [← xy]; rcases loc x m with ⟨u, un, ui⟩
      rcases mem_nhds_iff.mp un with ⟨v, vu, vo, xv⟩
      use v, nhdsWithin_le_nhds (vo.mem_nhds xv), v, vo, xv
      apply Filter.eventually_of_mem (vo.mem_nhdsSet.mpr (subset_refl _))
      exact ui.mono vu
    · -- We're injective near (x,y) for x ≠ y by continuity and injectivity on s
      rcases t2_separation (inj.ne m ym xy) with ⟨ux, uy, uxo, uyo, xu, yu, uxy⟩
      rcases mem_nhds_iff.mp (tendsto_nhds.mp (fc _ m) ux uxo xu) with ⟨tx, xf, xo, xt⟩
      rcases mem_nhds_iff.mp (tendsto_nhds.mp (fc _ ym) uy uyo yu) with ⟨ty, yf, yo, yt⟩
      use ty, nhdsWithin_le_nhds (yo.mem_nhds yt), tx, xo, xt
      apply Filter.eventually_of_mem (yo.mem_nhdsSet.mpr (subset_refl _))
      intro y ym x xm e; contrapose e
      replace xf := xf xm
      replace yf := yf ym
      simp only [mem_preimage] at xf yf
      exact (disjoint_iff_forall_ne.mp uxy xf yf).symm

/-- `p` and `q` occur frequently along two filters iff `p ∧ q` occurs frequently in the product
    filter -/
theorem Prod.frequently {A B : Type} {f : Filter A} {g : Filter B} {p : A → Prop} {q : B → Prop} :
    (∃ᶠ x : A × B in f ×ˢ g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ ∃ᶠ b in g, q b := by
  constructor
  · exact fun h ↦ ⟨Filter.tendsto_fst.frequently (h.mono fun _ ↦ And.left),
      Filter.tendsto_snd.frequently (h.mono fun _ ↦ And.right)⟩
  · intro ⟨u, v⟩; simp only [Filter.frequently_iff] at u v ⊢; intro s m
    rcases Filter.mem_prod_iff.mp m with ⟨s0, m0, s1, m1, sub⟩
    rcases u m0 with ⟨a, am, ap⟩
    rcases v m1 with ⟨b, bm, bq⟩
    exact ⟨⟨a, b⟩, sub (mk_mem_prod am bm), ap, bq⟩

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
    ∀ {x}, x < g → ∃ n, x < f n := by
  intro x h; contrapose h; simp only [not_lt, not_exists] at h ⊢; exact le_of_tendsto' tend h

/-- `≠ → eventual ≠` -/
theorem Ne.eventually_ne {X : Type} [TopologicalSpace X] [T2Space X] {x y : X} (h : x ≠ y) :
    ∀ᶠ q : X × X in 𝓝 (x, y), q.1 ≠ q.2 := by
  contrapose h; simp only [not_not, Filter.not_eventually] at h ⊢
  refine' tendsto_nhds_unique_of_frequently_eq _ _ h; exact continuousAt_fst; exact continuousAt_snd

/-- In a metric space, `sphere ⊆ ball` -/
theorem Metric.sphere_subset_ball {z : ℂ} {a b : ℝ} (ab : a < b) : sphere z a ⊆ ball z b := by
  intro x m; simp only [mem_sphere, mem_ball, Complex.dist_eq] at m ⊢; rwa [m]

/-- Near any real, there are frequently smaller reals -/
theorem Real.frequently_smaller (x : ℝ) : ∃ᶠ y in 𝓝 x, y < x := by
  rw [(nhds_basis_Ioo x).frequently_iff]
  intro ⟨a, b⟩ ⟨ax, xb⟩; use(a + x) / 2; simp only [mem_Ioo]
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- Near any real, there are frequently larger reals -/
theorem Real.frequently_larger (x : ℝ) : ∃ᶠ y in 𝓝 x, x < y := by
  rw [(nhds_basis_Ioo x).frequently_iff]
  intro ⟨a, b⟩ ⟨ax, xb⟩; use(x + b) / 2; simp only [mem_Ioo]
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩

/-- A set is closed if the closure doesn't add new points -/
theorem isClosed_iff_closure_diff {X : Type} [TopologicalSpace X] {s : Set X} :
    IsClosed s ↔ closure s \ s = ∅ := by
  rw [diff_eq_empty, closure_subset_iff_isClosed]

/-- The `⊥` filter has no cluster_pts -/
theorem ClusterPt.bot {X : Type} [TopologicalSpace X] {x : X} : ¬ClusterPt x ⊥ := fun h ↦
  (h.neBot.mono inf_le_right).ne rfl
