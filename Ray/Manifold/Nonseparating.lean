module
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Cases
import Ray.Analytic.Holomorphic
import Ray.Manifold.Manifold
import Ray.Manifold.OneDimension

/-!
## Sets that don't separate open sets when they are removed

Given `t : Set X`, `Nonseparating t` means that removing `t` from any connected open set
does not disconnect the set.  The simplest case is a single point in more than one real
dimension (or in at least one complex dimension), but we also need `line ×ˢ point` in two
complex dimensions.
-/

open Complex
open Metric (ball mem_ball)
open OneDimension
open Set
open scoped Real Topology
noncomputable section

variable {X : Type} [TopologicalSpace X]
variable {Y : Type} [TopologicalSpace Y]
variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- A sufficient condition on `t` such that removing it from a connected open set does not
    disconnect the set -/
structure Nonseparating (t : Set X) : Prop where
  dense : Dense (tᶜ)
  loc : ∀ x u, x ∈ t → u ∈ 𝓝 x → ∃ c, c ⊆ u \ t ∧ c ∈ 𝓝[tᶜ] x ∧ IsPreconnected c

/-- `univ ×ˢ t` is nonseparating if `t` is -/
theorem Nonseparating.univ_prod [LocallyConnectedSpace X] {t : Set Y} (n : Nonseparating t) :
    Nonseparating ((univ : Set X) ×ˢ t) := by
  have e : ((univ : Set X) ×ˢ t)ᶜ = univ ×ˢ tᶜ := by
    apply Set.ext; intro ⟨a, x⟩; rw [mem_compl_iff]
    simp only [prodMk_mem_set_prod_eq, mem_univ, mem_compl_iff, true_and]
  constructor; · rw [e]; exact dense_univ.prod n.dense
  · intro ⟨a, x⟩ u m un; simp only [mem_prod_eq, mem_univ, true_and] at m
    rcases mem_nhds_prod_iff.mp un with ⟨u0, n0, u1, n1, uu⟩
    rcases n.loc x u1 m n1 with ⟨c1, cs1, cn1, cp1⟩
    rcases locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp (by infer_instance) a u0 n0 with
      ⟨c0, cs0, co0, cm0, cc0⟩
    use c0 ×ˢ c1; refine ⟨?_, ?_, ?_⟩
    · intro ⟨b, y⟩ m'; simp only [mem_prod_eq, mem_sdiff, mem_univ, true_and] at m' ⊢
      refine ⟨?_, (cs1 m'.2).2⟩; apply uu; use cs0 m'.1, (cs1 m'.2).1
    · rw [e, nhdsWithin_prod_eq, nhdsWithin_univ]; exact Filter.prod_mem_prod (co0.mem_nhds cm0) cn1
    · exact cc0.isPreconnected.prod cp1

/-- Nonseparation in a manifold is the same as nonseparation in each chart -/
theorem Nonseparating.complexManifold {t : Set S}
    (h : ∀ z, Nonseparating ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t)) :
    Nonseparating t :=
  { dense := by
      rw [dense_iff_inter_open]; intro u uo ⟨z, m⟩
      by_cases zt : z ∉ t; use z, m, zt
      simp only [not_not] at zt
      generalize hv : (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' u = v
      have vo : IsOpen v := by
        rw [← hv]
        exact (continuousOn_extChartAt_symm z).isOpen_inter_preimage (isOpen_extChartAt_target z) uo
      have vn : v.Nonempty := by
        use extChartAt I z z
        simp only [mem_inter_iff, mem_extChartAt_target, true_and, mem_preimage,
          PartialEquiv.left_inv _ (mem_extChartAt_source z), m, ← hv]
      rcases dense_iff_inter_open.mp (h z).dense v vo vn with ⟨y, m⟩
      use(extChartAt I z).symm y
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, not_and, ← hv] at m
      rcases m with ⟨⟨ym, yu⟩, yt⟩
      simp only [mem_inter_iff, yu, true_and, mem_compl_iff]; exact yt ym
    loc := by
      intro z u zt un
      have m : extChartAt I z z ∈ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' t := by
        simp only [mem_inter_iff, mem_extChartAt_target z, true_and, mem_preimage,
          PartialEquiv.left_inv _ (mem_extChartAt_source z), zt]
      have n : (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' u ∈ 𝓝 (extChartAt I z z) := by
        apply Filter.inter_mem
        exact (isOpen_extChartAt_target z).mem_nhds (mem_extChartAt_target z)
        exact extChartAt_preimage_mem_nhds un
      rcases (h z).loc _ _ m n with ⟨c, cs, cn, cp⟩
      have e : (extChartAt I z).source ∩ extChartAt I z ⁻¹' c = (extChartAt I z).symm '' c := by
        apply Set.ext; intro x; simp only [mem_inter_iff, mem_preimage, mem_image]; constructor
        · intro ⟨xz, xc⟩; refine ⟨_, xc, ?_⟩; simp only [PartialEquiv.left_inv _ xz]
        · intro ⟨y, yc, yx⟩; rw [← yx]
          have xc := cs yc; simp only [mem_sdiff, mem_inter_iff, mem_preimage] at xc
          have yz := xc.1.1; use PartialEquiv.map_target _ yz
          simp only [PartialEquiv.right_inv _ yz, yc]
      use(extChartAt I z).source ∩ extChartAt I z ⁻¹' c; refine ⟨?_, ?_, ?_⟩
      · intro x xm; simp only [mem_inter_iff, mem_preimage] at xm; rcases xm with ⟨xz, xc⟩
        replace xc := cs xc
        simp only [mem_sdiff, mem_inter_iff, mem_preimage, PartialEquiv.map_source _ xz, true_and,
          PartialEquiv.left_inv _ xz] at xc
        exact xc
      · rw [e]; convert Filter.image_mem_map cn
        have ee : ⇑(extChartAt I z).symm = (extChartAt' I z).symm := rfl
        rw [ee, (extChartAt' I z).symm.map_nhdsWithin_eq (mem_extChartAt_target z), ← ee]
        simp only [extChartAt', OpenPartialHomeomorph.symm_source,
          PartialEquiv.left_inv _ (mem_extChartAt_source z), compl_inter, inter_union_distrib_left,
          inter_compl_self, empty_union]
        apply nhdsWithin_eq_nhdsWithin (mem_extChartAt_source z)
          (isOpen_extChartAt_source (I := I) z)
        apply Set.ext; intro x
        simp only [mem_inter_iff, mem_compl_iff, mem_image, mem_preimage]; constructor
        · intro ⟨xt, xz⟩; refine ⟨⟨extChartAt I z x, ?_⟩, xz⟩
          simp only [PartialEquiv.left_inv _ xz, xt, PartialEquiv.map_source _ xz, not_false_iff,
            and_self_iff]
        · intro ⟨⟨y, ⟨⟨yz, yt⟩, yx⟩⟩, _⟩
          simp only [← yx, yt, PartialEquiv.map_target _ yz, not_false_iff, true_and]
      · rw [e]; apply cp.image; apply (continuousOn_extChartAt_symm z).mono
        exact _root_.trans cs (_root_.trans sdiff_subset inter_subset_left) }

/-- A sufficient condition on `t` for `s \ t` to be preconnected, for `s` open and preconnected.
    Roughly, `t` has empty interior and there are arbitrarily small connected rings around each
    `x ∈ t`. -/
theorem IsPreconnected.open_diff {s t : Set X} (sc : IsPreconnected s) (so : IsOpen s)
    (ts : Nonseparating t) : IsPreconnected (s \ t) := by
  rw [isPreconnected_iff_subset_of_disjoint] at sc ⊢
  intro u v uo vo suv duv
  generalize hf : (fun u : Set X ↦ u ∪ {x | x ∈ s ∧ x ∈ t ∧ ∀ᶠ y in 𝓝[tᶜ] x, y ∈ u}) = f
  have mono : ∀ u, u ⊆ f u := by rw [← hf]; exact fun _ ↦ subset_union_left
  have fopen : ∀ {u}, IsOpen u → IsOpen (f u) := by
    intro u o; rw [isOpen_iff_eventually]; intro x m
    by_cases xu : x ∈ u
    · rw [← hf]
      exact (o.eventually_mem xu).mp (.of_forall fun q m ↦ subset_union_left m)
    by_cases xt : x ∉ t
    · contrapose xu; clear xu
      simp only [mem_union, mem_ofPred, xt, false_and, and_false, or_false, ← hf] at m
      exact m
    simp only [not_not] at xt
    have n := m
    simp only [mem_union, xt, xu, false_or, true_and, mem_ofPred,
      eventually_nhdsWithin_iff, ← hf] at n
    refine (so.eventually_mem n.1).mp (n.2.eventually_nhds.mp (.of_forall fun y n m ↦ ?_))
    by_cases yt : y ∈ t
    simp only [mem_union, mem_ofPred, eventually_nhdsWithin_iff, ← hf]; right; use m, yt, n
    exact mono _ (n.self_of_nhds yt)
  have mem : ∀ {x u c}, x ∈ s → x ∈ t → c ∈ 𝓝[tᶜ] x → c ⊆ u → x ∈ f u := by
    intro x u c m xt cn cu; rw [← hf]; right; use m, xt
    simp only [Filter.eventually_iff, ofPred_mem_eq]; exact Filter.mem_of_superset cn cu
  have cover : s ⊆ f u ∪ f v := by
    intro x m
    by_cases xt : x ∉ t; exact union_subset_union (mono _) (mono _) (suv (mem_sdiff_of_mem m xt))
    simp only [not_not] at xt
    rcases ts.loc x s xt (so.mem_nhds m) with ⟨c, cst, cn, cp⟩
    have d := inter_subset_inter_left (u ∩ v) cst; rw [duv, subset_empty_iff] at d
    cases' isPreconnected_iff_subset_of_disjoint.mp cp u v uo vo (_root_.trans cst suv) d with cu cv
    exact subset_union_left (mem m xt cn cu)
    exact subset_union_right (mem m xt cn cv)
  have fdiff : ∀ {u}, f u \ t ⊆ u := by
    intro u x m; simp only [mem_sdiff, mem_union, mem_ofPred, ← hf] at m
    simp only [m.2, false_and, and_false, or_false, not_false_iff, and_true] at m
    exact m
  have fnon : ∀ {x u}, IsOpen u → x ∈ f u → ∀ᶠ y in 𝓝[tᶜ] x, y ∈ u := by
    intro x u o m; simp only [mem_union, mem_ofPred, ← hf] at m
    cases' m with xu m; exact (o.eventually_mem xu).filter_mono nhdsWithin_le_nhds; exact m.2.2
  have disj : s ∩ (f u ∩ f v) = ∅ := by
    contrapose duv; simp only [← ne_eq, ← nonempty_iff_ne_empty] at duv ⊢
    rcases duv with ⟨x, m⟩; simp only [mem_inter_iff] at m
    have b := ((so.eventually_mem m.1).filter_mono nhdsWithin_le_nhds).and
      ((fnon uo m.2.1).and (fnon vo m.2.2))
    simp only [eventually_nhdsWithin_iff] at b
    rcases eventually_nhds_iff.mp b with ⟨n, h, no, xn⟩
    rcases ts.dense.exists_mem_open no ⟨_, xn⟩ with ⟨y, yt, yn⟩
    use y; simp only [mem_inter_iff, mem_sdiff, ← mem_compl_iff]; specialize h y yn yt
    exact ⟨⟨h.1,yt⟩,h.2.1,h.2.2⟩
  cases' sc (f u) (f v) (fopen uo) (fopen vo) cover disj with su sv
  left; exact _root_.trans (sdiff_subset_sdiff_left su) fdiff
  right; exact _root_.trans (sdiff_subset_sdiff_left sv) fdiff

/-- ∅ is nonseparating -/
theorem Nonseparating.empty : Nonseparating (∅ : Set X) :=
  { dense := by simp only [compl_empty, dense_univ]
    loc := by simp only [mem_empty_iff_false, IsEmpty.forall_iff, forall_const, imp_true_iff] }

/-- Punctured complex balls are preconnected -/
theorem IsPreconnected.ball_diff_center {a : ℂ} {r : ℝ} : IsPreconnected (ball a r \ {a}) := by
  by_cases rp : r ≤ 0; simp only [Metric.ball_eq_empty.mpr rp, empty_sdiff]
  exact isPreconnected_empty
  simp only [not_le] at rp
  have e : ball a r \ {a} =
      (fun p : ℝ × ℝ ↦ a + p.1 * Complex.exp (p.2 * Complex.I)) '' Ioo 0 r ×ˢ univ := by
    apply Set.ext; intro z
    simp only [mem_sdiff, mem_ball, Complex.dist_eq, mem_singleton_iff, mem_image, Prod.exists,
      mem_prod_eq, mem_Ioo, mem_univ, and_true]
    constructor
    · intro ⟨zr, za⟩
      use ‖z - a‖, Complex.arg (z - a)
      simp only [norm_pos_iff, Ne, Complex.norm_mul_exp_arg_mul_I, add_sub_cancel, sub_eq_zero, za,
        zr, not_false_iff, and_true]
    · intro ⟨s, t, ⟨s0, sr⟩, e⟩
      simp only [← e, add_sub_cancel_left, norm_mul, Complex.norm_real, abs_of_pos s0,
        Complex.norm_exp_ofReal_mul_I, mul_one, sr, true_and, add_eq_left, mul_eq_zero,
        Complex.exp_ne_zero, or_false, Complex.ofReal_eq_zero, Real.norm_eq_abs]
      exact s0.ne'
  rw [e]; apply IsPreconnected.image; exact isPreconnected_Ioo.prod isPreconnected_univ
  apply Continuous.continuousOn; continuity

/-- `{z}ᶜ` is nonseparating in `ℂ` -/
theorem Complex.nonseparating_singleton (a : ℂ) : Nonseparating ({a} : Set ℂ) :=
  { dense := by
      rw [dense_iff_inter_open]; intro u uo ⟨z, m⟩
      by_cases za : z ≠ a
      · use z; use m; exact za
      simp only [not_not] at za; rw [za] at m; clear za z
      rcases Metric.isOpen_iff.mp uo a m with ⟨r, rp, rs⟩
      use a + r / 2
      simp only [mem_inter_iff, mem_compl_iff, mem_singleton_iff, add_eq_left, div_eq_zero_iff,
        Complex.ofReal_eq_zero, or_false, rp.ne', not_false_iff, and_true, two_ne_zero]
      apply rs
      simp only [mem_ball, dist_self_add_left, norm_div, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_two, abs_of_pos rp, half_lt_self rp]
    loc := by
      intro z u m n; simp only [mem_singleton_iff] at m; simp only [m] at n ⊢; clear m z
      rcases Metric.mem_nhds_iff.mp n with ⟨r, rp, rs⟩
      use ball a r \ {a}; refine ⟨sdiff_subset_sdiff_left rs, ?_, IsPreconnected.ball_diff_center⟩
      exact sdiff_mem_nhdsWithin_compl (Metric.ball_mem_nhds _ rp) _ }

/-- `{z}ᶜ` is nonseparating in 1D complex manifolds -/
theorem AnalyticManifold.nonseparating_singleton (a : S) : Nonseparating ({a} : Set S) := by
  apply Nonseparating.complexManifold; intro z
  by_cases az : a ∈ (extChartAt I z).source
  · convert Complex.nonseparating_singleton (extChartAt I z a)
    simp only [eq_singleton_iff_unique_mem, mem_inter_iff, PartialEquiv.map_source _ az, true_and,
      mem_preimage, mem_singleton_iff, PartialEquiv.left_inv _ az]
    intro x ⟨m, e⟩; simp only [← e, PartialEquiv.right_inv _ m]
  · convert Nonseparating.empty
    simp only [eq_empty_iff_forall_notMem, mem_inter_iff, mem_preimage, mem_singleton_iff, not_and]
    intro x m; contrapose az; rw [← az]
    exact PartialEquiv.map_target _ m

/-- Removing a point in a complex manifold `S` leaves it locally connected -/
public theorem IsPreconnected.open_diff_singleton {s : Set S} (sc : IsPreconnected s) (so : IsOpen s)
    (a : S) : IsPreconnected (s \ {a}) :=
  IsPreconnected.open_diff sc so (AnalyticManifold.nonseparating_singleton a)

/-- Removing a line in `ℂ × S` leaves it locally connected -/
theorem IsPreconnected.open_diff_line {s : Set (ℂ × S)} (sc : IsPreconnected s) (so : IsOpen s)
    (a : S) : IsPreconnected (s \ {p | p.2 = a}) := by
  apply IsPreconnected.open_diff sc so
  have e : {p : ℂ × S | p.2 = a} = univ ×ˢ {a} := by
    apply Set.ext; intro ⟨c, z⟩
    simp only [mem_prod_eq, mem_ofPred, mem_univ, true_and, mem_singleton_iff]
  rw [e]; exact Nonseparating.univ_prod (AnalyticManifold.nonseparating_singleton _)
