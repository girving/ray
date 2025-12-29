module
public import Ray.Dynamics.Defs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Tactic.Cases
import Mathlib.Topology.AlexandrovDiscrete
import Ray.Analytic.Analytic
import Ray.Dynamics.BottcherNear
import Ray.Manifold.Analytic
import Ray.Manifold.Inverse
import Ray.Manifold.Nontrivial
import Ray.Manifold.OneDimension
import Ray.Misc.Multilinear
import Ray.Misc.Topology

/-!
## Böttcher map near a superattracting fixed point

We define superattracting fixed points of a parameterized analytic map `f : ℂ → S → S` on a 1D
complex manifold S (fixed points of order `d ≥ 2`).  If `a` is such a fixpoint, we get Böttcher
coordinates `s.bottcherNear : ℂ → S → ℂ` that conjugate `f c` to `z ^ d` near `a`

  `s.bottcherNear c (f c z) = s.bottcherNear c z ^ d`

`s.bottcherNear` is defined on `s.near`, an open set close enough to `(c,a)` such that (1) it is
contained within the chart, and (2) the local theory of `BottcherNear.lean` applies.  In particular,
iteration sends `s.near` to `s.near`.
-/

open Classical
open Complex (exp log cpow)
open Filter (Tendsto atTop)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped ContDiff NNReal Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}

/-- `f^[n] z` attracts iff `z` does -/
public theorem attracts_shift {f : S → S} {z a : S} (k : ℕ) :
    Attracts f (f^[k] z) a ↔ Attracts f z a := by
  simp only [Attracts, ← Function.iterate_add_apply]
  apply @Filter.tendsto_add_atTop_iff_nat _ fun n ↦ f^[n] z

variable [CompactSpace S] [ChartedSpace ℂ S] [IsManifold I ω S]

-- `d` facts
public lemma Super.dp (s : Super f d a) : 0 < d := lt_trans (by norm_num) s.d2
public lemma Super.dnp (s : Super f d a) {n : ℕ} : 0 < d ^ n := pow_pos s.dp _
public lemma Super.d1 (s : Super f d a) : 1 < d := lt_of_lt_of_le (by norm_num) s.d2
public lemma Super.d0 (s : Super f d a) : d ≠ 0 := s.dp.ne'

-- Teach `bound` about `Super` and `d`
attribute [bound_forward] Super.dp Super.d1

/-- Iterating at `a` does nothing -/
public theorem Super.iter_a (s : Super f d a) (n : ℕ) : (f c)^[n] a = a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply', h, s.f0]

/-- `fl` is analytic -/
public theorem Super.fla (s : Super f d a) (c : ℂ) : AnalyticAt ℂ (uncurry s.fl) (c, 0) := by
  rw [analyticAt_iff_mAnalyticAt II I]
  refine ((analyticAt_id.sub analyticAt_const).mAnalyticAt I I).comp _ ?_
  refine (contMDiffAt_extChartAt' ?_).comp _ ?_
  · simp only [s.f0, extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans, zero_add,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.coe_coe, Function.comp_apply,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.coe_coe_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, ModelWithCorners.left_inv,
      OpenPartialHomeomorph.left_inv, mem_chart_source]
  · refine (s.fa _).comp₂ contMDiffAt_fst ?_
    refine ((contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' ?_)).comp _ ?_
    · simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans, zero_add,
        ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.coe_coe, Function.comp_apply,
        PartialEquiv.trans_target, ModelWithCorners.target_eq,
        ModelWithCorners.toPartialEquiv_coe_symm, Set.mem_inter_iff, Set.mem_range_self,
        Set.mem_preimage, ModelWithCorners.left_inv, OpenPartialHomeomorph.map_source,
        mem_chart_source, and_self_iff]
    · exact (analyticAt_snd.add analyticAt_const).mAnalyticAt _ _

/-- `(f c)^[k]` is analytic -/
theorem Super.mAnalyticAt_iter (s : Super f d a) {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] [IsManifold I ω T]
    {g : ℂ × T → ℂ} {h : ℂ × T → S} {p : ℂ × T} {n : ℕ}
    (ga : ContMDiffAt II I ω g p) (ha : ContMDiffAt II I ω h p) :
    ContMDiffAt II I ω (fun p : ℂ × T ↦ (f (g p))^[n] (h p)) p := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact ha
  simp_rw [Function.iterate_succ']; exact (s.fa _).comp₂ ga h

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuous_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {n : ℕ} (gc : Continuous g) (hc : Continuous h) :
    Continuous fun x ↦ (f (g x))^[n] (h x) := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact hc
  simp_rw [Function.iterate_succ']; exact s.fa.continuous.comp (gc.prodMk h)

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuousOn_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {t : Set T} {n : ℕ} (gc : ContinuousOn g t) (hc : ContinuousOn h t) :
    ContinuousOn (fun x ↦ (f (g x))^[n] (h x)) t := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact hc
  simp_rw [Function.iterate_succ']; exact s.fa.continuous.comp_continuousOn (gc.prodMk h)

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
public theorem Super.continuousAt_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {x : T} {n : ℕ} (gc : ContinuousAt g x) (hc : ContinuousAt h x) :
    ContinuousAt (fun x ↦ (f (g x))^[n] (h x)) x := by
  induction' n with n h; simp only [Function.iterate_zero, id]; exact hc
  simp_rw [Function.iterate_succ']; exact (s.fa _).continuousAt.comp (gc.prodMk h)

/-- `(f c)^[k]` is analytic -/
theorem Super.mAnalytic_iter (s : Super f d a) {k : ℕ} :
    ContMDiff II I ω (fun p : ℂ × S ↦ (f p.1)^[k] p.2) := fun _ ↦
  s.mAnalyticAt_iter contMDiffAt_fst contMDiffAt_snd

/-- `(c,z) ↦ (c, (f c)^[k] z)` is analytic -/
theorem Super.mAnalytic_prod_iter (s : Super f d a) (n : ℕ) :
    ContMDiff II II ω (fun p : ℂ × S ↦ (p.1, (f p.1)^[n] p.2)) := by
  intro p; apply contMDiffAt_fst.prodMk; apply s.mAnalytic_iter

/-- `fl c 0 = 0` -/
theorem Super.fl0 (s : Super f d a) {c : ℂ} : s.fl c 0 = 0 := by
  simp only [Super.fl, _root_.fl, s.f0, Function.comp_apply, zero_add, PartialEquiv.left_inv,
    mem_extChartAt_source, sub_self]

/-- `0` is a critical point for `fl` -/
theorem Super.critical_0 (s : Super f d a) (c : ℂ) : Critical (s.fl c) 0 := by
  simp only [Critical, mfderiv_eq_fderiv, Super.fl]
  have p := (s.fla c).along_snd.leading_approx
  simp only [sub_zero, smul_eq_mul, Super.fl, s.fd, s.fc, mul_one, uncurry] at p
  generalize hg : _root_.fl f a c = g; rw [hg] at p
  have g0 : g 0 = 0 := by rw [← hg]; exact s.fl0
  apply HasFDerivAt.fderiv
  simp only [hasFDerivAt_iff_isLittleO_nhds_zero, sub_zero, zero_add, g0]
  have od : (fun z : ℂ ↦ z ^ d) =o[𝓝 0] (fun z ↦ z) := by
    rw [Asymptotics.isLittleO_iff]; intro e ep
    apply ((@Metric.isOpen_ball ℂ _ 0 (min 1 e)).eventually_mem (mem_ball_self (by bound))).mp
    refine .of_forall fun z b ↦ ?_
    simp only at b; rw [mem_ball_zero_iff, lt_min_iff] at b
    simp only [norm_pow]
    rw [← Nat.sub_add_cancel s.d2, pow_add, pow_two]
    calc ‖z‖ ^ (d - 2) * (‖z‖ * ‖z‖)
      _ ≤ (1:ℝ) ^ (d - 2) * (‖z‖ * ‖z‖) := by bound
      _ = ‖z‖ * ‖z‖ := by simp only [one_pow, one_mul]
      _ ≤ e * ‖z‖ := by bound
  have p' := (p.trans od).add od
  simp only [sub_add_cancel] at p'
  refine p'.congr_left ?_
  intro z; exact (sub_zero _).symm

/-- `a` is a critical point for `f` -/
public theorem Super.critical_a (s : Super f d a) (c : ℂ) : Critical (f c) a := by
  have h := s.critical_0 c
  have e := PartialEquiv.left_inv _ (mem_extChartAt_source (I := I) a)
  contrapose h; simp only [Critical, Super.fl, fl, ← ne_eq] at h ⊢
  simp only [mfderiv_eq_fderiv, _root_.fl, Function.comp_def]
  rw [fderiv_sub_const, ←mfderiv_eq_fderiv]
  apply mderiv_comp_ne_zero' (extChartAt_mderiv_ne_zero' ?_)
  · apply mderiv_comp_ne_zero' (f := f c)
    · rw [zero_add, e]; exact h
    · apply mderiv_comp_ne_zero' (extChartAt_symm_mderiv_ne_zero' ?_)
      · rw [mfderiv_eq_fderiv, fderiv_add_const, ←mfderiv_eq_fderiv]; exact id_mderiv_ne_zero
      · rw [zero_add]; apply mem_extChartAt_target
  · simp only [zero_add, e, s.f0]
    apply mem_extChartAt_source

/-- `f c` is nontrivial at `a` -/
theorem Super.f_nontrivial (s : Super f d a) (c : ℂ) : NontrivialMAnalyticAt (f c) a := by
  refine ⟨(s.fa _).along_snd, ?_⟩; simp only [s.f0]
  have n : ∃ᶠ w in 𝓝 (0 : ℂ), s.fl c w ≠ 0 := by
    have e := (nontrivialMAnalyticAt_of_order (s.fla c).along_snd ?_).nonconst
    · simp only [s.fl0, uncurry] at e; exact e
    · simp only [Super.fl, s.fd, uncurry]; exact s.d0
  contrapose n
  simp only [Filter.not_frequently, not_not, Super.fl, fl] at n ⊢
  have gc : ContinuousAt (fun x ↦ (extChartAt I a).symm (x + extChartAt I a a)) 0 := by
    refine (continuousAt_extChartAt_symm a).comp_of_eq ?_ (by simp only [zero_add])
    exact continuousAt_id.add continuousAt_const
  simp only [ContinuousAt, zero_add, PartialEquiv.left_inv _ (mem_extChartAt_source _)] at gc
  refine (gc.eventually n).mp (.of_forall ?_)
  intro x h; simp only [_root_.fl, Function.comp_def, h, sub_self]

/-- Close enough to `a`, `f c z ∈ (ext_chart_at I a).source` -/
theorem Super.stays_in_chart (s : Super f d a) (c : ℂ) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), f p.1 p.2 ∈ (extChartAt I a).source := by
  apply ContinuousAt.eventually_mem_nhd
  exact (s.fa.continuous.comp continuous_id).continuousAt
  simp only [s.f0, extChartAt_source_mem_nhds a]

/-- There is a open set around the attractor in `ext_chart I a` where things are nice -/
theorem Super.fr_prop (s : Super f d a) (c : ℂ) :
    ∃ r, r > 0 ∧ AnalyticOnNhd ℂ (uncurry s.fl) (ball (c, 0) r) ∧
      ∀ p : ℂ × S, p ∈ (extChartAt II (c, a)).source →
        extChartAt II (c, a) p ∈ ball (extChartAt II (c, a) (c, a)) r →
          f p.1 p.2 ∈ (extChartAt I a).source := by
  rcases(s.fla c).exists_ball_analyticOnNhd with ⟨r0, r0p, fla⟩
  rcases eventually_nhds_iff.mp (s.stays_in_chart c) with ⟨t, tp, ot, ta⟩
  set ch := extChartAt II (c, a)
  set s := ch.target ∩ ch.symm ⁻¹' t
  have os : IsOpen s :=
    (continuousOn_extChartAt_symm (c, a)).isOpen_inter_preimage (isOpen_extChartAt_target (c, a)) ot
  have m : ch (c, a) ∈ s := by
    apply Set.mem_inter (mem_extChartAt_target _)
    rw [Set.mem_preimage, ch.left_inv (mem_extChartAt_source _)]
    exact ta
  rcases Metric.isOpen_iff.mp os (ch (c, a)) m with ⟨r1, r1p, rs⟩
  · use min r0 r1, by bound
    use fla.mono (Metric.ball_subset_ball (by bound))
    intro p ps pr; apply tp p
    rw [← ch.left_inv ps, ← Set.mem_preimage]
    exact Set.mem_of_mem_inter_right (rs (Metric.ball_subset_ball (by bound) pr))

/-- A radius around `(c,0)` on which `f` and `fl` are nice -/
def Super.fr (s : Super f d a) (c : ℂ) : ℝ :=
  choose (s.fr_prop c)

theorem Super.frp (s : Super f d a) (c : ℂ) : 0 < s.fr c :=
  (choose_spec (s.fr_prop c)).1

theorem Super.fla_on (s : Super f d a) (c : ℂ) :
    AnalyticOnNhd ℂ (uncurry s.fl) (ball (c, 0) (s.fr c)) :=
  (choose_spec (s.fr_prop c)).2.1

theorem Super.fr_stays (s : Super f d a) (c : ℂ) (p : ℂ × S)
    (ps : p ∈ (extChartAt II (c, a)).source)
    (pr : extChartAt II (c, a) p ∈ ball (extChartAt II (c, a) (c, a)) (s.fr c)) :
    f p.1 p.2 ∈ (extChartAt I a).source :=
  (choose_spec (s.fr_prop c)).2.2 p ps pr

/-- We'll stay within this set when constructing `s.nice` -/
def Super.fls (s : Super f d a) : Set (ℂ × ℂ) :=
  ⋃ c, ball (c, (0 : ℂ)) (s.fr c)

lemma Super.fls_open (s : Super f d a) : IsOpen s.fls :=
  isOpen_iUnion fun _ ↦ isOpen_ball

/-- `b ∈ ball 0 r → (b,0) ∈ ball 0 r` -/
theorem prod_zero_mem_ball {c b : ℂ} {r : ℝ} (m : b ∈ ball c r) :
    (b, (0 : ℂ)) ∈ ball (c, (0 : ℂ)) r := by
  simp only [Metric.mem_ball] at m; simpa only [Metric.mem_ball, dist_prod_same_right]

/-- `Super → SuperAtC` in charts -/
public theorem Super.superAtC (s : Super f d a) : SuperAtC s.fl d univ :=
  { o := isOpen_univ
    fa := fun {_} _ ↦ s.fla _
    s := fun {c} _ ↦
      { d2 := s.d2
        fd := s.fd _
        fc := s.fc _
        fa0 := (s.fla c).along_snd } }

/-- `Super → SuperNearC` in charts for a suitable set -/
theorem Super.exists_superNearC (s : Super f d a) :
    ∃ t, t ⊆ s.fls ∧ SuperNearC s.fl d univ t (1 / 2) (1 / 4) := by
  refine s.superAtC.superNearC' s.fls_open fun c _ ↦ ?_
  rw [Super.fls, Set.mem_iUnion]; use c; exact mem_ball_self (s.frp c)

/-- The set of points on which `bottcherNear` is defined, in charts -/
public def Super.near' (s : Super f d a) : Set (ℂ × ℂ) :=
  choose s.exists_superNearC

theorem Super.near_subset' (s : Super f d a) : s.near' ⊆ s.fls :=
  (choose_spec s.exists_superNearC).1

/-- The set on which `bottcherNear` is defined, where we are both within the chart and close
    enough to `a` to satisfy the smallness conditions needed for `SuperNearC` -/
public def Super.near (s : Super f d a) : Set (ℂ × S) :=
  (extChartAt II ((0 : ℂ), a)).source ∩
    extChartAt II ((0 : ℂ), a) ⁻¹' {p : ℂ × ℂ | (p.1, p.2 - extChartAt I a a) ∈ s.near'}

public theorem Super.superNearC (s : Super f d a) :
    SuperNearC s.fl d univ s.near' (1 / 2) (1 / 4) :=
  (choose_spec s.exists_superNearC).2

public theorem Super.isOpen_near (s : Super f d a) : IsOpen s.near := by
  apply (continuousOn_extChartAt _).isOpen_inter_preimage (isOpen_extChartAt_source _)
  exact IsOpen.preimage (continuous_fst.prodMk (continuous_snd.sub continuous_const))
    s.superNearC.o

/-- `(c,a)` is near -/
@[simp] public theorem Super.mem_near (s : Super f d a) (c : ℂ) : (c, a) ∈ s.near := by
  simp only [Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, Set.mem_inter_iff,
    mem_extChartAt_source, extChartAt_eq_refl, PartialEquiv.refl_source, Set.mem_univ, true_and,
    Set.mem_preimage, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, Set.mem_setOf_eq, sub_self]
  exact (s.superNearC.s (Set.mem_univ _)).t0

/-- `s.near` stays within the chart -/
theorem Super.near_subset_chart (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near) :
    z ∈ (extChartAt I a).source := by
  have h := Set.mem_of_mem_inter_left m
  simp only [extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod_eq] at h
  exact h.2

theorem Super.mem_near_to_near' (s : Super f d a) {p : ℂ × S} (m : p ∈ s.near) :
    (p.1, extChartAt I a p.2 - extChartAt I a a) ∈ s.near' := by
  have h := Set.mem_of_mem_inter_right m
  simp only [Set.mem_preimage, extChartAt_prod, PartialEquiv.prod_coe, extChartAt_eq_refl,
    PartialEquiv.refl_coe, id] at h
  exact h

/-- Once we're in `s.near`, we stay there -/
public theorem Super.stays_near (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near) :
    (c, f c z) ∈ s.near := by
  simp only [Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, Set.mem_inter_iff,
    extChartAt_eq_refl, PartialEquiv.refl_source, Set.mem_univ, true_and, Set.mem_preimage,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, Set.mem_setOf_eq] at m ⊢
  rcases mem_iUnion.mp (s.near_subset' m.2) with ⟨b, mb⟩
  simp only [mem_ball_iff_norm, Prod.norm_def, max_lt_iff, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at mb
  constructor
  · apply s.fr_stays b (c, z)
    simp only [m.1, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, extChartAt_eq_refl,
      PartialEquiv.refl_source, Set.mem_univ, true_and]
    simp only [mb.1, mb.2, extChartAt_prod, extChartAt_eq_refl, true_and, PartialEquiv.prod_coe,
      PartialEquiv.refl_coe, id, mem_ball_iff_norm, Prod.norm_def, max_lt_iff, Prod.fst_sub,
      Prod.snd_sub]
  · have h := (s.superNearC.s (Set.mem_univ c)).ft m.2
    simp only [Super.fl, _root_.fl, Function.comp_def, sub_add_cancel,
      PartialEquiv.left_inv _ m.1] at h
    exact h

/-- Once we're in `s.near`, we stay there forever -/
public theorem Super.iter_stays_near (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near)
    (n : ℕ) : (c, (f c)^[n] z) ∈ s.near := by
  induction' n with n h; simp only [Function.iterate_zero, id, m]
  simp only [Nat.add_succ, Function.iterate_succ', s.stays_near h, Function.comp_def]

/-- More iterations stay in `s.near` -/
public theorem Super.iter_stays_near' (s : Super f d a) {a b : ℕ} (m : (c, (f c)^[a] z) ∈ s.near)
    (ab : a ≤ b) : (c, (f c)^[b] z) ∈ s.near := by
  rw [← Nat.sub_add_cancel ab, Function.iterate_add_apply]; exact s.iter_stays_near m _

/-- If `z` attracts, it eventually reaches `s.near` -/
theorem Super.reaches_near (s : Super f d a) {z : S} (a : Attracts (f c) z a) :
    ∀ᶠ n in atTop, (c, (f c)^[n] z) ∈ s.near := by
  rw [Attracts, Filter.tendsto_iff_forall_eventually_mem] at a
  have e := a {z | (c, z) ∈ s.near} ?_; exact e
  apply IsOpen.mem_nhds; apply IsOpen.snd_preimage s.isOpen_near; exact s.mem_near c

/-- If `z` reaches `s.near`, it attracts to `a` -/
public theorem Super.attracts (s : Super f d a) {n : ℕ} (r : (c, (f c)^[n] z) ∈ s.near) :
    Attracts (f c) z a := by
  have m := s.mem_near_to_near' r
  have t := iterates_tendsto (s.superNearC.s (Set.mem_univ c)) m
  generalize hg : (fun x : ℂ ↦ (extChartAt I a).symm (x + extChartAt I a a)) = g
  have gc : ContinuousAt g 0 := by
    rw [← hg]
    refine (continuousAt_extChartAt_symm'' ?_).comp
      (continuous_id.add continuous_const).continuousAt
    simp only [zero_add]; exact mem_extChartAt_target a
  have g0 : g 0 = a := by
    simp only [← hg]; simp only [zero_add]; exact PartialEquiv.left_inv _ (mem_extChartAt_source _)
  have h := gc.tendsto.comp t; clear t gc m
  simp only [Function.comp_def, g0] at h
  rw [← attracts_shift n]
  refine Filter.Tendsto.congr ?_ h; clear h
  intro k; simp only [← hg]; induction' k with k h
  simp only [Function.iterate_zero_apply]; rw [sub_add_cancel]
  exact PartialEquiv.left_inv _ (s.near_subset_chart r)
  simp only [Function.iterate_succ_apply']
  generalize hx : (s.fl c)^[k] (extChartAt I a ((f c)^[n] z) - extChartAt I a a) = x; rw [hx] at h
  simp only [Super.fl, _root_.fl, Function.comp_def, sub_add_cancel, h,
    ←Function.iterate_succ_apply' (f c)]
  apply PartialEquiv.left_inv _ (s.near_subset_chart (s.iter_stays_near r _))

/-- The basin is all points that reach `s.near` -/
public lemma Super.basin_iff_near (s : Super f d a) {p : ℂ × S} :
    p ∈ s.basin ↔ ∃ n, (p.1, (f p.1)^[n] p.2) ∈ s.near := by
  constructor
  · intro m
    simp only [basin, mem_setOf_eq] at m
    have e : ∀ᶠ n in atTop, (f p.1)^[n] p.2 ∈ {x : S | (p.1, x) ∈ s.near} :=
      m.eventually_mem ((s.isOpen_near.snd_preimage p.1).mem_nhds (by simp))
    exact e.exists
  · intro ⟨n,  m⟩
    exact s.attracts m

/-- Anything in `s.basin` attracts -/
public theorem Super.basin_attracts (s : Super f d a) (m : (c, z) ∈ s.basin) :
    Attracts (f c) z a := by
  rcases s.basin_iff_near.mp m with ⟨n, m⟩
  exact s.attracts m

public theorem Super.isOpen_preimage (s : Super f d a) (n : ℕ) :
    IsOpen {p : ℂ × S | (p.1, (f p.1)^[n] p.2) ∈ s.near} :=
  IsOpen.preimage (continuous_fst.prodMk (s.continuous_iter continuous_fst continuous_snd))
    s.isOpen_near

/-- `s.basin` is open -/
public theorem Super.isOpen_basin (s : Super f d a) : IsOpen s.basin := by
  have e : s.basin = ⋃ n, {p : ℂ × S | (p.1, (f p.1)^[n] p.2) ∈ s.near} := by
    ext p; simp [s.basin_iff_near]
  rw [e]
  exact isOpen_iUnion fun n ↦ s.isOpen_preimage n

/-- Anything in `s.basin` is eventually in `s.near` -/
public theorem Super.basin_stays (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∀ᶠ n in atTop, (c, (f c)^[n] z) ∈ s.near := by
  rcases s.basin_iff_near.mp m with ⟨n, m⟩
  rw [Filter.eventually_atTop]; use n; intro k kn
  rw [← Nat.sub_add_cancel kn, Function.iterate_add_apply]
  exact s.iter_stays_near m _

/-- `s.basin` is exactly the set of attracting points -/
public theorem Super.basin_iff_attracts (s : Super f d a) :
    (c, z) ∈ s.basin ↔ Attracts (f c) z a := by
  constructor
  · exact s.basin_attracts
  · intro h
    rcases tendsto_atTop_nhds.mp h {z | (c, z) ∈ s.near} (s.mem_near c)
      (s.isOpen_near.snd_preimage c) with ⟨n, h⟩
    simp only [s.basin_iff_near]
    exact ⟨n, h _ (le_refl _)⟩

/-- `f` acting on and returning pairs -/
@[expose] public def Super.fp (_ : Super f d a) : ℂ × S → ℂ × S := fun p : ℂ × S ↦ (p.1, f p.1 p.2)

/-- `s.fp` is analytic -/
public theorem Super.fpa (s : Super f d a) : ContMDiff II II ω s.fp := fun _ ↦
  contMDiffAt_fst.prodMk (s.fa _)

theorem Super.fp1 (s : Super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).1 = p.1 := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply]
  · simp only [Function.iterate_succ_apply', h, fp]

theorem Super.fp2 (s : Super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).2 = (f p.1)^[n] p.2 := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply]
  · simp only [Function.iterate_succ_apply', s.fp1 n p, h, fp]

/-- `s.bottcherNear` is analytic -/
theorem Super.bottcherNear_mAnalytic (s : Super f d a) :
    ContMDiffOn II I ω (uncurry s.bottcherNear) s.near := by
  intro p m
  have e : uncurry s.bottcherNear =
      (fun p : ℂ × ℂ ↦ _root_.bottcherNear (s.fl p.1) d p.2) ∘ fun p : ℂ × S ↦
        (p.1, extChartAt I a p.2 - extChartAt I a a) :=
    rfl
  rw [e]; clear e
  have h1 := (bottcherNear_analytic s.superNearC _ (s.mem_near_to_near' m)).mAnalyticAt II I
  have h2 : ContMDiffAt II II ω (fun p : ℂ × S ↦
      (p.1, extChartAt I a p.2 - extChartAt I a a)) p := by
    apply contMDiffAt_fst.prodMk; apply ContMDiffAt.sub
    exact (contMDiffAt_extChartAt' (extChartAt_source I a ▸ (s.near_subset_chart m))).comp _ contMDiffAt_snd
    exact contMDiffAt_const
  exact (h1.comp_of_eq h2 rfl).contMDiffWithinAt

/-- `s.bottcherNear` is analytic -/
public theorem Super.bottcherNear_mAnalytic' (s : Super f d a) {p : ℂ × S} (m : p ∈ s.near) :
    ContMDiffAt II I ω (uncurry s.bottcherNear) p :=
  s.bottcherNear_mAnalytic.contMDiffAt (s.isOpen_near.mem_nhds m)

public theorem Super.bottcherNearIter_mAnalytic (s : Super f d a) {n : ℕ}
    (r : (c, (f c)^[n] z) ∈ s.near) :
    ContMDiffAt II I ω (uncurry (s.bottcherNearIter n)) (c, z) := by
  -- For this reason this doesn't infer unless we give tons of type hints
  apply ContMDiffAt.comp (g := uncurry (s.bottcherNear)) (f := fun p ↦ (p.1, (f p.1)^[n] p.2))
    (x := (c, z)) (I := II) (I' := II) (I'' := I)
  · exact s.bottcherNear_mAnalytic' r
  · exact contMDiffAt_fst.prodMk (s.mAnalytic_iter _)

/-- `s.bottcherNear` satisfies the defining equation -/
public theorem Super.bottcherNear_eqn (s : Super f d a) (m : (c, z) ∈ s.near) :
    s.bottcherNear c (f c z) = s.bottcherNear c z ^ d := by
  simp only [Super.bottcherNear]
  have e : extChartAt I a (f c z) - extChartAt I a a =
      s.fl c (extChartAt I a z - extChartAt I a a) := by
    simp only [Function.comp_def, Super.fl, _root_.fl, sub_add_cancel,
      PartialEquiv.left_inv _ (s.near_subset_chart m)]
  rw [e, _root_.bottcherNear_eqn (s.superNearC.s (Set.mem_univ c)) (s.mem_near_to_near' m)]

/-- `s.bottcherNear_eqn` iterated -/
public theorem Super.bottcherNear_eqn_iter (s : Super f d a) (m : (c, z) ∈ s.near) {n : ℕ} :
    s.bottcherNear c ((f c)^[n] z) = s.bottcherNear c z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  simp only [Function.iterate_succ_apply', s.bottcherNear_eqn (s.iter_stays_near m n), h, ←
    pow_mul, ← pow_succ]

/-- The defining equation in terms of `s.bottcherNearp` and `s.fp` -/
theorem Super.bottcherNearp_eqn (s : Super f d a) {p : ℂ × S} (m : p ∈ s.near) :
    s.bottcherNearp (s.fp p) = s.bottcherNearp p ^ d := by
  rcases p with ⟨c, z⟩
  exact s.bottcherNear_eqn m

/-- `abs (s.bottcherNear c z) < 1` -/
public theorem Super.bottcherNear_lt_one (s : Super f d a) (m : (c, z) ∈ s.near) :
    ‖s.bottcherNear c z‖ < 1 := by
  simp only [Super.bottcherNear]
  exact _root_.bottcherNear_lt_one (s.superNearC.s (Set.mem_univ c)) (s.mem_near_to_near' m)

/-- `s.bottcherNear = 0` only at `a` -/
public theorem Super.bottcherNear_eq_zero (s : Super f d a) (m : (c, z) ∈ s.near) :
    s.bottcherNear c z = 0 ↔ z = a := by
  simp only [Super.bottcherNear]; constructor
  · intro za; contrapose za
    apply bottcherNear_ne_zero (s.superNearC.s (Set.mem_univ _)) (s.mem_near_to_near' m)
    simp only [sub_ne_zero]
    exact (extChartAt I a).injOn.ne (s.near_subset_chart m) (mem_extChartAt_source a) za
  · intro za; simp only [za, sub_self, bottcherNear_zero]

/-- `s.bottcherNear c a = 0` -/
public theorem Super.bottcherNear_a (s : Super f d a) : s.bottcherNear c a = 0 := by
  simp only [Super.bottcherNear, sub_self, bottcherNear_zero]

/-- `s.bottcherNear' ≠ 0` at `0` -/
public theorem Super.bottcherNear_mfderiv_ne_zero (s : Super f d a) (c : ℂ) :
    mfderiv I I (s.bottcherNear c) a ≠ 0 := by
  apply mderiv_comp_ne_zero' (f := _root_.bottcherNear (s.fl c) d)
  · simp only [sub_self, mfderiv_eq_fderiv,
      (_root_.bottcherNear_monic (s.superNearC.s (Set.mem_univ c))).hasFDerivAt.fderiv]
    exact ContinuousLinearMap.smulRight_ne_zero ContinuousLinearMap.one_ne_zero (by norm_num)
  · have u : (fun z : S ↦ extChartAt I a z - extChartAt I a a) =
        extChartAt I a - fun _ : S ↦ extChartAt I a a := rfl
    rw [u, mfderiv_sub, mfderiv_const, sub_zero]
    · exact extChartAt_mderiv_ne_zero a
    · exact (contMDiffAt_extChartAt' (mem_chart_source _ a)).mdifferentiableAt one_ne_zero
    · apply mdifferentiableAt_const

/-- `s.bottcherNear` is invertible near any `(c,a)` -/
theorem Super.bottcherNear_has_inv (s : Super f d a) (c : ℂ) :
    ∃ bi : ℂ → ℂ → S,
      ContMDiffAt II I ω (uncurry bi) (c, 0) ∧
        (∀ᶠ p : ℂ × S in 𝓝 (c, a), bi p.1 (s.bottcherNear p.1 p.2) = p.2) ∧
          ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear p.1 (bi p.1 p.2) = p.2 := by
  have h := complex_inverse_fun (s.bottcherNear_mAnalytic' (s.mem_near c))
      (s.bottcherNear_mfderiv_ne_zero c)
  simp only [s.bottcherNear_a] at h; exact h

/-- `f` is locally noncritical near (but not at) `a`.
    This is a depressingly long proof for a very simple conceptual argument. -/
theorem Super.f_noncritical_near_a (s : Super f d a) (c : ℂ) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), Critical (f p.1) p.2 ↔ p.2 = a := by
  have t : ContinuousAt (fun p : ℂ × S ↦ (p.1, extChartAt I a p.2 - extChartAt I a a)) (c, a) := by
    refine continuousAt_fst.prodMk (ContinuousAt.sub ?_ continuousAt_const)
    exact (continuousAt_extChartAt a).comp_of_eq continuousAt_snd rfl
  simp only [ContinuousAt, sub_self] at t
  apply (inChart_critical (s.fa (c, a))).mp
  apply (t.eventually (df_ne_zero s.superNearC (Set.mem_univ c))).mp
  have am := mem_extChartAt_source (I := I) a
  have em := ((isOpen_extChartAt_source a).eventually_mem am).prod_inr (𝓝 c)
  simp only [← nhds_prod_eq] at em; apply em.mp
  have ezm : ∀ᶠ p : ℂ × S in 𝓝 (c, a), f p.1 p.2 ∈ (extChartAt I a).source := by
    refine (s.fa _).continuousAt.eventually_mem (extChartAt_source_mem_nhds' ?_)
    simp only [uncurry, s.f0, mem_extChartAt_source a]
  apply ezm.mp
  refine .of_forall ?_; clear t em
  intro ⟨e, z⟩ ezm zm d0 m0; simp only at ezm zm d0 m0 ⊢
  simp only [Super.fl, fl, sub_eq_zero, (PartialEquiv.injOn _).eq_iff zm am] at d0
  simp only [Critical, m0, ← d0]
  unfold inChart
  clear m0 d0
  generalize hg : (fun w ↦ extChartAt I (f c a) (f e ((extChartAt I a).symm w))) = g
  have hg' : extChartAt I a ∘ f e ∘ (extChartAt I a).symm = g := by
    rw [← hg]; simp only [Function.comp_def, s.f0]
  rw [_root_.fl, hg']; clear hg'; rw [Iff.comm]
  have dg : DifferentiableAt ℂ g (extChartAt I a z) := by
    rw [← hg]
    apply AnalyticAt.differentiableAt
    apply ContMDiffAt.analyticAt I I
    simp only [s.f0]
    apply (contMDiffAt_extChartAt' _).comp; apply (s.fa _).along_snd.comp
    exact (contMDiffOn_extChartAt_symm _).contMDiffAt
      (extChartAt_target_mem_nhds' (PartialEquiv.map_source _ zm))
    simp only [PartialEquiv.left_inv _ zm]; exact extChartAt_source I a ▸ ezm
  have d0 : ∀ z, DifferentiableAt ℂ (fun z ↦ z - extChartAt I a a) z := fun z ↦
    differentiableAt_id.sub (differentiableAt_const _)
  have d1 : DifferentiableAt ℂ (g ∘ fun z : ℂ ↦ z + extChartAt I a a)
      (extChartAt I a z - extChartAt I a a) := by
    apply DifferentiableAt.comp; simp only [sub_add_cancel, dg]
    exact differentiableAt_id.add (differentiableAt_const _)
  simp only [deriv_comp _ (d0 _) d1, deriv_sub_const, deriv_id'', one_mul]
  rw [deriv_comp _ _ _]
  · simp only [deriv_add_const, deriv_id'', mul_one, sub_add_cancel]
  · simp only [sub_add_cancel, dg]
  · exact differentiableAt_id.add (differentiableAt_const _)

/-- Critical points that are not `a` are closed, because `a` is an isolated critical point in `z` -/
public theorem Super.isClosed_critical_not_a (s : Super f d a) :
    IsClosed {p : ℂ × S | Critical (f p.1) p.2 ∧ p.2 ≠ a} := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually]; intro ⟨c, z⟩ m
  by_cases za : z = a
  · rw [za]; refine (s.f_noncritical_near_a c).mp (.of_forall ?_); intro ⟨e, w⟩ h
    simp only [mem_compl_iff, mem_setOf, not_and, not_not] at h ⊢; exact h.1
  · have o := isOpen_iff_eventually.mp (isOpen_noncritical s.fa)
    simp only [za, mem_compl_iff, mem_setOf, not_and, not_not, imp_false] at m o ⊢
    refine (o (c, z) m).mp (.of_forall ?_); intro ⟨e, w⟩ a b; exfalso; exact a b

/-- If `z ∈ s.basin`, iterating enough takes us to a noncritical point of `s.bottcherNear` -/
public theorem Super.eventually_noncritical (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∀ᶠ n in atTop, mfderiv I I (s.bottcherNear c) ((f c)^[n] z) ≠ 0 :=
  (s.basin_attracts m).eventually
    (mfderiv_ne_zero_eventually (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd
      (s.bottcherNear_mfderiv_ne_zero c))

/-- `s.bottcherNearIter` is noncritical given noncriticality of the two parts -/
public theorem Super.bottcherNearIter_mfderiv_ne_zero (s : Super f d a)
    (b0 : mfderiv I I (s.bottcherNear c) ((f c)^[n] z) ≠ 0) (f0 : ¬Precritical (f c) z) :
    mfderiv I I (s.bottcherNearIter n c) z ≠ 0 := by
  apply mderiv_comp_ne_zero' b0; contrapose f0
  exact critical_iter s.fa.along_snd f0

/-- `f c^[n]` is nontrivial at `a` -/
theorem Super.iter_nontrivial_a [T2Space S] (s : Super f d a) :
    NontrivialMAnalyticAt (fun z ↦ (f c)^[n] z) a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]; apply nontrivialMAnalyticAt_id
  simp only [Function.iterate_succ_apply']; refine NontrivialMAnalyticAt.comp ?_ h
  simp only [s.iter_a]; exact s.f_nontrivial c

/-- `s.bottcherNearIter` is nontrivial at `a` -/
public theorem Super.bottcherNearIter_nontrivial_a [T2Space S] (s : Super f d a) :
    NontrivialMAnalyticAt (s.bottcherNearIter n c) a :=
  haveI b : NontrivialMAnalyticAt (s.bottcherNear c) ((f c)^[n] a) := by
    simp only [s.iter_a]
    exact nontrivialMAnalyticAt_of_mfderiv_ne_zero
      (s.bottcherNear_mAnalytic' (s.mem_near c)).along_snd
      (s.bottcherNear_mfderiv_ne_zero c)
  b.comp s.iter_nontrivial_a
