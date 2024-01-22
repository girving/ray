import Mathlib.Topology.AlexandrovDiscrete
import Ray.Dynamics.BottcherNear
import Ray.AnalyticManifold.AnalyticManifold
import Ray.AnalyticManifold.Inverse
import Ray.AnalyticManifold.Nontrivial
import Ray.AnalyticManifold.OneDimension
import Ray.Misc.Topology
import Ray.Tactic.Bound

/-!
## Böttcher map near a superattracting fixed point

We define superattracting fixed points of a parameterized holomorphic map `f : ℂ → S → S` on a 1D
complex manifold S (fixed points of order `d ≥ 2`).  If `a` is such a fixpoint, we get Böttcher
coordinates `s.bottcherNear : ℂ → S → ℂ` that conjugate `f c` to `z ^ d` near `a`

  `s.bottcherNear c (f c z) = s.bottcherNear c z ^ d`

`s.bottcherNear` is defined on `s.near`, an open set close enough to `(c,a)` such that (1) it is
contained within the chart, and (2) the local theory of `BottcherNear.lean` applies.  In particular,
iteration sends `s.near` to `s.near`.
-/

open Classical
open Complex (exp log abs cpow)
open Filter (Tendsto atTop eventually_of_forall)
open Function (curry uncurry)
open Metric (ball closedBall isOpen_ball ball_mem_nhds mem_ball_self nonempty_ball)
open Nat (iterate)
open OneDimension
open Set
open scoped NNReal Topology
noncomputable section

-- All information for a monic superattracting fixed point at the origin
variable {S : Type} [TopologicalSpace S] [CompactSpace S] [T3Space S] [ChartedSpace ℂ S]
  [AnalyticManifold I S]
variable {f : ℂ → S → S}
variable {c : ℂ}
variable {a z : S}
variable {d n : ℕ}
variable {p : ℂ × S}

/-- `z` tends to `a` under `f`-iteration -/
def Attracts (f : S → S) (z a : S) :=
  Tendsto (fun n ↦ f^[n] z) atTop (𝓝 a)

/-- `f^[n] z` attracts iff `z` does -/
theorem attracts_shift {f : S → S} {z a : S} (k : ℕ) : Attracts f (f^[k] z) a ↔ Attracts f z a := by
  simp only [Attracts, ← Function.iterate_add_apply]
  apply @Filter.tendsto_add_atTop_iff_nat _ fun n ↦ f^[n] z

/-- `f` as `ℂ → ℂ → ℂ` in charts, with the attractor at `0` -/
def fl {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] (f : ℂ → S → S) (a : S) : ℂ → ℂ → ℂ :=
  fun c ↦
  (fun z ↦ z - extChartAt I a a) ∘
    (extChartAt I a ∘ f c ∘ (extChartAt I a).symm) ∘ fun z ↦ z + extChartAt I a a

/-- `f c` has a monic superattracting fixpoint at `a`, for all `c` -/
structure Super {S : Type} [TopologicalSpace S] [CompactSpace S] [ChartedSpace ℂ S]
    [AnalyticManifold I S]
    (f : ℂ → S → S) (d : ℕ) (a : S) : Prop where
  d2 : 2 ≤ d
  fa : Holomorphic ((modelWithCornersSelf ℂ ℂ).prod I) I (uncurry f)
  f0 : ∀ c, f c a = a
  fd : ∀ c, orderAt (fl f a c) 0 = d
  fc : ∀ c, leadingCoeff (fl f a c) 0 = 1

-- `d` facts
theorem Super.dp (s : Super f d a) : 0 < d := lt_trans (by norm_num) s.d2
theorem Super.dnp (s : Super f d a) {n : ℕ} : 0 < d ^ n := pow_pos s.dp _
theorem Super.d1 (s : Super f d a) : 1 < d := lt_of_lt_of_le (by norm_num) s.d2
theorem Super.d0 (s : Super f d a) : d ≠ 0 := s.dp.ne'

/-- `s.fl` is `fl` with a few arguments filled in -/
@[nolint unusedArguments] def Super.fl (_ : Super f d a) := _root_.fl f a

/-- Iterating at `a` does nothing -/
theorem Super.iter_a (s : Super f d a) (n : ℕ) : (f c)^[n] a = a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply', h, s.f0]

/-- `fl` is analytic -/
theorem Super.fla (s : Super f d a) (c : ℂ) : AnalyticAt ℂ (uncurry s.fl) (c, 0) := by
  rw [@analyticAt_iff_holomorphicAt _ _ (ℂ × ℂ) (ModelProd ℂ ℂ) _ _ _ _ ℂ ℂ _ _ _ _ II I]
  refine' (((analyticAt_id _ _).sub analyticAt_const).holomorphicAt I I).comp _
  refine' (HolomorphicAt.extChartAt _).comp _
  simp only [s.f0, extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.coe_coe, Function.comp_apply, zero_add,
    PartialEquiv.coe_trans_symm, PartialHomeomorph.coe_coe_symm, ModelWithCorners.toPartialEquiv_coe_symm,
    ModelWithCorners.left_inv, PartialHomeomorph.left_inv, mem_chart_source, PartialEquiv.trans_source,
    ModelWithCorners.source_eq, Set.preimage_univ, Set.inter_univ]
  refine' (s.fa _).comp₂ holomorphicAt_fst _
  refine' (HolomorphicAt.extChartAt_symm _).comp _
  simp only [extChartAt, PartialHomeomorph.extend, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.coe_coe, Function.comp_apply, zero_add,
    PartialEquiv.trans_target, ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm,
    Set.mem_inter_iff, Set.mem_range_self, Set.mem_preimage, ModelWithCorners.left_inv,
    PartialHomeomorph.map_source, mem_chart_source, and_self_iff]
  exact ((analyticAt_snd _).add analyticAt_const).holomorphicAt _ _

/-- `(f c)^[k]` is holomorphic -/
theorem Super.holomorphicAt_iter (s : Super f d a) {T : Type} [TopologicalSpace T]
    [ChartedSpace ℂ T] {g : ℂ × T → ℂ} {h : ℂ × T → S} {p : ℂ × T} {n : ℕ}
    (ga : HolomorphicAt II I g p) (ha : HolomorphicAt II I h p) :
    HolomorphicAt II I (fun p : ℂ × T ↦ (f (g p))^[n] (h p)) p := by
  induction' n with n h; simp only [Function.iterate_zero, id.def]; exact ha
  simp_rw [Function.iterate_succ']; exact (s.fa _).comp₂ ga h

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuous_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {n : ℕ} (gc : Continuous g) (hc : Continuous h) :
    Continuous fun x ↦ (f (g x))^[n] (h x) := by
  induction' n with n h; simp only [Function.iterate_zero, id.def]; exact hc
  simp_rw [Function.iterate_succ']; exact s.fa.continuous.comp (gc.prod_mk h)

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuousOn_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {t : Set T} {n : ℕ} (gc : ContinuousOn g t) (hc : ContinuousOn h t) :
    ContinuousOn (fun x ↦ (f (g x))^[n] (h x)) t := by
  induction' n with n h; simp only [Function.iterate_zero, id.def]; exact hc
  simp_rw [Function.iterate_succ']; exact s.fa.continuous.comp_continuousOn (gc.prod h)

/-- `(f c)^[k] z` is continuous when `c,z` vary continuously -/
theorem Super.continuousAt_iter (s : Super f d a) {T : Type} [TopologicalSpace T] {g : T → ℂ}
    {h : T → S} {x : T} {n : ℕ} (gc : ContinuousAt g x) (hc : ContinuousAt h x) :
    ContinuousAt (fun x ↦ (f (g x))^[n] (h x)) x := by
  induction' n with n h; simp only [Function.iterate_zero, id.def]; exact hc
  simp_rw [Function.iterate_succ']; exact (s.fa _).continuousAt.comp (gc.prod h)

/-- `(f c)^[k]` is holomorphic -/
theorem Super.holomorphic_iter (s : Super f d a) {k : ℕ} :
    Holomorphic II I fun p : ℂ × S ↦ (f p.1)^[k] p.2 := fun _ ↦
  s.holomorphicAt_iter holomorphicAt_fst holomorphicAt_snd

/-- `(c,z) ↦ (c, (f c)^[k] z)` is holomorphic -/
theorem Super.holomorphic_prod_iter (s : Super f d a) (n : ℕ) :
    Holomorphic II II fun p : ℂ × S ↦ (p.1, (f p.1)^[n] p.2) := by
  intro p; apply holomorphicAt_fst.prod; apply s.holomorphic_iter

/-- `fl c 0 = 0` -/
theorem Super.fl0 (s : Super f d a) {c : ℂ} : s.fl c 0 = 0 := by
  simp only [Super.fl, _root_.fl, s.f0, Function.comp_apply, zero_add, PartialEquiv.left_inv,
    mem_extChartAt_source, sub_self]

/-- `0` is a critical point for `fl` -/
theorem Super.critical_0 (s : Super f d a) (c : ℂ) : Critical (s.fl c) 0 := by
  simp only [Critical, mfderiv_eq_fderiv, Super.fl]
  have p := (s.fla c).along_snd.leading_approx
  simp only [sub_zero, Algebra.id.smul_eq_mul, Super.fl, s.fd, s.fc, mul_one, uncurry] at p
  generalize hg : _root_.fl f a c = g; rw [hg] at p
  have g0 : g 0 = 0 := by rw [← hg]; exact s.fl0
  apply HasFDerivAt.fderiv
  simp only [hasFDerivAt_iff_isLittleO_nhds_zero, ContinuousLinearMap.zero_apply, sub_zero,
    zero_add, g0]
  have od : (fun z : ℂ ↦ z ^ d) =o[𝓝 0] (fun z ↦ z) := by
    rw [Asymptotics.isLittleO_iff]; intro e ep
    apply ((@Metric.isOpen_ball ℂ _ 0 (min 1 e)).eventually_mem (mem_ball_self (by bound))).mp
    refine' eventually_of_forall fun z b ↦ _
    simp only at b; rw [mem_ball_zero_iff, Complex.norm_eq_abs, lt_min_iff] at b
    simp only [Complex.norm_eq_abs, Complex.abs.map_pow]
    rw [← Nat.sub_add_cancel s.d2, pow_add, pow_two]
    calc abs z ^ (d - 2) * (abs z * abs z)
      _ ≤ (1:ℝ) ^ (d - 2) * (abs z * abs z) := by bound [b.1]
      _ = abs z * abs z := by simp only [one_pow, one_mul]
      _ ≤ e * abs z := by bound [b.2]
  have p' := (p.trans od).add od
  simp only [sub_add_cancel] at p'
  refine p'.congr_left ?_
  intro z; exact (sub_zero _).symm

/-- `a` is a critical point for `f` -/
theorem Super.critical_a (s : Super f d a) (c : ℂ) : Critical (f c) a := by
  have h := s.critical_0 c
  have e := PartialEquiv.left_inv _ (mem_extChartAt_source I a)
  contrapose h; simp only [Critical, Super.fl, fl, ← Ne.def] at h ⊢
  simp only [mfderiv_eq_fderiv, _root_.fl, Function.comp]
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
theorem Super.f_nontrivial (s : Super f d a) (c : ℂ) : NontrivialHolomorphicAt (f c) a := by
  refine' ⟨(s.fa _).along_snd, _⟩; simp only [s.f0]
  have n : ∃ᶠ w in 𝓝 (0 : ℂ), s.fl c w ≠ 0 := by
    have e := (nontrivialHolomorphicAt_of_order (s.fla c).along_snd ?_).nonconst
    · simp only [s.fl0, uncurry] at e; exact e
    · simp only [Super.fl, s.fd, uncurry]; exact s.d0
  contrapose n
  simp only [Filter.not_frequently, not_not, Super.fl, fl, Function.comp, sub_eq_zero] at n ⊢
  have gc : ContinuousAt (fun x ↦ (extChartAt I a).symm (x + extChartAt I a a)) 0 := by
    refine' (continuousAt_extChartAt_symm I a).comp_of_eq _ (by simp only [zero_add])
    exact continuousAt_id.add continuousAt_const
  simp only [ContinuousAt, zero_add, PartialEquiv.left_inv _ (mem_extChartAt_source _ _)] at gc
  refine' (gc.eventually n).mp (eventually_of_forall _)
  intro x h; simp only [_root_.fl, Function.comp, h, sub_self]

/-- Close enough to `a`, `f c z ∈ (ext_chart_at I a).source` -/
theorem Super.stays_in_chart (s : Super f d a) (c : ℂ) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), f p.1 p.2 ∈ (extChartAt I a).source := by
  apply ContinuousAt.eventually_mem_nhd
  exact (s.fa.continuous.comp continuous_id).continuousAt
  simp only [s.f0, Function.comp_id, Function.uncurry_apply_pair, extChartAt_source_mem_nhds I a]

/-- There is a open set around the attractor in `ext_chart I a` where things are nice -/
theorem Super.fr_prop (s : Super f d a) (c : ℂ) :
    ∃ r, r > 0 ∧ AnalyticOn ℂ (uncurry s.fl) (ball (c, 0) r) ∧
      ∀ p : ℂ × S, p ∈ (extChartAt II (c, a)).source →
        extChartAt II (c, a) p ∈ ball (extChartAt II (c, a) (c, a)) r →
          f p.1 p.2 ∈ (extChartAt I a).source := by
  rcases(s.fla c).exists_ball_analyticOn with ⟨r0, r0p, fla⟩
  rcases eventually_nhds_iff.mp (s.stays_in_chart c) with ⟨t, tp, ot, ta⟩
  set ch := extChartAt II (c, a)
  set s := ch.target ∩ ch.symm ⁻¹' t
  have os : IsOpen s :=
    (continuousOn_extChartAt_symm II (c, a)).isOpen_inter_preimage
      (extChartAt_open_target II (c, a)) ot
  have m : ch (c, a) ∈ s := by
    apply Set.mem_inter (mem_extChartAt_target _ _)
    rw [Set.mem_preimage, ch.left_inv (mem_extChartAt_source _ _)]
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
    AnalyticOn ℂ (uncurry s.fl) (ball (c, 0) (s.fr c)) :=
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
theorem Super.superAtC (s : Super f d a) : SuperAtC s.fl d univ :=
  { o := isOpen_univ
    fa := fun {_} _ ↦ s.fla _
    s := fun {c} _ ↦
      { d2 := s.d2
        fd := s.fd _
        fc := s.fc _
        fa0 := (s.fla c).along_snd } }

/-- `Super → SuperNearC` in charts for a suitable set -/
theorem Super.exists_superNearC (s : Super f d a) : ∃ t, t ⊆ s.fls ∧ SuperNearC s.fl d univ t := by
  refine' s.superAtC.superNearC' s.fls_open fun c _ ↦ _
  rw [Super.fls, Set.mem_iUnion]; use c; exact mem_ball_self (s.frp c)

/-- The set of points on which `bottcherNear` is defined, in charts -/
def Super.near' (s : Super f d a) : Set (ℂ × ℂ) :=
  choose s.exists_superNearC

theorem Super.near_subset' (s : Super f d a) : s.near' ⊆ s.fls :=
  (choose_spec s.exists_superNearC).1

/-- The set on which `bottcherNear` is defined, where we are both within the chart and close
    enough to `a` to satisfy the smallness conditions needed for `SuperNearC` -/
def Super.near (s : Super f d a) : Set (ℂ × S) :=
  (extChartAt II ((0 : ℂ), a)).source ∩
    extChartAt II ((0 : ℂ), a) ⁻¹' {p : ℂ × ℂ | (p.1, p.2 - extChartAt I a a) ∈ s.near'}

theorem Super.superNearC (s : Super f d a) : SuperNearC s.fl d univ s.near' :=
  (choose_spec s.exists_superNearC).2

theorem Super.isOpen_near (s : Super f d a) : IsOpen s.near := by
  apply (continuousOn_extChartAt _ _).isOpen_inter_preimage (isOpen_extChartAt_source _ _)
  exact IsOpen.preimage (continuous_fst.prod_mk (continuous_snd.sub continuous_const))
    s.superNearC.o

/-- `(c,a)` is near -/
theorem Super.mem_near (s : Super f d a) (c : ℂ) : (c, a) ∈ s.near := by
  simp only [Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, Set.mem_inter_iff,
    mem_extChartAt_source, extChartAt_eq_refl, PartialEquiv.refl_source, Set.mem_univ, true_and_iff,
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
theorem Super.stays_near (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near) :
    (c, f c z) ∈ s.near := by
  simp only [Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod, Set.mem_inter_iff,
    mem_extChartAt_source, extChartAt_eq_refl, PartialEquiv.refl_source, Set.mem_univ, true_and_iff,
    Set.mem_preimage, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id, Set.mem_setOf_eq,
    sub_self] at m ⊢
  rcases mem_iUnion.mp (s.near_subset' m.2) with ⟨b, mb⟩
  simp only [mem_ball_iff_norm, Prod.norm_def, max_lt_iff, Prod.fst_sub, Prod.snd_sub,
    sub_zero] at mb
  constructor
  · apply s.fr_stays b (c, z)
    simp only [m.1, Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod,
      Set.mem_inter_iff, mem_extChartAt_source, extChartAt_eq_refl, PartialEquiv.refl_source,
      Set.mem_univ, true_and_iff, Set.mem_preimage, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id,
      Set.mem_setOf_eq, sub_self]
    simp only [m.1, mb.1, mb.2, Super.near, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod,
      Set.mem_inter_iff, mem_extChartAt_source, extChartAt_eq_refl, PartialEquiv.refl_source,
      Set.mem_univ, true_and_iff, Set.mem_preimage, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id,
      Set.mem_setOf_eq, sub_self, mem_ball_iff_norm, Prod.norm_def, max_lt_iff, Prod.fst_sub,
      Prod.snd_sub, sub_zero]
  · have h := (s.superNearC.s (Set.mem_univ c)).ft m.2
    simp only [Super.fl, _root_.fl, Function.comp, sub_add_cancel, PartialEquiv.left_inv _ m.1] at h
    exact h

/-- Once we're in `s.near`, we stay there forever -/
theorem Super.iter_stays_near (s : Super f d a) {c : ℂ} {z : S} (m : (c, z) ∈ s.near) (n : ℕ) :
    (c, (f c)^[n] z) ∈ s.near := by
  induction' n with n h; simp only [Function.iterate_zero, id, m]
  simp only [Nat.add_succ, Function.iterate_succ', s.stays_near h, Function.comp]

/-- More iterations stay in `s.near` -/
theorem Super.iter_stays_near' (s : Super f d a) {a b : ℕ} (m : (c, (f c)^[a] z) ∈ s.near)
    (ab : a ≤ b) : (c, (f c)^[b] z) ∈ s.near := by
  rw [← Nat.sub_add_cancel ab, Function.iterate_add_apply]; exact s.iter_stays_near m _

/-- If `z` attracts, it eventually reaches `s.near` -/
theorem Super.reaches_near (s : Super f d a) {z : S} (a : Attracts (f c) z a) :
    ∀ᶠ n in atTop, (c, (f c)^[n] z) ∈ s.near := by
  rw [Attracts, Filter.tendsto_iff_forall_eventually_mem] at a
  have e := a {z | (c, z) ∈ s.near} ?_; exact e
  apply IsOpen.mem_nhds; apply IsOpen.snd_preimage s.isOpen_near; exact s.mem_near c

/-- If `z` reaches `s.near`, it attracts to `a` -/
theorem Super.attracts (s : Super f d a) {n : ℕ} (r : (c, (f c)^[n] z) ∈ s.near) :
    Attracts (f c) z a := by
  have m := s.mem_near_to_near' r
  have t := iterates_tendsto (s.superNearC.s (Set.mem_univ c)) m
  generalize hg : (fun x : ℂ ↦ (extChartAt I a).symm (x + extChartAt I a a)) = g
  have gc : ContinuousAt g 0 := by
    rw [← hg]
    refine'
      (continuousAt_extChartAt_symm'' I a _).comp (continuous_id.add continuous_const).continuousAt
    simp only [zero_add]; exact mem_extChartAt_target I a
  have g0 : g 0 = a := by
    simp only [← hg]; simp only [zero_add]; exact PartialEquiv.left_inv _ (mem_extChartAt_source _ _)
  have h := gc.tendsto.comp t; clear t gc m
  simp only [Function.comp, g0] at h
  rw [← attracts_shift n]
  refine' Filter.Tendsto.congr _ h; clear h
  intro k; simp only [← hg]; induction' k with k h
  simp only [Function.iterate_zero_apply]; rw [sub_add_cancel]
  exact PartialEquiv.left_inv _ (s.near_subset_chart r)
  simp only [Function.iterate_succ_apply']
  generalize hx : (s.fl c)^[k] (extChartAt I a ((f c)^[n] z) - extChartAt I a a) = x; rw [hx] at h
  simp only [Super.fl, _root_.fl, Function.comp, sub_add_cancel, h,
    ←Function.iterate_succ_apply' (f c)]
  apply PartialEquiv.left_inv _ (s.near_subset_chart (s.iter_stays_near r _))

/-- The basin of points that attract to `a` -/
def Super.basin (s : Super f d a) : Set (ℂ × S) :=
  {p : ℂ × S | ∃ n, (p.1, (f p.1)^[n] p.2) ∈ s.near}

theorem Super.isOpen_preimage (s : Super f d a) (n : ℕ) :
    IsOpen {p : ℂ × S | (p.1, (f p.1)^[n] p.2) ∈ s.near} :=
  IsOpen.preimage (continuous_fst.prod_mk (s.continuous_iter continuous_fst continuous_snd))
    s.isOpen_near

/-- `s.basin` is open -/
theorem Super.isOpen_basin (s : Super f d a) : IsOpen s.basin := by
  simp only [Super.basin, setOf_exists]; exact isOpen_iUnion fun n ↦ s.isOpen_preimage n

/-- Anything in `s.basin` is eventually in `s.near` -/
theorem Super.basin_stays (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∀ᶠ n in atTop, (c, (f c)^[n] z) ∈ s.near := by
  simp only [Super.basin, Set.mem_setOf] at m
  rcases m with ⟨n, m⟩
  rw [Filter.eventually_atTop]; use n; intro k kn
  rw [← Nat.sub_add_cancel kn, Function.iterate_add_apply]
  exact s.iter_stays_near m _

/-- Anything in `s.basin` attracts -/
theorem Super.basin_attracts (s : Super f d a) (m : (c, z) ∈ s.basin) : Attracts (f c) z a := by
  rcases m with ⟨n, m⟩; exact s.attracts m

/-- `s.basin` is exactly the set of attracting points -/
theorem Super.basin_iff_attracts (s : Super f d a) : (c, z) ∈ s.basin ↔ Attracts (f c) z a := by
  constructor; exact s.basin_attracts; intro h
  rcases tendsto_atTop_nhds.mp h {z | (c, z) ∈ s.near} (s.mem_near c)
    (s.isOpen_near.snd_preimage c) with ⟨n, h⟩
  exact ⟨n, h _ (le_refl _)⟩

/-- `f` acting on and returning pairs -/
@[nolint unusedArguments]
def Super.fp (_ : Super f d a) : ℂ × S → ℂ × S := fun p : ℂ × S ↦ (p.1, f p.1 p.2)

/-- `s.fp` is holomorphic -/
theorem Super.fpa (s : Super f d a) : Holomorphic II II s.fp := fun _ ↦
  holomorphicAt_fst.prod (s.fa _)

theorem Super.fp1 (s : Super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).1 = p.1 := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply]
  · simp only [Function.iterate_succ_apply', h, fp]

theorem Super.fp2 (s : Super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).2 = (f p.1)^[n] p.2 := by
  induction' n with n h
  · simp only [Function.iterate_zero_apply]
  · have c := s.fp1 n p; simp only [Super.fp] at c
    simp only [Function.iterate_succ_apply', c, h, fp]

/-- `bottcherNear` on the manifold -/
@[pp_dot] def Super.bottcherNear (s : Super f d a) (c : ℂ) (z : S) : ℂ :=
  _root_.bottcherNear (s.fl c) d (extChartAt I a z - extChartAt I a a)

/-- `s.bottcherNear`, uncurried -/
def Super.bottcherNearp (s : Super f d a) : ℂ × S → ℂ :=
  uncurry s.bottcherNear

/-- `s.bottcherNear` is analytic -/
theorem Super.bottcherNear_holomorphic (s : Super f d a) :
    HolomorphicOn II I (uncurry s.bottcherNear) s.near := by
  intro p m
  have e : uncurry s.bottcherNear =
      (fun p : ℂ × ℂ ↦ _root_.bottcherNear (s.fl p.1) d p.2) ∘ fun p : ℂ × S ↦
        (p.1, extChartAt I a p.2 - extChartAt I a a) :=
    rfl
  rw [e]; clear e
  have h1 := (bottcherNear_analytic s.superNearC _ (s.mem_near_to_near' m)).holomorphicAt II I
  have h2 : HolomorphicAt II II (fun p : ℂ × S ↦
      (p.1, extChartAt I a p.2 - extChartAt I a a)) p := by
    apply holomorphicAt_fst.prod; apply HolomorphicAt.sub
    exact (HolomorphicAt.extChartAt (s.near_subset_chart m)).comp holomorphicAt_snd
    exact holomorphicAt_const
  refine h1.comp_of_eq h2 ?_
  simp only [sub_self]

/-- `s.bottcherNear` after some iterations of `f` -/
@[pp_dot] def Super.bottcherNearIter (s : Super f d a) (n : ℕ) : ℂ → S → ℂ := fun c z ↦
  s.bottcherNear c ((f c)^[n] z)

theorem Super.bottcherNearIter_holomorphic (s : Super f d a) {n : ℕ}
    (r : (c, (f c)^[n] z) ∈ s.near) :
    HolomorphicAt II I (uncurry (s.bottcherNearIter n)) (c, z) := by
  refine (s.bottcherNear_holomorphic _ ?_).comp₂ holomorphicAt_fst (s.holomorphic_iter _)
  exact r

/-- `s.bottcherNear` satisfies the defining equation -/
theorem Super.bottcherNear_eqn (s : Super f d a) (m : (c, z) ∈ s.near) :
    s.bottcherNear c (f c z) = s.bottcherNear c z ^ d := by
  simp only [Super.bottcherNear]
  have e : extChartAt I a (f c z) - extChartAt I a a =
      s.fl c (extChartAt I a z - extChartAt I a a) := by
    simp only [Function.comp, Super.fl, _root_.fl, sub_add_cancel,
      PartialEquiv.left_inv _ (s.near_subset_chart m)]
  rw [e, _root_.bottcherNear_eqn (s.superNearC.s (Set.mem_univ c)) (s.mem_near_to_near' m)]

/-- `s.bottcherNear_eqn` iterated -/
theorem Super.bottcherNear_eqn_iter (s : Super f d a) (m : (c, z) ∈ s.near) {n : ℕ} :
    s.bottcherNear c ((f c)^[n] z) = s.bottcherNear c z ^ d ^ n := by
  induction' n with n h; simp only [Function.iterate_zero_apply, pow_zero, pow_one]
  simp only [Function.iterate_succ_apply', s.bottcherNear_eqn (s.iter_stays_near m n), h, ←
    pow_mul, ← pow_succ']

/-- The defining equation in terms of `s.bottcherNearp` and `s.fp` -/
theorem Super.bottcherNearp_eqn (s : Super f d a) (m : p ∈ s.near) :
    s.bottcherNearp (s.fp p) = s.bottcherNearp p ^ d := by
  rcases p with ⟨c, z⟩; exact s.bottcherNear_eqn m

/-- `abs (s.bottcherNear c z) < 1` -/
theorem Super.bottcherNear_lt_one (s : Super f d a) (m : (c, z) ∈ s.near) :
    abs (s.bottcherNear c z) < 1 := by
  simp only [Super.bottcherNear, mem_setOf]
  exact _root_.bottcherNear_lt_one (s.superNearC.s (Set.mem_univ c)) (s.mem_near_to_near' m)

/-- `s.bottcherNear = 0` only at `a` -/
theorem Super.bottcherNear_eq_zero (s : Super f d a) (m : (c, z) ∈ s.near) :
    s.bottcherNear c z = 0 ↔ z = a := by
  simp only [Super.bottcherNear]; constructor
  · intro za; contrapose za
    apply bottcherNear_ne_zero (s.superNearC.s (Set.mem_univ _)) (s.mem_near_to_near' m)
    simp only [sub_ne_zero]
    exact (extChartAt I a).injOn.ne (s.near_subset_chart m) (mem_extChartAt_source I a) za
  · intro za; simp only [za, sub_self, bottcherNear_zero]

/-- `s.bottcherNear c a = 0` -/
theorem Super.bottcherNear_a (s : Super f d a) : s.bottcherNear c a = 0 := by
  simp only [Super.bottcherNear, sub_self, bottcherNear_zero]

/-- `s.bottcherNear' ≠ 0` at `0` -/
theorem Super.bottcherNear_mfderiv_ne_zero (s : Super f d a) (c : ℂ) :
    mfderiv I I (s.bottcherNear c) a ≠ 0 := by
  apply mderiv_comp_ne_zero' (f := _root_.bottcherNear (s.fl c) d)
  · simp only [sub_self, mfderiv_eq_fderiv,
      (_root_.bottcherNear_monic (s.superNearC.s (Set.mem_univ c))).hasFDerivAt.fderiv]
    exact ContinuousLinearMap.smulRight_ne_zero ContinuousLinearMap.one_ne_zero (by norm_num)
  · have u : (fun z : S ↦ extChartAt I a z - extChartAt I a a) =
        extChartAt I a - fun _ : S ↦ extChartAt I a a := rfl
    rw [u, mfderiv_sub, mfderiv_const, sub_zero]
    exact extChartAt_mderiv_ne_zero a
    exact (HolomorphicAt.extChartAt (mem_extChartAt_source I a)).mdifferentiableAt
    apply mdifferentiableAt_const

/-- `s.bottcherNear` is invertible near any `(c,a)` -/
theorem Super.bottcherNear_has_inv (s : Super f d a) (c : ℂ) :
    ∃ bi : ℂ → ℂ → S,
      HolomorphicAt II I (uncurry bi) (c, 0) ∧
        (∀ᶠ p : ℂ × S in 𝓝 (c, a), bi p.1 (s.bottcherNear p.1 p.2) = p.2) ∧
          ∀ᶠ p : ℂ × ℂ in 𝓝 (c, 0), s.bottcherNear p.1 (bi p.1 p.2) = p.2 := by
  have h := complex_inverse_fun (s.bottcherNear_holomorphic _ (s.mem_near c))
      (s.bottcherNear_mfderiv_ne_zero c)
  simp only [s.bottcherNear_a] at h; exact h

/-- `f` is locally noncritical near (but not at) `a`.
    This is a depressingly long proof for a very simple conceptual argument. -/
theorem Super.f_noncritical_near_a (s : Super f d a) (c : ℂ) :
    ∀ᶠ p : ℂ × S in 𝓝 (c, a), Critical (f p.1) p.2 ↔ p.2 = a := by
  have t : ContinuousAt (fun p : ℂ × S ↦ (p.1, extChartAt I a p.2 - extChartAt I a a)) (c, a) := by
    refine' continuousAt_fst.prod (ContinuousAt.sub _ continuousAt_const)
    exact (continuousAt_extChartAt I a).comp_of_eq continuousAt_snd rfl
  simp only [ContinuousAt, sub_self] at t
  apply (inChart_critical (s.fa (c, a))).mp
  apply (t.eventually (df_ne_zero s.superNearC (Set.mem_univ c))).mp
  have am := mem_extChartAt_source I a
  have em := ((isOpen_extChartAt_source I a).eventually_mem am).prod_inr (𝓝 c)
  simp only [← nhds_prod_eq] at em; apply em.mp
  have ezm : ∀ᶠ p : ℂ × S in 𝓝 (c, a), f p.1 p.2 ∈ (extChartAt I a).source := by
    apply (s.fa _).continuousAt.eventually_mem (isOpen_extChartAt_source I a)
    simp only [uncurry, s.f0, mem_extChartAt_source I a]
  apply ezm.mp
  apply eventually_of_forall; clear t em
  intro ⟨e, z⟩ ezm zm d0 m0; simp only at ezm zm d0 m0 ⊢
  simp only [Super.fl, fl, sub_eq_zero, (PartialEquiv.injOn _).eq_iff zm am] at d0
  simp only [Critical, m0, inChart, ← d0]; clear m0 d0
  generalize hg : (fun w ↦ extChartAt I (f c a) (f e ((extChartAt I a).symm w))) = g
  have hg' : extChartAt I a ∘ f e ∘ (extChartAt I a).symm = g := by
    rw [← hg]; simp only [Function.comp, s.f0]
  rw [_root_.fl, hg']; clear hg'; rw [Iff.comm]
  have dg : DifferentiableAt ℂ g (extChartAt I a z) := by
    rw [← hg]; apply AnalyticAt.differentiableAt; apply HolomorphicAt.analyticAt I I
    simp only [s.f0]
    apply (HolomorphicAt.extChartAt _).comp; apply (s.fa _).along_snd.comp
    exact HolomorphicAt.extChartAt_symm (PartialEquiv.map_source _ zm)
    simp only [PartialEquiv.left_inv _ zm, s.f0]; exact ezm
  have d0 : ∀ z, DifferentiableAt ℂ (fun z ↦ z - extChartAt I a a) z := fun z ↦
    differentiableAt_id.sub (differentiableAt_const _)
  have d1 : DifferentiableAt ℂ (g ∘ fun z : ℂ ↦ z + extChartAt I a a)
      (extChartAt I a z - extChartAt I a a) := by
    apply DifferentiableAt.comp; simp only [sub_add_cancel, dg]
    exact differentiableAt_id.add (differentiableAt_const _)
  simp only [deriv.comp _ (d0 _) d1, deriv_sub_const, deriv_id'']
  rw [deriv.comp _ _ _]
  · simp only [deriv_add_const, deriv_sub_const, deriv_id'', mul_one, sub_add_cancel, Function.comp]
    rw [deriv_add_const, deriv_sub_const, deriv_id'']; simp only [one_mul, mul_one]
    exact Eq.congr (congrFun (congrArg deriv (id hg.symm)) (extChartAt I a z)) rfl
  · simp only [sub_add_cancel, dg]
  · exact differentiableAt_id.add (differentiableAt_const _)

/-- Critical points that are not `a` are closed, because `a` is an isolated critical point in `z` -/
theorem Super.isClosed_critical_not_a (s : Super f d a) :
    IsClosed {p : ℂ × S | Critical (f p.1) p.2 ∧ p.2 ≠ a} := by
  rw [← isOpen_compl_iff]; rw [isOpen_iff_eventually]; intro ⟨c, z⟩ m
  by_cases za : z = a
  · rw [za]; refine' (s.f_noncritical_near_a c).mp (eventually_of_forall _); intro ⟨e, w⟩ h
    simp only [mem_compl_iff, mem_setOf, not_and, not_not] at h ⊢; exact h.1
  · have o := isOpen_iff_eventually.mp (isOpen_noncritical s.fa)
    simp only [za, mem_compl_iff, mem_setOf, not_and, not_not, imp_false] at m o ⊢
    refine' (o (c, z) m).mp (eventually_of_forall _); intro ⟨e, w⟩ a b; exfalso; exact a b

/-- If `z ∈ s.basin`, iterating enough takes us to a noncritical point of `s.bottcherNear` -/
theorem Super.eventually_noncritical (s : Super f d a) (m : (c, z) ∈ s.basin) :
    ∀ᶠ n in atTop, mfderiv I I (s.bottcherNear c) ((f c)^[n] z) ≠ 0 :=
  (s.basin_attracts m).eventually
    (mfderiv_ne_zero_eventually (s.bottcherNear_holomorphic _ (s.mem_near c)).along_snd
      (s.bottcherNear_mfderiv_ne_zero c))

/-- `s.bottcherNearIter` is noncritical given noncriticality of the two parts -/
theorem Super.bottcherNearIter_mfderiv_ne_zero (s : Super f d a)
    (b0 : mfderiv I I (s.bottcherNear c) ((f c)^[n] z) ≠ 0) (f0 : ¬Precritical (f c) z) :
    mfderiv I I (s.bottcherNearIter n c) z ≠ 0 := by
  apply mderiv_comp_ne_zero' b0; contrapose f0
  simp only [not_not] at f0 ⊢; exact critical_iter s.fa.along_snd f0

/-- `f c^[n]` is nontrivial at `a` -/
theorem Super.iter_nontrivial_a (s : Super f d a) :
    NontrivialHolomorphicAt (fun z ↦ (f c)^[n] z) a := by
  induction' n with n h; simp only [Function.iterate_zero_apply]; apply nontrivialHolomorphicAt_id
  simp only [Function.iterate_succ_apply']; refine' NontrivialHolomorphicAt.comp _ h
  simp only [s.iter_a]; exact s.f_nontrivial c

/-- `s.bottcherNearIter` is nontrivial at `a` -/
theorem Super.bottcherNearIter_nontrivial_a (s : Super f d a) :
    NontrivialHolomorphicAt (s.bottcherNearIter n c) a :=
  haveI b : NontrivialHolomorphicAt (s.bottcherNear c) ((f c)^[n] a) := by
    simp only [s.iter_a]
    exact nontrivialHolomorphicAt_of_mfderiv_ne_zero
      (s.bottcherNear_holomorphic _ (s.mem_near c)).along_snd
      (s.bottcherNear_mfderiv_ne_zero c)
  b.comp s.iter_nontrivial_a
