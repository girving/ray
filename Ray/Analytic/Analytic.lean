import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.ENNReal
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Topology.Basic
import Ray.Misc.Bounds
import Ray.Misc.Multilinear
import Ray.Misc.Topology

/-!
## Facts about analytic functions (general field case)
-/

-- Remove once https://github.com/leanprover/lean4/issues/2220 is fixed
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Classical
open Filter (atTop eventually_of_forall)
open Function (curry uncurry)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped Real NNReal ENNReal Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
variable {H : Type} [NormedAddCommGroup H] [NormedSpace 𝕜 H] [CompleteSpace H]

/-- `id` is entire -/
theorem analyticOn_id {s : Set E} : AnalyticOn 𝕜 (fun x : E ↦ x) s := fun _ _ ↦ analyticAt_id _ _

/-- Finite sums of analytic functions are analytic -/
theorem AnalyticAt.sum {f : ℕ → E → F} {c : E} (h : ∀ n, AnalyticAt 𝕜 (f n) c) (N : Finset ℕ) :
    AnalyticAt 𝕜 (fun z ↦ N.sum fun n ↦ f n z) c := by
  induction' N using Finset.induction with a B aB hB
  · simp only [Finset.sum_empty]; exact analyticAt_const
  · simp_rw [Finset.sum_insert aB]
    apply AnalyticAt.add
    exact h a
    exact hB

/-- Finite sums of analytic functions are analytic -/
theorem AnalyticOn.sum {f : ℕ → E → F} {s : Set E} (h : ∀ n, AnalyticOn 𝕜 (f n) s) (N : Finset ℕ) :
    AnalyticOn 𝕜 (fun z ↦ N.sum fun n ↦ f n z) s := fun z zs ↦
  AnalyticAt.sum (fun n ↦ h n z zs) N

/-- Power series terms are analytic -/
theorem ChangeOrigin.analyticAt (p : FormalMultilinearSeries 𝕜 E F) (rp : p.radius > 0) (n : ℕ) :
    AnalyticAt 𝕜 (fun x ↦ p.changeOrigin x n) 0 :=
  (FormalMultilinearSeries.hasFPowerSeriesOnBall_changeOrigin p n rp).analyticAt

/-- Analytic at a point means analytic in a small ball -/
theorem AnalyticAt.ball {f : E → F} {z : E} :
    AnalyticAt 𝕜 f z → ∃ r : ℝ, r > 0 ∧ AnalyticOn 𝕜 f (ball z r) := by
  intro a
  rcases a with ⟨p, r, h⟩
  by_cases ri : r = ∞
  · exists (1 : ℝ)
    exact ⟨by norm_num, fun z _ ↦ HasFPowerSeriesOnBall.analyticOn h z (by rw [ri]; simp)⟩
  · exists r.toReal
    constructor; · exact ENNReal.toReal_pos h.r_pos.ne' ri
    · intro z zs
      refine' HasFPowerSeriesOnBall.analyticOn h z _
      simp at zs ⊢
      have rr := ENNReal.ofReal_toReal ri
      rw [← rr, edist_lt_ofReal]; assumption

/-- Analytic at a point means analytic in a small closed ball -/
theorem AnalyticAt.cball {f : E → F} {z : E} :
    AnalyticAt 𝕜 f z → ∃ r : ℝ, r > 0 ∧ AnalyticOn 𝕜 f (closedBall z r) := by
  intro a
  rcases AnalyticAt.ball a with ⟨r, rp, ao⟩
  exists r / 2
  constructor; · linarith
  · intro z zs
    refine' ao z _
    simp at zs ⊢
    exact lt_of_le_of_lt zs (by linarith)

/-- `fst` is analytic -/
theorem analyticAt_fst {p : E × F} : AnalyticAt 𝕜 (fun p : E × F ↦ p.fst) p :=
  (ContinuousLinearMap.fst 𝕜 E F).analyticAt p

/-- `snd` is analytic -/
theorem analyticAt_snd {p : E × F} : AnalyticAt 𝕜 (fun p : E × F ↦ p.snd) p :=
  (ContinuousLinearMap.snd 𝕜 E F).analyticAt p

/-- `fst` is analytic -/
theorem analyticOn_fst {s : Set (E × F)} : AnalyticOn 𝕜 (fun p : E × F ↦ p.fst) s := fun _ _ ↦
  analyticAt_fst

/-- `snd` is analytic -/
theorem analyticOn_snd {s : Set (E × F)} : AnalyticOn 𝕜 (fun p : E × F ↦ p.snd) s := fun _ _ ↦
  analyticAt_snd

/-- `AnalyticAt.comp` for a curried function -/
theorem AnalyticAt.curry_comp {h : F → G → H} {f : E → F} {g : E → G} {x : E}
    (ha : AnalyticAt 𝕜 (uncurry h) (f x, g x)) (fa : AnalyticAt 𝕜 f x) (ga : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun x ↦ h (f x) (g x)) x := by
  have e : (fun x ↦ h (f x) (g x)) = uncurry h ∘ fun x ↦ (f x, g x) := rfl
  rw [e]; exact AnalyticAt.comp ha (fa.prod ga)

/-- `AnalyticOn.comp` for a curried function -/
theorem AnalyticOn.curry_comp {h : F → G → H} {f : E → F} {g : E → G} {s : Set (F × G)} {t : Set E}
    (ha : AnalyticOn 𝕜 (uncurry h) s) (fa : AnalyticOn 𝕜 f t) (ga : AnalyticOn 𝕜 g t)
    (m : ∀ x, x ∈ t → (f x, g x) ∈ s) : AnalyticOn 𝕜 (fun x ↦ h (f x) (g x)) t := fun _ xt ↦
  (ha _ (m _ xt)).curry_comp (fa _ xt) (ga _ xt)

/-- Curried analytic functions are analytic in the first coordinate -/
theorem AnalyticAt.in1 {f : E → F → G} {x : E} {y : F} (fa : AnalyticAt 𝕜 (uncurry f) (x, y)) :
    AnalyticAt 𝕜 (fun x ↦ f x y) x :=
  AnalyticAt.curry_comp fa (analyticAt_id _ _) analyticAt_const

/-- Curried analytic functions are analytic in the second coordinate -/
theorem AnalyticAt.in2 {f : E → F → G} {x : E} {y : F} (fa : AnalyticAt 𝕜 (uncurry f) (x, y)) :
    AnalyticAt 𝕜 (fun y ↦ f x y) y :=
  AnalyticAt.curry_comp fa analyticAt_const (analyticAt_id _ _)

/-- Curried analytic functions are analytic in the first coordinate -/
theorem AnalyticOn.in1 {f : E → F → G} {s : Set (E × F)} {y : F} (fa : AnalyticOn 𝕜 (uncurry f) s) :
    AnalyticOn 𝕜 (fun x ↦ f x y) {x | (x, y) ∈ s} := fun x m ↦ (fa (x, y) m).in1

/-- Curried analytic functions are analytic in the second coordinate -/
theorem AnalyticOn.in2 {f : E → F → G} {x : E} {s : Set (E × F)} (fa : AnalyticOn 𝕜 (uncurry f) s) :
    AnalyticOn 𝕜 (fun y ↦ f x y) {y | (x, y) ∈ s} := fun y m ↦ (fa (x, y) m).in2

/-- Analytic everywhere means continuous -/
theorem AnalyticOn.continuous {f : E → F} (fa : AnalyticOn 𝕜 f univ) : Continuous f := by
  rw [continuous_iff_continuousOn_univ]; exact fa.continuousOn

/-- Multiplication is analytic -/
theorem analyticOn_mul [CompleteSpace 𝕜] : AnalyticOn 𝕜 (fun x : 𝕜 × 𝕜 ↦ x.1 * x.2) univ := by
  set p : FormalMultilinearSeries 𝕜 (𝕜 × 𝕜) 𝕜 := fun n ↦ if n = 2 then termCmmap 𝕜 n 1 1 else 0
  rw [←Metric.eball_top_eq_univ 0]; apply HasFPowerSeriesOnBall.analyticOn (p := p)
  exact {
    r_le := by
      rw [FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero]
      rw [Filter.eventually_atTop]; use 3; intro n n2
      have ne : n ≠ 2 := by linarith
      simp only [ge_iff_le, ne, ite_false, implies_true]
    r_pos := by simp only
    hasSum := by
      intro (x,y) _; simp only [zero_add]
      have e : (fun n ↦ (if n = 2 then termCmmap 𝕜 n 1 1 else 0) (fun _ ↦ (x, y))) =
          (fun n ↦ if n = 2 then x * y else 0) := by
        ext n; by_cases n2 : n = 2
        repeat simp only [n2, ite_true, termCmmap_apply, ge_iff_le, min_eq_left, pow_one,
            Nat.succ_sub_succ_eq_sub, tsub_zero, smul_eq_mul, mul_one, ite_false,
            ContinuousMultilinearMap.zero_apply]
      rw [e]; apply hasSum_ite_eq }

/-- `f * g` is analytic -/
theorem AnalyticOn.mul [CompleteSpace 𝕜] {f g : E → 𝕜} {s : Set E}
    (fa : AnalyticOn 𝕜 f s) (ga : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun x ↦ f x * g x) s := fun x m ↦ (fa x m).mul (ga x m)

/-- `(f x)⁻¹` is analytic away from `f x = 0` -/
theorem AnalyticAt.inv {f : E → 𝕜} {x : E} (fa : AnalyticAt 𝕜 f x) (f0 : f x ≠ 0) :
    AnalyticAt 𝕜 (fun x ↦ (f x)⁻¹) x := (analyticAt_inv _ f0).comp fa

/-- `x⁻¹` is analytic away from zero -/
theorem analyticOn_inv : AnalyticOn 𝕜 (fun z ↦ z⁻¹) {z : 𝕜 | z ≠ 0} := by
  intro z m; exact analyticAt_inv _ m

/-- `x⁻¹` is analytic away from zero -/
theorem AnalyticOn.inv {f : E → 𝕜} {s : Set E} (fa : AnalyticOn 𝕜 f s) (f0 : ∀ x, x ∈ s → f x ≠ 0) :
    AnalyticOn 𝕜 (fun x ↦ (f x)⁻¹) s := fun x m ↦ (fa x m).inv (f0 x m)

/-- `f x / g x` is analytic away from `g x = 0` -/
theorem AnalyticAt.div [CompleteSpace 𝕜] {f g : E → 𝕜} {x : E}
    (fa : AnalyticAt 𝕜 f x) (ga : AnalyticAt 𝕜 g x) (g0 : g x ≠ 0) :
    AnalyticAt 𝕜 (fun x ↦ f x / g x) x := by
  simp_rw [div_eq_mul_inv]; exact fa.mul (ga.inv g0)

/-- `f x / g x` is analytic away from `g x = 0` -/
theorem AnalyticOn.div [CompleteSpace 𝕜] {f g : E → 𝕜} {s : Set E}
    (fa : AnalyticOn 𝕜 f s) (ga : AnalyticOn 𝕜 g s) (g0 : ∀ x, x ∈ s → g x ≠ 0) :
    AnalyticOn 𝕜 (fun x ↦ f x / g x) s := fun x m ↦
  (fa x m).div (ga x m) (g0 x m)

/-- `z^n` is analytic -/
theorem AnalyticAt.monomial [CompleteSpace 𝕜] (n : ℕ) {z : 𝕜} :
    AnalyticAt 𝕜 (fun z : 𝕜 ↦ z ^ n) z :=
  (analyticAt_id _ _).pow _

/-- `z^n` is entire -/
theorem AnalyticOn.monomial [CompleteSpace 𝕜] (n : ℕ) : AnalyticOn 𝕜 (fun z : 𝕜 ↦ z ^ n) univ :=
  fun _ _ ↦ AnalyticAt.monomial _

/-- Finite products of analytic functions are analytic -/
theorem prod_analytic [CompleteSpace 𝕜] {f : ℕ → E → 𝕜} {s : Set E}
    (h : ∀ n, AnalyticOn 𝕜 (f n) s) (N : Finset ℕ) :
    AnalyticOn 𝕜 (fun z ↦ N.prod fun n ↦ f n z) s := by
  induction' N using Finset.induction with a B aB hB; · simp; intro z _; exact analyticAt_const
  · simp_rw [Finset.prod_insert aB]; exact (h a).mul hB

/-- The order of a zero at a point.
    We define this in terms of the function alone so that expressions involving order can
    depend only on `f`. -/
def orderAt (f : 𝕜 → E) (c : 𝕜) : ℕ :=
  if p : AnalyticAt 𝕜 f c then (choose p).order else 0

/-- `orderAt` is unique, since power series are -/
theorem HasFPowerSeriesAt.orderAt_unique {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    (fp : HasFPowerSeriesAt f p c) : orderAt f c = p.order := by
  have fa : AnalyticAt 𝕜 f c := ⟨p, fp⟩
  simp only [orderAt, fa, dif_pos]
  have s := choose_spec fa
  generalize hq : choose fa = q
  simp_rw [hq] at s
  rw [fp.eq_formalMultilinearSeries s]

/-- `orderAt` is zero for nonzeros -/
theorem orderAt_eq_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) : orderAt f c = 0 := by
  by_cases fp : AnalyticAt 𝕜 f c
  · rcases fp with ⟨p, fp⟩; rw [fp.orderAt_unique]; rw [← fp.coeff_zero 1] at f0
    rw [FormalMultilinearSeries.order_eq_zero_iff']; right
    contrapose f0; simp only [not_not] at f0
    simp only [f0, ContinuousMultilinearMap.zero_apply, Ne.def, eq_self_iff_true, not_true,
      not_false_iff]
  · simp [orderAt, fp]

/-- `orderAt = 0` means either `f = 0` or `f c ≠ 0` -/
theorem orderAt_eq_zero_iff {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) :
    orderAt f c = 0 ↔ f =ᶠ[𝓝 c] 0 ∨ f c ≠ 0 := by
  rcases fa with ⟨p, fp⟩
  simp only [fp.orderAt_unique, ←fp.coeff_zero fun _ ↦ 0,
    FormalMultilinearSeries.order_eq_zero_iff']
  rw [←@norm_ne_zero_iff _ _ (p 0 fun _ ↦ 0), ContinuousMultilinearMap.fin0_apply_norm,
    norm_ne_zero_iff]
  apply or_congr_left'; intro _; exact fp.locally_zero_iff.symm

/-- `orderAt = 1 → deriv ≠ 0` -/
theorem deriv_ne_zero_of_orderAt_eq_one {f : 𝕜 → E} {c : 𝕜} (o : orderAt f c = 1) :
    deriv f c ≠ 0 := by
  by_cases fa : AnalyticAt 𝕜 f c
  · rcases fa with ⟨p, fp⟩
    rw [fp.orderAt_unique] at o
    have o0 : p.order ≠ 0 := by rw [o]; exact one_ne_zero
    have p0 := FormalMultilinearSeries.apply_order_ne_zero' o0
    rw [o] at p0
    simpa only [fp.deriv, FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul,
      FormalMultilinearSeries.coeff_eq_zero, Ne.def]
  · simp only [orderAt, fa] at o; rw [dif_neg] at o; norm_num at o; exact not_false

/-- The leading nonzero coefficient of `f`'s power series -/
def leadingCoeff (f : 𝕜 → E) (c : 𝕜) : E :=
  ((Function.swap dslope c)^[orderAt f c]) f c

/-- `leadingCoeff` for nonzeros -/
theorem leadingCoeff_of_ne_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) : leadingCoeff f c = f c := by
  simp only [leadingCoeff, orderAt_eq_zero f0, Function.iterate_zero_apply]

/-- `f` is approximated by its leading monomial -/
theorem AnalyticAt.leading_approx {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) :
    (fun z ↦ f z - (z - c) ^ orderAt f c • leadingCoeff f c) =o[𝓝 c] fun z ↦
      (z - c) ^ orderAt f c := by
  rcases fa with ⟨p, fp⟩
  generalize ha : leadingCoeff f c = a
  generalize hd : orderAt f c = d
  have ha' : (Function.swap dslope c)^[d] f c = a := by rw [← ha, ← hd, leadingCoeff]
  have e := fp.eq_pow_order_mul_iterate_dslope
  simp_rw [← fp.orderAt_unique, hd] at e
  apply Asymptotics.IsLittleO.of_isBigOWith; intro k kp
  rw [Asymptotics.isBigOWith_iff]
  apply e.mp
  have dc : ContinuousAt ((Function.swap dslope c)^[d] f) c :=
    (fp.has_fpower_series_iterate_dslope_fslope d).analyticAt.continuousAt
  rcases Metric.continuousAt_iff.mp dc k kp with ⟨r, rp, rh⟩
  rw [ha'] at rh
  generalize hg : (Function.swap dslope c)^[d] f = g; rw [hg] at rh
  rw [Metric.eventually_nhds_iff]; use r, rp; intro y yr fe; rw [fe]
  specialize rh yr; rw [dist_eq_norm] at rh
  calc ‖(y - c) ^ d • g y - (y - c) ^ d • a‖
    _ = ‖(y - c) ^ d‖ * ‖g y - a‖ := by rw [←smul_sub, norm_smul]
    _ ≤ ‖(y - c) ^ d‖ * k := mul_le_mul_of_nonneg_left rh.le (norm_nonneg _)
    _ = k * ‖(y - c) ^ d‖ := by rw [mul_comm]

/-- `orderAt > 0` means `f` has a zero -/
theorem AnalyticAt.zero_of_order_pos {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (p : orderAt f c > 0) : f c = 0 := by
  have a := (Asymptotics.isBigOWith_iff.mp (fa.leading_approx.forall_isBigOWith zero_lt_one)).self
  simp only [(pow_eq_zero_iff p).mpr, sub_self, zero_smul, sub_zero, norm_zero,
    MulZeroClass.mul_zero, norm_le_zero_iff] at a
  exact a

/-- The power series of `(z - c) • f z` -/
def FormalMultilinearSeries.unshift' (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) :
    FormalMultilinearSeries 𝕜 𝕜 E :=
  ((ContinuousLinearMap.smulRightL 𝕜 𝕜 E (ContinuousLinearMap.id 𝕜 𝕜)).compFormalMultilinearSeries
        p).unshift c

@[simp]
lemma FormalMultilinearSeries.unshift_coeff_zero (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) :
    (p.unshift' c).coeff 0 = c := by
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.unshift',
    FormalMultilinearSeries.unshift, continuousMultilinearCurryFin0_symm_apply]

@[simp]
lemma FormalMultilinearSeries.unshift_coeff_succ (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E)
    (n : ℕ) : (p.unshift' c).coeff (n + 1) = p.coeff n := by
  simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.unshift',
    FormalMultilinearSeries.unshift, ContinuousLinearMap.compFormalMultilinearSeries_apply,
    LinearIsometryEquiv.norm_map]
  simp [ContinuousLinearMap.smulRightL, Finset.univ, Fintype.elems, Fin.init]

/-- The power series of `(z - c)^n • f z` -/
def FormalMultilinearSeries.unshiftIter (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :=
  (fun p ↦ FormalMultilinearSeries.unshift' p (0 : E))^[n] p

lemma FormalMultilinearSeries.unshiftIter_coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ)
    (i : ℕ) : (p.unshiftIter n).coeff i = if i < n then 0 else p.coeff (i - n) := by
  revert i; induction' n with n h
  · simp only [FormalMultilinearSeries.unshiftIter, Function.iterate_zero, id.def, not_lt_zero',
      tsub_zero, if_false, eq_self_iff_true, forall_const, Nat.zero_eq]
  · simp_rw [FormalMultilinearSeries.unshiftIter] at h
    simp only [FormalMultilinearSeries.unshiftIter, Function.iterate_succ', Function.comp]
    generalize hq : (fun p : FormalMultilinearSeries 𝕜 𝕜 E ↦ p.unshift' 0)^[n] p = q
    rw [hq] at h; clear hq
    intro i; induction' i with i _
    · simp only [FormalMultilinearSeries.unshift_coeff_zero, Nat.succ_pos', if_true]
    · simp only [Nat.succ_lt_succ_iff, h i, FormalMultilinearSeries.unshift_coeff_succ,
        Nat.succ_sub_succ_eq_sub]

/-- `unshift'` respects norm -/
lemma FormalMultilinearSeries.unshift_norm' (p : FormalMultilinearSeries 𝕜 𝕜 E) (c : E) (n : ℕ) :
    ‖p.unshift' c (n + 1)‖ = ‖p n‖ := by
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef,
    FormalMultilinearSeries.unshift_coeff_succ]

/-- `unshift'` respects radius -/
lemma FormalMultilinearSeries.unshift_radius' (p : FormalMultilinearSeries 𝕜 𝕜 E) {c : E} :
    (p.unshift' c).radius = p.radius := by
  simp_rw [FormalMultilinearSeries.radius]
  apply le_antisymm
  · refine' iSup₂_le _; intro r k; refine' iSup_le _; intro h
    refine' le_trans _ (le_iSup₂ r (k * ↑r⁻¹))
    have h := fun n ↦ mul_le_mul_of_nonneg_right (h (n + 1)) (NNReal.coe_nonneg r⁻¹)
    by_cases r0 : r = 0; · simp only [r0, ENNReal.coe_zero, ENNReal.iSup_zero_eq_zero, le_zero_iff]
    simp only [pow_succ', ←mul_assoc _ _ (r:ℝ), mul_assoc _ (r:ℝ) _,
      mul_inv_cancel (NNReal.coe_ne_zero.mpr r0), NNReal.coe_inv, mul_one, p.unshift_norm'] at h
    simp only [NNReal.coe_inv]
    convert le_iSup _ h; rfl
  · refine' iSup₂_le _; intro r k; refine' iSup_le _; intro h
    refine' le_trans _ (le_iSup₂ r (max ‖c‖ (k * ↑r)))
    have h' : ∀ n, ‖p.unshift' c n‖ * (r:ℝ)^n ≤ max ‖c‖ (k * ↑r) := by
      intro n; induction' n with n _
      · simp only [FormalMultilinearSeries.unshift_coeff_zero,
          FormalMultilinearSeries.norm_apply_eq_norm_coef, pow_zero, mul_one, le_max_iff, le_refl,
          true_or_iff]
      · simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef] at h
        simp only [FormalMultilinearSeries.unshift_coeff_succ, pow_succ', ← mul_assoc,
          FormalMultilinearSeries.norm_apply_eq_norm_coef, le_max_iff]
        right; exact mul_le_mul_of_nonneg_right (h n) (NNReal.coe_nonneg _)
    convert le_iSup _ h'; rfl

/-- The power series of `(z - c) • f z` is the unshifted power series -/
theorem HasFPowerSeriesOnBall.unshift {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    {r : ENNReal} (fp : HasFPowerSeriesOnBall f p c r) :
    HasFPowerSeriesOnBall (fun z ↦ (z - c) • f z) (p.unshift' 0) c r :=
  { r_le := le_trans fp.r_le (ge_of_eq p.unshift_radius')
    r_pos := fp.r_pos
    hasSum := by
      intro y yr; simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, add_sub_cancel']
      generalize hs : (fun n ↦ y ^ n • (p.unshift' 0).coeff n) = s
      have s0 : y • f (c + y) = y • f (c + y) + (Finset.range 1).sum s := by
        simp only [← hs, p.unshift_coeff_zero, Finset.range_one, Finset.sum_singleton, smul_zero,
          add_zero]
      rw [s0, ← hasSum_nat_add_iff, ← hs]
      simp only [p.unshift_coeff_succ, pow_succ, ← smul_smul]; apply HasSum.const_smul
      have h := fp.hasSum yr; simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff] at h
      exact h }

theorem HasFPowerSeriesAt.unshift {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    (fp : HasFPowerSeriesAt f p c) :
    HasFPowerSeriesAt (fun z ↦ (z - c) • f z) (p.unshift' 0) c := by
  rcases fp with ⟨r, fa⟩; use r; exact fa.unshift

theorem HasFPowerSeriesAt.unshiftIter {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    {n : ℕ} (fp : HasFPowerSeriesAt f p c) :
    HasFPowerSeriesAt (fun z ↦ (z - c) ^ n • f z) (p.unshiftIter n) c := by
  induction' n with n h; · simp only [Nat.zero_eq, pow_zero, one_smul]; exact fp
  · simp only [pow_succ, ← smul_smul, FormalMultilinearSeries.unshiftIter, Function.iterate_succ',
      Function.comp]
    exact h.unshift

/-- Power series terms are zero iff their coeffs are zero -/
theorem FormalMultilinearSeries.zero_iff_coeff_zero (p : FormalMultilinearSeries 𝕜 𝕜 E) {n : ℕ} :
    p n = 0 ↔ p.coeff n = 0 := by
  constructor
  · intro h; rw [FormalMultilinearSeries.coeff, h]; simp only [ContinuousMultilinearMap.zero_apply]
  · intro h; rw [←p.mkPiField_coeff_eq n, h]; simp only [ContinuousMultilinearMap.mkPiField_zero]

/-- Power series terms are zero iff their coeffs are zero -/
theorem FormalMultilinearSeries.ne_zero_iff_coeff_ne_zero (p : FormalMultilinearSeries 𝕜 𝕜 E)
    {n : ℕ} : p n ≠ 0 ↔ p.coeff n ≠ 0 := by
  constructor
  · intro h; contrapose h; simp only [not_not] at h ⊢; exact p.zero_iff_coeff_zero.mpr h
  · intro h; contrapose h; simp only [not_not] at h ⊢; exact p.zero_iff_coeff_zero.mp h

/-- The order of `(z - n)^n • f z` is `n` greater than `f`'s -/
theorem AnalyticAt.monomial_mul_orderAt {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ) :
    orderAt (fun z ↦ (z - c) ^ n • f z) c = n + orderAt f c := by
  rcases fa with ⟨p, fp⟩
  have pnz : p ≠ 0 := by
    contrapose fnz; simp only [ne_eq, not_not] at fnz
    simpa only [HasFPowerSeriesAt.locally_zero_iff fp, Filter.not_frequently, not_not]
  have pe : ∃ i, p i ≠ 0 := by rw [Function.ne_iff] at pnz; exact pnz
  have pne : ∃ i, (p.unshiftIter n) i ≠ 0 := by
    rcases pe with ⟨i, pi⟩; use n + i
    simp only [FormalMultilinearSeries.ne_zero_iff_coeff_ne_zero] at pi ⊢
    simpa only [p.unshiftIter_coeff, add_lt_iff_neg_left, add_tsub_cancel_left]
  have fq : HasFPowerSeriesAt (fun z ↦ (z - c) ^ n • f z) (p.unshiftIter n) c := fp.unshiftIter
  rw [fp.orderAt_unique, fq.orderAt_unique]
  rw [FormalMultilinearSeries.order_eq_find pe, FormalMultilinearSeries.order_eq_find pne]
  rw [Nat.find_eq_iff]; constructor
  · have s := Nat.find_spec pe
    simp only [p.zero_iff_coeff_zero, Ne.def] at s
    simp only [p.unshiftIter_coeff, FormalMultilinearSeries.zero_iff_coeff_zero, s, Ne.def,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left, if_false, not_false_iff, true_and,
      not_not]
  · intro m mp; simp [FormalMultilinearSeries.zero_iff_coeff_zero, p.unshiftIter_coeff]; intro mn
    generalize ha : m - n = a; have hm : m = n + a := by rw [← ha, add_comm, Nat.sub_add_cancel mn]
    simp only [hm, add_lt_add_iff_left, Nat.lt_find_iff, not_not] at mp
    specialize mp a (le_refl _); rwa [← FormalMultilinearSeries.zero_iff_coeff_zero]

/-- The leading coefficient of `(z - n)^n • f z` is the same as `f`'s -/
theorem AnalyticAt.monomial_mul_leadingCoeff {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ) :
    leadingCoeff (fun z ↦ (z - c) ^ n • f z) c = leadingCoeff f c := by
  simp [leadingCoeff, fa.monomial_mul_orderAt fnz n]; generalize orderAt f c = a
  induction' n with n h
  · simp only [zero_add, pow_zero, one_smul, Nat.zero_eq]
  · simp [pow_succ, ← smul_smul, Nat.succ_add]
    generalize hg : (fun z ↦ (z - c) ^ n • f z) = g
    have hg' : ∀ z, (z - c) ^ n • f z = g z := by
      rw [←hg]; simp only [eq_self_iff_true, forall_const]
    simp_rw [hg'] at h ⊢
    have e : (Function.swap dslope c fun z ↦ (z - c) • g z) = g := by
      simp only [Function.swap, dslope_sub_smul, Function.update_eq_self_iff, sub_self]
      rw [deriv_smul]
      simp only [sub_self, zero_smul, deriv_sub, differentiableAt_id', differentiableAt_const,
        deriv_id'', deriv_const', sub_zero, one_smul, zero_add]
      exact differentiableAt_id.sub (differentiableAt_const _)
      rw [←hg]
      exact ((differentiableAt_id.sub (differentiableAt_const _)).pow _).smul fa.differentiableAt
    rw [e, h]

/-- `fderiv` is analytic -/
theorem AnalyticAt.fderiv {f : E → F} {c : E} (fa : AnalyticAt 𝕜 f c) :
    AnalyticAt 𝕜 (fderiv 𝕜 f) c := by
  rcases fa.ball with ⟨r, rp, fa⟩; exact fa.fderiv _ (Metric.mem_ball_self rp)

/-- `deriv` is analytic -/
theorem AnalyticAt.deriv {f : 𝕜 → 𝕜} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) [CompleteSpace 𝕜] :
    AnalyticAt 𝕜 (fun x ↦ deriv f x) c := by
  simp only [← fderiv_deriv]
  have a1 : ∀ g, AnalyticAt 𝕜 (fun g : 𝕜 →L[𝕜] 𝕜 ↦ ContinuousLinearMap.apply 𝕜 𝕜 1 g) g := fun g ↦
    ContinuousLinearMap.analyticAt _ _
  refine' (a1 _).comp fa.fderiv

/-- `deriv` in the second variable is analytic -/
theorem AnalyticAt.deriv2 [CompleteSpace 𝕜] {f : E → 𝕜 → 𝕜} {c : E × 𝕜}
    (fa : AnalyticAt 𝕜 (uncurry f) c) :
    AnalyticAt 𝕜 (fun x : E × 𝕜 ↦ _root_.deriv (f x.1) x.2) c := by
  set p : (E × 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.apply 𝕜 𝕜 (0, 1)
  have e : ∀ᶠ x : E × 𝕜 in 𝓝 c, _root_.deriv (f x.1) x.2 = p (_root_.fderiv 𝕜 (uncurry f) x) := by
    refine' fa.eventually_analyticAt.mp (eventually_of_forall _)
    intro ⟨x, y⟩ fa; simp only [← fderiv_deriv]
    have e : f x = uncurry f ∘ fun y ↦ (x, y) := rfl
    rw [e]; rw [fderiv.comp]
    have pd : _root_.fderiv 𝕜 (fun y : 𝕜 ↦ (x, y)) y = ContinuousLinearMap.inr 𝕜 E 𝕜 := by
      apply HasFDerivAt.fderiv; apply hasFDerivAt_prod_mk_right
    rw [pd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.apply_apply]
    · exact fa.differentiableAt
    · exact (differentiableAt_const _).prod differentiableAt_id
  rw [analyticAt_congr e]
  exact (p.analyticAt _).comp fa.fderiv

/-- Scaling commutes with power series -/
theorem HasFPowerSeriesAt.const_smul {f : 𝕜 → E} {c a : 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    (fp : HasFPowerSeriesAt f p c) : HasFPowerSeriesAt (fun z ↦ a • f z) (fun n ↦ a • p n) c := by
  rw [hasFPowerSeriesAt_iff] at fp ⊢; refine' fp.mp (eventually_of_forall fun z h ↦ _)
  simp only [FormalMultilinearSeries.coeff, ContinuousMultilinearMap.smul_apply, smul_comm _ a]
  exact h.const_smul a

/-- Nonzero scaling does not change analyticitiy -/
theorem analyticAt_iff_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) :
    AnalyticAt 𝕜 (fun z ↦ a • f z) c ↔ AnalyticAt 𝕜 f c := by
  constructor
  · intro ⟨p, fp⟩
    have e : f = fun z ↦ a⁻¹ • a • f z := by
      funext; simp only [← smul_assoc, smul_eq_mul, inv_mul_cancel a0, one_smul]
    rw [e]; exact ⟨_, fp.const_smul⟩
  · intro ⟨p, fp⟩; exact ⟨_, fp.const_smul⟩

/-- Nonzero scaling does not change `orderAt` -/
theorem orderAt_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) :
    orderAt (fun z ↦ a • f z) c = orderAt f c := by
  by_cases fa : AnalyticAt 𝕜 f c
  · rcases fa with ⟨p, fp⟩
    have e : ∀ n, a • p n ≠ 0 ↔ p n ≠ 0 := fun n ↦ by
      simp only [a0, Ne.def, smul_eq_zero, false_or_iff]
    simp only [fp.orderAt_unique, fp.const_smul.orderAt_unique, FormalMultilinearSeries.order, e]
  · have ga := fa; rw [← analyticAt_iff_const_smul a0] at ga
    simp only [orderAt, fa, ga]; rw [dif_neg, dif_neg]
    exact not_false; exact not_false

/-- The leading coefficient of zero is zero -/
theorem leadingCoeff.zero {c : 𝕜} : leadingCoeff (fun _ : 𝕜 ↦ (0 : E)) c = 0 := by
  simp only [leadingCoeff]
  generalize hn : orderAt (fun _ : 𝕜 ↦ (0 : E)) c = n; clear hn
  induction' n with n h; simp only [Function.iterate_zero_apply]
  simp only [Function.iterate_succ_apply]; convert h
  simp only [Function.swap, dslope, deriv_const]
  funext; simp only [slope_fun_def, vsub_eq_sub, sub_zero, smul_zero, Function.update_apply]
  split_ifs; rfl; rfl

/-- `deriv` scales linearly without assuming differentiability -/
theorem deriv_const_smul' {f : 𝕜 → E} {c : 𝕜} (a : 𝕜) :
    deriv (fun x ↦ a • f x) c = a • deriv f c := by
  by_cases a0 : a = 0; simp only [a0, zero_smul, deriv_const]
  by_cases d : DifferentiableAt 𝕜 f c; exact deriv_const_smul _ d
  have ad : ¬DifferentiableAt 𝕜 (fun x ↦ a • f x) c := by
    contrapose d; simp only [not_not] at d ⊢
    have e : f = fun z ↦ a⁻¹ • a • f z := by
      funext; simp only [←smul_assoc, smul_eq_mul, inv_mul_cancel a0, one_smul]
    rw [e]; exact d.const_smul _
  simp only [deriv_zero_of_not_differentiableAt d, deriv_zero_of_not_differentiableAt ad, smul_zero]

/-- `leadingCoeff` has linear scaling -/
theorem leadingCoeff_const_smul {f : 𝕜 → E} {c a : 𝕜} :
    leadingCoeff (fun z ↦ a • f z) c = a • leadingCoeff f c := by
  by_cases a0 : a = 0; simp only [a0, zero_smul, leadingCoeff.zero]
  simp only [leadingCoeff, orderAt_const_smul a0]
  generalize hn : orderAt f c = n; clear hn
  have e : ((Function.swap dslope c)^[n] fun z : 𝕜 ↦ a • f z) =
      a • (Function.swap dslope c)^[n] f := by
    induction' n with n h; funext; simp only [Function.iterate_zero_apply, Pi.smul_apply]
    generalize hg : (Function.swap dslope c)^[n] f = g
    simp only [Function.iterate_succ_apply', h, hg]
    funext x; simp only [Function.swap]
    by_cases cx : x = c
    simp only [cx, dslope_same, Pi.smul_apply, Pi.smul_def, deriv_const_smul']
    simp only [dslope_of_ne _ cx, Pi.smul_apply, slope, vsub_eq_sub, ← smul_sub, smul_comm _ a]
  simp only [e, Pi.smul_apply]

/-- `leadingCoeff` is nonzero for nonzero order -/
theorem leadingCoeff_ne_zero {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) (o0 : orderAt f c ≠ 0) :
    leadingCoeff f c ≠ 0 := by
  rcases fa with ⟨p, fp⟩
  simp only [fp.orderAt_unique, leadingCoeff] at o0 ⊢
  exact fp.iterate_dslope_fslope_ne_zero (FormalMultilinearSeries.ne_zero_of_order_ne_zero o0)
