module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Ray.Analytic.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FormalMultilinearSeries
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Stream.Defs
import Mathlib.Tactic.Cases
import Mathlib.Topology.Basic
import Ray.Misc.Bounds
import Ray.Misc.Multilinear
import Ray.Misc.Topology

/-!
## Facts about analytic functions (general field case)
-/

open Classical
open Filter (atTop)
open Function (curry uncurry)
open Metric (ball closedBall sphere isOpen_ball)
open Set (univ)
open scoped ContDiff Real NNReal ENNReal Topology
noncomputable section

variable {𝕜 : Type} [NontriviallyNormedField 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Drop 'Within' from `AnalyticWithinAt` if we have a neighborhood -/
public lemma AnalyticWithinAt.analyticAt {f : E → F} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (xs : s ∈ 𝓝 x) : AnalyticAt 𝕜 f x := by
  obtain ⟨p, r, fp⟩ := fa
  obtain ⟨e, e0, es⟩ := Metric.mem_nhds_iff.mp xs
  refine ⟨p, min r (.ofReal e),
    {r_le := by simp [fp.r_le], r_pos := by simp [fp.r_pos, e0], hasSum := fun {y} yr ↦ ?_}⟩
  simp only [EMetric.mem_ball, edist_zero_right, lt_inf_iff] at yr
  obtain ⟨yr, ye⟩ := yr
  simp only [← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff e0] at ye
  exact fp.hasSum (.inr (es (by simp [ye]))) (by simp [yr])

/-- Extract `AnalyticAt` from `ContDiffOn 𝕜 ω` if we have a neighborhood -/
public lemma ContDiffOn.analyticAt {f : E → F} {s : Set E} (fa : ContDiffOn 𝕜 ω f s) {x : E}
    (xs : s ∈ 𝓝 x) : AnalyticAt 𝕜 f x :=
  (fa x (mem_of_mem_nhds xs)).analyticWithinAt.analyticAt xs

/-- Extract `AnalyticOnNhd` from `ContDiffOn 𝕜 ω` if we're open -/
public lemma ContDiffOn.analyticOnNhd {f : E → F} {s : Set E} (fa : ContDiffOn 𝕜 ω f s)
    (os : IsOpen s) : AnalyticOnNhd 𝕜 f s :=
  fun x xs ↦ (fa x xs).analyticWithinAt.analyticAt (os.mem_nhds xs)

public lemma AnalyticAt.div_const {f : E → 𝕜} {c : E} (fa : AnalyticAt 𝕜 f c) {w : 𝕜} :
    AnalyticAt 𝕜 (fun z ↦ f z / w) c := by
  by_cases w0 : w = 0
  · simp only [w0, div_zero, analyticAt_const]
  · exact fa.div analyticAt_const w0

public lemma AnalyticAt.dslope {f : 𝕜 → E} {c x : 𝕜} (fa : AnalyticAt 𝕜 f x) :
    AnalyticAt 𝕜 (dslope f c) x := by
  by_cases e : x = c
  · obtain ⟨p,fp⟩ := fa
    simp only [← e]
    exact ⟨_, fp.has_fpower_series_dslope_fslope⟩
  · rw [analyticAt_congr (dslope_eventuallyEq_slope_of_ne _ e)]
    apply AnalyticAt.smul
    · exact AnalyticAt.inv (by fun_prop) (by simpa only [ne_eq, sub_eq_zero])
    · simp only [vsub_eq_sub]
      exact fa.sub analyticAt_const

/-- Power series coefficients in terms of iterated derivatives -/
public lemma HasFPowerSeriesAt.coeff_eq_iteratedDeriv_div [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 𝕜} {c : 𝕜} (fp : HasFPowerSeriesAt f p c) (n : ℕ) :
    p.coeff n = iteratedDeriv n f c / n.factorial := by
  simp only [fp.eq_formalMultilinearSeries (AnalyticAt.hasFPowerSeriesAt ⟨_, fp⟩),
    FormalMultilinearSeries.coeff_ofScalars]

/-- `orderAt` is unique, since power series are -/
public theorem HasFPowerSeriesAt.orderAt_unique {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    {c : 𝕜} (fp : HasFPowerSeriesAt f p c) : orderAt f c = p.order := by
  have fa : AnalyticAt 𝕜 f c := ⟨p, fp⟩
  simp only [orderAt, fa, dif_pos]
  have s := choose_spec fa
  generalize hq : choose fa = q
  simp_rw [hq] at s
  rw [fp.eq_formalMultilinearSeries s]

/-- `orderAt` is zero for nonzeros -/
public theorem orderAt_eq_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) : orderAt f c = 0 := by
  by_cases fp : AnalyticAt 𝕜 f c
  · rcases fp with ⟨p, fp⟩; rw [fp.orderAt_unique]; rw [← fp.coeff_zero 1] at f0
    rw [FormalMultilinearSeries.order_eq_zero_iff']; right
    contrapose f0
    simp only [f0, ContinuousMultilinearMap.zero_apply]
  · simp [orderAt, fp]

/-- `orderAt = 0` means either `f = 0` or `f c ≠ 0` -/
public theorem orderAt_eq_zero_iff {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) :
    orderAt f c = 0 ↔ f =ᶠ[𝓝 c] 0 ∨ f c ≠ 0 := by
  rcases fa with ⟨p, fp⟩
  simp only [fp.orderAt_unique, ←fp.coeff_zero fun _ ↦ 0,
    FormalMultilinearSeries.order_eq_zero_iff']
  rw [←@norm_ne_zero_iff _ _ (p 0 fun _ ↦ 0), ContinuousMultilinearMap.fin0_apply_norm,
    norm_ne_zero_iff]
  apply or_congr_left'; intro _; exact fp.locally_zero_iff.symm

/-- `orderAt = 1 → deriv ≠ 0` -/
public theorem deriv_ne_zero_of_orderAt_eq_one {f : 𝕜 → E} {c : 𝕜} (o : orderAt f c = 1) :
    deriv f c ≠ 0 := by
  by_cases fa : AnalyticAt 𝕜 f c
  · rcases fa with ⟨p, fp⟩
    rw [fp.orderAt_unique] at o
    have o0 : p.order ≠ 0 := by rw [o]; exact one_ne_zero
    have p0 := FormalMultilinearSeries.apply_order_ne_zero' o0
    rw [o] at p0
    simpa only [fp.deriv, FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul,
      FormalMultilinearSeries.coeff_eq_zero, Ne]
  · simp only [orderAt, fa] at o; rw [dif_neg] at o; norm_num at o; exact not_false

/-- `leadingCoeff` for nonzeros -/
public theorem leadingCoeff_of_ne_zero {f : 𝕜 → E} {c : 𝕜} (f0 : f c ≠ 0) :
    leadingCoeff f c = f c := by
  simp only [leadingCoeff, orderAt_eq_zero f0, Function.iterate_zero_apply]

/-- `f` is approximated by its leading monomial -/
public theorem AnalyticAt.leading_approx {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c) :
    (fun z ↦ f z - (z - c) ^ orderAt f c • leadingCoeff f c) =o[𝓝 c] fun z ↦
      (z - c) ^ orderAt f c := by
  rcases fa with ⟨p, fp⟩
  generalize ha : leadingCoeff f c = a
  generalize hd : orderAt f c = d
  have ha' : (Function.swap _root_.dslope c)^[d] f c = a := by rw [← ha, ← hd, leadingCoeff]
  have e := fp.eq_pow_order_mul_iterate_dslope
  simp_rw [← fp.orderAt_unique, hd] at e
  apply Asymptotics.IsLittleO.of_isBigOWith; intro k kp
  rw [Asymptotics.isBigOWith_iff]
  apply e.mp
  have dc : ContinuousAt ((Function.swap _root_.dslope c)^[d] f) c :=
    (fp.has_fpower_series_iterate_dslope_fslope d).analyticAt.continuousAt
  rcases Metric.continuousAt_iff.mp dc k kp with ⟨r, rp, rh⟩
  rw [ha'] at rh
  generalize hg : (Function.swap _root_.dslope c)^[d] f = g; rw [hg] at rh
  rw [Metric.eventually_nhds_iff]; use r, rp; intro y yr fe; rw [fe]
  specialize rh yr; rw [dist_eq_norm] at rh
  calc ‖(y - c) ^ d • g y - (y - c) ^ d • a‖
    _ = ‖(y - c) ^ d‖ * ‖g y - a‖ := by rw [←smul_sub, norm_smul]
    _ ≤ ‖(y - c) ^ d‖ * k := mul_le_mul_of_nonneg_left rh.le (norm_nonneg _)
    _ = k * ‖(y - c) ^ d‖ := by rw [mul_comm]

/-- `orderAt > 0` means `f` has a zero -/
public theorem AnalyticAt.zero_of_order_pos {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (p : 0 < orderAt f c) : f c = 0 := by
  have a := (Asymptotics.isBigOWith_iff.mp (fa.leading_approx.forall_isBigOWith zero_lt_one)).self_of_nhds
  simp only [(pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp p)).mpr, sub_self, zero_smul, sub_zero,
    norm_zero, MulZeroClass.mul_zero, norm_le_zero_iff] at a
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
    FormalMultilinearSeries.unshift, ContinuousLinearMap.compFormalMultilinearSeries_apply]
  simp [ContinuousLinearMap.smulRightL, Finset.univ, Fintype.elems, Fin.init]

/-- The power series of `(z - c)^n • f z` -/
def FormalMultilinearSeries.unshiftIter (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) :=
  (fun p ↦ FormalMultilinearSeries.unshift' p (0 : E))^[n] p

lemma FormalMultilinearSeries.unshiftIter_coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ)
    (i : ℕ) : (p.unshiftIter n).coeff i = if i < n then 0 else p.coeff (i - n) := by
  revert i; induction' n with n h
  · simp only [FormalMultilinearSeries.unshiftIter, Function.iterate_zero, id_eq, not_lt_zero',
    tsub_zero, if_false, forall_const]
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
  · refine iSup₂_le ?_; intro r k; refine iSup_le ?_; intro h
    refine le_trans ?_ (le_iSup₂ r (k * ↑r⁻¹))
    have h := fun n ↦ mul_le_mul_of_nonneg_right (h (n + 1)) (NNReal.coe_nonneg r⁻¹)
    by_cases r0 : r = 0; · simp only [r0, ENNReal.coe_zero, ENNReal.iSup_zero, le_zero_iff]
    simp only [pow_succ, ←mul_assoc _ _ (r:ℝ), mul_assoc _ (r:ℝ) _,
      mul_inv_cancel₀ (NNReal.coe_ne_zero.mpr r0), NNReal.coe_inv, mul_one, p.unshift_norm'] at h
    simp only [NNReal.coe_inv]
    convert le_iSup _ h; rfl
  · refine iSup₂_le ?_; intro r k; refine iSup_le ?_; intro h
    refine le_trans ?_ (le_iSup₂ r (max ‖c‖ (k * ↑r)))
    have h' : ∀ n, ‖p.unshift' c n‖ * (r:ℝ)^n ≤ max ‖c‖ (k * ↑r) := by
      intro n; induction' n with n _
      · simp only [FormalMultilinearSeries.unshift_coeff_zero,
          FormalMultilinearSeries.norm_apply_eq_norm_coef, pow_zero, mul_one, le_max_iff, le_refl,
          true_or]
      · simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef] at h
        simp only [FormalMultilinearSeries.unshift_coeff_succ, pow_succ, ← mul_assoc,
          FormalMultilinearSeries.norm_apply_eq_norm_coef, le_max_iff]
        right; exact mul_le_mul_of_nonneg_right (h n) (NNReal.coe_nonneg _)
    convert le_iSup _ h'; rfl

/-- The power series of `(z - c) • f z` is the unshifted power series -/
theorem HasFPowerSeriesOnBall.unshift' {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    {r : ENNReal} (fp : HasFPowerSeriesOnBall f p c r) :
    HasFPowerSeriesOnBall (fun z ↦ (z - c) • f z) (p.unshift' 0) c r :=
  { r_le := le_trans fp.r_le (ge_of_eq p.unshift_radius')
    r_pos := fp.r_pos
    hasSum := by
      intro y yr; simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, add_sub_cancel_left]
      generalize hs : (fun n ↦ y ^ n • (p.unshift' 0).coeff n) = s
      have s0 : y • f (c + y) = y • f (c + y) + (Finset.range 1).sum s := by
        simp only [← hs, p.unshift_coeff_zero, Finset.range_one, Finset.sum_singleton, smul_zero,
          add_zero]
      rw [s0, ← hasSum_nat_add_iff, ← hs]
      simp only [p.unshift_coeff_succ, pow_succ', ← smul_smul]; apply HasSum.const_smul
      have h := fp.hasSum yr; simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff] at h
      exact h }

theorem HasFPowerSeriesAt.unshift {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    (fp : HasFPowerSeriesAt f p c) :
    HasFPowerSeriesAt (fun z ↦ (z - c) • f z) (p.unshift' 0) c := by
  rcases fp with ⟨r, fa⟩; use r; exact fa.unshift'

theorem HasFPowerSeriesAt.unshiftIter {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E} {c : 𝕜}
    {n : ℕ} (fp : HasFPowerSeriesAt f p c) :
    HasFPowerSeriesAt (fun z ↦ (z - c) ^ n • f z) (p.unshiftIter n) c := by
  induction' n with n h; · simp only [pow_zero, one_smul]; exact fp
  · simp only [pow_succ', ← smul_smul, FormalMultilinearSeries.unshiftIter, Function.iterate_succ',
      Function.comp]
    exact h.unshift

/-- Power series terms are zero iff their coeffs are zero -/
theorem FormalMultilinearSeries.ne_zero_iff_coeff_ne_zero (p : FormalMultilinearSeries 𝕜 𝕜 E)
    {n : ℕ} : p n ≠ 0 ↔ p.coeff n ≠ 0 := by
  constructor
  · intro h; contrapose h; exact coeff_eq_zero.mp h
  · intro h; contrapose h; exact coeff_eq_zero.mpr h

/-- The order of `(z - n)^n • f z` is `n` greater than `f`'s -/
public theorem AnalyticAt.monomial_mul_orderAt {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ) :
    orderAt (fun z ↦ (z - c) ^ n • f z) c = n + orderAt f c := by
  rcases fa with ⟨p, fp⟩
  have pnz : p ≠ 0 := by
    contrapose fnz
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
    simp only [← p.coeff_eq_zero, Ne] at s
    simp only [p.unshiftIter_coeff, ← FormalMultilinearSeries.coeff_eq_zero, s, Ne,
      add_lt_iff_neg_left, not_lt_zero', add_tsub_cancel_left, if_false, not_false_iff]
  · intro m mp; simp [← FormalMultilinearSeries.coeff_eq_zero, p.unshiftIter_coeff]; intro mn
    generalize ha : m - n = a; have hm : m = n + a := by rw [← ha, add_comm, Nat.sub_add_cancel mn]
    simp only [hm, add_lt_add_iff_left, Nat.lt_find_iff, not_not] at mp
    specialize mp a (le_refl _); rwa [FormalMultilinearSeries.coeff_eq_zero]

/-- The leading coefficient of `(z - n)^n • f z` is the same as `f`'s -/
public theorem AnalyticAt.monomial_mul_leadingCoeff {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (fnz : ∃ᶠ z in 𝓝 c, f z ≠ 0) (n : ℕ) :
    leadingCoeff (fun z ↦ (z - c) ^ n • f z) c = leadingCoeff f c := by
  simp [leadingCoeff, fa.monomial_mul_orderAt fnz n]; generalize orderAt f c = a
  induction' n with n h
  · simp only [zero_add, pow_zero, one_smul]
  · simp [pow_succ', ← smul_smul, Nat.succ_add]
    generalize hg : (fun z ↦ (z - c) ^ n • f z) = g
    have hg' : ∀ z, (z - c) ^ n • f z = g z := by
      rw [←hg]; simp only [forall_const]
    simp_rw [hg'] at h ⊢
    have e : (Function.swap _root_.dslope c fun z ↦ (z - c) • g z) = g := by
      simp only [Function.swap, dslope_sub_smul, Function.update_eq_self_iff]
      rw [deriv_fun_smul]
      simp only [sub_self, zero_smul, deriv_fun_sub, differentiableAt_fun_id,
        differentiableAt_const, deriv_id'', deriv_const', sub_zero, one_smul, zero_add]
      exact differentiableAt_id.sub (differentiableAt_const _)
      rw [←hg]
      exact ((differentiableAt_id.sub (differentiableAt_const _)).pow _).smul fa.differentiableAt
    rw [e, h]

/-- `deriv` in the second variable is analytic -/
public theorem AnalyticAt.deriv2 [CompleteSpace 𝕜] {f : E → 𝕜 → 𝕜} {c : E × 𝕜}
    (fa : AnalyticAt 𝕜 (uncurry f) c) :
    AnalyticAt 𝕜 (fun x : E × 𝕜 ↦ _root_.deriv (f x.1) x.2) c := by
  set p : (E × 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.apply 𝕜 𝕜 (0, 1)
  have e : ∀ᶠ x : E × 𝕜 in 𝓝 c, _root_.deriv (f x.1) x.2 = p (_root_.fderiv 𝕜 (uncurry f) x) := by
    refine fa.eventually_analyticAt.mp (.of_forall ?_)
    intro ⟨x, y⟩ fa; simp only [← fderiv_apply_one_eq_deriv]
    have e : f x = uncurry f ∘ fun y ↦ (x, y) := rfl
    rw [e]; rw [fderiv_comp]
    have pd : _root_.fderiv 𝕜 (fun y : 𝕜 ↦ (x, y)) y = ContinuousLinearMap.inr 𝕜 E 𝕜 := by
      apply HasFDerivAt.fderiv; apply hasFDerivAt_prodMk_right
    rw [pd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.apply_apply]
    · exact fa.differentiableAt
    · exact (differentiableAt_const _).prodMk differentiableAt_id
  rw [analyticAt_congr e]
  exact (p.analyticAt _).comp fa.fderiv

/-- Scaling commutes with power series -/
theorem HasFPowerSeriesAt.const_fun_smul {f : 𝕜 → E} {c a : 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    (fp : HasFPowerSeriesAt f p c) : HasFPowerSeriesAt (fun z ↦ a • f z) (fun n ↦ a • p n) c := by
  rw [hasFPowerSeriesAt_iff] at fp ⊢; refine fp.mp (.of_forall fun z h ↦ ?_)
  simp only [FormalMultilinearSeries.coeff, ContinuousMultilinearMap.smul_apply, smul_comm _ a]
  exact h.const_smul a

/-- Nonzero scaling does not change analyticitiy -/
theorem analyticAt_iff_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) :
    AnalyticAt 𝕜 (fun z ↦ a • f z) c ↔ AnalyticAt 𝕜 f c := by
  constructor
  · intro ⟨p, fp⟩
    have e : f = fun z ↦ a⁻¹ • a • f z := by
      funext; simp only [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ a0, one_smul]
    rw [e]; exact ⟨_, fp.const_smul⟩
  · intro ⟨p, fp⟩; exact ⟨_, fp.const_smul⟩

/-- Nonzero scaling does not change `orderAt` -/
public theorem orderAt_const_smul {f : 𝕜 → E} {c a : 𝕜} (a0 : a ≠ 0) :
    orderAt (fun z ↦ a • f z) c = orderAt f c := by
  by_cases fa : AnalyticAt 𝕜 f c
  · rcases fa with ⟨p, fp⟩
    have e : ∀ n, a • p n ≠ 0 ↔ p n ≠ 0 := fun n ↦ by
      simp only [a0, Ne, smul_eq_zero, false_or]
    simp only [fp.orderAt_unique, fp.const_fun_smul.orderAt_unique,
      FormalMultilinearSeries.order, e]
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
  simp only [slope_fun_def, vsub_eq_sub, sub_zero, smul_zero, Function.update_apply]
  split_ifs; rfl; rfl

/-- `leadingCoeff` has linear scaling -/
public theorem leadingCoeff_const_smul {f : 𝕜 → E} {c a : 𝕜} :
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
    · simp only [cx, dslope_same, Pi.smul_apply, Pi.smul_def, deriv_fun_const_smul']
    · simp only [dslope_of_ne _ cx, Pi.smul_apply, slope, vsub_eq_sub, ← smul_sub, smul_comm _ a]
  simp only [e, Pi.smul_apply]

/-- `leadingCoeff` is nonzero for nonzero order -/
public theorem leadingCoeff_ne_zero {f : 𝕜 → E} {c : 𝕜} (fa : AnalyticAt 𝕜 f c)
    (o0 : orderAt f c ≠ 0) : leadingCoeff f c ≠ 0 := by
  rcases fa with ⟨p, fp⟩
  simp only [fp.orderAt_unique, leadingCoeff] at o0 ⊢
  exact fp.iterate_dslope_fslope_ne_zero (FormalMultilinearSeries.ne_zero_of_order_ne_zero o0)
