module
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Ray.Misc.Bound
import Ray.Misc.Topology

/-!
## Monotone convergence theorem for series
-/

open Filter (Tendsto atTop)
open Set
open scoped ENNReal NNReal Topology

variable {ι : Type} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Monotone convergence theorem for series, `ℝ≥0∞` `HasSum` version -/
theorem ENNReal.hasSum_iSup {f : ℕ → ι → ℝ≥0∞} (mono : Monotone f) :
    HasSum (fun i ↦ ⨆ n, f n i) (⨆ n, ∑' i, f n i) := by
  rw [ENNReal.summable.hasSum_iff]
  simp only [← MeasureTheory.lintegral_count]
  exact MeasureTheory.lintegral_iSup (fun _ ↦ measurable_of_countable _) mono

/-- Monotone convergence theorem for series, `ℝ≥0∞` `∑'` version -/
theorem ENNReal.tsum_iSup {f : ℕ → ι → ℝ≥0∞} (mono : Monotone f) :
    ∑' i, ⨆ n, f n i = ⨆ n, ∑' i, f n i := (hasSum_iSup mono).tsum_eq

/-- Monotone convergence theorem for series, `ℝ≥0` `HasSum` version -/
theorem NNReal.hasSum_ciSup {f : ℕ → ι → ℝ≥0} {a : ℕ → ℝ≥0} (sum : ∀ n, HasSum (f n) (a n))
    (mono : Monotone f) (bound : BddAbove (range a)) : HasSum (fun i ↦ ⨆ n, f n i) (⨆ n, a n) := by
  set f' : ℕ → ι → ℝ≥0∞ := fun n i ↦ f n i
  set a' : ℕ → ℝ≥0∞ := fun n ↦ a n
  have mono' : Monotone f' := by
    intro n m nm i
    simp only [ENNReal.coe_le_coe, f']
    apply mono nm
  have sum' : ∀ n, HasSum (f' n) (a' n) := by
    intro n
    simpa [Function.comp_def] using ENNReal.continuous_coe.continuousAt.tendsto.comp (sum n)
  have bdd_f : ∀ {i}, BddAbove (range (fun n ↦ f n i)) := by
    refine fun {i} ↦ bound.range_mono _ fun n ↦ ?_
    trans ∑ i ∈ {i}, f n i
    · simp
    · exact sum_le_hasSum _ (by simp) (sum n)
  have h := (ENNReal.continuousAt_toNNReal ?_).tendsto.comp (ENNReal.hasSum_iSup mono')
  · simpa only [(sum' _).tsum_eq, HasSum, f', a', Function.comp_def, ← ENNReal.coe_iSup bdd_f,
      ← ENNReal.coe_finset_sum, ENNReal.toNNReal_coe, ← ENNReal.coe_iSup bound] using h
  · simp [f', ENNReal.tsum_coe_eq (sum _), ENNReal.iSup_coe_eq_top.not, bound]

/-- Monotone convergence theorem for series, `ℝ` `HasSum` version -/
theorem Real.hasSum_ciSup [Nonempty ι] {f : ℕ → ι → ℝ} {a : ℕ → ℝ} (sum : ∀ n, HasSum (f n) (a n))
    (mono : Monotone f) (bound_f : ∀ i, BddAbove (range (fun n ↦ f n i)))
    (bound_a : BddAbove (range a)) : HasSum (fun i ↦ ⨆ n, f n i) (⨆ n, a n) := by
  have f_nonneg : ∀ {n i}, 0 ≤ f n i - f 0 i := by
    intro n i
    simp only [sub_nonneg]
    exact mono (Nat.zero_le _) _
  have a_nonneg : ∀ {n}, 0 ≤ a n - a 0 := by
    intro n
    simp only [sub_nonneg]
    exact hasSum_le (fun i ↦ mono (Nat.zero_le _) _) (sum 0) (sum n)
  set f' : ℕ → ι → ℝ≥0 := fun n i ↦ (f n i - f 0 i).toNNReal
  set a' : ℕ → ℝ≥0 := fun n ↦ (a n - a 0).toNNReal
  have sum' : ∀ n, HasSum (f' n) (a' n) := fun n ↦ ((sum n).sub (sum 0)).toNNReal (by bound)
  have mono' : Monotone f' := by intro n m nm; simp only [Pi.le_def]; bound
  have bound_a' : BddAbove (range a') :=
    bound_a.range_comp (g := fun x ↦ (x - a 0).toNNReal) fun x y xy ↦ by bound
  have s := NNReal.hasSum_ciSup sum' mono' bound_a'
  simp [← NNReal.hasSum_coe, f', a', max_eq_left a_nonneg, max_eq_left f_nonneg,
    ← ciSup_sub bound_a, ← ciSup_sub (bound_f _)] at s
  simpa only [sub_add_cancel] using s.add (sum 0)

/- Variant where we know the limit of the sums -/
public theorem Real.hasSum_ciSup_of_tendsto [Nonempty ι] {f : ℕ → ι → ℝ} {a : ℕ → ℝ} {b : ℝ}
    (sum : ∀ n, HasSum (f n) (a n)) (mono : Monotone f)
    (bound_f : ∀ i, BddAbove (range (fun n ↦ f n i))) (bound_a : BddAbove (range a))
    (tendsto : Tendsto a atTop (𝓝 b)) : HasSum (fun i ↦ ⨆ n, f n i) b := by
  have t : Tendsto a atTop (𝓝 (⨆ n, a n)) := by
    refine tendsto_atTop_ciSup ?_ bound_a
    intro n m nm
    refine hasSum_le ?_ (sum n) (sum m)
    bound
  exact tendsto_nhds_unique tendsto t ▸ Real.hasSum_ciSup sum mono bound_f bound_a
