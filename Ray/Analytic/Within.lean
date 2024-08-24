import Mathlib.Analysis.Analytic.Within
import Mathlib.Tactic.Bound
import Ray.Misc.Topology

/-!
## Facts about `AnalyticWithin`
-/

open Filter (atTop)
open Set
open scoped Real ENNReal Topology
noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

/-- Congruence w.r.t. the set -/
lemma AnalyticWithinAt.congr_set {f : E → F} {s t : Set E} {x : E} (hf : AnalyticWithinAt 𝕜 f s x)
    (hst : (· ∈ s) =ᶠ[𝓝 x] (· ∈ t)) : AnalyticWithinAt 𝕜 f t x := by
  rcases Metric.eventually_nhds_iff.mp hst with ⟨e, e0, st⟩
  rcases hf with ⟨p, r, hp⟩
  exact ⟨p, min (.ofReal e) r, {
    r_le := min_le_of_right_le hp.r_le
    r_pos := by bound
    hasSum := by
      intro y m n
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at m n ⊢
      exact hp.hasSum (by simpa only [mem_def, dist_self_add_left, n.1, @st (x + y)]) n.2
    continuousWithinAt := by
      have e : 𝓝[s] x = 𝓝[t] x := nhdsWithin_eq_iff_eventuallyEq.mpr hst
      simpa only [ContinuousWithinAt, e] using hp.continuousWithinAt }⟩

/-- Analyticity within is open (within the set) -/
lemma AnalyticWithinAt.eventually_analyticWithinAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) : ∀ᶠ y in 𝓝[s] x, AnalyticWithinAt 𝕜 f s y := by
  obtain ⟨_, g, fg, ga⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  simp only [Filter.EventuallyEq, eventually_nhdsWithin_iff] at fg ⊢
  filter_upwards [fg.eventually_nhds, ga.eventually_analyticAt]
  intro z fg ga zs
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨?_, g, ?_, ga⟩
  · refine ga.continuousAt.continuousWithinAt.congr_of_eventuallyEq ?_ (fg.self_of_nhds zs)
    rw [← eventually_nhdsWithin_iff] at fg
    exact fg
  · simpa only [Filter.EventuallyEq, eventually_nhdsWithin_iff]
