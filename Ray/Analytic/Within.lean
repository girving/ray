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
      apply hp.hasSum
      simp only [mem_insert_iff, add_right_eq_self, EMetric.mem_ball, lt_min_iff, edist_lt_ofReal,
        dist_zero_right] at m n ⊢
      rcases m with m | m
      · exact .inl m
      · specialize @st (x + y) _
        · simpa only [dist_self_add_left] using n.1
        · simp only [eq_iff_iff] at st
          exact Or.inr (st.mpr m)
      · simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at n ⊢
        exact n.2 }⟩

/-- Analyticity within is open (within the set) -/
lemma AnalyticWithinAt.eventually_analyticWithinAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) : ∀ᶠ y in 𝓝[s] x, AnalyticWithinAt 𝕜 f s y := by
  obtain ⟨g, fg, ga⟩ := analyticWithinAt_iff_exists_analyticAt.mp hf
  simp only [Filter.EventuallyEq, eventually_nhdsWithin_iff] at fg ⊢
  filter_upwards [fg.eventually_nhds, ga.eventually_analyticAt]
  intro z fg ga zs
  refine analyticWithinAt_iff_exists_analyticAt.mpr ⟨g, ?_, ga⟩
  rw [← eventually_nhdsWithin_iff] at fg
  refine fg.filter_mono (nhdsWithin_mono _ ?_)
  simp only [zs, insert_eq_of_mem, subset_insert]
