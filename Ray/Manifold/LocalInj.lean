module
public import Ray.Manifold.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Ray.Manifold.Inverse
import Ray.Manifold.Nontrivial
import Ray.Manifold.OpenMapping

/-!
## Nonzero derivative analytic functions are locally injective

This is a straightforward consequence of the inverse function theorem.  We also prove
parameterized versions, where `f : ℂ → S → T`.
-/

open Classical
open Filter (Tendsto)
open Function (uncurry)
open OneDimension
open Set
open scoped ContDiff Topology
noncomputable section

variable {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] [cms : IsManifold I ω S]
variable {T : Type} [TopologicalSpace T] [ChartedSpace ℂ T] [cmt : IsManifold I ω T]

/-- Nonzero derivative analytic functions are locally injective -/
public theorem ContMDiffAt.local_inj {f : S → T} {z : S}
    (fa : ContMDiffAt I I ω f z) (nc : mfderiv I I f z ≠ 0) :
    ∀ᶠ p : S × S in 𝓝 (z, z), f p.1 = f p.2 → p.1 = p.2 := by
  rcases complex_inverse_fun' fa nc with ⟨g, ga, gf, fg⟩
  have n : NontrivialMAnalyticAt g (f z) := by
    rw [← gf.self_of_nhds] at fa
    refine (NontrivialMAnalyticAt.anti ?_ fa ga).2
    exact (nontrivialMAnalyticAt_id _).congr (Filter.EventuallyEq.symm fg)
  have o := n.nhds_eq_map_nhds; rw [gf.self_of_nhds] at o
  simp only [nhds_prod_eq, o, Filter.prod_map_map_eq, Filter.eventually_map]
  refine (fg.prod_mk fg).mp (.of_forall ?_); intro ⟨x, y⟩ ⟨ex, ey⟩ h
  simp only at ex ey; simp only [ex, ey] at h; simp only [h]

/-- Nonzero derivative analytic functions are locally injective, parameterized version.
    Specifically, we show local injectivity of `(c,z) ↦ (c, f c z)`. -/
public theorem ContMDiffAt.local_inj'' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (nc : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : (ℂ × S) × ℂ × S in 𝓝 ((c, z), (c, z)),
      p.1.1 = p.2.1 → f p.1.1 p.1.2 = f p.2.1 p.2.2 → p.1 = p.2 := by
  rcases complex_inverse_fun fa nc with ⟨g, ga, gf, fg⟩
  have n : NontrivialMAnalyticAt (g c) (f c z) := by
    have e : (c, z) = (c, g c (f c z)) := by rw [gf.self_of_nhds]
    rw [e] at fa
    refine (NontrivialMAnalyticAt.anti ?_ fa.along_snd ga.along_snd).2
    refine (nontrivialMAnalyticAt_id _).congr ?_
    refine ((continuousAt_const.prodMk continuousAt_id).eventually fg).mp (.of_forall ?_)
    exact fun _ e ↦ e.symm
  have o := n.nhds_eq_map_nhds_param ga; rw [gf.self_of_nhds] at o; simp only at o
  rw [nhds_prod_eq, o]; simp only [Filter.prod_map_map_eq, Filter.eventually_map]
  refine (fg.prod_mk fg).mp (.of_forall ?_); intro ⟨x, y⟩ ⟨ex, ey⟩ h1 h2
  simp only at h1; simp only [h1] at ex ey h2 ⊢; simp only [ex, ey] at h2; simp only [h2]

/-- Nonzero derivative analytic functions are locally injective, parameterized version.
    Specifically, we show local injectivity of `(c,z) ↦ (c, f c z)`. -/
public theorem ContMDiffAt.local_inj' {f : ℂ → S → T} {c : ℂ} {z : S}
    (fa : ContMDiffAt II I ω (uncurry f) (c, z)) (nc : mfderiv I I (f c) z ≠ 0) :
    ∀ᶠ p : ℂ × S × S in 𝓝 (c, z, z), f p.1 p.2.1 = f p.1 p.2.2 → p.2.1 = p.2.2 := by
  set g : ℂ × S × S → (ℂ × S) × ℂ × S := fun p ↦ ((p.1, p.2.1), (p.1, p.2.2))
  have t : Tendsto g (𝓝 (c, z, z)) (𝓝 ((c, z), (c, z))) := by
    apply Continuous.continuousAt; apply Continuous.prodMk
    · exact continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    · exact continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  refine (t.eventually (fa.local_inj'' nc)).mp (.of_forall ?_)
  intro ⟨e, x, y⟩ inj fe; exact (Prod.ext_iff.mp (inj rfl fe)).2
