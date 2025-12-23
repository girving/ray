module
public import Ray.Multibrot.Defs
import Ray.Manifold.Analytic
import Ray.Manifold.Nonseparating
import Ray.Misc.Connected
import Ray.Multibrot.Basic
import Ray.Multibrot.Isomorphism

/-!
## The Multibrot set and its complement are connected

`bottcherHomeomorph` from `Multibrot.lean` is an analytic homeomorphism from the exterior of the
Multibrot set (with `∞` included) to `ball 0 1`.  From this, the exterior is immediately (path)
connected: it's a ball.  But also the Multibrot set itself is connected, since it is the downward
intersection of compact, connected sets (the levelsets of `potential d`).
-/

open Complex
open Filter (Tendsto atTop)
open Function (uncurry)
open Metric (ball sphere closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall
  mem_closedBall_self mem_sphere)
open Real (exp log)
open RiemannSphere
open Set
open scoped OnePoint RiemannSphere Topology Real
noncomputable section

variable {c : ℂ}

-- Fix d ≥ 2
variable {d : ℕ} [Fact (2 ≤ d)]

/-- `multibrotExt` is path connected -/
public theorem isPathConnected_multibrotExt (d : ℕ) [Fact (2 ≤ d)] :
    IsPathConnected (multibrotExt d) := by
  rw [← ray_surj d]; apply IsPathConnected.image_of_continuousOn
  exact (convex_ball _ _).isPathConnected (Metric.nonempty_ball.mpr one_pos)
  exact (rayMAnalytic d).continuousOn

/-- Levelsets of `potential d` are connected -/
theorem isPathConnected_potential_levelset (p : ℝ) (p0 : 0 ≤ p) (p1 : p < 1) :
    IsPathConnected (potential d ⁻¹' {p}) := by
  have e : potential d ⁻¹' {p} = ray d '' sphere 0 p := by
    apply Set.ext; intro c
    simp only [mem_preimage, mem_singleton_iff, ← norm_bottcher, mem_image, mem_sphere,
      Complex.dist_eq, sub_zero]
    constructor
    · intro h; use bottcher d c; use h; rw [ray_bottcher]
      rw [← potential_lt_one, ← norm_bottcher, h]; exact p1
    · intro ⟨e, ep, ec⟩; rw [← ec, bottcher_ray]; exact ep
      simp only [mem_ball, Complex.dist_eq, sub_zero, ep, p1]
  rw [e]; apply (isPathConnected_sphere p0).image_of_continuousOn
  exact (rayMAnalytic d).continuousOn.mono (Metric.sphere_subset_ball p1)

/-- `(multibrotEext d)ᶜ` is connected, since it is the downward intersection of the compact,
    connected sets `potential d ⁻¹' (Ici p)`. -/
public theorem isConnected_compl_multibrotExt (d : ℕ) [Fact (2 ≤ d)] :
    IsConnected (multibrotExt d)ᶜ := by
  refine ⟨⟨((0 : ℂ) : 𝕊),?_⟩,?_⟩
  · simp only [mem_compl_iff, multibrotExt_coe, not_not, multibrot_zero]
  have e : (multibrotExt d)ᶜ = ⋂ p : Ico 0 (1 : ℝ), potential d ⁻¹' Ici p := by
    apply Set.ext; intro z
    simp only [mem_compl_iff, ← potential_lt_one, mem_iInter, mem_preimage, not_lt, mem_Ici]
    constructor; intro p1 ⟨q, m⟩; simp only [mem_Ico] at m ⊢; linarith
    intro h; contrapose h; simp only [not_le, not_forall] at h ⊢
    rcases exists_between h with ⟨y, py, y1⟩
    exact ⟨⟨y, ⟨le_trans potential_nonneg py.le, y1⟩⟩, py⟩
  rw [e]; refine @IsPreconnected.directed_iInter _ _ _ _ ?_ _ ?_ ?_ ?_
  · exact Zero.instNonempty
  · intro ⟨a, a0, a1⟩ ⟨b, b0, b1⟩
    refine ⟨⟨max a b, mem_Ico.mpr ⟨le_max_of_le_left a0, max_lt a1 b1⟩⟩, ?_, ?_⟩
    · intro z h; simp only [mem_preimage, mem_Ici, max_le_iff] at h ⊢; exact h.1
    · intro z h; simp only [mem_preimage, mem_Ici, max_le_iff] at h ⊢; exact h.2
  · intro ⟨p, m⟩; simp only
    refine IsConnected.isPreconnected (IsPathConnected.isConnected ?_)
    apply IsPathConnected.of_frontier
    · rw [frontier_Ici]; exact isPathConnected_potential_levelset _ m.1 m.2
    · exact potential_continuous
    · exact isClosed_Ici
  · intro ⟨p, m⟩; exact (isClosed_Ici.preimage potential_continuous).isCompact

/-- `multibrot d` is connected -/
public theorem isConnected_multibrot (d : ℕ) [Fact (2 ≤ d)] : IsConnected (multibrot d) := by
  have e : _root_.multibrot d = (fun z : 𝕊 ↦ z.toComplex) '' (multibrotExt d)ᶜ := by
    apply Set.ext; intro z; simp only [mem_image, mem_compl_iff]; constructor
    intro m; use z
    simp only [multibrotExt_coe, not_not, m, toComplex_coe, true_and]
    intro ⟨w, m, wz⟩; induction w using OnePoint.rec
    · contrapose m; clear m; simp only [multibrotExt_inf]
    · simp only [multibrotExt_coe, not_not, toComplex_coe] at m wz; rwa [← wz]
  rw [e]; apply (isConnected_compl_multibrotExt d).image
  refine continuousOn_toComplex.mono ?_; intro z m
  contrapose m; simp only [mem_compl_iff, mem_singleton_iff, not_not] at m
  simp only [m, notMem_compl_iff, multibrotExt_inf]

/-- `(multibrot d)ᶜ` is connected -/
public theorem isConnected_compl_multibrot (d : ℕ) [Fact (2 ≤ d)] :
    IsConnected (_root_.multibrot d)ᶜ := by
  have dc : IsConnected (multibrotExt d \ {∞}) := by
    refine ⟨⟨(((3 : ℝ) : ℂ) : 𝕊),?_⟩,?_⟩
    constructor
    · simp only [multibrotExt_coe]; apply multibrot_two_lt
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]; norm_num; norm_num
    · simp only [mem_singleton_iff, coe_ne_inf, not_false_iff]
    · exact (isPathConnected_multibrotExt d).isConnected.isPreconnected.open_diff_singleton
        isOpen_multibrotExt _
  have e : (_root_.multibrot d)ᶜ = (fun z : 𝕊 ↦ z.toComplex) '' (multibrotExt d \ {∞}) := by
    apply Set.ext; intro z; simp only [mem_compl_iff, mem_image]; constructor
    · intro m; use z
      simp only [multibrotExt_coe, m, toComplex_coe, not_false_iff, mem_diff, and_true,
        mem_singleton_iff, coe_ne_inf]
    · intro ⟨w, ⟨m, wi⟩, wz⟩; induction w using OnePoint.rec
      · contrapose wi; clear wi; simp only [mem_singleton_iff]
      · simp only [multibrotExt_coe, toComplex_coe] at m wz; rwa [← wz]
  rw [e]; apply dc.image
  refine continuousOn_toComplex.mono ?_; intro z ⟨_, i⟩
  simp only [mem_singleton_iff, mem_compl_iff] at i ⊢; exact i
