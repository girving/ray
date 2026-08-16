module
public import Ray.Multibrot.Defs
import Ray.Dynamics.Multiple
import Ray.Manifold.Analytic
import Ray.Manifold.GlobalInverse
import Ray.Manifold.LocalInj
import Ray.Manifold.OpenMapping
import Ray.Misc.Bounds
import Ray.Misc.Topology
import Ray.Multibrot.Basic
import Ray.Multibrot.Bottcher

/-!
## Böttcher coordinates form an isomorphism between the exterior Multibrot set and the unit disk

We show that

1. `(c,c)` is postcritical for each `c` not in the Multibrot set.  To see this, note that `0` and
   `∞` are the only critical points of `f z = z^d + c`, and `c` is postcritical since it is the
   image of `0` (and thus has smaller potential).
2. Therefore, the diagonal Böttcher map `bottcher d c = s.bottcher c c` is analytic throughout
   the exterior of the Multibrot set.
3. `bottcher d` is nontrivial throughout the exterior of the Multibrot set, as otherwise triviality
   spreads throughout `𝕊`.
4. `bottcher d` bijects from the exterior of the Multibrot set to `ball 0 1`.
5. There is an explicit, analytic homeomorphism `bottcherHomeomorph d` from the exterior of the
   Multibrot set to `ball 0 1`.

Connectivity of the Multibrot set and its complement are easy consequences of (5); see
`Multibrot/Connected.lean` and `Mandelbrot.lean`.
-/

open Complex
open Filter (Tendsto atTop)
open Function (uncurry)
open Metric (ball closedBall isOpen_ball mem_ball_self mem_ball mem_closedBall mem_closedBall_self)
open Real (exp log)
open RiemannSphere
open OneDimension
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

variable {c : ℂ}

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]

/-!
## Injectivity of Böttcher coordinates
-/

/-- `bottcher d` is injective.

    We use induction on potential down 0, expressed using closed sets of pairs.  Intuitively,
    1. Near 0, `bottcher d` is injective since it is noncritical.
    2. The set of potentials with an injectivity counterexample is open.
    3. A limit of counterexamples is either already a counterexample, or shows that `bottcher d`
       is critical at the limit.
    4. But every value is repeated near critical points of analytic functions, so in particular
       smaller values are repeated, which gives us a smaller potential counterexample. -/
public theorem bottcher_inj : InjOn (bottcher d) (multibrotExt d) := by
  -- We operate by induction on potential down to 0, expressed using closed sets of pairs.
  -- Preliminaries first:
  by_contra bad
  simp only [InjOn, not_forall, ← ne_eq] at bad
  rcases bad with ⟨x, xm, y, ym, bxy, xy⟩
  generalize hb : potential d x = b
  have b1 : b < 1 := by rwa [← hb, potential_lt_one]
  set u := {c | potential d c ≤ b}
  set t0 := u ×ˢ u
  set t1 := {q : 𝕊 × 𝕊 | bottcher d q.1 = bottcher d q.2 ∧ q ∈ t0}
  set t2 := {q : 𝕊 × 𝕊 | q.1 ≠ q.2 ∧ q ∈ t1}
  have t2ne : t2.Nonempty := by
    refine ⟨⟨x, y⟩, xy, bxy, ?_, ?_⟩
    · simp only [mem_ofPred, ← hb, le_refl, u]
    · simp only [mem_ofPred, ← hb, ← norm_bottcher, bxy, le_refl, u]
  clear x xm y ym bxy xy hb
  have ue : u ⊆ multibrotExt d := by intro c m; rw [← potential_lt_one]; exact lt_of_le_of_lt m b1
  have t01 : t1 ⊆ t0 := inter_subset_right
  have t12 : t2 ⊆ t1 := inter_subset_right
  have uc : IsClosed u := isClosed_le potential_continuous continuous_const
  have t0c : IsClosed t0 := uc.prod uc
  have t1c : IsClosed t1 := by
    rw [isClosed_iff_frequently]; intro ⟨x, y⟩ f
    have m0 : (x, y) ∈ t0 :=
      Filter.Frequently.mem_of_closed (f.mp (.of_forall fun _ m ↦ t01 m)) t0c
    refine ⟨tendsto_nhds_unique_of_frequently_eq ?_ ?_
      (f.mp (.of_forall fun _ m ↦ m.1)), m0⟩
    · exact (bottcherMAnalytic d _ (ue m0.1)).continuousAt.comp continuousAt_fst
    · exact (bottcherMAnalytic d _ (ue m0.2)).continuousAt.comp continuousAt_snd
  have t12' : closure t2 ⊆ t1 := by rw [← t1c.closure_eq]; exact closure_mono t12
  have t2c' : IsCompact (closure t2) := isClosed_closure.isCompact
  have t2ne' : (closure t2).Nonempty := t2ne.closure
  -- Find the smallest potential which (almost) violates injectivity,
  -- and a pair (x,y) which realizes it
  have pc : Continuous fun q : 𝕊 × 𝕊 ↦ potential d q.1 := potential_continuous.comp continuous_fst
  rcases t2c'.exists_isMinOn t2ne' pc.continuousOn with ⟨⟨x, y⟩, m2, min⟩
  simp only [isMinOn_iff] at min
  generalize xp : potential d x = p; rw [xp] at min
  have m1 := t12' m2
  have pb : p ≤ b := by rw [← xp]; exact m1.2.1
  have xm : x ∈ multibrotExt d := ue m1.2.1
  have ym : y ∈ multibrotExt d := ue m1.2.2
  have yp : potential d y = p := by rw [← norm_bottcher, ← m1.1, norm_bottcher, xp]
  have p0i : p = 0 → x = ∞ ∧ y = ∞ := by intro p0; rw [p0, potential_eq_zero] at xp yp; use xp, yp
  -- Split into three cases to find a contradiction
  by_cases xy : x ≠ y
  · -- Case 1: If x ≠ y, we can move a bit downwards in potential
    have p0 : p ≠ 0 := by
      contrapose xy; rcases p0i xy with ⟨xi, yi⟩; rw [xi, yi]
    have f : ∃ᶠ q : ℂ × ℂ in Filter.map
        (fun q : 𝕊 × 𝕊 ↦ (bottcher d q.1, bottcher d q.2)) (𝓝 (x, y)),
        q.1 = q.2 ∧ ‖q.1‖ < p := by
      rw [nhds_prod_eq, ← Filter.prod_map_map_eq, ← (bottcherNontrivial xm).nhds_eq_map_nhds, ←
        (bottcherNontrivial ym).nhds_eq_map_nhds, m1.1, ← nhds_prod_eq]
      apply (continuous_id.prodMk continuous_id).continuousAt.frequently
      simp only [true_and, ← yp, ← norm_bottcher]; apply frequently_smaller
      rw [← norm_ne_zero_iff, norm_bottcher, yp]; exact p0
    simp only [Filter.frequently_map] at f
    rcases(f.and_eventually (Ne.eventually_ne xy)).exists with ⟨⟨v, w⟩, ⟨bvw, pv⟩, vw⟩
    simp only [norm_bottcher] at vw bvw pv ⊢
    have pw : potential d w < p := by rwa [← norm_bottcher, ← bvw, norm_bottcher]
    have m : (v, w) ∈ t2 := ⟨vw, bvw, le_trans pv.le pb, le_trans pw.le pb⟩
    contrapose pv; clear pv; simp only [not_lt]; exact min ⟨v, w⟩ (subset_closure m)
  -- x = y, so we're at a singular point
  simp only [not_not] at xy
  rw [← xy] at m1 m2 p0i; clear xy ym yp y
  have db : mfderiv I I (bottcher d) x = 0 := by
    contrapose m2; simp only [mem_closure_iff_frequently, Filter.not_frequently]
    refine ((bottcherMAnalytic d _ xm).local_inj m2).mp (.of_forall ?_)
    intro ⟨x, y⟩ inj ⟨xy, e, _⟩; simp only at xy e inj; exact xy (inj e)
  by_cases p0 : p ≠ 0
  · -- Case 2: At a singular point we're not locally injective,
    -- so we can find a smaller potential value
    rcases not_local_inj_of_mfderiv_zero (bottcherMAnalytic d _ xm) db with ⟨r, ra, rx, e⟩
    simp only [eventually_nhdsWithin_iff, mem_compl_singleton_iff] at e
    rw [← xp, ← norm_bottcher, norm_ne_zero_iff] at p0
    have h := frequently_smaller p0
    rw [(bottcherNontrivial xm).nhds_eq_map_nhds, Filter.frequently_map] at h
    have m : ∃ᶠ z in 𝓝 x, potential d z < p ∧ (z, r z) ∈ t2 := by
      refine h.mp (e.mp (.of_forall fun z e lt ↦ ?_))
      have zx : z ≠ x := by
        contrapose lt; simp only [not_lt] at lt ⊢; simp only [lt, le_refl]
      rw [norm_bottcher, norm_bottcher, xp] at lt
      rcases e zx with ⟨rz, e⟩
      refine ⟨lt, rz.symm, e.symm, le_trans lt.le pb, ?_⟩
      rw [← norm_bottcher, ← e, norm_bottcher] at lt; exact le_trans lt.le pb
    rcases m.exists with ⟨y, yp, m⟩
    linarith [min _ (subset_closure m)]
  · -- Case 1: x = ∞, which we know is nonsingular
    simp only [not_not] at p0; rw [(p0i p0).1] at db
    exact bottcher_mfderiv_inf_ne_zero db

@[simp] public lemma bottcher_coe_ne_zero : bottcher d c ≠ 0 := by
  by_cases m : ↑c ∈ multibrotExt d
  · rw [← bottcher_inf (d := d)]
    exact bottcher_inj.ne m (by simp) (by simp)
  · simp only [← potential_lt_one, not_lt] at m
    rw [← norm_ne_zero_iff, norm_bottcher]
    linarith

public lemma bottcher_inj' : InjOn (bottcher' d) (multibrot d)ᶜ := by
  intro a am b bm e
  simp only [mem_compl_iff, ← multibrotExt_coe] at am bm
  simpa using bottcher_inj (d := d) am bm (by simp [bottcher, e])

public lemma deriv_bottcher_ne_zero (m : c ∉ multibrot d) : deriv (bottcher' d) c ≠ 0 :=
  bottcher_inj'.deriv_ne_zero isCompact_multibrot.isClosed.isOpen_compl m (bottcher_analytic _ m)

/-!
## The external ray map, and `bottcherHomeomorph`
-/

lemma ray_exists (d : ℕ) [Fact (2 ≤ d)] :
    ∃ g, ContMDiffOnNhd I I g (bottcher d '' multibrotExt d) ∧
      ∀ z : 𝕊, z ∈ multibrotExt d → g (bottcher d z) = z :=
  global_complex_inverse_fun_open' (bottcherMAnalytic d).contMDiffOn bottcher_inj
    isOpen_multibrotExt

/-- The inverse to `bottcher d`, defining external rays throughout the exterior -/
public def ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → 𝕊 :=
  Classical.choose (ray_exists d)

/-- `ray` as an analytic `ℂ → ℂ` function -/
@[expose] public def inv_ray (d : ℕ) [Fact (2 ≤ d)] : ℂ → ℂ :=
  fun z ↦ (ray d z)⁻¹.toComplex

/-- The function we need to plug into Grönwall's area theorem: `z / inv_ray d` -/
@[expose] public def pray (d : ℕ) [Fact (2 ≤ d)] (z : ℂ) : ℂ :=
  (dslope (inv_ray d) 0 z)⁻¹

/-- `ray d` is analytic on `ball 0 1` -/
public theorem rayMAnalytic (d : ℕ) [Fact (2 ≤ d)] : ContMDiffOnNhd I I (ray d) (ball 0 1) := by
  rw [← bottcher_surj d]; exact (Classical.choose_spec (ray_exists d)).1

/-- `ray d` is the left inverse to `bottcher d` -/
public theorem ray_bottcher {c : 𝕊} (m : c ∈ multibrotExt d) : ray d (bottcher d c) = c :=
  (Classical.choose_spec (ray_exists d)).2 _ m

/-- `ray d` is the right inverse to `bottcher d` -/
public theorem bottcher_ray {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : bottcher d (ray d z) = z := by
  rw [← bottcher_surj d] at m; rcases m with ⟨c, m, cz⟩
  nth_rw 1 [← cz]; rw [ray_bottcher m]; exact cz

/-- `ray d` surjects from `ball 0 1` to the exterior of the Multibrot set -/
public theorem ray_surj (d : ℕ) [Fact (2 ≤ d)] : ray d '' ball 0 1 = multibrotExt d := by
  rw [← bottcher_surj d]; apply Set.ext; intro c; simp only [← image_comp, mem_image]; constructor
  · intro ⟨e, m, ec⟩; simp only [Function.comp, ray_bottcher m] at ec; rwa [← ec]
  · intro m; use c, m, ray_bottcher m

/-- `bottcher d` as an (analytic) homeomorphism from `multibrotExt d` to `ball 0 1` -/
public def bottcherHomeomorph (d : ℕ) [Fact (2 ≤ d)] : OpenPartialHomeomorph 𝕊 ℂ where
  toFun := bottcher d
  invFun := ray d
  source := multibrotExt d
  target := ball 0 1
  map_source' := by intro c m; simp only [← bottcher_surj d]; exact mem_image_of_mem _ m
  map_target' := by intro z m; simp only [← ray_surj d]; exact mem_image_of_mem _ m
  left_inv' c m := ray_bottcher m
  right_inv' z m := bottcher_ray m
  open_source := isOpen_multibrotExt
  open_target := isOpen_ball
  continuousOn_toFun := (bottcherMAnalytic d).continuousOn
  continuousOn_invFun := (rayMAnalytic d).continuousOn

public lemma ray_inj : InjOn (ray d) (ball (0 : ℂ) 1) :=
  (bottcherHomeomorph d).symm.injOn

public lemma ray_mem_multibrotExt {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : ray d z ∈ multibrotExt d :=
  (bottcherHomeomorph d).map_target m

@[simp] public lemma ray_zero : ray d 0 = ∞ := by
  simpa only [bottcher_inf] using ray_bottcher (d := d) (c := ∞) (by simp)

@[simp] public lemma ray_ne_zero {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : ray d z ≠ 0 := by
  have h := (bottcherHomeomorph d).map_target m
  contrapose h
  simp [bottcherHomeomorph, h]

@[simp] public lemma ray_eq_inf {z : ℂ} (m : z ∈ ball (0 : ℂ) 1) : ray d z = ∞ ↔ z = 0 := by
  rw [← ray_zero (d := d)]
  exact ray_inj.eq_iff m (by simp)

@[simp] public lemma norm_bottcher_lt_one {z : 𝕊} (m : z ∈ multibrotExt d) : ‖bottcher d z‖ < 1 := by
  simpa [bottcherHomeomorph] using (bottcherHomeomorph d).map_source m
