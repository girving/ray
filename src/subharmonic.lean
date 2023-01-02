-- Subharmonic / harmonic functions and Hartogs's lemma

import analysis.convex.integral
import analysis.fourier

import analytic
import duals
import fubini_ball
import holomorphic
import max_log
import measure
import tactics

open complex (abs exp I log)
open filter (tendsto liminf limsup at_top)
open function (uncurry)
open measure_theory
open metric (ball closed_ball sphere)
open linear_order (min)
open set (Ioc Icc univ)
open topological_space (second_countable_topology)
open_locale real nnreal ennreal topological_space complex_conjugate
noncomputable theory

variables {S : Type} [is_R_or_C S] [smul_comm_class ℝ S S]
variables {T : Type} [is_R_or_C T] [smul_comm_class ℝ T T]
variables {E : Type} [normed_add_comm_group E] [complete_space E] [normed_space ℝ E] [second_countable_topology E]
variables {F : Type} [normed_add_comm_group F] [complete_space F] [normed_space ℝ F] [second_countable_topology F]
variables {H : Type} [normed_add_comm_group H] [complete_space H] [normed_space ℂ H] [second_countable_topology H]

-- f : ℂ → S is harmonic if it is continuous and equal to means on circles.
-- We require the mean property for large circles because it is easy to prove
-- for the cases we need, and will be needed for the large submean theorem
-- for subharmonic functions.
structure harmonic_on (f : ℂ → E) (s : set ℂ) : Prop :=
  (cont : continuous_on f s)
  (mean : ∀ (c : ℂ) (r : ℝ), r > 0 → closed_ball c r ⊆ s → f c = ⨍ t in Itau, f (circle_map c r t))

-- f : ℂ → ℝ is subharmonic if it is upper semicontinuous and is below means on small disks.
-- We require the submean property only locally, and will prove the global version below.
-- Out of laziness, we assume continuity as well.  Ideally we'd allow -∞ as values, but using
-- ereal instead of ℝ adds a lot of annoying technicalities.
structure subharmonic_on (f : ℂ → ℝ) (s : set ℂ) : Prop :=
  (cont : continuous_on f s)
  (submean' : ∀ c, c ∈ interior s → ∃ r (rp : r > 0), ∀ s, 0 < s → s < r → f c ≤ ⨍ t in Itau, f (circle_map c s t))

lemma subharmonic_on.mono {f : ℂ → ℝ} {s t : set ℂ}
    (fs : subharmonic_on f s) (ts : t ⊆ s) : subharmonic_on f t := {
  cont := fs.cont.mono ts,
  submean' := λ c cs, fs.submean' c (interior_mono ts cs),
}

-- Convex functions of harmonic functions are subharmonic
theorem harmonic_on.convex {f : ℂ → E} {s : set ℂ} {g : E → ℝ}
    (fh : harmonic_on f s) (c : continuous g) (gc : convex_on ℝ set.univ g)
    : subharmonic_on (λ z, g (f z)) s := {
  cont := c.comp_continuous_on fh.cont,
  submean' := begin
    intros z zs,
    rcases metric.is_open_iff.mp (is_open_interior) z zs with ⟨r,rp,rh⟩,
    existsi [r, rp], intros t tp tr,
    have cs : closed_ball z t ⊆ s := trans (metric.closed_ball_subset_ball tr) (trans rh interior_subset),
    simp [fh.mean z t tp cs],
    have n := nice_volume.Itau,
    apply convex_on.map_set_average_le gc c.continuous_on is_closed_univ n.ne_zero n.ne_top,
    simp,
    exact (fh.cont.mono cs).integrable_on_sphere tp,
    exact ((c.comp_continuous_on fh.cont).mono cs).integrable_on_sphere tp,
  end,
}

-- Harmonic functions are subharmonic
lemma harmonic_on.subharmonic_on {f : ℂ → ℝ} {s : set ℂ} (h : harmonic_on f s)
    : subharmonic_on (λ z, f z) s := begin
  have e : (λ z, f z) = (λ z, (λ x, x) (f z)) := rfl,
  rw e, exact h.convex continuous_id (convex_on_id convex_univ),
end

-- Norms of harmonic functions are subharmonic
lemma harmonic_on.norm {f : ℂ → E} {s : set ℂ} (h : harmonic_on f s)
    : subharmonic_on (λ z, ∥f z∥) s :=
  h.convex continuous_norm (convex_on_norm convex_univ)

-- subharmonic_on depends only on values in s (→ version)
theorem subharmonic_on.congr {f g : ℂ → ℝ} {s : set ℂ}
    (fs : subharmonic_on f s) (h : set.eq_on g f s) : subharmonic_on g s := {
  cont := fs.cont.congr h,
  submean' := begin
    intros c cs,
    rcases metric.is_open_iff.mp is_open_interior c cs with ⟨r0,r0p,r0s⟩,
    rcases fs.submean' c cs with ⟨r1,r1p,sm⟩,
    have r01p : min r0 r1 > 0 := by bound,
    existsi [min r0 r1, r01p],
    intros t tp tr,
    specialize sm t tp (lt_of_lt_of_le tr (by bound)),
    have hs : (λ u, f (circle_map c t u)) =ᵐ[volume.restrict Itau] (λ u, g (circle_map c t u)), {
      rw filter.eventually_eq, rw ae_restrict_iff' measurable_set_Itau, apply filter.eventually_of_forall,
      intros u us, apply h.symm,
      apply trans r0s interior_subset,
      simp [complex.dist_eq, abs_of_pos tp], exact lt_of_lt_of_le tr (by bound),
    },
    rw set_average_eq at ⊢ sm,
    rwa [←h.symm (interior_subset cs), ←integral_congr_ae hs],
  end
}

-- subharmonic_at depends only on values near c (↔ version)
theorem subharmonic_on_congr {f g : ℂ → ℝ} {s : set ℂ}
    (h : set.eq_on f g s) : subharmonic_on f s ↔ subharmonic_on g s :=
  ⟨λ fs, fs.congr h.symm, λ gs, gs.congr h⟩

-- Constants are harmonic
lemma harmonic_on.const (a : E) {s : set ℂ} : harmonic_on (λ _, a) s := {
  cont := continuous_on_const,
  mean := begin
    intros c r rp cs,
    rw set_average_eq, simp [←smul_assoc, smul_eq_mul],
    field_simp [ne_of_gt nice_volume.Itau.real_pos],
  end,
}

-- Differences are harmonic
lemma harmonic_on.sub {f g : ℂ → E} {s : set ℂ} (fh : harmonic_on f s) (gh : harmonic_on g s)
    : harmonic_on (f - g) s := {
  cont := continuous_on.sub fh.cont gh.cont,
  mean := begin
    intros c r rp cs, simp [fh.mean c r rp cs, gh.mean c r rp cs],
    rw set_average.sub ((fh.cont.mono cs).integrable_on_sphere rp) ((gh.cont.mono cs).integrable_on_sphere rp),
  end,
}

-- Subharmonic functions add
lemma subharmonic_on.add {f g : ℂ → ℝ} {s : set ℂ} (fs : subharmonic_on f s) (gs : subharmonic_on g s)
    : subharmonic_on (λ z, f z + g z) s := {
  cont := fs.cont.add gs.cont,
  submean' := begin
    intros c cs,
    rcases fs.submean' c cs with ⟨r0,r0p,r0m⟩,
    rcases gs.submean' c cs with ⟨r1,r1p,r1m⟩,
    rcases metric.is_open_iff.mp is_open_interior c cs with ⟨r2,r2p,r2s⟩,
    set r := min r0 (min r1 r2),
    have rr1 : r ≤ r1 := trans (min_le_right _ _) (by bound),
    have rr2 : r ≤ r2 := trans (min_le_right _ _) (by bound),
    use [r, by bound], intros u up ur,
    have us : closed_ball c u ⊆ s :=
      trans (metric.closed_ball_subset_ball (lt_of_lt_of_le ur (by bound))) (trans r2s interior_subset),
    rw set_average.add ((fs.cont.mono us).integrable_on_sphere up) ((gs.cont.mono us).integrable_on_sphere up),
    have m0 := r0m u up (lt_of_lt_of_le ur (by bound)),
    have m1 := r1m u up (lt_of_lt_of_le ur (by bound)),
    exact add_le_add m0 m1,
  end,
}

-- Negations are harmonic
lemma harmonic_on.neg {f : ℂ → E} {s : set ℂ} (fh : harmonic_on f s) : harmonic_on (-f) s := begin
  have nh := harmonic_on.sub (harmonic_on.const 0) fh,
  have e : (λ _ : ℂ, (0 : E)) - f = -f, { ext, simp },
  rwa ←e,
end

-- Additions are harmonic
lemma harmonic_on.add {f g : ℂ → E} {s : set ℂ} (fh : harmonic_on f s) (gh : harmonic_on g s)
    : harmonic_on (f + g) s := begin
  have e : f + g = f - (-g), { ext, simp },
  rw e, exact fh.sub gh.neg,
end

-- Scalar multiples are harmonic
lemma harmonic_on.const_mul {f : ℂ → S} {s : set ℂ} (fh : harmonic_on f s) (a : S)
    : harmonic_on (λ z, a * f z) s := {
  cont := continuous_on.mul (continuous_on_const) fh.cont,
  mean := begin
    intros c r rp cs, rw set_average_eq,
    simp_rw [←smul_eq_mul, integral_smul, smul_comm _ a, ←set_average_eq, ←fh.mean c r rp cs],
  end,
}

-- Scalar multiples are subharmonic
lemma subharmonic_on.const_mul {f : ℂ → ℝ} {s : set ℂ} {a : ℝ} (fs : subharmonic_on f s) (ap : a ≥ 0)
    : subharmonic_on (λ z, a * f z) s := {
  cont := continuous_on.mul (continuous_on_const) fs.cont,
  submean' := begin
    intros c cs, rcases fs.submean' c cs with ⟨r,rp,rm⟩, use [r,rp], intros s sp sr, specialize rm s sp sr,
    rw [set_average_eq, smul_eq_mul] at ⊢ rm,
    calc a * f c ≤ a * (((volume Itau).to_real)⁻¹ * ∫ t in Itau, f (circle_map c s t)) : by bound
    ... = ((volume Itau).to_real)⁻¹ * (a * ∫ t in Itau, f (circle_map c s t)) : by ring
    ... = ((volume Itau).to_real)⁻¹ * ∫ t in Itau, a * f (circle_map c s t) : by rw integral_mul_left,
  end,
}

-- Analytic functions equal circle means
lemma analytic_on.circle_mean_eq {f : ℂ → H} {c : ℂ} {r : ℝ}
    (fa : analytic_on ℂ f (closed_ball c r)) (rp : r > 0) : ⨍ t in Itau, f (circle_map c r t) = f c := begin
  have h := complex.circle_integral_sub_inv_smul_of_differentiable_on_off_countable
    set.countable_empty  (metric.mem_ball_self rp) fa.continuous_on _,
  {
    simp_rw [circle_integral, deriv_circle_map, circle_map_sub_center, smul_smul, mul_comm _ I] at h,
    field_simp [circle_map_ne_center (ne_of_gt rp)] at h,
    rw [←smul_smul, is_unit.smul_left_cancel (ne.is_unit complex.I_ne_zero)] at h,
    rw [interval_integral.integral_of_le (le_of_lt real.two_pi_pos)] at h,
    rw [set_average_eq, Itau, h],
    simp, rw ennreal.to_real_of_real (le_of_lt real.two_pi_pos),
    rw [←smul_assoc, complex.real_smul], field_simp [real.pi_ne_zero],
  }, {
    intros z zs, rw set.diff_empty at zs,
    exact (fa z (metric.ball_subset_closed_ball zs)).differentiable_at,
  },
end

-- Analytic functions are harmonic
theorem analytic_on.harmonic_on {f : ℂ → H} {s : set ℂ} (fa : analytic_on ℂ f s) : harmonic_on f s := begin
  exact {
    cont := fa.continuous_on,
    mean := begin intros c r rp cs, rw (fa.mono cs).circle_mean_eq rp end,
  },
end

-- Harmonic functions compose with linear maps
theorem harmonic_on.linear {f : ℂ → E} {s : set ℂ} (fh : harmonic_on f s) (g : E →L[ℝ] F)
    : harmonic_on (λ z, g (f z)) s := {
  cont := g.continuous.comp_continuous_on fh.cont,
  mean := begin
    intros c r rp cs,
    rw average_linear_comm ((fh.cont.mono cs).integrable_on_sphere rp),
    rw fh.mean c r rp cs,
  end,
}

-- Real parts of harmonic functions are harmonic
theorem harmonic_on.re {f : ℂ → ℂ} {s : set ℂ} (fh : harmonic_on f s) : harmonic_on (λ z, (f z).re) s := begin
  simp only [←re_clm_apply], exact fh.linear _,
end

-- Complex conjugates of harmonic functions are harmonic
theorem harmonic_on.conj {f : ℂ → ℂ} {s : set ℂ} (fh : harmonic_on f s) : harmonic_on (λ z, conj (f z)) s := begin
  simp only [←conj_clm_apply], exact fh.linear _,
end

-- Real parts of analytic functions are subharmonic
theorem analytic_on.re_subharmonic_on {f : ℂ → ℂ} {s : set ℂ} (fa : analytic_on ℂ f s)
    : subharmonic_on (λ z, (f z).re) s := fa.harmonic_on.re.subharmonic_on

-- The submean property holds at minima
lemma minimum.submean {f : ℂ → ℝ} {s : set ℂ} {c : ℂ} (fc : continuous_on f s) (cs : c ∈ interior s) (fm : ∀ z, f c ≤ f z)
    : ∃ r (rp : r > 0), ∀ s, 0 < s → s < r → f c ≤ ⨍ t in Itau, f (circle_map c s t) := begin
  rcases metric.is_open_iff.mp is_open_interior c cs with ⟨r,rp,rs⟩,
  use [r,rp], intros t tp tr, rw set_average_eq,
  have fg : ∀ u (us : u ∈ Itau), f c ≤ f (circle_map c t u) := λ _ _, fm _,
  have ss : closed_ball c t ⊆ s := trans (metric.closed_ball_subset_ball tr) (trans rs interior_subset),
  have n := nice_volume.Itau,
  have m := set_integral_ge_of_const_le n.measurable n.ne_top fg ((fc.mono ss).integrable_on_sphere tp),
  rw [smul_eq_mul, ←inv_mul_le_iff (inv_pos.mpr n.real_pos)], simp, rwa mul_comm,
end

-- max b (log ∥f z∥) is subharmonic for analytic f, ℂ case
theorem analytic_on.max_log_abs_subharmonic_on {f : ℂ → ℂ} {s : set ℂ}
    (fa : analytic_on ℂ f s) (b : ℝ) : subharmonic_on (λ z, max_log b (f z).abs) s := {
  cont := fa.continuous_on.max_log_norm b,
  submean' := begin
    intros c cs,
    by_cases bf : b.exp ≥ (f c).abs, {
      apply minimum.submean (fa.continuous_on.max_log_norm b) cs,
      intro z, simp [max_log_eq_b bf, le_max_log],
    },
    simp at bf,
    have anz : ∥f c∥ ≠ 0 := ne_of_gt (trans (real.exp_pos _) bf),
    have fac : continuous_at f c := fa.continuous_on.continuous_at (mem_interior_iff_mem_nhds.mp cs),
    -- We define g carefully to avoid the logarithmic branch cut
    generalize hh : (λ z, complex.log (complex.abs (f c) / f c * f z)) = h,
    generalize hg : (λ z, (h z).re) = g,
    have ha : analytic_at ℂ h c, {
      rw ←hh,
      apply log_analytic_re_pos (analytic_at.mul (entire.const _ _) (fa c (interior_subset cs))),
      simp only, field_simp [complex.abs_ne_zero.mp anz],
    },
    rcases metric.is_open_iff.mp (is_open_analytic_at ℂ h) c ha with ⟨r0,r0p,r0a⟩,
    rcases metric.continuous_at_iff.mp fac ((f c).abs - b.exp) (sub_pos.mpr bf) with ⟨r1,r1p,r1h⟩,
    set r := min r0 r1,
    have fg : set.eq_on (λ z, max_log b (complex.abs (f z))) g (ball c r), {
      intros z zs, simp [complex.dist_eq] at zs r1h, specialize r1h zs.2,
      have zp : abs (f z) > b.exp, {
        calc abs (f z) = abs (f c + (f z - f c)) : by ring_nf
        ... ≥ abs (f c) - abs (f z - f c) : by bound
        ... > abs (f c) - (abs (f c) - b.exp) : by bound [sub_lt_sub_left]
        ... = b.exp : by ring_nf
      },
      simp [max_log_eq_log (le_of_lt zp)],
      rw [←hg, ←hh], simp [complex.log_re],
      field_simp [anz],
    },
    have gs : subharmonic_on g (ball c r), {
      rw ←hg, apply analytic_on.re_subharmonic_on, intros z zs,
      exact r0a (metric.ball_subset_ball (by bound) zs),
    },
    rw subharmonic_on_congr fg.symm at gs,
    refine gs.submean' c _,
    rw metric.is_open_ball.interior_eq, exact metric.mem_ball_self (by bound),
  end,
}

-- If a continuous subharmonic function is maximal at the center of a ball, it is constant on the ball.
theorem subharmonic_on.maximum_principle_ball {f : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (fs : subharmonic_on f (closed_ball c r)) (rp : r > 0) 
    : is_max_on f (closed_ball c r) c → ∀ z, z ∈ closed_ball c r → f c = f z := begin
  intros cm g gs,
  by_cases gc : g = c, { rw gc },
  generalize hu : complex.abs (g - c) = u,
  have u0 : u > 0, { rw ←hu, simp, contrapose gc, simp at ⊢ gc, rw sub_eq_zero at gc, exact gc },
  have ur : u ≤ r, { simp [complex.dist_eq] at gs, simp [←hu, gs] },
  generalize hy : (g - c) / u = y,
  have y1 : abs y = 1, { simp [←hy, ←hu, gc], field_simp [complex.abs_ne_zero.mpr (sub_ne_zero.mpr gc)] },
  generalize hs : (λ t : ℝ, f (c + t*y)) ⁻¹' {f c} = s,
  have s0 : (0 : ℝ) ∈ s := by simp [←hs],
  have us : u ∈ s, {
    refine is_closed.mem_of_ge_of_forall_exists_gt _ s0 (le_of_lt u0) _, {
      rw ←hs, rw set.inter_comm,
      refine continuous_on.preimage_closed_of_closed _ is_closed_Icc is_closed_singleton,
      apply fs.cont.comp (continuous.continuous_on _) _,
      exact continuous.add continuous_const (continuous.mul complex.continuous_of_real continuous_const),
      intros t ts, simp at ts, simp [y1, abs_of_nonneg ts.left, trans ts.right ur],
    }, {
      intros t ts, rw ←hs at ts, simp at ts,
      set z := c + t*y,
      rcases ts with ⟨fz,tp,tu⟩,
      have tz : abs (z - c) = t, { simp [y1, abs_of_nonneg tp] },
      have zs : z ∈ ball c r, { simp [y1, abs_of_nonneg tp], exact lt_of_lt_of_le tu ur },
      rw ←interior_closed_ball _ (ne_of_gt rp) at zs,
      rcases fs.submean' z zs with ⟨e,ep,lo⟩,
      generalize he' : min (e/2) (u-t) = e',
      have e'p : e' > 0, { rw ←he', bound },
      have teu : t + e' ≤ u, { rw ←he', transitivity t + (u-t), bound, simp },
      have e's : e' < e, { rw ←he', exact lt_of_le_of_lt (min_le_left _ _) (by bound) },
      specialize lo e' e'p e's,
      rw fz at lo,
      have ss : closed_ball z e' ⊆ closed_ball c r, {
        apply metric.closed_ball_subset_closed_ball', rw [complex.dist_eq, tz], linarith,
      },
      have hi : ∀ x, x ∈ Itau → f (circle_map z e' x) ≤ f c, {
        intros x xs, apply is_max_on_iff.mp cm, apply ss,
        simp [complex.dist_eq], simp [abs_of_pos e'p],
      },
      have fcc : continuous_on (λ a, f (circle_map z e' a)) Itau, {
        apply (fs.cont.mono ss).comp (continuous_circle_map _ _).continuous_on,
        intros a as, simp [complex.dist_eq, abs_of_pos e'p],
      },
      have fw := mean_squeeze nice_volume.Itau local_volume.Itau fcc ((fs.cont.mono ss).integrable_on_sphere e'p) lo hi,
      have eys : z + e'*y ∈ sphere z e' := by simp [abs_of_pos e'p, y1],
      rcases circle_map_Ioc eys with ⟨a,as,aey⟩,
      specialize fw a as, simp [←aey] at fw,
      existsi t+e', simp, refine ⟨_, e'p, teu⟩, rw ←hs, simp [right_distrib],
      rw ←add_assoc, exact fw, apply_instance,
    }
  },
  simp [←hs, ←hy] at us, 
  have unz : (u : ℂ) ≠ 0 := by simp [ne_of_gt u0],
  field_simp [unz] at us, ring_nf at us, field_simp [unz] at us,
  exact us.symm,
end

-- A subharmonic function achieves its maximum on the boundary
theorem subharmonic_on.maximum_principle {f : ℂ → ℝ} {s : set ℂ}
    (fs : subharmonic_on f s) (sc : is_compact s) (sn : s.nonempty)
    : ∃ w, w ∈ frontier s ∧ is_max_on f s w := begin
  rcases fs.cont.compact_max sc sn with ⟨x,xs,xm⟩,
  rcases exists_mem_frontier_inf_dist_compl_eq_dist xs sc.ne_univ with ⟨w,wb,h⟩,
  existsi [w, wb],
  generalize hr : abs (w - x) = r,
  by_cases wx : w = x, { rwa wx },
  have rp : r > 0, { simp [←hr, complex.abs_pos], apply sub_ne_zero.mpr, exact wx },
  rw [dist_comm, complex.dist_eq, hr] at h,
  have rs : closed_ball x r ⊆ s, {
    rw [←closure_ball x (ne_of_gt rp), ←sc.is_closed.closure_eq], apply closure_mono, 
    rw ←h, apply metric.ball_inf_dist_compl_subset,
  },
  have rsi : ball x r ⊆ interior s, {
    rw ←interior_closed_ball _ (ne_of_gt rp), exact interior_mono rs, apply_instance,
  }, 
  have rm : is_max_on f (closed_ball x r) x, { intros y ys, exact xm (rs ys) },
  have wx : f x = f w, {
    apply subharmonic_on.maximum_principle_ball (fs.mono rs) rp rm,
    simp [complex.dist_eq], rw hr,
  },
  intros y ys, rw ←wx, exact xm ys,
end

-- A harmonic function achieves its maximum norm on the boundary.
theorem harmonic_on.maximum_principle {f : ℂ → E} {s : set ℂ}
    (fh : harmonic_on f s) (sc : is_compact s) (sn : s.nonempty)
    : ∃ w, w ∈ frontier s ∧ ∀ z, z ∈ s → ∥f z∥ ≤ ∥f w∥ := begin
  rcases fh.norm.maximum_principle sc sn with ⟨w,wf,wh⟩,
  existsi [w, wf], intros z zs, specialize wh zs, simp at wh, exact wh,
end

-- Uniform limits of harmonic functions are harmonic
theorem uniform_harmonic_lim {f : ℕ → ℂ → E} {g : ℂ → E} {s : set ℂ}
    (h : ∀ n, harmonic_on (f n) s) (u : tendsto_uniformly_on f g at_top s)
    : harmonic_on g s := {
  cont := u.continuous_on (filter.eventually_of_forall (λ n, (h n).cont)),
  mean := begin
    intros c r rp cs,
    have m := λ n, (h n).mean c r rp cs,
    simp_rw set_average_eq at ⊢ m,
    have se : Itau =ᵐ[volume] Icc 0 (2*π) := Ioc_ae_eq_Icc,
    have vp := nice_volume.Itau.real_pos,
    generalize hv : (volume Itau).to_real = v, simp_rw hv at ⊢ m vp, clear hv,
    simp_rw set_integral_congr_set_ae se at ⊢ m,
    have cc : Icc 0 (2*π) ⊆ circle_map c r ⁻¹' s, {
      rw set.subset_def, intros t ts, simp, apply cs,
      simp [complex.dist_eq, abs_of_pos rp],
    },
    have fu := (u.comp (circle_map c r)).mono cc,
    have fc : ∀ n, continuous_on (λ t, f n (circle_map c r t)) (Icc 0 (2*π)), {
      intro n, apply continuous.continuous_on,
      apply ((h n).cont.mono cs).comp_continuous (continuous_circle_map _ _),
      intro t, simp [complex.dist_eq, abs_of_pos rp],
    },
    have ti' := fu.integral_tendsto fc is_compact_Icc,
    have ti := ti'.const_smul v⁻¹, clear ti',
    have ci := u.tendsto_at (cs (metric.mem_closed_ball_self (by bound))),
    simp_rw ←m at ti,
    exact tendsto_nhds_unique ci ti,
  end
}

section harmonic_extension

variables {c : ℂ} {r : ℝ}
lemma rri (rp : r > 0) (z : ℂ) : c + r*(r⁻¹ * (z - c)) = z := begin ring_nf, field_simp [ne_of_gt rp] end
lemma rir (rp : r > 0) (z : ℂ) : (↑r)⁻¹ * ((c + r*z) - c) = z := begin ring_nf, field_simp [ne_of_gt rp] end

-- Harmonic extensions inwards the circle
structure has_extension (f : C(circle, S)) (g : ℂ → S) (c : ℂ) (r : ℝ) : Prop :=
  (gh : harmonic_on g (closed_ball c r))
  (b : ∀ z, f z = g (c + r*z))

def extendable (f : C(circle, S)) (c : ℂ) (r : ℝ) := ∃ g : ℂ → S, has_extension f g c r

-- has_extension is linear
lemma has_extension.sub {f0 f1 : C(circle, ℂ)} {g0 g1 : ℂ → ℂ} 
    (e0 : has_extension f0 g0 c r) (e1 : has_extension f1 g1 c r)
    : has_extension (f0 - f1) (g0 - g1) c r := {
  gh := e0.gh.sub e1.gh,
  b := by simp [e0.b, e1.b],
}

lemma extension.maximum_principle {f : C(circle, ℂ)} {g : ℂ → ℂ} (e : has_extension f g c r) {b : ℝ}
    (fb : ∀ z, ∥f z∥ ≤ b) (rp : r > 0) : ∀ z, z ∈ closed_ball c r → ∥g z∥ ≤ b := begin
  rcases e.gh.maximum_principle (is_compact_closed_ball _ _) _ with ⟨w,wf,wh⟩,
  intros z zs, specialize wh z zs,
  rw [frontier_closed_ball _ (ne_of_gt rp)] at wf, simp at wf,
  set w' := (↑r)⁻¹ * (w - c),
  have wf' : abs w' = 1, { simp [wf, abs_of_pos rp], field_simp [ne_of_gt rp] },
  rw [←mem_circle_iff_abs] at wf',
  have b := e.b ⟨w',wf'⟩, simp [rri rp] at b, rw ←b at wh,
  exact trans wh (fb _),
  apply_instance,
  exact ⟨c, by simp [le_of_lt rp]⟩,
end

-- extendable is closed
lemma is_closed.extendable {s : set C(circle, ℂ)} (e : ∀ f, f ∈ s → extendable f c r) (rp : r > 0)
    : ∀ f, f ∈ closure s → extendable f c r := begin
  intros F Fe,
  rw ←seq_closure_eq_closure at Fe,
  rcases Fe with ⟨f,fs,fF⟩,
  rw continuous_map.tendsto_iff_tendsto_locally_uniformly at fF, simp at fF,
  rw tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space at fF,
  set g := λ n, classical.some (e _ (fs n)),
  have gs : ∀ n, has_extension (f n) (g n) c r := λ n, classical.some_spec (e _ (fs n)),
  have cauchy : uniform_cauchy_seq_on g at_top (closed_ball c r), {
    rw metric.uniform_cauchy_seq_on_iff,
    simp_rw [metric.tendsto_uniformly_iff, filter.eventually_at_top] at fF,
    intros t tp, rcases fF (t/4) (by bound) with ⟨N,H⟩, existsi N,
    intros a aN b bN z zs,
    have eab := (gs a).sub (gs b),
    have fab : ∀ z : circle, ∥f a z - f b z∥ ≤ t/2, {
      intro z,
      have ta := H a aN z,
      have tb := H b bN z,
      rw ←dist_eq_norm, rw dist_comm at ta,
      calc dist (f a z) (f b z) ≤ dist (f a z) (F z) + dist (F z) (f b z) : by bound
      ... ≤ t/4 + t/4 : by bound
      ... = t/2 : by ring_nf
    },
    have m := extension.maximum_principle eab fab rp z zs,
    simp [complex.dist_eq] at m ⊢, exact lt_of_le_of_lt m (by bound),
  },
  set G := λ z, lim at_top (λ n, g n z),
  have gG : tendsto_uniformly_on g G at_top (closed_ball c r), {
    apply uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto cauchy,
    intros z zs, exact (cauchy.cauchy_seq z zs).tendsto_lim,
  },
  existsi G, exact {
    gh := uniform_harmonic_lim (λ n, (gs n).gh) gG,
    b := begin
      intros z,
      refine (filter.tendsto.lim_eq _).symm,
      simp_rw ←(gs _).b,
      exact fF.tendsto_at z,
    end,
  },
end

-- p is true for all integers if it is true for nonnegative and nonpositive integers
lemma int.induction_overlap {p : ℤ → Prop} (hi : ∀ n : ℕ, p n) (lo : ∀ n : ℕ, p (-n)) : ∀ n : ℤ, p n := begin
  intro n, induction n with n, exact hi n, exact lo (n+1),
end

-- Fourier terms extend
lemma fourier_extend' (rp : r > 0) (n : ℤ) : extendable (fourier n) c r := begin
  have mh : ∀ n : ℕ, harmonic_on (λ z, ((↑r)⁻¹ * (z - c))^n) (closed_ball c r), {
    intro n, apply analytic_on.harmonic_on, refine analytic_on.mono _ (set.subset_univ _),
    rw ←differentiable_iff_analytic (is_open_univ), apply differentiable.differentiable_on,
    apply differentiable.pow, apply differentiable.mul (differentiable_const _),
    apply differentiable.sub differentiable_id (differentiable_const _),
    apply_instance,
  },
  induction n using int.induction_overlap, {
    existsi (λ z : ℂ, ((↑r)⁻¹ * (z - c))^n), exact {
      gh := mh n,
      b := begin simp_rw rir rp, simp [fourier] end,
    },
  }, {
    existsi (λ z : ℂ, conj (((↑r)⁻¹ * (z - c))^n)), exact {
      gh := (mh n).conj,
      b := begin simp_rw rir rp, simp [fourier, complex.inv_def, complex.norm_sq_eq_abs] end,
    },
  },
end

-- Fourier sums extend
lemma fourier_extend {f : C(circle, ℂ)} (rp : r > 0) (s : f ∈ submodule.span ℂ (set.range fourier)) : extendable f c r := begin
  apply @submodule.span_induction _ _ _ _ _ f _ (λ f, extendable f c r) s, {
    intros g gs, simp at gs, rcases gs with ⟨n,ng⟩, rw ←ng, exact fourier_extend' rp _,
  }, {
    existsi (λ _ : ℂ, (0 : ℂ)), exact { gh := harmonic_on.const _, b := by simp },
  }, {
    intros x y xe ye, rcases xe with ⟨x',xh,xb⟩, rcases ye with ⟨y',yh,yb⟩,
    existsi (λ z, x' z + y' z), exact { gh := xh.add yh, b := by simp [xb,yb] },
  }, {
    intros a x xe, rcases xe with ⟨x',xh,xb⟩,
    existsi (λ z : ℂ, a * x' z), exact { gh := xh.const_mul _, b := by simp [xb] },
  },
end

-- All continuous functions extend
lemma continuous_extend (f : C(circle, ℂ)) (c : ℂ) (rp : r > 0) : extendable f c r := begin
  set s := submodule.span ℂ (set.range fourier),
  have se : ∀ f, f ∈ s.carrier → extendable f c r := λ f fs, fourier_extend rp fs,
  have ce : ∀ f, f ∈ closure s.carrier → extendable f c r := is_closed.extendable se rp,
  have e : closure s.carrier = s.topological_closure.carrier := rfl,
  rw [e, span_fourier_closure_eq_top] at ce,
  apply ce, simp,
end

end harmonic_extension

-- Everything is "harmonic" on the null set
lemma harmonic_on.empty {f : ℂ → S} : harmonic_on f ∅ := {
  cont := continuous_on_empty _,
  mean := begin intros z s sp zs, have b : z ∈ ∅ := zs (metric.mem_closed_ball_self (by bound)), simp at b, finish end,
}

-- Everything is "harmonic" on singletons
lemma harmonic_on.singleton {f : ℂ → S} {c : ℂ} : harmonic_on f {c} := {
  cont := continuous_on_singleton _ _,
  mean := begin
    intros z s sp zs,
    have zc : z ∈ {c} := zs (metric.mem_closed_ball_self (by bound)),
    simp at zc, rw zc at zs,
    have sc : c + s ∈ {c} := zs (by simp [abs_of_pos sp]),
    simp [ne_of_gt sp] at sc, finish,
  end,
}

-- Continuous functions on the sphere extend to harmonic functions on the ball (complex case)
lemma continuous_to_harmonic_complex {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (fc : continuous_on f (sphere c r))
    : ∃ g : ℂ → ℂ, harmonic_on g (closed_ball c r) ∧ ∀ z, z ∈ sphere c r → f z = g z := begin
  by_cases r0 : r = 0, { existsi f, simp [r0, harmonic_on.singleton] },
  by_cases rn : r < 0, { existsi f, simp [metric.closed_ball_eq_empty.mpr rn, harmonic_on.empty] },
  simp at rn, have rp := lt_of_le_of_ne rn (ne.symm r0), clear r0 rn,
  generalize hf' : (λ z : circle, f (c + r*z)) = f',
  have fc' : continuous f', { rw ←hf', apply fc.comp_continuous, continuity, simp, bound },
  rcases continuous_extend ⟨f',fc'⟩ c rp with ⟨g,e⟩,
  existsi [g, e.gh],
  intros z zs,
  set z' := (↑r)⁻¹ * (z - c),
  have m : z' ∈ circle, { simp at ⊢ zs, simp [zs, abs_of_pos rp], field_simp [ne_of_gt rp] },
  have rr : c + r*(⟨_,m⟩ : circle) = z := rri rp _,
  nth_rewrite 1 ←rr, rw ←e.b ⟨_,m⟩, simp [←hf'], ring_nf, rw [mul_comm, rri rp],
end

-- Continuous functions on the sphere extend to harmonic functions on the ball (real case)
lemma continuous_to_harmonic_real {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (fc : continuous_on f (sphere c r))
    : ∃ g : ℂ → ℝ, harmonic_on g (closed_ball c r) ∧ ∀ z, z ∈ sphere c r → f z = g z := begin
  set f' := λ z, (f z : ℂ),
  have fc' : continuous_on f' (sphere c r) := complex.continuous_of_real.comp_continuous_on fc,
  rcases continuous_to_harmonic_complex fc' with ⟨g,gh,b⟩,
  existsi [λ z, (g z).re, gh.re],
  intros z zs, simp [←b z zs],
end

-- The submean property holds globally
theorem subharmonic_on.submean {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (fs : subharmonic_on f (closed_ball c r)) (rp : r > 0)
    : f c ≤ ⨍ t in Itau, f (circle_map c r t) := begin 
  rcases continuous_to_harmonic_real (fs.cont.mono metric.sphere_subset_closed_ball) with ⟨g,gh,fg⟩,
  generalize hd : (λ z, f z - g z) = d,
  have ds : subharmonic_on d (closed_ball c r), { rw ←hd, apply fs.add gh.neg.subharmonic_on },
  have dz : ∀ z, z ∈ sphere c r → d z = 0, { intros z zs, simp [←hd], rw fg z zs, simp },
  have dz' : ∀ᵐ t, t ∈ Itau → d (circle_map c r t) = 0, { apply ae_of_all, intros t ts, apply dz, simp, bound },
  rcases ds.maximum_principle (is_compact_closed_ball _ _) ⟨c, metric.mem_closed_ball_self (le_of_lt rp)⟩ with ⟨w,wf,wm⟩,
  rw frontier_closed_ball _ (ne_of_gt rp) at wf, swap, apply_instance,
  have fd : f = (λ z, d z + g z), { funext z, rw ←hd, simp },
  simp_rw [fd, set_average.add (ds.cont.integrable_on_sphere rp) (gh.cont.integrable_on_sphere rp)],
  simp [←gh.mean c r rp (subset_refl _)],
  simp [average_congr_on nice_volume.Itau dz'],
  rw ←dz w wf, apply wm (metric.mem_closed_ball_self (le_of_lt rp)),  
end

-- A continuous function is subharmonic if it is globally subharmonic.
-- This is useful since there are sometimes fewer technicalities in proving global subharmonicity.
lemma subharmonic_on_iff_submean {f : ℂ → ℝ} {s : set ℂ} (fc : continuous_on f s)
    : subharmonic_on f s ↔ ∀ (c : ℂ) (r : ℝ), r > 0 → closed_ball c r ⊆ s → f c ≤ ⨍ t in Itau, f (circle_map c r t) := begin
  constructor, {
    intros fs c r rp cs, exact (fs.mono cs).submean rp,
  }, {
    intro sm, exact {
      cont := fc,
      submean' := begin
        intros c ci,
        rcases metric.is_open_iff.mp is_open_interior c ci with ⟨r,rp,rs⟩,
        use [r,rp], intros t tp tr, apply sm c t tp,
        exact trans (metric.closed_ball_subset_ball tr) (trans rs interior_subset),
      end,
    },
  },
end

 -- The submean property holds for disks
lemma subharmonic_on.submean_disk {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (fs : subharmonic_on f (closed_ball c r)) (rp : r > 0)
    : f c ≤ ⨍ z in closed_ball c r, f z := begin
  rw [set_average_eq, complex.volume_closed_ball' (le_of_lt rp), fubini_ball fs.cont],
  have m : (λ s, (2*π*s) • f c) ≤ᵐ[volume.restrict (Ioc 0 r)] λ s, s • ∫ (t : ℝ) in set.Ioc 0 (2*π), f (circle_map c s t), {
    rw filter.eventually_le, rw ae_restrict_iff' measurable_set_Ioc, apply ae_of_all, intros s sr, simp at sr,
    have e := (fs.mono (metric.closed_ball_subset_closed_ball sr.2)).submean sr.1,
    rw smul_eq_mul, rw [set_average_eq, Itau_real_volume, smul_eq_mul] at e,
    generalize hi : ∫ t in Itau, f (circle_map c s t) = i, rw hi at e,
    calc 2*π*s * f c ≤ 2*π*s * ((2*π)⁻¹ * i) : by bound [real.pi_pos, sr.1]
    ... = s * (2*π * (2*π)⁻¹) * i : by ring_nf
    ... ≤ s * i : by field_simp [ne_of_gt real.two_pi_pos],
    apply_instance, apply_instance, apply_instance,
  },
  have im := integral_mono_ae _ _ m, {
    generalize hi : ∫ s in Ioc 0 r, s • ∫ t in Ioc 0 (2*π), f (circle_map c s t) = i, rw hi at im, clear hi m,
    simp [←interval_integral.integral_of_le (le_of_lt rp)] at im,
    ring_nf at im ⊢, rw smul_eq_mul,
    calc f c = (r^2 * π)⁻¹ * (f c * r^2 * π) : by { ring_nf, field_simp [ne_of_gt rp, ne_of_gt real.pi_pos], ring_nf }
    ... ≤ (r^2 * π)⁻¹ * i : by bound [real.pi_pos]
  }, {
    apply continuous.integrable_on_Ioc, continuity,
  }, {
    refine integrable_on.mono_set _ set.Ioc_subset_Icc_self,
    apply continuous_on.integrable_on_Icc, apply continuous_on.smul continuous_on_id, swap, apply_instance,
    simp_rw ←interval_integral.integral_of_le (le_of_lt real.two_pi_pos),
    refine continuous_on.interval_integral _ is_compact_Icc (le_of_lt real.two_pi_pos), simp [uncurry],
    refine fs.cont.comp (continuous.continuous_on (by continuity)) _,
    intros t ts, simp at ts, simp [complex.dist_eq, abs_of_nonneg ts.1.1, ts.2.1],
  },
end

-- The max of two subharmonic functions is subharmonic
lemma subharmonic_on.max {f g : ℂ → ℝ} {s : set ℂ} (fs : subharmonic_on f s) (gs : subharmonic_on g s)
    : subharmonic_on (λ z, max (f z) (g z)) s := begin
  simp_rw ←pair_max_eq,
  have pc : continuous_on (λ z, (f z, g z)) s := fs.cont.prod (gs.cont),
  have mc : continuous_on (λ z, pair_max (f z, g z)) s := continuous_max.comp_continuous_on pc,
  rw subharmonic_on_iff_submean mc,
  intros c r rp cs,
  have tf : is_finite_measure (volume.restrict Itau), { refine ⟨_⟩, simp, exact nice_volume.Itau.finite },
  have pi : integrable_on (λ t, (f (circle_map c r t), g (circle_map c r t))) Itau := (pc.mono cs).integrable_on_sphere rp,
  refine trans _ (@convex_on.map_average_le _ _ _ _ _ _ _ _ _ _ tf convex_on_pair_max
      continuous_max.continuous_on is_closed_univ _ (by simp) pi _), {
    simp_rw pair_max, apply max_le_max, {
      have e : ∀ p : ℝ × ℝ, p.fst = continuous_linear_map.fst ℝ ℝ ℝ p, { intro p, simp [continuous_linear_map.fst] },
      rw e, rw ←average_linear_comm pi, simp [continuous_linear_map.fst], exact (fs.mono cs).submean rp,
    }, {
      have e : ∀ p : ℝ × ℝ, p.snd = continuous_linear_map.snd ℝ ℝ ℝ p, { intro p, simp [continuous_linear_map.snd] },
      rw e, rw ←average_linear_comm pi, simp [continuous_linear_map.snd], exact (gs.mono cs).submean rp, apply_instance,
    },
  }, {
    simp, exact nice_volume.Itau.ne_zero,
  }, {
    have e : (pair_max ∘ λ t, (f (circle_map c r t), g (circle_map c r t)))
        = (λ t, (pair_max ∘ (λ z, (f z, g z))) (circle_map c r t)), { funext t, simp },
    rw e, refine (mc.mono cs).integrable_on_sphere rp,
  },
end

-- The maxima of a finite set of subharmonic functions is subharmonic
lemma subharmonic_on.range_max {f : ℕ → ℂ → ℝ} {s : set ℂ} (fs : ∀ n, subharmonic_on (f n) s) (n : ℕ)
    : subharmonic_on (λ z, range_max (λ k, f k z) n) s := begin
  induction n with n h, simp [fs 0], simp, exact h.max (fs (n+1)),
end

-- Continuous, monotonic limits of subharmonic functions are subharmonic
theorem subharmonic_on.monotone_lim {f : ℕ → ℂ → ℝ} {g : ℂ → ℝ} {s : set ℂ}
    (fs : ∀ n, subharmonic_on (f n) s) (fm : monotone f)
    (ft : ∀ z, z ∈ s → tendsto (λ n, f n z) at_top (𝓝 (g z))) (gc : continuous_on g s)
    : subharmonic_on g s := begin
  rw subharmonic_on_iff_submean gc, intros c r rp cs,
  have sm := λ n, ((fs n).mono cs).submean rp,
  have r0 : r ≥ 0 := le_of_lt rp,
  have cts : ∀ t, circle_map c r t ∈ s := λ _, cs (circle_map_mem_closed_ball _ r0 _),
  have mt : tendsto (λ n, ⨍ t in Itau, f n (circle_map c r t)) at_top (𝓝 (⨍ t in Itau, g (circle_map c r t))), {
    simp_rw set_average_eq, apply filter.tendsto.const_smul,
    set b' := λ z, |f 0 z| + |g z|,
    set b := λ t, b' (circle_map c r t),
    have bc' : continuous_on b' (closed_ball c r) := continuous_on.add ((fs 0).mono cs).cont.abs (gc.mono cs).abs,
    have fcc : ∀ n, continuous (λ t, f n (circle_map c r t)) :=
      λ n, ((fs n).cont.mono cs).comp_continuous (continuous_circle_map _ _) (λ t, circle_map_mem_closed_ball _ r0 _),
    apply tendsto_integral_of_dominated_convergence b, {
      intro n, exact (fcc n).ae_strongly_measurable,
    }, {
      exact bc'.integrable_on_sphere rp,
    }, {
      intro n, rw ae_restrict_iff' measurable_set_Itau, apply ae_of_all, intros t ts,
      generalize hz : circle_map c r t = z,
      have zs : z ∈ s, { rw ←hz, apply cts },
      rw real.norm_eq_abs, rw abs_le, constructor, {
        calc -b t ≤ -(|f 0 z| + 0) : by { rw ←hz, bound [neg_le_neg] }
        ... = -|f 0 z| : by simp
        ... ≤ f 0 z : neg_abs_le_self _
        ... ≤ f n z : fm (by simp) _,
      }, {
        have mn : monotone (λ n, f n z) := λ _ _ ab, fm ab z,
        calc f n z ≤ g z : @monotone.ge_of_tendsto _ _ _ _ _ _ (λ n, f n z) _ mn (ft z zs) n
        ... ≤ |g z| : by bound
        ... = 0 + |g z| : by ring
        ... ≤ b t : by { rw ←hz, bound },
      },
    }, {
      rw ae_restrict_iff' measurable_set_Itau, apply ae_of_all, intros t ts, exact ft _ (cts _),
    },
  },
  exact le_of_tendsto_of_tendsto' (ft c (cs (metric.mem_closed_ball_self r0))) mt sm,
end

-- max b (log ∥f z∥) is subharmonic for analytic f.
-- Some machinery is required to handle general Banach spaces: we rewrite ∥f z∥ as the limit
-- of norms along larger and larger finite subspaces, and use the fact that linear ∘ analytic
-- is analytic to reduce to the case of H = ℂ.
theorem analytic_on.max_log_norm_subharmonic_on {f : ℂ → H} {s : set ℂ}
    (fa : analytic_on ℂ f s) (b : ℝ) : subharmonic_on (λ z, max_log b ∥f z∥) s :=  begin
  have gc := fa.continuous_on.max_log_norm b,
  have ft := λ z (zs : z ∈ s), duals_lim_tendsto_max_log_norm b (f z),
  refine subharmonic_on.monotone_lim _ _ ft gc, {
    intro m, apply subharmonic_on.range_max, intro n, simp_rw complex.norm_eq_abs,
    exact ((duals n).comp_analytic_on fa).max_log_abs_subharmonic_on b,
  }, {
    intros a b ab z, simp, apply monotone.range_max ab,
  },
end

-- limsup -f = -liminf f
lemma limsup.neg {f : ℕ → ℝ} : at_top.limsup (λ n, f n) = -at_top.liminf (λ n, -f n) := begin
  rw filter.limsup_eq, rw filter.liminf_eq, rw real.Inf_def,
  have ns : -{a | ∀ᶠ n in at_top, a ≤ -f n} = {a | ∀ᶠ n in at_top, f n ≤ a}, { apply set.ext, simp },
  simp_rw ←ns, simp,
end

-- p is true for all ennreals if it is true for ⊤ and positive reals
lemma ennreal.induction {p : ennreal → Prop} (pi : p ⊤) (pf : ∀ (x : ℝ) (xp : 0 ≤ x), p (ennreal.of_real x)) : ∀ e, p e := begin
  rw ennreal.forall_ennreal, refine ⟨_,pi⟩, rw nnreal.forall, simpa [←ennreal.of_real_eq_coe_nnreal],
end

-- positive liminf lower bounds are equivalent over ℝ and ennreal
lemma le_liminf_real_to_ennreal {f : ℕ → ℝ} {c : ℝ} (fp : ∀ n, f n ≥ 0) (cp : c > 0)
    (h : c ≤ at_top.liminf f) : ennreal.of_real c ≤ at_top.liminf (λ n, ennreal.of_real (f n)) := begin
  rw filter.liminf_eq, refine le_Sup_iff.mpr _, intros b bs,
  induction b using ennreal.induction with b, simp,
  simp [upper_bounds] at bs, apply ennreal.of_real_le_of_real,
  rw filter.liminf_eq at h, rw real.le_Sup_iff at h, {
    simp at h, apply le_of_forall_small_le_add cp, intros e ep ec,
    rcases h (-e) (neg_lt_zero.mpr ep) with ⟨x,⟨n,xb⟩,cx⟩, specialize @bs (ennreal.of_real x) n,
    have xb : x ≤ b, {
      rw ←ennreal.of_real_le_of_real_iff b_xp, apply bs,
      intros a an, exact ennreal.of_real_le_of_real (xb a an),
    },
    simp at cx, rw add_comm at cx, exact trans (le_of_lt cx) (by bound),
  }, {
    contrapose h, rw real.Sup_of_not_bdd_above h, simp, exact cp,
  }, {
    contrapose h, rw set.not_nonempty_iff_eq_empty at h, rw h, simp, exact cp,
  }
end

lemma le_of_lt_imp_le {L : Type} [linear_order L] [densely_ordered L] {a b : L} (h : ∀ c, c < a → c ≤ b) : a ≤ b := begin
  contrapose h, simp at ⊢ h, rcases exists_between h with ⟨x,bx,xa⟩, exact ⟨x,xa,bx⟩,
end

-- Simple characterization of c ≤ liminf
lemma le_liminf.simple {L : Type} [complete_linear_order L] [densely_ordered L] {f : ℕ → L} {c : L}
    : c ≤ at_top.liminf f ↔ ∀ d, d < c → ∀ᶠ n in at_top, d ≤ f n := begin
  constructor, {
    intros h d dc, rw [filter.liminf_eq, le_Sup_iff, upper_bounds] at h, simp at h,
    specialize h d, contrapose h, simp [dc] at ⊢ h,
    intros a n an, rcases h n with ⟨m,nm,fmd⟩,
    exact trans (an m nm) (le_of_lt fmd),
  }, {
    intros h, rw [filter.liminf_eq, le_Sup_iff, upper_bounds], simp,
    intros a ah, apply le_of_lt_imp_le, intros d dc, 
    rcases filter.eventually_at_top.mp (h d dc) with ⟨n,hn⟩, exact ah n hn,
  },
end

lemma ennreal.of_real_neg_lt_of_real_neg {x y : ℝ} (xy : x < y) (xn : x < 0)
    : ennreal.of_real (-y) < ennreal.of_real (-x) := begin
  apply (ennreal.of_real_lt_of_real_iff _).mpr, simp [xy], simp [xn],
end

lemma metric.closed_ball_subset_ball' {M : Type} [pseudo_metric_space M] {x y : M} {r s : ℝ}
    (h : r + dist x y < s) : closed_ball x r ⊆ metric.ball y s := begin
  intros z zs, simp at zs ⊢,
  calc dist z y ≤ dist z x + dist x y : by bound
  ... ≤ r + dist x y : by bound
  ... < s : by bound,
end

-- Superharmonic ennreal functions
structure superharmonic_on (f : ℂ → ennreal) (s : set ℂ) : Prop :=
  (ae_measurable : ae_measurable f (volume.restrict s))
  (supmean : ∀ (c : ℂ) (r : ℝ), r > 0 → closed_ball c r ⊆ s →
               f c ≥ ennreal.of_real (π * r^2)⁻¹ * ∫⁻ z in closed_ball c r, f z)

-- ennreal.of_real (-f) is superharmonic if f is negative superharmonic
lemma subharmonic_on.neg {f : ℂ → ℝ} {s : set ℂ}
    (fs : subharmonic_on f s) (fn : ∀ z, z ∈ s → f z ≤ 0) (sm : measurable_set s)
    : superharmonic_on (λ z, ennreal.of_real (-f z)) s := {
  ae_measurable := begin
    apply ennreal.measurable_of_real.ae_measurable.comp_ae_measurable,
    apply fs.cont.neg.ae_measurable sm,
  end,
  supmean := begin
    intros c r rp cs,
    rw ←of_real_integral_eq_lintegral_of_real, {
      rw ←ennreal.of_real_mul, apply ennreal.of_real_le_of_real,
      rw [integral_neg, mul_neg], apply neg_le_neg,
      rw [←complex.volume_closed_ball' (le_of_lt rp), ←smul_eq_mul, ←set_average_eq],
      exact (fs.mono cs).submean_disk rp, bound [real.pi_pos],
    }, {
      exact (fs.mono cs).cont.neg.integrable_on_closed_ball,
    }, {
      rw filter.eventually_le, rw ae_restrict_iff' measurable_set_closed_ball, apply filter.eventually_of_forall,
      intros z zs, simp, exact fn z (cs zs), apply_instance,
    },
  end,
}

-- Hartogs's lemma from https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf, superharmonic ennreal case.
-- Superharmonic functions that are bounded below and liminf bounded pointwise are liminf bounded uniformly.
lemma superharmonic_on.hartogs {f : ℕ → ℂ → ennreal} {s k : set ℂ} {c : ennreal}
    (fs : ∀ n, superharmonic_on (f n) s) (fc : ∀ z, z ∈ s → at_top.liminf (λ n, f n z) ≥ c)
    (ck : is_compact k) (ks : k ⊆ interior s)
    : ∀ d, d < c → ∀ᶠ n in at_top, ∀ z, z ∈ k → f n z ≥ d := begin
  -- Prepare d and c
  intros d dc,
  by_cases dz : d = 0, { simp [dz] },
  have dp : d > 0 := pos_iff_ne_zero.mpr dz,
  have df : d ≠ ⊤ := ne_top_of_lt dc,
  have cp : c > 0 := trans dc dp,
  have drp : d.to_real > 0 := ennreal.to_real_pos dz df,
  -- Choose e ∈ (c,d) so that c → e is due to Fatou, and e → d is due to area bounding
  rcases exists_between dc with ⟨e,de,ec⟩,
  have ep : e > 0 := trans de dp,
  have ez : e ≠ 0 := pos_iff_ne_zero.mp ep,
  have ef : e ≠ ⊤ := ne_top_of_lt ec,
  have erp : e.to_real > 0 := ennreal.to_real_pos ez ef,
  -- Handle induction up from small balls
  apply is_compact.induction_on ck, {
    simp,
  }, {
    intros k0 k1 k01 h1,
    refine h1.mp (filter.eventually_of_forall _),
    exact λ n a1 z z0, a1 z (k01 z0),
  }, {
    intros k0 k1 h0 h1,
    refine (h0.and h1).mp(filter.eventually_of_forall _),
    intros n h z zs, cases zs, exact h.1 z zs, exact h.2 z zs,
  },
  -- Base case: Hartogs's lemma near a point.  We choose radii r1 < r2 within s, apply
  -- Fatou's lemma at r1, use monotonicity to bound by r2 integrals, and apply the submean
  -- property with radius r2 to get Hartogs's within radius r2-r1.
  intros z zs,
  rcases metric.is_open_iff.mp is_open_interior z (ks zs) with ⟨r,rp,rs⟩,
  generalize hr2 : r/2 = r2,  -- We'll use the submean property on disks of radius r2 < r
  generalize hr1 : r2 * real.sqrt (d.to_real / e.to_real) = r1,  -- We'll apply Fatou's lemma to a disk of radius r1 < r2 < r
  have dep : d.to_real / e.to_real > 0 := div_pos drp erp,
  have r2p : r2 > 0, { rw ←hr2, bound },
  have r1p : r1 > 0, { rw ←hr1, bound [real.sqrt_pos_of_pos] },
  have r12 : r1 < r2, {
    rw ←hr1, apply mul_lt_of_lt_one_right r2p, rw real.sqrt_lt (le_of_lt dep) zero_le_one, simp,
    apply (div_lt_one erp).mpr, exact (ennreal.to_real_lt_to_real df ef).mpr de,
  },
  have r1r : r1 < r, { apply trans r12, rw ←hr2, bound },
  have r1s : closed_ball z r1 ⊆ s := trans (metric.closed_ball_subset_ball r1r) (trans rs interior_subset),
  have rde : d = e * (ennreal.of_real (π*r1^2) * ennreal.of_real (π*r2^2)⁻¹), {
    rw [←ennreal.of_real_mul (by bound [real.pi_pos] : π*r1^2 ≥ 0), ←hr1, mul_pow, real.sq_sqrt (le_of_lt dep)],
    have smash : (π * (r2^2 * (d.to_real / e.to_real)) * (π * r2^2)⁻¹) = d.to_real / e.to_real, {
      calc (π * (r2^2 * (d.to_real / e.to_real)) * (π * r2^2)⁻¹)
          = (π * (r2^2 * (d.to_real / e.to_real)) * (π⁻¹ * (r2^2)⁻¹)) : by simp_rw [mul_inv]
      ... = d.to_real / e.to_real * (π * π⁻¹) * (r2^2 * (r2^2)⁻¹) : by ring_nf
      ... = d.to_real / e.to_real : by simp [mul_inv_cancel (ne_of_gt real.pi_pos),
                                             mul_inv_cancel (pow_ne_zero _ (ne_of_gt r2p))]
    },
    rw [smash, ennreal.of_real_div_of_pos erp, ennreal.of_real_to_real df, ennreal.of_real_to_real ef],
    rw ennreal.mul_div_cancel' ez ef,
  },
  have s12 : ∀ w, w ∈ (closed_ball z (r2-r1)) → closed_ball z r1 ⊆ closed_ball w r2, {
    intros w wr, apply metric.closed_ball_subset_closed_ball', simp [dist_comm] at wr, linarith,
  },
  have r2s : ∀ w, w ∈ closed_ball z (r2-r1) → closed_ball w r2 ⊆ s, {
    intros w ws, refine trans _ (trans rs interior_subset), simp [complex.dist_eq, ←hr2] at ⊢ ws,
    apply metric.closed_ball_subset_ball', simp [complex.dist_eq],
    calc r/2 + abs (w - z) ≤ r/2 + (r/2 - r1) : by bound 
    ... = r - r1 : by ring_nf
    ... < r : sub_lt_self _ r1p
  },
  -- Apply Fatou's lemma to closed_ball z (r/2)
  set fi := λ z, at_top.liminf (λ n, f n z),
  have fm : ∀ n, ae_measurable (f n) (volume.restrict (closed_ball z r1)) :=
    λ n, ae_measurable.mono_set r1s (fs n).ae_measurable,
  have fatou' := @lintegral_liminf_le' _ _ (volume.restrict (closed_ball z r1)) f fm,
  have im := @set_lintegral_mono_ae_measurable _ _ _ _ (closed_ball z r1) (λ _, c) _ ae_measurable_const
    (ae_measurable_liminf fm) measurable_set_closed_ball (λ _ zs, fc _ (r1s zs)),
  simp at im,
  have vec : e * volume (closed_ball z r1) < c * volume (closed_ball z r1), {
    have n := nice_volume.closed_ball z r1p, exact (ennreal.mul_lt_mul_right n.ne_zero n.ne_top).mpr ec,
  },
  have fatou := le_liminf.simple.mp (trans im fatou') (e * volume (closed_ball z r1)) vec,
  rw complex.volume_closed_ball (le_of_lt r1p) at fatou,
  clear fatou' im fc vec,
  -- Within radius r2-r1, Fatou's lemma implies local Hartogs's
  use [closed_ball z (r2-r1), mem_nhds_within_of_mem_nhds (metric.closed_ball_mem_nhds _ (by bound))],
  refine fatou.mp (filter.eventually_of_forall _),
  intros n fn w ws,
  calc d = e * (ennreal.of_real (π*r1^2) * ennreal.of_real (π*r2^2)⁻¹) : by rw rde
  ... = e * ennreal.of_real (π*r1^2) * ennreal.of_real (π*r2^2)⁻¹ : by rw mul_assoc
  ... ≤ (∫⁻ v in closed_ball z r1, f n v) * ennreal.of_real (π*r2^2)⁻¹ : ennreal.mul_right_mono fn
  ... ≤ (∫⁻ v in closed_ball w r2, f n v) * ennreal.of_real (π*r2^2)⁻¹ : ennreal.mul_right_mono (lintegral_mono_set (s12 w ws))
  ... = ennreal.of_real (π*r2^2)⁻¹ * ∫⁻ v in closed_ball w r2, f n v : by rw mul_comm
  ... ≤ f n w : (fs n).supmean w r2 r2p (r2s w ws),
end

-- Hartogs's lemma from https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf, real case.
-- Subharmonic functions that are bounded above and limsup bounded pointwise are limsup bounded uniformly.
-- I'm going to write out the definition of limsup ≤ c since ℝ not being complete makes it otherwise complicated.
lemma subharmonic_on.hartogs {f : ℕ → ℂ → ℝ} {s k : set ℂ} {c b : ℝ}
    (fs : ∀ n, subharmonic_on (f n) s) (fb : ∀ n z, z ∈ s → f n z ≤ b)
    (fc : ∀ z, z ∈ s → ∀ d, d > c → ∀ᶠ n in at_top, f n z ≤ d)
    (ck : is_compact k) (ks : k ⊆ interior s)
    : ∀ d, d > c → ∀ᶠ n in at_top, ∀ z, z ∈ k → f n z ≤ d := begin
  -- Deal with degenerate b ≤ c case
  by_cases bc : b ≤ c, {
    exact λ d dc, filter.eventually_of_forall (λ n z zk,
      trans (fb n z (trans ks interior_subset zk)) (trans bc (le_of_lt dc))),
  },
  simp at bc,
  -- Port subharmonic problem to superharmonic ennreal problem
  generalize hf' : (λ n z, f n z - b) = f',
  generalize hg : (λ n z, ennreal.of_real (-f' n z)) = g,
  have fs' : ∀ n, subharmonic_on (f' n) s, { rw ←hf', exact λ n, (fs n).add (harmonic_on.const _).subharmonic_on },
  have fn' : ∀ n z, z ∈ interior s → f' n z ≤ 0 := λ n z zs, by simp [←hf', fb n z (interior_subset zs)],
  have gs : ∀ n, superharmonic_on (g n) (interior s), {
    rw ←hg, exact λ n, ((fs' n).mono interior_subset).neg (fn' n) measurable_set_interior,
  },
  have gc : ∀ z, z ∈ interior s → at_top.liminf (λ n, g n z) ≥ ennreal.of_real (b - c), {
    intros z zs, specialize fc z (interior_subset zs), refine le_liminf.simple.mpr _,
    intros d dc,
    have df : d ≠ ⊤ := ne_top_of_lt dc,
    have dc' : b - d.to_real > c, {
      calc b - d.to_real > b - (ennreal.of_real (b - c)).to_real
          : sub_lt_sub_left ((ennreal.to_real_lt_to_real df ennreal.of_real_ne_top).mpr dc) b
      ... = b - (b - c) : by rw ennreal.to_real_of_real (le_of_lt (sub_pos.mpr bc))
      ... = c : by ring_nf,
    },
    refine (fc _ dc').mp (filter.eventually_of_forall _), intros n fb,
    calc g n z = ennreal.of_real (b - f n z) : by simp [←hg, ←hf']
    ... ≥ ennreal.of_real (b - (b - d.to_real)) : by bound [ennreal.of_real_le_of_real]
    ... = ennreal.of_real (d.to_real) : by ring_nf
    ... = d : by rw ennreal.of_real_to_real df,
  },
  -- Apply Hartogs's lemma to g
  have ks' := ks, rw ←interior_interior at ks',
  have h := superharmonic_on.hartogs gs gc ck ks',
  -- Finish up
  intros d dc,
  have dc' : ennreal.of_real (b - d) < ennreal.of_real (b - c), {
    rw ennreal.of_real_lt_of_real_iff (sub_pos.mpr bc), simpa,
  },
  refine (h _ dc').mp (filter.eventually_of_forall _),
  intros n hn z zk, specialize hn z zk,
  simp [←hg, ←hf'] at hn,
  rw ennreal.of_real_le_of_real_iff (sub_nonneg.mpr (fb n z (interior_subset (ks zk)))) at hn,
  rwa ←sub_le_sub_iff_left,
end