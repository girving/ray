-- Bottcher map throughout a superattracting basis (up to critical points)

import topology.extend_from
import topology.subset_properties

import connected
import continuation
import interval
import nonseparating
import postcritical
import potential

open complex (abs)
open filter (tendsto at_top eventually_of_forall)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball ball_mem_nhds mem_ball mem_closed_ball mem_ball_self)
open one_dimension
open set
open_locale topology
noncomputable theory

-- All information for a monic superattracting fixed point at the origin
variables {S : Type} [topological_space S] [compact_space S] [normal_space S] [complex_manifold I S]
variables {f : ℂ → S → S}
variables {c : ℂ}
variables {a z : S}
variables {d n : ℕ}
variables {p : ℝ}
variables {s : super f d a}
variables {r : ℂ → ℂ → S}

-- With bottcher_near and potential defined in potential.lean, we can now grow external rays that start
-- at (c,a) and extend out to the critical radius s.p c.  We first define what it means to grow rays
-- holomorphically, then prove we can continue the process out through a neighborhood of
-- {c} ×ˢ closed_ball 0 (s.p c).  ray.lean will then use grow to define a global s.ray map realizing
-- all of these rays.

-- A lot of the detailed work is related to working with holomorphic functions in neighborhoods of points
-- and sets without using the heavier machinery of germs, stalks, and sheaves.  However, I don't know that
-- machinery well, so I am sticking to the low tech approach for now.

-- The defining equation of rays, with c suppressed, is
--   bottcher (r z u) = u * bottcher z
-- The grow structure encapsulates the defining equation holding on a set of u's,
-- using only bottcher_near (as we will then define bottcher in terms of rays).  To do this,
-- we map forwards with f until we're inside s.near:
--   bottcher (r z u) = u * bottcher z
--   bottcher (r z u)^d^n = u^d^n * bottcher z^d^n
--   bottcher (f^[n] (r z u)) = u^d^n * bottcher (f^[n] z)

-- r is an inverse to s.bottcher_near on {x} ×ˢ ball 0 p 
structure eqn (s : super f d a) (n : ℕ) (r : ℂ → ℂ → S) (x : ℂ × ℂ) : Prop :=
  (holo : holomorphic_at II I (uncurry r) x)
  (near : (x.1, f x.1^[n] (r x.1 x.2)) ∈ s.near)
  (eqn : s.bottcher_near x.1 (f x.1^[n] (r x.1 x.2)) = x.2^d^n)
structure grow (s : super f d a) (c : ℂ) (p : ℝ) (n : ℕ) (r : ℂ → ℂ → S) : Prop :=
  (nonneg : 0 ≤ p)
  (zero : r c 0 = a)
  (start : ∀ᶠ x : ℂ × ℂ in 𝓝 (c,0), s.bottcher_near x.1 (r x.1 x.2) = x.2)
  (eqn : ∀ᶠ x : ℂ × ℂ in 𝓝ˢ ({c} ×ˢ closed_ball 0 p), eqn s n r x)

-- eqn using fewer ∀ᶠ
lemma eqn_near {s : super f d a} {n : ℕ} {r : ℂ → ℂ → S} {c x : ℂ}
    (holo : holomorphic_at II I (uncurry r) (c,x)) (mem : (c, f c^[n] (r c x)) ∈ s.near)
    (loc : ∀ᶠ y : ℂ × ℂ in 𝓝 (c,x), s.bottcher_near y.1 (f y.1^[n] (r y.1 y.2)) = y.2^d^n)
    : ∀ᶠ y in 𝓝 (c,x), eqn s n r y := begin
  have m : ∀ᶠ y : ℂ × ℂ in 𝓝 (c,x), (y.1, f y.1^[n] (r y.1 y.2)) ∈ s.near, {
    refine continuous_at.eventually_mem _ s.is_open_near mem,
    exact continuous_at_fst.prod (s.continuous_at_iter continuous_at_fst holo.continuous_at),
  },
  apply holo.eventually.mp, apply loc.mp, apply m.mp,
  apply eventually_of_forall, intros _ m l h, exact ⟨h,m,l⟩,
end

-- eqn is local
lemma eqn.congr {x : ℂ × ℂ} {r0 r1 : ℂ → ℂ → S} (e : eqn s n r0 x) (loc : uncurry r0 =ᶠ[𝓝 x] uncurry r1)
    : eqn s n r1 x := begin
  have s := loc.self, simp only [uncurry] at s,
  exact { holo := e.holo.congr loc, near := by simp only [←s, e.near], eqn := by simp only [←s, e.eqn] },
end

-- We can increase n
lemma eqn.mono {x : ℂ × ℂ} (e : eqn s n r x) {m : ℕ} (nm : n ≤ m) : eqn s m r x := {
  holo := e.holo, near := s.iter_stays_near' e.near nm, eqn := begin
    refine nat.le_induction e.eqn _ m nm, intros k nk h,
    simp only [h, function.iterate_succ_apply', s.bottcher_near_eqn (s.iter_stays_near' e.near nk),
      pow_succ', pow_mul],
  end,
}
lemma grow.mono (g : grow s c p n r) {m : ℕ} (nm : n ≤ m) : grow s c p m r := {
  nonneg := g.nonneg, zero := g.zero, start := g.start,
  eqn := g.eqn.mp (eventually_of_forall (λ x e, e.mono nm)),
}

-- Centers are in the domain
lemma mem_domain (c : ℂ) {p : ℝ} (p0 : 0 ≤ p) : (c,(0:ℂ)) ∈ ({c} ×ˢ closed_ball 0 p : set (ℂ × ℂ)) :=
  mk_mem_prod rfl (metric.mem_closed_ball_self p0)

-- The boundary is in the domain
lemma mem_domain_self {c x : ℂ} : (c,x) ∈ ({c} ×ˢ closed_ball 0 (complex.abs x) : set (ℂ × ℂ)) :=
  by simp only [mem_prod_eq, mem_singleton_iff, eq_self_iff_true, mem_closed_ball, complex.dist_eq, sub_zero,
    true_and]

-- Our domain is preconnected
lemma domain_preconnected (c : ℂ) (p : ℝ) : is_preconnected ({c} ×ˢ closed_ball 0 p : set (ℂ × ℂ)) :=
  is_preconnected_singleton.prod (convex_closed_ball _ _).is_preconnected

-- Our domain is monotonic in p
lemma domain_mono (c : ℂ) {p0 p1 : ℝ} (le : p0 ≤ p1)
    : ({c} ×ˢ closed_ball 0 p0 : set (ℂ × ℂ)) ⊆ {c} ×ˢ closed_ball 0 p1 :=
  prod_mono_right (metric.closed_ball_subset_closed_ball le)

-- Growing our closed domain a bit
lemma domain_open' {p : ℝ} {t : set ℂ} (sub : closed_ball (0:ℂ) p ⊆ t) (ot : is_open t)
    : ∃ q, p < q ∧ closed_ball 0 q ⊆ t := begin
  set u := complex.abs '' (closed_ball 0 (p+1) \ t),
  by_cases ne : u = ∅, { use [p+1, by linarith], rw [image_eq_empty, diff_eq_empty] at ne, exact ne },
  replace ne := nonempty_iff_ne_empty.mpr ne,
  have uc : is_closed u := (((is_compact_closed_ball _ _).diff ot).image complex.continuous_abs).is_closed,
  have up : ∀ x : ℝ, x ∈ u → p < x, {
    intros x m, rcases m with ⟨z,⟨mp,mt⟩,e⟩, rw ←e, contrapose mt, simp only [not_not, not_lt] at mt ⊢,
    apply sub, simp only [mem_closed_ball, complex.dist_eq, sub_zero, mt],
  },
  have ub : bdd_below u := ⟨p, λ _ m, le_of_lt (up _ m)⟩,
  have iu : Inf u ∈ u := is_closed.cInf_mem uc ne ub,
  rcases exists_between (up _ iu) with ⟨q,pq,qi⟩,
  use [min q (p+1), lt_min pq (by linarith)],
  intros z m, simp only [mem_closed_ball, complex.dist_eq, sub_zero, le_min_iff] at m,
  rcases m with ⟨zq,zp⟩, have zi := lt_of_le_of_lt zq qi,
  contrapose zi, simp only [not_lt], refine cInf_le ub (mem_image_of_mem _ _),
  simp only [mem_diff, mem_closed_ball, complex.dist_eq, sub_zero], use [zp, zi],
end
lemma domain_open {p : ℝ} {t : set (ℂ × ℂ)} (sub : {c} ×ˢ closed_ball 0 p ⊆ t) (o : is_open t)
    : ∃ q, p < q ∧ {c} ×ˢ closed_ball 0 q ⊆ t := begin
  rcases domain_open' _ (o.snd_preimage c) with ⟨q,pq,sub⟩, {
    use [q,pq], rintros ⟨e,z⟩ ⟨ec,m⟩, simp only [mem_singleton_iff] at ec,
    replace m := sub m, simp only [←ec, mem_set_of] at m, exact m,
  }, {
    intros z m, simp only [mem_set_of], apply sub, exact ⟨mem_singleton _,m⟩,
  },
end

-- grow is local
lemma grow.congr {r0 r1 : ℂ → ℂ → S} (g : grow s c p n r0)
    (e : uncurry r0 =ᶠ[𝓝ˢ ({c} ×ˢ closed_ball 0 p)] uncurry r1) : grow s c p n r1 := {
  nonneg := g.nonneg,
  zero := begin
    have e := e.self_set _ (mem_domain c g.nonneg),
    simp only [uncurry] at e, rw ←e, exact g.zero,
  end,
  start := begin
    refine g.start.mp ((e.filter_mono (nhds_le_nhds_set (mem_domain c g.nonneg))).mp _),
    refine eventually_of_forall (λ x e s, _),
    rw [uncurry] at e, simp only at e, rw ←e, exact s,
  end,
  eqn := begin
    have eqn := g.eqn, simp only [filter.eventually_eq, eventually_nhds_set_iff_forall] at eqn e ⊢,
    intros x m, refine (eqn x m).mp ((e x m).eventually_nhds.mp (eventually_of_forall (λ y e eqn, _))),
    exact eqn.congr e,
  end,
}

-- The equation satisfied by potential
lemma eqn.potential {x : ℂ × ℂ} (e : eqn s n r x) : s.potential x.1 (r x.1 x.2) = abs x.2 :=
  by simp only [s.potential_eq e.near, super.potential', e.eqn, complex.abs.map_pow, ←nat.cast_pow,
    real.pow_nat_rpow_nat_inv (complex.abs.nonneg _) (pow_ne_zero _ s.d0)]

-- eqn → bottcher_near is noncritical
lemma eqn_noncritical {x : ℂ × ℂ} (e : ∀ᶠ y in 𝓝 x, eqn s n r y) (x0 : x.2 ≠ 0)
    : mfderiv I I (s.bottcher_near_iter n x.1) (r x.1 x.2) ≠ 0 := begin
  rcases x with ⟨c,x⟩, contrapose x0, simp only [not_not] at ⊢ x0,
  replace x0 : mfderiv I I (λ y, s.bottcher_near_iter n c (r c y)) x = 0 :=
    by rw [mfderiv_comp x (s.bottcher_near_iter_holomorphic e.self.near).in2.mdifferentiable_at
      e.self.holo.in2.mdifferentiable_at, x0, continuous_linear_map.zero_comp],
  have loc : (λ y, s.bottcher_near_iter n c (r c y)) =ᶠ[𝓝 x] (λ y, y^d^n) :=
    ((continuous_at_const.prod continuous_at_id).eventually e).mp (eventually_of_forall (λ _ e, e.eqn)),
  rw [mfderiv_eq_fderiv, loc.fderiv_eq] at x0,
  have d := (differentiable_at_pow (d^n)).has_fderiv_at.has_deriv_at.deriv,
  rw [x0, continuous_linear_map.zero_apply, deriv_pow, mul_eq_zero, nat.cast_eq_zero, pow_eq_zero_iff',
    pow_eq_zero_iff'] at d,
  simp only [s.d0, false_and, false_or] at d, exact d.1,
end

-- p < 1
lemma grow.p1 (g : grow s c p n r) : p < 1 := begin
  by_contradiction p1, simp only [not_lt] at p1,
  have e := (g.eqn.filter_mono (@nhds_le_nhds_set _ _ _ (c,1) _)).self, {
    have lt := s.potential_lt_one ⟨_,e.near⟩,
    simp only [e.potential, complex.abs.map_one, lt_self_iff_false] at lt,
    exact lt,
  }, {
    simp only [p1, singleton_prod, mem_image, mem_closed_ball_zero_iff, complex.norm_eq_abs, prod.mk.inj_iff,
      eq_self_iff_true, true_and, exists_eq_right, complex.abs.map_one],
  },
end

lemma grow.holo (g : grow s c p n r) : holomorphic_on II I (uncurry r) ({c} ×ˢ closed_ball 0 p) :=
  λ x m, (g.eqn.filter_mono (nhds_le_nhds_set m)).self.holo

-- grow exists for small p
lemma super.grow_start (s : super f d a) (c : ℂ) [one_preimage s] : ∃ p r, 0 < p ∧ grow s c p 0 r := begin
  have ba := s.bottcher_near_holomorphic _ (s.mem_near c),
  have nc := s.bottcher_near_mfderiv_ne_zero c,
  rcases complex_inverse_fun ba nc with ⟨r,ra,rb,br⟩,
  rw s.bottcher_near_a at ra br,
  have rm : ∀ᶠ x : ℂ × ℂ in 𝓝 (c,0), (x.1, r x.1 x.2) ∈ s.near, {
    apply (continuous_at_fst.prod ra.continuous_at).eventually_mem s.is_open_near,
    have r0 := rb.self, simp only [s.bottcher_near_a] at r0,
    simp only [uncurry, r0], exact s.mem_near c,
  },
  rcases eventually_nhds_iff.mp (ra.eventually.and (br.and rm)) with ⟨t,h,o,m⟩,
  rcases metric.is_open_iff.mp o _ m with ⟨p,pp,sub⟩,
  replace h := λ (x : ℂ × ℂ) m, h x (sub m),
  have nb : ball (c,(0:ℂ)) p ∈ 𝓝ˢ ({c} ×ˢ closed_ball (0:ℂ) (p/2)), {
    rw [is_open_ball.mem_nhds_set, ←ball_prod_same], apply prod_mono,
    rw singleton_subset_iff, exact mem_ball_self pp,
    apply metric.closed_ball_subset_ball, exact half_lt_self pp,
  },
  use [p/2, r, half_pos pp], exact {
    nonneg := le_of_lt (half_pos pp),
    zero := begin convert rb.self, simp only [s.bottcher_near_a] end,
    start := filter.eventually_iff_exists_mem.mpr ⟨_, ball_mem_nhds _ pp, λ _ m, (h _ m).2.1⟩,
    eqn := filter.eventually_iff_exists_mem.mpr ⟨_, nb, λ _ m, {
      holo := (h _ m).1, 
      near := (h _ m).2.2,
      eqn := by simp only [function.iterate_zero_apply, pow_zero, pow_one, (h _ m).2.1],
    }⟩,
  },
end

-- We can grow p and vary c a bit
lemma grow.open (g : grow s c p n r) [one_preimage s] : ∃ p', p < p' ∧ ∀ᶠ c' in 𝓝 c, grow s c' p' n r := begin
  have e := g.eqn, simp only [nhds_set_prod is_compact_singleton (is_compact_closed_ball _ _)] at e,
  rcases filter.mem_prod_iff.mp e with ⟨a',an,b',bn,sub⟩,
  simp only [subset_set_of] at sub,
  rcases eventually_nhds_iff.mp (nhds_set_singleton.subst an) with ⟨a,aa,ao,am⟩,
  rcases eventually_nhds_set_iff.mp bn with ⟨b,bo,bp,bb⟩,
  rcases domain_open' bp bo with ⟨q,pq,qb⟩,
  use [q,pq],
  have m : ∀ᶠ c' in 𝓝 c, (c', r c' 0) ∈ s.near, {
    refine (continuous_at_id.prod _).eventually_mem s.is_open_near _,
    exact (g.eqn.filter_mono (nhds_le_nhds_set (mem_domain c g.nonneg))).self.holo.in1.continuous_at,
    simp only [id, g.zero, s.mem_near c],
  },
  apply m.mp,
  apply ((continuous_at_id.prod continuous_at_const).eventually g.start.eventually_nhds).mp,
  refine eventually_nhds_iff.mpr ⟨a, _, ao, am⟩,
  rintros c' am' start m, exact {
    nonneg := trans g.nonneg (le_of_lt pq),
    zero := begin
      have e := start.self, simp only [id, s.bottcher_near_eq_zero m] at e, exact e,
    end,
    start := start,
    eqn := begin
      refine eventually_nhds_set_iff.mpr ⟨a ×ˢ b, ao.prod bo, _, _⟩,
      exact prod_mono (singleton_subset_iff.mpr am') qb,
      rintros x ⟨cm,xm⟩, exact sub x ⟨aa _ cm, bb _ xm⟩,
    end,
  },
end

-- We can decrease p
lemma grow.anti (g : grow s c p n r) {q : ℝ} (nonneg : 0 ≤ q) (le : q ≤ p) : grow s c q n r := {
  nonneg := nonneg, zero := g.zero, start := g.start,
  eqn := g.eqn.filter_mono (nhds_set_mono (prod_mono_right (metric.closed_ball_subset_closed_ball le))),
}

-- Growing up to but not including potential p, with fixed n covering the boundary too
structure grow_open (s : super f d a) (c : ℂ) (p : ℝ) (r : ℂ → ℂ → S) : Prop := 
  (pos : 0 < p)
  (post : p < s.p c)
  (zero : r c 0 = a)
  (start : ∀ᶠ x : ℂ × ℂ in 𝓝 (c,0), s.bottcher_near x.1 (r x.1 x.2) = x.2)
  (eqn : ∀ᶠ x : ℂ × ℂ in 𝓝ˢ ({c} ×ˢ ball 0 p), eqn s (s.np c p) r x)

-- We can extend to any point in the closure
lemma grow_open.point (g : grow_open s c p r) [one_preimage s] {x : ℂ} (ax : abs x ≤ p)
    : ∃ r' : ℂ → ℂ → S, (∀ᶠ y : ℂ × ℂ in 𝓝 (c,x), eqn s (s.np c p) r' y) ∧
        (∃ᶠ y in 𝓝 x, y ∈ ball (0:ℂ) p ∧ r' c y = r c y) := begin
  -- If z = a, we can use r
  by_cases za : abs x = 0, {
    use r, simp only [complex.abs.eq_zero] at za, simp only [za, eq_self_iff_true, and_true], constructor,
    refine g.eqn.filter_mono (nhds_le_nhds_set _), exact mk_mem_prod rfl (mem_ball_self g.pos),
    exact (is_open_ball.eventually_mem (mem_ball_self g.pos)).frequently,
  },
  replace za := (ne.symm za).lt_of_le (complex.abs.nonneg _),
  -- Choose a value z = r' c x as a cluster point of r c at 𝓝[t] x
  set t := ball (0:ℂ) p,
  have xt : x ∈ closure t :=
    by simp only [closure_ball _ (ne_of_gt g.pos), mem_closed_ball, complex.dist_eq, sub_zero, ax],
  have ez : ∃ z : S, map_cluster_pt z (𝓝[t] x) (r c) :=
    @cluster_point_of_compact _ _ _ _ (@filter.map_ne_bot _ _ _ _ (mem_closure_iff_nhds_within_ne_bot.mp xt)),
  rcases ez with ⟨z,cp⟩,
  have pz : s.potential c z = abs x, {
    refine eq_of_nhds_ne_bot (cp.map (continuous.potential s).in2.continuous_at (filter.tendsto_map' _)),
    have e : ∀ y, y ∈ t → (s.potential c ∘ r c) y = abs y, {
      intros y m, simp only [function.comp], exact (g.eqn.self_set (c,y) ⟨rfl,m⟩).potential,
    },
    exact tendsto_nhds_within_congr (λ t m, (e t m).symm) complex.continuous_abs.continuous_within_at,
  },
  rcases s.nice_np c (lt_of_lt_of_le g.post s.p_le_one) z (trans (le_of_eq pz) ax) with ⟨m,nc⟩,
  replace nc := nc _ (le_refl _),
  generalize hn : s.np c p = n, rw hn at m nc,
  generalize hb : s.bottcher_near_iter n = b,
  have bz : b c z = x^d^n, {
    refine eq_of_nhds_ne_bot (cp.map _ (filter.tendsto_map' _)),
    rw ←hb, exact (s.bottcher_near_iter_holomorphic m).in2.continuous_at,
    have e : ∀ y, y ∈ t → (b c ∘ r c) y = y^d^n, {
      intros y m, simp only [function.comp, ←hb, ←hn], exact (g.eqn.self_set (c,y) ⟨rfl,m⟩).eqn,
    },
    exact tendsto_nhds_within_congr (λ t m, (e t m).symm) (continuous_pow _).continuous_within_at,
  },
  have post : postcritical s c z := lt_of_le_of_lt (trans (le_of_eq pz) ax) g.post,
  rw ←pz at za,
  -- Invert s.bottcher_near_iter at z
  have ba := s.bottcher_near_iter_holomorphic m,
  replace nc := s.bottcher_near_iter_mfderiv_ne_zero nc (post.not_precritical (ne_of_gt za)),
  rcases complex_inverse_fun ba nc with ⟨i,ia,ib,bi⟩,
  simp only [hb,bz] at ia bi ib,
  have pt : tendsto (λ p : ℂ × ℂ, (p.1, p.2^d^n)) (𝓝 (c,x)) (𝓝 (c,x^d^n)) :=
    continuous_at_fst.prod (continuous_at_snd.pow _),
  have ian : holomorphic_at II I (uncurry (λ e y : ℂ, i e (y^d^n))) (c,x) :=
    ia.curry_comp_of_eq holomorphic_at_fst holomorphic_at_snd.pow rfl,
  use λ e y, i e (y^d^n), constructor, {
    -- We satisfy eqn near x
    apply eqn_near ian,
    simp only [←bz, ib.self], exact m, 
    refine (pt.eventually bi).mp (eventually_of_forall _),
    intros _ bi, simp only [←hb] at bi, exact bi,
  }, {
    -- We frequently match r, by local injectivity of b
    have ne : map_cluster_pt (z,z) (𝓝[t] x) (λ y, (r c y, i c (y^d^n))), {
      apply cp.prod, refine filter.tendsto.mono_left _ nhds_within_le_nhds,
      convert ian.in2.continuous_at, simp only [←bz, ib.self],
    },
    have inj := (@filter.eventually.frequently _ _ ne _
      (filter.eventually.filter_mono inf_le_left (ba.in2.local_inj nc))).filter_mono inf_le_right,
    simp only [filter.frequently_map, frequently_nhds_within_iff] at inj,
    apply inj.mp,
    apply ((continuous_at_const.prod (continuous_at_pow _ _)).eventually bi).mp,
    apply eventually_of_forall, simp only [←hb, ←hn], rintros x bi ⟨inj,m⟩,
    refine ⟨m, (inj _).symm⟩, simp only [bi],
    exact (g.eqn.self_set ⟨c,x⟩ (mk_mem_prod rfl m)).eqn,
  },
end

-- eqn determines r locally, given equality at a point
lemma eqn_unique {r0 r1 : ℂ → ℂ → S} {x : ℂ × ℂ} [one_preimage s]
    (e0 : ∀ᶠ y in 𝓝 x, eqn s n r0 y) (e1 : ∀ᶠ y in 𝓝 x, eqn s n r1 y)
    (r01 : r0 x.1 x.2 = r1 x.1 x.2) (x0 : x.2 ≠ 0)
    : uncurry r0 =ᶠ[𝓝 x] uncurry r1 := begin
  have ba := s.bottcher_near_iter_holomorphic e0.self.near,
  have p0 : s.potential x.1 (r0 x.1 x.2) ≠ 0, {
    simp only [e0.self.potential, complex.abs.ne_zero_iff], exact x0,
  },
  have inj := ba.local_inj' (eqn_noncritical e0 x0), nth_rewrite 1 r01 at inj,
  have t : tendsto (λ x : ℂ × ℂ, (x.1, r0 x.1 x.2, r1 x.1 x.2)) (𝓝 x) (𝓝 (x.1, r0 x.1 x.2, r1 x.1 x.2)) :=
    continuous_at_fst.prod (e0.self.holo.continuous_at.prod e1.self.holo.continuous_at),
  apply (t.eventually inj).mp,
  refine e0.mp (e1.mp (eventually_of_forall (λ x e1 e0 inj, _))),
  specialize inj _,
  simp only [prod.fst],
  simp only [uncurry, prod.fst, prod.snd, super.bottcher_near_iter, e0.eqn, e1.eqn],
  simp only [uncurry, prod.fst, prod.snd, prod.ext_iff] at inj, exact inj,
end

-- Merge of eqn and start for use in holomorphic continuation
structure eqns (s : super f d a) (n : ℕ) (r0 r : ℂ → ℂ → S) (x : ℂ × ℂ) : Prop :=
  (eqn : ∀ᶠ y in 𝓝 x, eqn s n r y)
  (start : x.2 = 0 → uncurry r =ᶠ[𝓝 x] uncurry r0)

-- eqns basics
lemma eqns.holo {r0 r : ℂ → ℂ → S} {x : ℂ × ℂ} (e : eqns s n r0 r x) : holomorphic_at II I (uncurry r) x :=
  e.eqn.self.holo
lemma eqns.congr {x : ℂ × ℂ} {r0 r1 r2 : ℂ → ℂ → S} (e1 : eqns s n r0 r1 x)
    (loc : uncurry r1 =ᶠ[𝓝 x] uncurry r2) : eqns s n r0 r2 x := {
  eqn := e1.eqn.mp (loc.eventually_nhds.mp (eventually_of_forall (λ y loc e, e.congr loc))),
  start := λ x0, loc.symm.trans (e1.start x0),
}

-- eqns determines r once a point is fixed
lemma eqns_unique {r0 r1 r2 : ℂ → ℂ → S} {t : set (ℂ × ℂ)} (op : is_open t) (pre : is_preconnected t)
    (e1 : ∀ x, x ∈ t → eqns s n r0 r1 x) (e2 : ∀ x, x ∈ t → eqns s n r0 r2 x)
    (ne : ∃ x, x ∈ t ∧ uncurry r1 x = uncurry r2 x) [one_preimage s]
    : eq_on (uncurry r1) (uncurry r2) t := begin
  -- The set on which r0 = r1 is both relatively open and closed, so it's everything
  set u := {x | uncurry r1 x = uncurry r2 x},
  replace ne : (t ∩ u).nonempty := ne,
  have op : t ∩ u ⊆ interior u, {
    rintros ⟨c,x⟩ ⟨mt,mu⟩, rw mem_interior_iff_mem_nhds,
    by_cases x0 : x = 0, exact ((e1 _ mt).start x0).trans ((e2 _ mt).start x0).symm,
    exact eqn_unique (e1 _ mt).eqn (e2 _ mt).eqn mu x0,
  },
  have cl : t ∩ closure u ⊆ u, {
    rintros x ⟨mt,mu⟩, simp only [mem_set_of, mem_closure_iff_frequently, mem_inter_iff] at ⊢ mu,
    exact tendsto_nhds_unique_of_frequently_eq (e1 _ mt).holo.continuous_at (e2 _ mt).holo.continuous_at mu,
  },
  exact trans (pre.relative_clopen ne op cl) interior_subset,
end

-- r is unique in grow
lemma grow.unique {r0 r1 : ℂ → ℂ → S} {p0 p1 : ℝ} {n0 n1 : ℕ}
    (g0 : grow s c p0 n0 r0) (g1 : grow s c p1 n1 r1) (p01 : p0 ≤ p1)
    : uncurry r0 =ᶠ[𝓝ˢ ({c} ×ˢ closed_ball 0 p0)] uncurry r1 := begin
  -- Reduce to equality near (c,0)
  by_cases pos : p0 < 0, {
    simp only [metric.closed_ball_eq_empty.mpr pos, singleton_prod, image_empty, nhds_set_empty],
  },
  have m : (c,(0:ℂ)) ∈ {c} ×ˢ closed_ball (0:ℂ) p0 := mem_domain c (not_lt.mp pos),
  refine holomorphic_on.eq_of_locally_eq g0.holo (g1.holo.mono (domain_mono _ p01))
    (domain_preconnected _ _) ⟨(c,0),m,_⟩,
  -- Injectivity of s.bottcher_near gives us the rest
  have t : continuous_at (λ x : ℂ × ℂ, (x.1, r0 x.1 x.2, r1 x.1 x.2)) (c,0) :=
    continuous_at_fst.prod ((g0.eqn.filter_mono (nhds_le_nhds_set m)).self.holo.continuous_at.prod
      (g1.eqn.filter_mono (nhds_le_nhds_set (domain_mono c p01 m))).self.holo.continuous_at),
  simp only [continuous_at, g0.zero, g1.zero] at t,
  have inj := (s.bottcher_near_holomorphic _ (s.mem_near c)).local_inj' (s.bottcher_near_mfderiv_ne_zero c),
  refine ((t.eventually inj).and (g0.start.and g1.start)).mp (eventually_of_forall _),
  rintros ⟨e,y⟩ ⟨inj,s0,s1⟩, exact inj (s0.trans s1.symm),
end

lemma grow_open.grow (g : grow_open s c p r) [one_preimage s] : ∃ r', grow s c p (s.np c p) r' := begin
  set n := s.np c p,
  have b : base (λ f x, eqns s n r (curry f) x) ({c} ×ˢ ball (0:ℂ) p) (uncurry r) := {
    convex := (convex_singleton c).prod (convex_ball 0 p),
    compact := begin
      simp only [closure_prod_eq, closure_ball _ (ne_of_gt g.pos), closure_singleton],
      exact is_compact_singleton.prod (is_compact_closed_ball _ _),
    end,
    congr := λ r0 r1 x e0 r01, e0.congr (by simp only [function.uncurry_curry, r01]),
    start := begin
      simp only [filter.eventually_iff, mem_nhds_set_iff_forall], intros x m,
      exact (g.eqn.filter_mono (nhds_le_nhds_set m)).eventually_nhds.mp (eventually_of_forall (λ y e, {
        eqn := e, start := by simp only [function.curry_uncurry, filter.eventually_eq.refl, imp_true_iff],
      })),
    end,
    point := begin
      rintros ⟨c',x⟩ m,
      simp only [closure_prod_eq, closure_ball _ (ne_of_gt g.pos), closure_singleton, mem_prod_eq,
        mem_singleton_iff, mem_closed_ball, complex.dist_eq, sub_zero] at m,
      have ct : tendsto (λ x, (c,x)) (𝓝 x) (𝓝 (c,x)) := continuous_at_const.prod continuous_at_id,
      by_cases x0 : x ≠ 0, {
        rw m.1, rcases g.point m.2 with ⟨r',e,rr⟩,
        use uncurry r', constructor, {
          have t : continuous_at (λ y : ℂ × ℂ, y.2) (c,x) := continuous_at_snd,
          refine e.eventually_nhds.mp ((t.eventually_ne x0).mp (eventually_of_forall _)),
          intros y y0 e, exact { eqn := e, start := λ h, (y0 h).elim },
        }, {
          refine ct.frequently (rr.mp (eventually_of_forall _)), rintros x ⟨m,e⟩,
          simp only [mem_prod_eq, mem_singleton_iff, eq_self_iff_true, true_and], use [m,e],
        },
      }, {
        use uncurry r, simp only [not_not] at x0,
        simp only [m.1, x0, eq_self_iff_true, and_true] at ⊢ ct, constructor, {
          refine (g.eqn.filter_mono (nhds_le_nhds_set _)).eventually_nhds.mp (eventually_of_forall (λ y e, _)),
          use [rfl, mem_ball_self g.pos], simp only [function.curry_uncurry], exact {
            eqn := e, start := by simp only [filter.eventually_eq.refl, imp_true_iff, filter.eventually_true],
          },
        }, {
          refine ct.frequently (filter.eventually.frequently _),
          simp only [mem_prod_eq, mem_singleton_iff, eq_self_iff_true, true_and],
          exact is_open_ball.eventually_mem (mem_ball_self g.pos),
        },
      },
    end,
    unique := begin
      rintros r0 r1 t op pre e0 e1 r01,
      have u := eqns_unique op pre e0 e1 _,
      simp only [function.uncurry_curry] at u, exact u,
      simp only [function.uncurry_curry], exact r01,
    end,
  },
  have m0 : (c,(0:ℂ)) ∈ ({c} ×ˢ ball 0 p : set (ℂ × ℂ)) := 
    by simp only [mem_prod_eq, mem_singleton_iff, eq_self_iff_true, true_and, mem_ball_self g.pos],
  use curry b.f, exact {
    nonneg := le_of_lt g.pos,
    zero := begin convert g.zero, exact b.ff.self_set _ m0 end,
    start := begin
      refine g.start.mp ((b.ff.filter_mono (nhds_le_nhds_set m0)).mp (eventually_of_forall _)),
      intros x e b, simp only [curry, uncurry, prod.mk.eta] at e ⊢, rw e, exact b,
    end,
    eqn := begin
      have fp := b.fp, simp only [closure_prod_eq, closure_singleton, closure_ball _ (ne_of_gt g.pos)] at fp,
      exact fp.mp (eventually_of_forall (λ x e, e.eqn.self)),
    end,
  },
end

-- Piece together a sequence of r's into a single r
lemma join_r (s : super f d a) {p : ℕ → ℝ} {n : ℕ → ℕ} {ps : ℝ} {r : ℕ → ℂ → ℂ → S} [one_preimage s]
    (g : ∀ k, grow s c (p k) (n k) (r k)) (mono : monotone p) (tend : tendsto p at_top (𝓝 ps))
    : ∃ rs : ℂ → ℂ → S, ∀ k (x : ℂ), abs x < p k → uncurry rs =ᶠ[𝓝 (c,x)] uncurry (r k) := begin
  have above : ∀ k, p k ≤ ps := λ k, mono.ge_of_tendsto tend k,
  generalize hrs : (λ e x : ℂ, @dite _ (abs x < ps) (classical.dec _)
    (λ h, r (nat.find (tend.exists_lt h)) e x) (λ _, a)) = rs,
  use rs,
  -- rs is locally each r, via induction
  have loc : ∀ k, ∀ᶠ e in 𝓝 c, ∀ x : ℂ, abs x < p k → rs e x = r k e x, {
    intros k, induction k with k h, {
      apply eventually_of_forall, intros e x x0,
      have xe : ∃ k, abs x < p k := ⟨0,x0⟩,
      simp only [←hrs, lt_of_lt_of_le x0 (above _), dif_pos, (nat.find_eq_zero xe).mpr x0],
    }, {
      have eq := (g k).unique (g (k+1)) (mono (le_of_lt (nat.lt_succ_self _))),
      simp only [nhds_set_prod is_compact_singleton (is_compact_closed_ball _ _)] at eq,
      apply h.mp,
      rcases filter.mem_prod_iff.mp eq with ⟨u0,n0,u1,n1,eq⟩,
      simp only [nhds_set_singleton] at n0,
      refine filter.eventually_of_mem n0 (λ e eu h x xk1, _),
      by_cases xk0 : abs x < p k, {
        have m : (e,x) ∈ u0 ×ˢ u1, {
          refine mk_mem_prod eu (subset_of_nhds_set n1 _),
          simp only [mem_closed_ball, complex.dist_eq, sub_zero, le_of_lt xk0],
        },
        specialize eq m, simp only [mem_set_of, uncurry] at eq,
        rw [h _ xk0, eq],
      }, {
        have xe : ∃ k, abs x < p k := ⟨k+1,xk1⟩, 
        have n := (nat.find_eq_iff xe).mpr ⟨xk1,_⟩,
        simp only [←hrs, lt_of_lt_of_le xk1 (above _), dif_pos, n],
        intros j jk, simp only [not_lt, nat.lt_succ_iff] at jk xk0 ⊢, exact trans (mono jk) xk0,
      },
    },
  },
  -- rs is locally each r, final form
  intros k x xk,
  rcases eventually_nhds_iff.mp (loc k) with ⟨u,eq,uo,uc⟩,
  have m : u ×ˢ ball (0:ℂ) (p k) ∈ 𝓝 (c,x), {
    refine prod_mem_nhds (uo.mem_nhds uc) (is_open_ball.mem_nhds _),
    simp only [mem_ball, complex.dist_eq, sub_zero, xk],
  },
  apply filter.eventually_of_mem m, rintros ⟨e,y⟩ ⟨m0,m1⟩,
  simp only [mem_ball, complex.dist_eq, sub_zero] at m1,
  exact eq _ m0 _ m1,
end

-- Joined grows form a grow_open
lemma joined_grow_open (s : super f d a) {p : ℕ → ℝ} {ps : ℝ} {r : ℕ → ℂ → ℂ → S} {rs : ℂ → ℂ → S}
    [one_preimage s] (g : ∀ k, grow s c (p k) (s.np c ps) (r k))
    (tend : tendsto p at_top (𝓝 ps)) (post : ps < s.p c) (pos : 0 < ps)
    (loc : ∀ k (x : ℂ), abs x < p k → uncurry rs =ᶠ[𝓝 (c,x)] uncurry (r k))
    : grow_open s c ps rs := {
  pos := pos, post := post,
  zero := begin
    rcases tend.exists_lt pos with ⟨k,pos⟩,
    have e := (loc k 0 (by simp only [complex.abs.map_zero, pos])).self,
    simp only [uncurry] at e, simp only [e, (g k).zero],
  end,
  start := begin
    rcases tend.exists_lt pos with ⟨k,pos⟩,
    apply (g k).start.mp,
    apply (loc k 0 (by simp only [complex.abs.map_zero, pos])).mp,
    apply eventually_of_forall, rintros ⟨e,x⟩ loc start,
    simp only [uncurry] at loc ⊢ start, simp only [start, loc],
  end,
  eqn := begin
    apply mem_nhds_set_iff_forall.mpr, rintros ⟨c',x⟩ lt,
    simp only [mem_prod_eq, mem_singleton_iff, mem_ball, complex.dist_eq, sub_zero] at lt,
    simp only [lt.1, eq_self_iff_true, true_and, ←filter.eventually_iff] at ⊢ lt, clear c',
    rcases tend.exists_lt lt with ⟨k,ltp⟩,
    have m : (c,x) ∈ {c} ×ˢ closed_ball (0:ℂ) (p k), {
      simp only [mem_prod_eq, mem_singleton_iff, metric.mem_closed_ball, eq_self_iff_true, true_and,
        complex.dist_eq, sub_zero, le_of_lt ltp],
    },
    have lt' : ∀ᶠ y : ℂ × ℂ in 𝓝 (c,x), abs y.2 < ps :=
      (complex.continuous_abs.continuous_at.comp continuous_at_snd).eventually_lt continuous_at_const lt,
    apply ((g k).eqn.filter_mono (nhds_le_nhds_set m)).mp,
    apply (loc _ _ ltp).eventually_nhds.mp,
    apply lt'.mp,
    apply eventually_of_forall, rintros ⟨e,y⟩ lt' loc eq,
    exact eq.congr (filter.eventually_eq.symm loc),
  end,
}
 
-- We can grow up to s.p c
lemma super.grow (s : super f d a) [one_preimage s]
    : ∀ p, 0 ≤ p → p < s.p c → ∃ r, grow s c p (s.np c p) r := begin
  set t : set ℝ := {p | 0 ≤ p ∧ ∀ q, 0 ≤ q → q ≤ p → ∃ r, grow s c q (s.np c q) r},
  have self : ∀ {p}, p ∈ t → ∃ r, grow s c p (s.np c p) r := λ p m, m.2 _ m.1 (le_refl _),
  have t1 : ∀ p : ℝ, p ∈ t → p < 1, { rintros p m, rcases self m with ⟨r,g⟩, exact g.p1 },
  have above : bdd_above t := bdd_above_def.mpr ⟨1, λ p m, le_of_lt (t1 p m)⟩,
  rcases s.grow_start c with ⟨p0,r0,pos0,g0⟩,
  have start : p0 ∈ t, { use g0.nonneg, intros q q0 qp, use r0, exact (g0.anti q0 qp).mono (nat.zero_le _) },
  have ne : t.nonempty := ⟨p0, start⟩,
  have pos : 0 < Sup t := lt_cSup_of_lt above start pos0,
  by_cases missing : Sup t ∈ t, {
    -- Contradict by growing a bit beyond Sup t
    rcases self missing with ⟨r,g⟩, rcases g.open with ⟨p,sp,g'⟩,
    suffices m : p ∈ t, linarith [le_cSup above m],
    use g'.self.nonneg,
    intros q q0 qp, by_cases le : q ≤ Sup t, exact missing.2 _ q0 le,
    use r, simp only [not_le] at le,
    exact (g'.self.anti q0 qp).mono (s.np_mono c (le_of_lt le) (lt_of_le_of_lt qp g'.self.p1)),
  },
  by_cases post : Sup t < s.p c, {
    exfalso, apply missing, use le_of_lt pos, intros q q0 le,
    -- q < Sup t is trivial
    by_cases lt : q < Sup t, {
      rcases exists_lt_of_lt_cSup ne lt with ⟨q',⟨q1,m⟩,qq⟩,
      exact m _ q0 (le_of_lt qq),
    },
    have eq := le_antisymm le (not_lt.mp lt), rw eq, clear eq lt le q0 q,
    -- Piece together a single r that works < Sup t, then close to Sup t
    rcases exists_seq_tendsto_Sup ne above with ⟨p,mono,tend,sub⟩,
    simp only [set.range_subset_iff, mem_set_of] at sub,
    set pr := λ k, classical.some (self (sub k)),
    have pg : ∀ k, grow s c (p k) (s.np c (Sup t)) (pr k) := λ k, 
      (classical.some_spec (self (sub k))).mono (s.np_mono c (le_cSup above (sub k))
        (lt_of_lt_of_le post s.p_le_one)),
    rcases join_r s pg mono tend with ⟨r,loc⟩,
    exact (joined_grow_open s pg tend post pos loc).grow,
  },
  -- Finish!
  simp only [not_lt] at post,
  intros p p0 lt,
  rcases exists_lt_of_lt_cSup ne (lt_of_lt_of_le lt post) with ⟨q,m,pq⟩,
  exact m.2 _ p0 (le_of_lt pq),
end

-- There is a single r that achieves all grows for all c and p < s.p c
lemma super.has_ray (s : super f d a) [one_preimage s]
    : ∃ r : ℂ → ℂ → S, ∀ c p, 0 ≤ p → p < s.p c → grow s c p (s.np c p) r := begin
  generalize hr : (λ {c p} (h : 0 ≤ p ∧ p < s.p c), classical.some (s.grow _ h.1 h.2)) = r,
  have g : ∀ {c p} (h : 0 ≤ p ∧ p < s.p c), grow s c p (s.np c p) (r h), {
    intros c p h, rw ←hr, exact classical.some_spec _,
  },
  clear hr,
  generalize hray : (λ c x : ℂ, @dite _ (abs x < s.p c) (classical.dec _)
    (λ h, r ⟨complex.abs.nonneg _,h⟩ c x) (λ h, a)) = ray,
  have loc : ∀ {c p} (h : 0 ≤ p ∧ p < s.p c), uncurry ray =ᶠ[𝓝ˢ ({c} ×ˢ closed_ball 0 p)] uncurry (r h), {
    intros c p h,
    rcases (g h).open with ⟨q',pq',gh⟩,
    rcases exists_between (lt_min pq' h.2) with ⟨q,pq,qlo⟩,
    rcases lt_min_iff.mp qlo with ⟨qq',qs⟩,
    have q0 : 0 ≤ q := trans h.1 (le_of_lt pq), 
    replace gh := gh.mp (eventually_of_forall (λ c' g, g.anti q0 (le_of_lt qq'))),
    clear qlo qq' pq' q',
    rcases eventually_nhds_iff.mp gh with ⟨t0,gh,ot0,ct0⟩,
    rcases eventually_nhds_iff.mp (s.lower_semicontinuous_p _ _ qs) with ⟨t1,lo,ot1,ct1⟩,
    refine eventually_nhds_set_iff.mpr ⟨(t0 ∩ t1) ×ˢ ball 0 q, (ot0.inter ot1).prod is_open_ball, _, _⟩,
    exact prod_mono (singleton_subset_iff.mpr ⟨ct0,ct1⟩) (metric.closed_ball_subset_ball pq),
    rintros ⟨e,x⟩ ⟨⟨et0,et1⟩,xq⟩, simp only [uncurry] at et0 et1 xq ⊢,
    simp only [mem_ball, complex.dist_eq, sub_zero] at xq, 
    have hx : 0 ≤ abs x ∧ abs x < s.p e := ⟨complex.abs.nonneg _, trans xq (lo _ et1)⟩,
    simp only [←hray, dif_pos hx.2],
    refine ((g hx).unique (gh _ et0) (le_of_lt xq)).self_set ⟨e,x⟩ ⟨rfl,_⟩,
    simp only [mem_closed_ball, complex.dist_eq, sub_zero],
  },
  use ray, intros c p p0 h,
  exact (g ⟨p0,h⟩).congr (loc ⟨p0,h⟩).symm,
end