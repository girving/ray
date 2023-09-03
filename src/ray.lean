-- The external ray map

import grow

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
variables {c x : ℂ}
variables {a z : S}
variables {d n : ℕ}
variables {s : super f d a}
variables {y : ℂ × ℂ}

-- The definition of external rays!
def super.ray (s : super f d a) [one_preimage s] : ℂ → ℂ → S := classical.some s.has_ray

-- The domain of s.ray
def super.ext (s : super f d a) : set (ℂ × ℂ) := {y : ℂ × ℂ | abs y.2 < s.p y.1}

-- The c-slice of s.ext is as expected
lemma super.ext_slice (s : super f d a) (c : ℂ) : {x | (c,x) ∈ s.ext} = ball (0:ℂ) (s.p c) := begin
  apply set.ext, intros x, simp only [super.ext, mem_ball, mem_set_of, complex.dist_eq, sub_zero],
end

-- s.ext is open
lemma super.is_open_ext (s : super f d a) [one_preimage s] : is_open s.ext := begin
  set f := λ y : ℂ × ℂ, s.p y.1 - abs y.2,    
  have fc : lower_semicontinuous f := (s.lower_semicontinuous_p.comp continuous_fst).add
    (complex.continuous_abs.comp continuous_snd).neg.lower_semicontinuous,
  have e : s.ext = f ⁻¹' Ioi 0 :=
    set.ext (λ _, by simp only [super.ext, mem_set_of, mem_preimage, mem_Ioi, sub_pos]),
  rw e, exact fc.is_open_preimage _,
end

-- (c,0) ∈ s.ext
lemma super.mem_ext (s : super f d a) [one_preimage s] (c : ℂ) : (c,(0:ℂ)) ∈ s.ext :=
  by simp only [super.ext, mem_set_of, complex.abs.map_zero, s.p_pos c]

-- s.ext and slices of s.ext are connected
lemma super.ext_slice_connected (s : super f d a) [one_preimage s] (c : ℂ)
    : is_connected {x | (c,x) ∈ s.ext} := begin
  rw s.ext_slice c, use [0, mem_ball_self (s.p_pos c), (convex_ball (0:ℂ) (s.p c)).is_preconnected],
end
lemma super.ext_connected (s : super f d a) [one_preimage s] : is_connected s.ext := begin
  use [(0,0), s.mem_ext 0], refine is_preconnected_of_forall (0,0) _, rintros ⟨c,x⟩ m,
  use (λ x, (c,x)) '' {x | (c,x) ∈ s.ext} ∪ (univ ×ˢ {0}),
  simp only [mem_image, mem_union, union_subset_iff, mem_set_of, mem_prod_eq, mem_univ, true_and,
    mem_singleton_iff, eq_self_iff_true, or_true],
  refine ⟨⟨_,_⟩,_,_⟩,
  intros y n, simp only [mem_image, mem_set_of] at n, rcases n with ⟨x,m,e⟩, rw e at m, exact m,
  rintros ⟨c,x⟩ m, simp only [mem_prod_eq, mem_singleton_iff] at m, rw m.2, exact s.mem_ext c,
  use [x,m],
  refine is_preconnected.union (c,0) _ _ _ _,
  use [0, s.mem_ext c], exact mk_mem_prod (mem_univ _) rfl,
  exact is_preconnected.image (s.ext_slice_connected c).is_preconnected _ (continuous.prod.mk _).continuous_on,
  exact is_preconnected_univ.prod is_preconnected_singleton,
end

-- s.ray satisfies grow
def super.ray_spec (s : super f d a) [one_preimage s]
    : ∀ {c p}, 0 ≤ p → p < s.p c → grow s c p (s.np c p) s.ray := classical.some_spec s.has_ray
def super.ray_eqn_self (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : eqn s (s.np c (abs x)) s.ray (c,x) :=
  (s.ray_spec (complex.abs.nonneg _) post).eqn.self_set _ mem_domain_self

-- s.ray is holomorphic up to the critical value
lemma super.ray_holomorphic (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : holomorphic_at II I (uncurry s.ray) (c,x) := (s.ray_eqn_self post).holo
lemma super.ray_holomorphic_slice (s : super f d a) [one_preimage s] (c : ℂ)
    : holomorphic_on I I (s.ray c) {x | (c,x) ∈ s.ext} := λ x m, (s.ray_holomorphic m).in2
lemma super.ray_holomorphic_on (s : super f d a) [one_preimage s]
    : holomorphic_on II I (uncurry s.ray) s.ext := begin
  rintros ⟨c,x⟩ m, exact s.ray_holomorphic m,
end

-- s.ray c 0 = a
lemma super.ray_zero (s : super f d a) [one_preimage s] (c : ℂ) : s.ray c 0 = a :=
  (s.ray_spec (le_refl _) (s.p_pos c)).zero

-- s.ray maps into s.basin
lemma super.ray_basin (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : (c, s.ray c x) ∈ s.basin := ⟨_, (s.ray_eqn_self post).near⟩

-- s.ray maps into n with the expected n
lemma super.ray_near (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : (c, f c^[s.np c (abs x)] (s.ray c x)) ∈ s.near := (s.ray_eqn_self post).near

-- s.ray inverts s.bottcher_near near 0
lemma super.ray_eqn_zero (s : super f d a) [one_preimage s] (c : ℂ)
    : ∀ᶠ y : ℂ × ℂ in 𝓝 (c,0), s.bottcher_near y.1 (s.ray y.1 y.2) = y.2 :=
  (s.ray_spec (le_refl _) (s.p_pos c)).start

-- s.ray inverts s.bottcher_near after iteration
lemma super.ray_eqn_iter (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : ∀ᶠ y : ℂ × ℂ in 𝓝 (c,x),
        s.bottcher_near_iter (s.np c (abs x)) y.1 (s.ray y.1 y.2) = y.2^d^(s.np c (abs x)) :=
  ((s.ray_spec (complex.abs.nonneg _) post).eqn.filter_mono (nhds_le_nhds_set mem_domain_self)).mp
    (eventually_of_forall (λ y e, e.eqn))

-- s.ray sends absolute value to potential
lemma super.ray_potential (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : s.potential c (s.ray c x) = abs x := (s.ray_eqn_self post).potential

-- s.ray maps into s.post
lemma super.ray_post (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : (c, s.ray c x) ∈ s.post := begin
  simp only [super.post, postcritical, mem_set_of, s.ray_potential post], exact post,
end

-- s.ray is noncritical at 0
lemma super.ray_noncritical_zero (s : super f d a) [one_preimage s] (c : ℂ)
    : mfderiv I I (s.ray c) 0 ≠ 0 := begin
  have h : mfderiv I I (s.bottcher_near c ∘ s.ray c) 0 ≠ 0, {
    have e : (s.bottcher_near c ∘ s.ray c) =ᶠ[𝓝 0] id :=
      (continuous_at_const.prod continuous_at_id).eventually (s.ray_eqn_zero c),
    rw e.mfderiv_eq, exact id_mderiv_ne_zero,
  },
  contrapose h, simp only [not_not] at h ⊢,
  have hb : mdifferentiable_at I I (s.bottcher_near c) (s.ray c 0), {
    rw s.ray_zero, exact (s.bottcher_near_holomorphic _ (s.mem_near c)).in2.mdifferentiable_at,
  },
  have hr : mdifferentiable_at I I (s.ray c) 0 := (s.ray_holomorphic (s.mem_ext c)).in2.mdifferentiable_at,
  rw [mfderiv_comp 0 hb hr, h, continuous_linear_map.comp_zero],
end

-- s.ray is noncritical
lemma super.ray_noncritical (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : mfderiv I I (s.ray c) x ≠ 0 := begin
  by_cases x0 : x = 0, rw x0, exact s.ray_noncritical_zero c,
  set n := s.np c (abs x),
  have h : mfderiv I I (s.bottcher_near_iter n c ∘ s.ray c) x ≠ 0, {
    have e : (s.bottcher_near_iter n c ∘ s.ray c) =ᶠ[𝓝 x] (λ x, x^d^n) :=
      (continuous_at_const.prod continuous_at_id).eventually (s.ray_eqn_iter post),
    rw e.mfderiv_eq, contrapose x0, simp only [not_not] at x0 ⊢,
    rw [mfderiv_eq_fderiv] at x0,
    have d := (differentiable_at_pow (d^n)).has_fderiv_at.has_deriv_at.deriv,
    rw [x0, continuous_linear_map.zero_apply, deriv_pow, mul_eq_zero, nat.cast_eq_zero, pow_eq_zero_iff',
      pow_eq_zero_iff'] at d,
    simp only [s.d0, false_and, false_or] at d, exact d.1,
  },
  simp only [mfderiv_comp x (s.bottcher_near_iter_holomorphic (s.ray_near post)).in2.mdifferentiable_at
      (s.ray_holomorphic post).in2.mdifferentiable_at, ne.def, mderiv_comp_eq_zero_iff, not_or_distrib] at h,
  exact h.2,
end

-- s.ray is nontrivial
lemma super.ray_nontrivial (s : super f d a) [one_preimage s] (post : (c,x) ∈ s.ext)
    : nontrivial_holomorphic_at (s.ray c) x :=
  (nontrivial_holomorphic_at_of_mfderiv_ne_zero (s.ray_holomorphic (s.mem_ext c)).in2
    (s.ray_noncritical_zero c)).on_preconnected (s.ray_holomorphic_slice c) (s.mem_ext c)
    (s.is_open_ext.snd_preimage c) (s.ext_slice_connected c).is_preconnected _ post

-- s.ray is injective
lemma super.ray_inj (s : super f d a) [one_preimage s] {x0 x1 : ℂ}
    : (c,x0) ∈ s.ext → (c,x1) ∈ s.ext → s.ray c x0 = s.ray c x1 → x0 = x1 := begin
  -- Preliminaries
  intros p0 p1 e,
  have ax : abs x0 = abs x1 := by simp only [←s.ray_potential p0, ←s.ray_potential p1, e],
  by_cases x00 : x0 = 0, {
    simp only [x00, complex.abs.map_zero] at ⊢ ax, exact (complex.abs.eq_zero.mp ax.symm).symm,
  },
  have tc : ∀ (x : ℂ) t, continuous_at (λ t : ℝ, ↑t*x) t :=
    λ x t, complex.continuous_of_real.continuous_at.mul continuous_at_const,
  have pt : ∀ {x : ℂ} {t : ℝ}, (c,x) ∈ s.ext → t ∈ Ioc (0:ℝ) 1 → (c,↑t*x) ∈ s.ext, {
    intros x t p m,
    simp only [super.ext, mem_set_of, complex.abs.map_mul, complex.abs_of_real, abs_of_pos m.1] at ⊢ p,
    exact lt_of_le_of_lt (mul_le_of_le_one_left (complex.abs.nonneg _) m.2) p,
  },
  -- It suffices to show that the set of t's where the x0 and x1 rays match is relatively clopen in Ioc 0 1
  set u : set ℝ := {t : ℝ | s.ray c (t*x0) = s.ray c (t*x1)},
  suffices h : Ioc (0 : ℝ) 1 ⊆ interior u, {
    replace h := trans h interior_subset,
    replace tc := (tc x0 0).prod_mk (tc x1 0), simp only [←nhds_prod_eq] at tc,
    simp only [continuous_at, complex.of_real_zero, zero_mul] at tc,
    have inj := tc.eventually ((s.ray_holomorphic (s.mem_ext c)).in2.local_inj (s.ray_noncritical_zero c)),
    rcases metric.eventually_nhds_iff.mp inj with ⟨r,rp,inj⟩,
    simp only [real.dist_eq, sub_zero] at inj,
    set t := min 1 (r/2),
    have t0 : 0 < t := lt_min zero_lt_one (half_pos rp),
    have t01 : t ∈ Ioc (0 : ℝ) 1 := mem_Ioc.mpr ⟨t0, min_le_left _ _⟩,
    specialize @inj t (by simp only [abs_of_pos t0, min_lt_of_right_lt (half_lt_self rp)]) (h t01),
    exact mul_left_cancel₀ (complex.of_real_ne_zero.mpr (ne_of_gt t0)) inj,
  },
  refine is_preconnected_Ioc.relative_clopen _ _ _, {
    use [1, right_mem_Ioc.mpr zero_lt_one],
    simp only [mem_set_of, complex.of_real_one, one_mul, e],
  }, {
    rintros t ⟨m,e⟩,
    simp only [mem_set_of, mem_interior_iff_mem_nhds, ←filter.eventually_iff] at e ⊢,
    generalize hn : s.np c (abs (↑t*x0)) = n,
    have t0 : (t : ℂ) ≠ 0 := complex.of_real_ne_zero.mpr (ne_of_gt m.1),
    have pe : abs (↑t*x0) = abs (↑t*x1) :=
      by simp only [←s.ray_potential (pt p0 m), ←s.ray_potential (pt p1 m), e],
    have e0 := ((s.ray_spec (complex.abs.nonneg _) (pt p0 m)).eqn.filter_mono
      (nhds_le_nhds_set mem_domain_self)),
    have e1 := ((s.ray_spec (complex.abs.nonneg _) (pt p1 m)).eqn.filter_mono
      (nhds_le_nhds_set mem_domain_self)),
    simp only [←pe, hn] at e0 e1,
    have de : (↑t*x0)^d^n = (↑t*x1)^d^n, {
      have e0 := e0.self.eqn, have e1 := e1.self.eqn, simp only [hn, ←pe, ←e] at e0 e1, exact e0.symm.trans e1,
    },
    simp only [mul_pow] at de,
    replace de := mul_left_cancel₀ (pow_ne_zero _ t0) de,
    generalize hr : (λ e x, s.ray e (x1/x0*x)) = r,
    have xe : x1/x0*(↑t*x0) = ↑t*x1 := by rw [←mul_assoc, mul_comm _ ↑t, mul_assoc, div_mul_cancel _ x00],
    have er : ∀ᶠ y in 𝓝 (c,↑t*x0), eqn s n r y, {
      rw ←hr, apply eqn_near,
      exact (s.ray_holomorphic (pt p1 m)).curry_comp_of_eq holomorphic_at_fst
        (holomorphic_at_const.mul holomorphic_at_snd) (by simp only [xe]),
      rw xe, exact e1.self.near,
      have xc : continuous_at (λ y : ℂ × ℂ, (y.1,x1/x0*y.2)) (c,↑t*x0) :=
        continuous_at_fst.prod (continuous_at_const.mul continuous_at_snd),
      simp only [continuous_at] at xc, rw [←mul_assoc, mul_comm _ ↑t, mul_assoc, div_mul_cancel _ x00] at xc,
      refine (xc.eventually e1).mp (eventually_of_forall _), rintros ⟨e,x⟩ e1,
      exact trans e1.eqn (by simp only [mul_pow, div_pow, ←de, div_self (pow_ne_zero _ x00), one_mul]),
    },
    refine ((continuous_at_const.prod (complex.continuous_of_real.continuous_at.mul
      continuous_at_const)).eventually (eqn_unique e0 er _ (mul_ne_zero t0 x00))).mp
      (eventually_of_forall (λ u e, _)),
    simp only [←hr], rw xe, exact e,
    rw ←hr at e, simp only [uncurry] at e,
    rw [←mul_assoc, mul_comm _ ↑u, mul_assoc, div_mul_cancel _ x00] at e,
    exact e,
  }, {
    rintros t ⟨m,e⟩, simp only [mem_set_of, mem_closure_iff_frequently] at ⊢ e,
    have rc : ∀ {x : ℂ}, (c,x) ∈ s.ext → continuous_at (λ t : ℝ, s.ray c (↑t*x)) t :=
      λ x p, (s.ray_holomorphic (pt p m)).in2.continuous_at.comp_of_eq
        (complex.continuous_of_real.continuous_at.mul continuous_at_const) rfl,
    exact tendsto_nhds_unique_of_frequently_eq (rc p0) (rc p1) e,
  },
end

-- s.potential has postcritical minima only at z = a
lemma super.potential_minima_only_a (s : super f d a) [one_preimage s] (p : postcritical s c z)
    (m : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w) : z = a := begin
  contrapose m, simp only [filter.not_eventually, not_le],
  rcases s.nice_n p.basin z (le_refl _) with ⟨near,nc⟩,
  set f : S → ℂ := s.bottcher_near_iter (s.n c z) c,
  have o : 𝓝 (f z) = filter.map f (𝓝 z) :=
    (nontrivial_holomorphic_at_of_mfderiv_ne_zero (s.bottcher_near_iter_holomorphic near).in2
      (s.bottcher_near_iter_mfderiv_ne_zero (nc _ (le_refl _))
      (p.not_precritical ((s.potential_ne_zero _).mpr m)))).nhds_eq_map_nhds,
  have e : ∃ᶠ x : ℂ in 𝓝 (f z), abs x < abs (f z), {
    apply frequently_smaller, contrapose m, simp only [not_not] at m ⊢,
    replace m := (s.bottcher_near_eq_zero near).mp m,
    rw s.preimage_eq at m, exact m,
  },
  rw [o, filter.frequently_map] at e,
  apply e.mp,
  apply (((s.is_open_preimage _).snd_preimage c).eventually_mem near).mp,
  refine eventually_of_forall (λ w m lt, _),
  simp only at m lt, rw [mem_set_of, mem_set_of] at m, simp only at m,
  simp only [s.potential_eq m, s.potential_eq near, super.potential'],
  exact real.rpow_lt_rpow (complex.abs.nonneg _) lt (inv_pos.mpr (pow_pos (nat.cast_pos.mpr s.dp) _)),
end

-- s.ray covers s.post
lemma super.ray_surj (s : super f d a) [one_preimage s]
    : ∀ {z}, (c,z) ∈ s.post → ∃ x, (c,x) ∈ s.ext ∧ s.ray c x = z := begin
  intros z0 m0,
  by_contradiction i0, simp only [not_forall, not_exists, not_and] at i0,
  set p0 := s.potential c z0,
  rcases exists_between m0 with ⟨p1,p01,post⟩, simp only at p01 post,
  set i := s.ray c '' {x | (c,x) ∈ s.ext},
  set j := {z | s.potential c z ≤ p1} ∩ i,
  set u := {z | s.potential c z ≤ p1} \ i,
  have pc : continuous (s.potential c) := (continuous.potential s).in2,
  have io : is_open i, {
    rw is_open_iff_eventually, rintros z ⟨x,m,xz⟩, 
    have eq := (s.ray_nontrivial m).nhds_eq_map_nhds, rw xz at eq,
    rw [eq, filter.eventually_map],
    exact ((s.is_open_ext.snd_preimage c).eventually_mem m).mp (eventually_of_forall (λ x m, ⟨x,m,rfl⟩)),
  },
  have jc : is_closed j, {
    have e : j = s.ray c '' closed_ball 0 p1, {
      refine set.ext (λ z, _),
      simp only [mem_inter_iff, mem_set_of, mem_image, mem_closed_ball, complex.dist_eq, sub_zero, super.ext],
      constructor,
      rintros ⟨zp1,x,xp,xz⟩, rw [←xz, s.ray_potential xp] at zp1, use [x,zp1,xz],
      rintros ⟨x,xp,xz⟩, have zp1 := lt_of_le_of_lt xp post, rw [←xz, s.ray_potential zp1], use [xp, x, zp1],
    },
    rw e, refine (is_compact.image_of_continuous_on (is_compact_closed_ball _ _) _).is_closed,
    intros x m, simp only [mem_closed_ball, complex.dist_eq, sub_zero] at m,
    exact (s.ray_holomorphic (lt_of_le_of_lt m post)).in2.continuous_at.continuous_within_at,
  },
  have uc : is_compact u := ((is_closed_le pc continuous_const).sdiff io).is_compact,
  have z0u : z0 ∈ u, {
    simp only [mem_diff, mem_set_of], use le_of_lt p01, contrapose i0,
    simp only [not_not, mem_image, mem_set_of, not_forall, exists_prop] at i0 ⊢, exact i0,
  },  
  have ne : u.nonempty := ⟨z0,z0u⟩,
  rcases pc.continuous_on.compact_min uc ne with ⟨z,zu,zm⟩,
  simp only [mem_diff, mem_set_of] at zu,
  replace zm : ∀ᶠ w in 𝓝 z, s.potential c z ≤ s.potential c w, {
    have m : z ∈ jᶜ, { rw compl_inter, right, exact zu.2 },
    have lt : s.potential c z < p1 := lt_of_le_of_lt (zm z0u) p01,
    apply (jc.is_open_compl.eventually_mem m).mp,
    apply ((continuous.potential s).in2.continuous_at.eventually_lt continuous_at_const lt).mp,
    refine eventually_of_forall (λ w lt m, _),
    rw compl_inter at m, cases m with m m, {
      simp only [compl_set_of, mem_set_of, not_le] at m, linarith,
    }, {
      apply zm, simp only [mem_diff, mem_set_of], use [le_of_lt lt,m],
    },
  },
  simp only [mem_set_of, mem_image, not_exists, not_and] at zu,
  have za := s.potential_minima_only_a (lt_of_le_of_lt zu.1 post) zm,
  have h := zu.2 0 (s.mem_ext c), simp only [s.ray_zero] at h, exact h za.symm,
end

-- s.ray is bijective from s.ext → s.post, accounting for c
lemma super.ray_bij (s : super f d a) [one_preimage s]
    : bij_on (λ y : ℂ × ℂ, (y.1, s.ray y.1 y.2)) s.ext s.post := begin
  refine ⟨λ _ m, s.ray_post m,_,_⟩, {
    rintros ⟨c0,x0⟩ m0 ⟨c1,x1⟩ m1 e, simp only [prod.ext_iff] at e ⊢, rcases e with ⟨ec,ex⟩,
    rw ec at m0 ex, use [ec, s.ray_inj m0 m1 ex],
  }, {
    rintros ⟨c,x⟩ m, simp only [mem_image, prod.ext_iff],
    rcases s.ray_surj m with ⟨x,m,e⟩, use [⟨c,x⟩,m,rfl,e],
  },
end