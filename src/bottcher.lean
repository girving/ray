-- The bottcher map throughout s.post

import ray

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

-- s.ray has a global inverse
lemma super.ray_inv (s : super f d a) [one_preimage s] 
    : ∃ b : ℂ → S → ℂ, holomorphic_on II I (uncurry b) s.post ∧
        ∀ y : ℂ × ℂ, y ∈ s.ext → b y.1 (s.ray y.1 y.2) = y.2 := begin
  rw ←s.ray_bij.image_eq,
  exact global_complex_inverse_fun_open s.ray_holomorphic_on (λ _ m, s.ray_noncritical m)
    s.ray_bij.inj_on s.is_open_ext,
end

-- The bottcher map throughout s.post
def super.bottcher_post (s : super f d a) [one_preimage s] : ℂ → S → ℂ := classical.some s.ray_inv

-- The bottcher map tweaked so the defining equation is satisfied even where it isn't continuous
def super.bottcher (s : super f d a) [one_preimage s] : ℂ → S → ℂ := 
  λ c z, @dite _ (∃ n, (c, f c^[n] z) ∈ s.post) (classical.dec _)
    (λ h, let n := @nat.find _ (classical.dec_pred _) h in (λ w, w ^ (d : ℂ)⁻¹)^[n] (s.bottcher_post c (f c^[n] z)))
    (λ _, 1)

-- bottcher = bottcher_post on post
lemma super.bottcher_eq_bottcher_post (s : super f d a) [one_preimage s] (m : (c,z) ∈ s.post)
    : s.bottcher c z = s.bottcher_post c z := begin
  have h : ∃ n, (c, f c^[n] z) ∈ s.post := ⟨0, by simpa only [function.iterate_zero_apply]⟩,
  have h0 := (@nat.find_eq_zero _ (classical.dec_pred _) h).mpr m,
  simp only [super.bottcher, h, dif_pos, h0, function.iterate_zero_apply, pow_zero, inv_one, complex.cpow_one],
end
lemma super.eq_on_bottcher_bottcher_post (s : super f d a) [one_preimage s]
    : eq_on (uncurry s.bottcher) (uncurry s.bottcher_post) s.post := λ _ m, s.bottcher_eq_bottcher_post m

-- s.bottcher is holomorphic
lemma super.bottcher_holomorphic_on (s : super f d a) [one_preimage s]
    : holomorphic_on II I (uncurry s.bottcher) s.post := begin
  rintros ⟨c,z⟩ m, apply ((classical.some_spec s.ray_inv).1 _ m).congr,
  exact s.eq_on_bottcher_bottcher_post.symm.eventually_eq_of_mem (s.is_open_post.mem_nhds m),
end

-- s.bottcher is the left inverse of s.ray
lemma super.bottcher_ray (s : super f d a) [one_preimage s] (m : (c,x) ∈ s.ext)
    : s.bottcher c (s.ray c x) = x := begin
  rw s.bottcher_eq_bottcher_post (s.ray_post m), exact (classical.some_spec s.ray_inv).2 _ m,
end

-- s.bottcher is the right inverse of s.ray
lemma super.ray_bottcher (s : super f d a) [one_preimage s] (m : (c,z) ∈ s.post)
    : s.ray c (s.bottcher c z) = z := begin
  rcases s.ray_surj m with ⟨x,m,e⟩, rw [←e, s.bottcher_ray m],
end

-- s.bottcher maps s.post to s.ext
lemma super.bottcher_ext (s : super f d a) [one_preimage s] (m : (c,z) ∈ s.post)
    : (c, s.bottcher c z) ∈ s.ext := begin
  rcases s.ray_surj m with ⟨x,m,e⟩, rw [←e, s.bottcher_ray m], exact m,
end

-- s.bottcher is locally s.bottcher_near
lemma super.bottcher_eq_bottcher_near (s : super f d a) [one_preimage s] (c : ℂ)
    : ∀ᶠ z in 𝓝 a, s.bottcher c z = s.bottcher_near c z := begin
  have eq := (s.ray_nontrivial (s.mem_ext c)).nhds_eq_map_nhds, simp only [s.ray_zero] at eq,
  simp only [eq, filter.eventually_map],
  apply ((continuous_at_const.prod continuous_at_id).eventually (s.ray_eqn_zero c)).mp,
  refine ((s.is_open_ext.snd_preimage c).eventually_mem (s.mem_ext c)).mp (eventually_of_forall (λ z m e, _)),
  simp only [s.bottcher_ray m], exact e.symm,
end

-- s.ext and s.post are homeomorphic
def super.equiv (s : super f d a) [one_preimage s] : local_equiv (ℂ × ℂ) (ℂ × S) := {
  to_fun := λ y : ℂ × ℂ, (y.1, s.ray y.1 y.2),  
  inv_fun := λ y : ℂ × S, (y.1, s.bottcher y.1 y.2),
  source := s.ext,
  target := s.post,
  map_source' := begin rintros ⟨c,x⟩ m, exact s.ray_post m end,
  map_target' := begin rintros ⟨c,z⟩ m, exact s.bottcher_ext m end,
  left_inv' := begin rintros ⟨c,x⟩ m, simp only [s.bottcher_ray m] end,
  right_inv' := begin rintros ⟨c,z⟩ m, simp only [s.ray_bottcher m] end, 
}
def super.homeomorph (s : super f d a) [one_preimage s] : local_homeomorph (ℂ × ℂ) (ℂ × S) := {
  to_local_equiv := s.equiv,
  open_source := s.is_open_ext,
  open_target := s.is_open_post,
  continuous_to_fun := continuous_on_fst.prod (s.ray_holomorphic_on.continuous_on),
  continuous_inv_fun := continuous_on_fst.prod (s.bottcher_holomorphic_on.continuous_on),
}

-- Slices of s.ext and s.post are homeomorphic
def super.equiv_slice (s : super f d a) [one_preimage s] (c : ℂ) : local_equiv ℂ S := {
  to_fun := s.ray c,
  inv_fun := s.bottcher c,
  source := {x | (c,x) ∈ s.ext},
  target := {z | (c,z) ∈ s.post},
  map_source' := λ _ m, s.ray_post m, map_target' := λ _ m, s.bottcher_ext m,
  left_inv' := λ _ m, by simp only [s.bottcher_ray m], right_inv' := λ _ m, by simp only [s.ray_bottcher m], 
}
def super.homeomorph_slice (s : super f d a) [one_preimage s] (c : ℂ) : local_homeomorph ℂ S := {
  to_local_equiv := s.equiv_slice c,
  open_source := s.is_open_ext.snd_preimage c,
  open_target := s.is_open_post.snd_preimage c,
  continuous_to_fun := λ _ m, (s.ray_holomorphic m).in2.continuous_at.continuous_within_at,
  continuous_inv_fun := λ _ m, (s.bottcher_holomorphic_on _ m).in2.continuous_at.continuous_within_at, 
}

-- s.post and s.post slices are connected
lemma super.post_connected (s : super f d a) [one_preimage s] : is_connected s.post := begin
  have e : s.post = s.homeomorph '' s.ext := s.homeomorph.image_source_eq_target.symm,
  rw e, exact s.ext_connected.image _ s.homeomorph.continuous_on,
end
lemma super.post_slice_connected (s : super f d a) [one_preimage s] (c : ℂ)
    : is_connected {z | (c,z) ∈ s.post} := begin
  have e : {z | (c,z) ∈ s.post} = s.homeomorph_slice c '' {x | (c,x) ∈ s.ext} :=
    (s.homeomorph_slice c).image_source_eq_target.symm,
  rw e, exact (s.ext_slice_connected c).image _ (s.homeomorph_slice c).continuous_on,
end

-- Outside of the basin, we've defined bottcher = 1 for simplicity
lemma super.bottcher_not_basin (s : super f d a) [one_preimage s] (m : (c,z) ∉ s.basin) : s.bottcher c z = 1 := begin
  have p : ¬∃ n, (c, f c^[n] z) ∈ s.post, {
    contrapose m, simp only [not_not] at m ⊢, rcases m with ⟨n,m⟩,
    rcases s.post_basin m with ⟨k,m⟩, simp only [←function.iterate_add_apply] at m, use [k+n, m],
  },
  simp only [super.bottcher, p], rw dif_neg, exact not_false,
end

lemma super.basin_post (s : super f d a) [one_preimage s] (m : (c,z) ∈ s.basin) : ∃ n, (c, f c^[n] z) ∈ s.post := begin
  rcases tendsto_at_top_nhds.mp (s.basin_attracts m) {z | (c,z) ∈ s.post} (s.post_a c)
    (s.is_open_post.snd_preimage c) with ⟨n,h⟩,  
  specialize h n (le_refl n), simp only [mem_set_of] at h, use [n,h],
end

-- The defining equation
lemma super.bottcher_eqn (s : super f d a) [one_preimage s] : s.bottcher c (f c z) = s.bottcher c z ^ d := begin
  have h0 : ∀ {c z}, (c,z) ∈ s.post → s.bottcher c (f c z) = s.bottcher c z ^ d, {
    intros c z m,
    suffices e : ∀ᶠ w in 𝓝 a, s.bottcher c (f c w) = s.bottcher c w ^ d, {
      refine (holomorphic_on.eq_of_locally_eq _ (λ z m, (s.bottcher_holomorphic_on (c,z) m).in2.pow)
        (s.post_slice_connected c).is_preconnected ⟨a, s.post_a c, e⟩).self_set _ m,
      exact λ z m, (s.bottcher_holomorphic_on _ (s.stays_post m)).in2.comp (s.fa _).in2,
    },
    have e := s.bottcher_eq_bottcher_near c,
    have fc := (s.fa (c,a)).in2.continuous_at, simp only [continuous_at, s.f0] at fc,
    apply e.mp, apply (fc.eventually e).mp,
    apply ((s.is_open_near.snd_preimage c).eventually_mem (s.mem_near c)).mp,
    refine eventually_of_forall (λ w m e0 e1, _), simp only at m e0 e1,
    simp only [e0,e1], exact s.bottcher_near_eqn m,
  },
  by_cases p : (c,z) ∈ s.post, simp only [h0 p],
  by_cases m : (c,z) ∈ s.basin, {
    have e0 : ∃ n, (c, f c^[n] z) ∈ s.post := s.basin_post m,
    have e1 : ∃ n, (c, f c^[n] (f c z)) ∈ s.post, {
      rcases e0 with ⟨n,e0⟩, use n,
      simp only [←function.iterate_succ_apply, function.iterate_succ_apply'],
      exact s.stays_post e0,
    },
    simp only [super.bottcher, e0, e1, dif_pos],
    generalize hk0 : @nat.find _ (classical.dec_pred _) e0 = k0,
    generalize hk1 : @nat.find _ (classical.dec_pred _) e1 = k1,
    have kk : k0 = k1 + 1, {
      rw [←hk0, ←hk1], apply le_antisymm, {
        apply nat.find_le, simp only [function.iterate_succ_apply],
        exact @nat.find_spec _ (classical.dec_pred _) e1,
      }, {
        rw [nat.succ_le_iff, nat.lt_find_iff], intros n n1,
        contrapose n1, simp only [not_not, not_le] at n1 ⊢,
        have n0 : n ≠ 0, {
          contrapose p, simp only [not_not] at ⊢ p, simp only [p, function.iterate_zero_apply] at n1, exact n1,
        },
        rw [←nat.succ_le_iff, nat.succ_eq_add_one, ←nat.sub_add_cancel (nat.pos_of_ne_zero n0)],
        apply nat.succ_le_succ, apply nat.find_le,
        simp only [←function.iterate_succ_apply, nat.succ_eq_add_one, nat.sub_add_cancel (nat.pos_of_ne_zero n0), n1],
      },
    },
    simp only [kk, ←function.iterate_succ_apply, function.iterate_succ_apply'],
    rw complex.cpow_nat_inv_pow _ s.d0,
  },
  have m1 : (c, f c z) ∉ s.basin, {
    contrapose m, simp only [not_not] at m ⊢,
    rcases m with ⟨n,m⟩, use n+1, simp only at ⊢ m, rwa function.iterate_succ_apply,
  },
  simp only [s.bottcher_not_basin m, s.bottcher_not_basin m1, one_pow],
end

-- The defining equation, iterated
lemma super.bottcher_eqn_iter (s : super f d a) [one_preimage s] (n : ℕ)
    : s.bottcher c (f c^[n] z) = s.bottcher c z ^ d^n := begin
  induction n with n h, simp only [function.iterate_zero_apply, pow_zero, pow_one],
  simp only [function.iterate_succ_apply', s.bottcher_eqn, h, ←pow_mul, pow_succ'],
end

-- abs bottcher = potential
lemma super.abs_bottcher (s : super f d a) [one_preimage s] : abs (s.bottcher c z) = s.potential c z := begin
  have base : ∀ {c z}, (c,z) ∈ s.post → abs (s.bottcher c z) = s.potential c z, {
    intros c z m, rcases s.ray_surj m with ⟨x,m,e⟩, rw [←e, s.bottcher_ray m, s.ray_potential m],
  },
  by_cases m : (c,z) ∈ s.basin, {
    rcases s.basin_post m with ⟨n,p⟩,
    rw [←real.pow_nat_rpow_nat_inv (complex.abs.nonneg _) (pow_ne_zero n s.d0),
      ←complex.abs.map_pow, ←s.bottcher_eqn_iter n, base p, s.potential_eqn_iter,
      real.pow_nat_rpow_nat_inv s.potential_nonneg (pow_ne_zero n s.d0)],
  }, {
    have m' := m, simp only [super.basin, not_exists, mem_set_of] at m',
    simp only [s.bottcher_not_basin m, complex.abs.map_one, s.potential_eq_one m'],
  },
end

-- abs < 1
lemma super.bottcher_lt_one (s : super f d a) [one_preimage s] (m : (c,z) ∈ s.post) : abs (s.bottcher c z) < 1 := begin
  replace m := s.bottcher_ext m, simp only [super.ext, mem_set_of] at m, exact lt_of_lt_of_le m s.p_le_one,
end