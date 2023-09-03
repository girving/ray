-- Postcritical points are those with potential below that of any critical point

import potential

open filter (eventually_of_forall)
open function (uncurry)
open one_dimension
open set
open_locale topology
noncomputable theory

-- All information for a monic superattracting fixed point at the origin
variables {S : Type} [topological_space S] [compact_space S] [normal_space S] [complex_manifold I S]
variables {f : ℂ → S → S}
variables {c : ℂ}
variables {a z z0 z1 : S}
variables {d n : ℕ}
variables {p : ℝ}
variables {s : super f d a}

-- The critical potential is the least potential of any non-a critical point
def super.ps (s : super f d a) (c : ℂ) : set ℝ :=
  {p | p = 1 ∨ p ≠ 0 ∧ ∃ z, s.potential c z = p ∧ critical (f c) z}
def super.p (s : super f d a) (c : ℂ) : ℝ := Inf (s.ps c)

-- Basic facts about the critical potential
lemma super.nonempty_ps (s : super f d a) : (s.ps c).nonempty :=
  ⟨1, by simp only [super.ps, mem_set_of, eq_self_iff_true, true_or]⟩
lemma super.compact_ps (s : super f d a) [one_preimage s] : is_compact (s.ps c) := begin
  have pc : continuous (s.potential c) := (continuous.potential s).in2,
  have c1 : is_compact {(1 : ℝ)} := is_compact_singleton, 
  convert c1.union ((s.is_closed_critical_not_a.snd_preimage c).is_compact.image pc),
  apply set.ext, intro p,
  simp only [mem_set_of, super.ps, mem_singleton_iff, mem_union, mem_image, ne.def,
    ←s.potential_eq_zero_of_one_preimage c],
  apply or_congr_right', constructor,
  rintros ⟨p0,z,e,c⟩, rw ←e at p0, exact ⟨z,⟨c,p0⟩,e⟩,
  rintros ⟨z,⟨c,p0⟩,e⟩, rw e at p0, exact ⟨p0,z,e,c⟩,
end
lemma super.ps_pos (s : super f d a) (c : ℂ) (m : p ∈ s.ps c) : 0 < p := begin
  cases m, simp only [m, zero_lt_one], rcases m with ⟨p0,z,e,c⟩, rw ←e at ⊢ p0,
  exact p0.symm.lt_of_le s.potential_nonneg,
end
lemma super.bdd_below_ps (s : super f d a) : bdd_below (s.ps c) :=
  bdd_below_def.mpr ⟨0, λ _ m, le_of_lt (s.ps_pos c m)⟩
lemma super.mem_ps (s : super f d a) (c : ℂ) [one_preimage s] : s.p c ∈ s.ps c := begin
  rw ←s.compact_ps.is_closed.closure_eq, exact cInf_mem_closure s.nonempty_ps s.bdd_below_ps,
end 
lemma super.p_pos (s : super f d a) (c : ℂ) [one_preimage s] : 0 < s.p c := s.ps_pos c (s.mem_ps c)
lemma super.p_le_one (s : super f d a) : s.p c ≤ 1 := cInf_le s.bdd_below_ps (or.inl rfl)

-- s.p doesn't jump down locally
lemma super.lower_semicontinuous_p (s : super f d a) [one_preimage s] : lower_semicontinuous s.p := begin
  intros c p h, contrapose h,
  simp only [not_lt, filter.not_eventually] at h ⊢,
  -- Add a bit of slack
  apply le_of_forall_lt', intros q' pq',
  rcases exists_between pq' with ⟨q,pq,qq⟩, refine lt_of_le_of_lt _ qq, clear qq pq' q',
  by_cases q1 : 1 ≤ q, exact trans s.p_le_one q1,
  simp only [not_le] at q1,
  -- Use closedness of the set of non-a critical points
  set t : set (ℂ × S) := {x | s.potential x.1 x.2 ≤ q ∧ critical (f x.1) x.2 ∧ x.2 ≠ a},
  have ct : is_closed t :=
    (is_closed_le (continuous.potential s) continuous_const).inter s.is_closed_critical_not_a,
  set u := prod.fst '' t,
  have cu : is_closed u := is_closed_map.fst _ ct,
  suffices m : c ∈ u, {
    rcases (mem_image _ _ _).mp m with ⟨⟨c',z⟩,⟨zp,zc,za⟩,cc⟩,
    simp only at cc za zc zp, simp only [cc] at za zc zp, clear cc c',
    simp only [ne.def, ←s.potential_eq_zero_of_one_preimage c] at za,
    refine trans (cInf_le s.bdd_below_ps _) zp, right, use [za, z, rfl, zc],
  },
  refine filter.frequently.mem_of_closed _ cu,
  refine h.mp (eventually_of_forall (λ e h, _)),
  rcases exists_lt_of_cInf_lt s.nonempty_ps (lt_of_le_of_lt h pq) with ⟨r,m,rq⟩,
  cases m, linarith, rcases m with ⟨r0,z,zr,zc⟩,
  rw [←zr, ne.def, s.potential_eq_zero_of_one_preimage] at r0, rw mem_image,
  refine ⟨(e,z),⟨_,zc,r0⟩,rfl⟩, simp only [zr], exact le_of_lt rq,
end

-- A point is "postcritical" if its potential is smaller than any critical point (except for a)
def postcritical (s : super f d a) (c : ℂ) (z : S) : Prop := s.potential c z < s.p c

-- postcritical implies basin
lemma postcritical.basin (p : postcritical s c z) [one_preimage s] : (c,z) ∈ s.basin :=
  s.potential_lt_one_iff.mp (lt_of_lt_of_le p s.p_le_one)

-- If potential z0 ≤ potential z1 and z1 is postcritical, then z0 is postcritical
lemma postscritical.mono (p : postcritical s c z1) (z01 : s.potential c z0 ≤ s.potential c z1)
    : postcritical s c z0 := lt_of_le_of_lt z01 p

-- Postcritical points are not precritical
lemma postcritical.not_precritical (p : postcritical s c z) (p0 : s.potential c z ≠ 0)
    : ¬precritical (f c) z := begin
  contrapose p, simp only [postcritical, not_not, not_forall, not_lt] at ⊢ p,
  rcases p with ⟨n,p⟩, transitivity s.potential c (f c^[n] z), {
    refine cInf_le s.bdd_below_ps (or.inr ⟨_,f c^[n] z,rfl,p⟩),
    simp only [s.potential_eqn_iter], exact pow_ne_zero _ p0,
  }, {
    simp only [s.potential_eqn_iter],
    exact pow_le_of_le_one s.potential_nonneg s.potential_le_one (pow_ne_zero _ s.d0),
  },
end
lemma postcritical.not_precritical' (p : postcritical s c z) (za : z ≠ a) [one_preimage s]
    : ¬precritical (f c) z := begin
  apply p.not_precritical, simp only [ne.def, s.potential_eq_zero_of_one_preimage], exact za,
end

-- The set of postcritical basin points
def super.post (s : super f d a) : set (ℂ × S) := {p : ℂ × S | postcritical s p.1 p.2}

-- s.post is open
lemma super.is_open_post (s : super f d a) [one_preimage s] : is_open s.post := begin
  set f := λ x : ℂ × S, s.p x.1 - s.potential x.1 x.2,
  have fc : lower_semicontinuous f :=
    (s.lower_semicontinuous_p.comp continuous_fst).add (continuous.potential s).neg.lower_semicontinuous,
  have e : s.post = f ⁻¹' Ioi 0 :=
    set.ext (λ _, by simp only [super.post, mem_set_of, postcritical, mem_preimage, mem_Ioi, sub_pos]),
  rw e, exact fc.is_open_preimage _,
end

-- postcritical holds locally
lemma postcritical.eventually (p : postcritical s c z) [one_preimage s]
    : ∀ᶠ p : ℂ × S in 𝓝 (c,z), postcritical s p.1 p.2 := begin
  refine (s.is_open_post.eventually_mem _).mp (eventually_of_forall (λ _ m, m)), exact p,
end

-- Basic s.post facts
lemma super.post_basin (s : super f d a) [one_preimage s] : s.post ⊆ s.basin := λ p m, postcritical.basin m
lemma super.post_postcritical (s : super f d a) {p : ℂ × S} (m : p ∈ s.post) : postcritical s p.1 p.2 := m
lemma super.post_a (s : super f d a) [one_preimage s] (c : ℂ) : (c,a) ∈ s.post := begin
  simp only [super.post, postcritical, s.potential_a, mem_set_of], exact s.p_pos c,
end
lemma super.stays_post (s : super f d a) {p : ℂ × S} (m : p ∈ s.post) : (p.1, f p.1 p.2) ∈ s.post := begin
  rcases p with ⟨c,z⟩, simp only [super.post, mem_set_of, postcritical, s.potential_eqn],
  exact lt_of_le_of_lt (pow_le_of_le_one s.potential_nonneg s.potential_le_one s.d0) m,
end
lemma super.iter_stays_post (s : super f d a) {p : ℂ × S} (m : p ∈ s.post) (n : ℕ): (p.1, f p.1^[n] p.2) ∈ s.post := begin
  induction n with n h, simp only [function.iterate_zero_apply], exact m,
  simp only [function.iterate_succ_apply'], exact s.stays_post h,
end

-- bottcher_near_iter is nontrivial at postcritical points
lemma super.bottcher_near_iter_nontrivial (s : super f d a) (r : (c, f c^[n] z) ∈ s.near)
    (p : postcritical s c z) [one_preimage s]
    : nontrivial_holomorphic_at (s.bottcher_near_iter n c) z := begin
  rcases ((filter.eventually_ge_at_top n).and (s.eventually_noncritical ⟨_,r⟩)).exists with ⟨m,nm,mc⟩,
  have r' := s.iter_stays_near' r nm,
  have h : nontrivial_holomorphic_at (s.bottcher_near_iter m c) z, {
    by_cases p0 : s.potential c z = 0, {
      rw s.potential_eq_zero_of_one_preimage at p0,
      rw p0, exact s.bottcher_near_iter_nontrivial_a,
    }, {
      exact nontrivial_holomorphic_at_of_mfderiv_ne_zero (s.bottcher_near_iter_holomorphic r').in2
        (s.bottcher_near_iter_mfderiv_ne_zero mc (p.not_precritical p0)),
    },
  },
  replace h := h.nonconst,
  refine ⟨(s.bottcher_near_iter_holomorphic r).in2, _⟩,
  contrapose h, simp only [filter.not_frequently, not_not] at h ⊢,
  rw [←nat.sub_add_cancel nm], generalize hk : m - n = k, clear hk nm mc r' p m,
  have er : ∀ᶠ w in 𝓝 z, (c, f c^[n] w) ∈ s.near :=
    (continuous_at_const.prod (s.continuous_at_iter continuous_at_const continuous_at_id)).eventually_mem
      s.is_open_near r,
  refine (h.and er).mp (eventually_of_forall _), rintros x ⟨e,m⟩,
  simp only [super.bottcher_near_iter] at e,
  simp only [super.bottcher_near_iter, function.iterate_add_apply, s.bottcher_near_eqn_iter m,
    s.bottcher_near_eqn_iter r, e],
end