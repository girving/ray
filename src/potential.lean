-- Böttcher map near a superattracting fixed point, and potential throughout the space

import bottcher_near
import complex_manifold
import continuation
import inverse
import one_dimension
import topology

open complex (exp log abs cpow)
open filter (tendsto at_top eventually_of_forall)
open function (curry uncurry)
open metric (ball closed_ball is_open_ball ball_mem_nhds mem_ball_self nonempty_ball)
open nat (iterate)
open one_dimension
open set
open_locale nnreal topology
noncomputable theory

-- All information for a monic superattracting fixed point at the origin
variables {S : Type} [topological_space S] [compact_space S] [t3_space S] [complex_manifold I S]
variables {f : ℂ → S → S}
variables {c : ℂ}
variables {a z : S}
variables {d n : ℕ}
variables {p : ℂ × S}

-- z tends to a under f-iteration
def attracts (f : S → S) (z a : S) := tendsto (λ n, f^[n] z) at_top (𝓝 a)

-- f^[n] z attracts iff z does
lemma attracts_shift {f : S → S} {z a : S} (k : ℕ)
    : attracts f (f^[k] z) a ↔ attracts f z a := begin
  simp only [attracts, ←function.iterate_add_apply],
  apply @filter.tendsto_add_at_top_iff_nat _ (λ n, f^[n] z),
end

-- f as ℂ → ℂ → ℂ using charts, with the attractor at 0
def fl {S : Type} [topological_space S] [complex_manifold I S] (f : ℂ → S → S) (a : S) : ℂ → ℂ → ℂ := λ c,
  (λ z, z - ext_chart_at I a a) ∘
  (ext_chart_at I a ∘ f c ∘ (ext_chart_at I a).symm) ∘
  (λ z, z + ext_chart_at I a a)

-- f has a monic superattractor at a
structure super {S : Type} [topological_space S] [compact_space S] [complex_manifold I S]
    (f : ℂ → S → S) (d : ℕ) (a : S) : Prop :=
  (d2 : 2 ≤ d)
  (fa : holomorphic ((model_with_corners_self ℂ ℂ).prod I) I (uncurry f))
  (f0 : ∀ c, f c a = a)
  (fd : ∀ c, order_at (fl f a c) 0 = d)
  (fc : ∀ c, leading_coeff (fl f a c) 0 = 1)

lemma super.dp (s : super f d a) : 0 < d := trans (by norm_num) s.d2
lemma super.dnp (s : super f d a) {n : ℕ} : 0 < d^n := pow_pos s.dp _
lemma super.d1 (s : super f d a) : 1 < d := lt_of_lt_of_le (by norm_num) s.d2
lemma super.d0 (s : super f d a) : d ≠ 0 := ne_of_gt s.dp
def super.fl (s : super f d a) := fl f a

-- Iterating at a does nothing
lemma super.iter_a (s : super f d a) (n : ℕ) : f c^[n] a = a := begin
  induction n with n h, simp only [function.iterate_zero_apply],
  simp only [function.iterate_succ_apply', h, s.f0],
end

-- fl is analytic
lemma super.fla (s : super f d a) (c : ℂ) : analytic_at ℂ (uncurry s.fl) (c,0) := begin
  rw @analytic_at_iff_holomorphic_at (ℂ × ℂ) (model_prod ℂ ℂ) _ _ _ _ ℂ ℂ _ _ _ _ II I,
  refine ((analytic_at_id.sub analytic_at_const).holomorphic_at I I).comp _,
  refine (holomorphic_at.ext_chart_at _).comp _,
  simp only [s.f0, ext_chart_at, local_homeomorph.extend, local_equiv.coe_trans,
    model_with_corners.to_local_equiv_coe, local_homeomorph.coe_coe, function.comp_app, zero_add,
    local_equiv.coe_trans_symm, local_homeomorph.coe_coe_symm, model_with_corners.to_local_equiv_coe_symm,
    model_with_corners.left_inv, local_homeomorph.left_inv, mem_chart_source, local_equiv.trans_source,
    model_with_corners.source_eq, set.preimage_univ, set.inter_univ],
  refine (s.fa _).curry_comp holomorphic_at_fst _,
  refine (holomorphic_at.ext_chart_at_symm _).comp _,
  simp only [ext_chart_at, local_homeomorph.extend, local_equiv.coe_trans, model_with_corners.to_local_equiv_coe,
    local_homeomorph.coe_coe, function.comp_app, zero_add, local_equiv.trans_target, model_with_corners.target_eq,
    model_with_corners.to_local_equiv_coe_symm, set.mem_inter_iff, set.mem_range_self, set.mem_preimage,
    model_with_corners.left_inv, local_homeomorph.map_source, mem_chart_source, and_self],
  exact (analytic_at_snd.add analytic_at_const).holomorphic_at _ _,
end

-- (f c)^[k] is holomorphic
lemma super.holomorphic_at_iter (s : super f d a) {T : Type} [topological_space T] [complex_manifold I T]
    {g : ℂ × T → ℂ} {h : ℂ × T → S} {p : ℂ × T} {n : ℕ}
    (ga : holomorphic_at II I g p) (ha : holomorphic_at II I h p)
    : holomorphic_at II I (λ p : ℂ × T, (f (g p))^[n] (h p)) p := begin
  induction n with n h, simp only [function.iterate_zero, id.def], exact ha,
  simp_rw function.iterate_succ', exact (s.fa _).curry_comp ga h,
end
lemma super.continuous_iter (s : super f d a) {T : Type} [topological_space T]
    {g : T → ℂ} {h : T → S} {n : ℕ} (gc : continuous g) (hc : continuous h)
    : continuous (λ x, (f (g x))^[n] (h x)) := begin
  induction n with n h, simp only [function.iterate_zero, id.def], exact hc,
  simp_rw function.iterate_succ', exact s.fa.continuous.comp (gc.prod h),
end
lemma super.continuous_on_iter (s : super f d a) {T : Type} [topological_space T]
    {g : T → ℂ} {h : T → S} {t : set T} {n : ℕ} (gc : continuous_on g t) (hc : continuous_on h t)
    : continuous_on (λ x, (f (g x))^[n] (h x)) t := begin
  induction n with n h, simp only [function.iterate_zero, id.def], exact hc,
  simp_rw function.iterate_succ', exact s.fa.continuous.comp_continuous_on (gc.prod h),
end
lemma super.continuous_at_iter (s : super f d a) {T : Type} [topological_space T]
    {g : T → ℂ} {h : T → S} {x : T} {n : ℕ} (gc : continuous_at g x) (hc : continuous_at h x)
    : continuous_at (λ x, (f (g x))^[n] (h x)) x := begin
  induction n with n h, simp only [function.iterate_zero, id.def], exact hc,
  simp_rw function.iterate_succ', exact (s.fa _).continuous_at.comp (gc.prod h),
end
lemma super.holomorphic_iter (s : super f d a) {k : ℕ} : holomorphic II I (λ p : ℂ × S, (f p.1)^[k] p.2) :=
  λ _, s.holomorphic_at_iter holomorphic_at_fst holomorphic_at_snd

-- fl c 0 = 0
lemma super.fl0 (s : super f d a) {c : ℂ} : s.fl c 0 = 0 :=
  by simp only [super.fl, fl, s.f0, function.comp_app, zero_add, local_equiv.left_inv, mem_ext_chart_source,
    sub_self]

-- 0 is a critical point for fl
lemma super.critical_0 (s : super f d a) (c : ℂ) : critical (s.fl c) 0 := begin
  simp only [critical, mfderiv_eq_fderiv, super.fl],
  have p := (s.fla c).in2.leading_approx,
  simp only [sub_zero, algebra.id.smul_eq_mul, super.fl, s.fd, s.fc, mul_one] at p,
  generalize hg : fl f a c = g, rw hg at p,
  have g0 : g 0 = 0, { rw ←hg, exact s.fl0 },
  apply has_fderiv_at.fderiv,
  simp only [has_fderiv_at_iff_is_o_nhds_zero, continuous_linear_map.zero_apply, sub_zero, zero_add, g0],
  have od : (λ z : ℂ, z^d) =o[𝓝 0] λ z, z, {
    rw asymptotics.is_o_iff, intros e ep,
    apply ((@metric.is_open_ball ℂ _ 0 (min 1 e)).eventually_mem (mem_ball_self (by bound))).mp,
    refine eventually_of_forall (λ z b, _),
    simp only at b, rw [mem_ball_zero_iff, complex.norm_eq_abs, lt_min_iff] at b,
    simp only [complex.norm_eq_abs, complex.abs.map_pow],
    rw [←nat.sub_add_cancel s.d2, pow_add, pow_two],
    calc abs z ^ (d-2) * (abs z * abs z) ≤ 1^(d-2) * (abs z * abs z) : by bound [b.1]
    ... = abs z * abs z : by simp only [one_pow, one_mul]
    ... ≤ e * abs z : by bound [b.2],
  },
  have p' := (p.trans od).add od,
  simp only [sub_add_cancel] at p',
  exact p',
end

-- a is a critical point for f
lemma super.critical_a (s : super f d a) (c : ℂ) : critical (f c) a := begin
  have h := s.critical_0 c,
  have e := local_equiv.left_inv _ (mem_ext_chart_source I a),
  contrapose h, simp only [critical, super.fl, fl, ←ne.def] at ⊢ h,
  apply mderiv_comp_ne_zero',
  rw [mfderiv_eq_fderiv, @fderiv_sub_const ℂ _ _ _ _ _ _ _ (λ z : ℂ, z) _ _, ←mfderiv_eq_fderiv],
  exact id_mderiv_ne_zero,
  apply mderiv_comp_ne_zero', apply mderiv_comp_ne_zero', apply mderiv_comp_ne_zero',
  apply ext_chart_at_mderiv_ne_zero',
  simp only [function.comp, zero_add, e, s.f0],
  exact mem_ext_chart_source I a,
  apply mderiv_comp_ne_zero', apply mderiv_comp_ne_zero',
  have b : (λ (z : ℂ), z + ext_chart_at I a a) 0 = 0 + ext_chart_at I a a := rfl,
  rw [b, zero_add, e], exact h,
  apply ext_chart_at_symm_mderiv_ne_zero', simp only [zero_add], exact mem_ext_chart_target I a,
  exact id_mderiv_ne_zero,
  rw [mfderiv_eq_fderiv, @fderiv_add_const ℂ _ _ _ _ _ _ _ (λ z : ℂ, z) _ _, ←mfderiv_eq_fderiv],
  exact id_mderiv_ne_zero,
  exact id_mderiv_ne_zero,
end

-- f c is nontrivial at a
lemma super.f_nontrivial (s : super f d a) (c : ℂ) : nontrivial_holomorphic_at (f c) a := begin
  refine ⟨(s.fa _).in2,_⟩, simp only [s.f0],
  have n : ∃ᶠ w in 𝓝 (0 : ℂ), s.fl c w ≠ 0, {
    have e := (nontrivial_holomorphic_at_of_order (s.fla c).in2 _).nonconst,
    simp only [s.fl0] at e, exact e,
    simp only [super.fl, s.fd], exact s.d0,
  },
  contrapose n, simp only [filter.not_frequently, not_not, super.fl, fl, function.comp, sub_eq_zero] at ⊢ n,
  have gc : continuous_at (λ x, (ext_chart_at I a).symm (x + ext_chart_at I a a)) 0, {
    refine (continuous_at_ext_chart_at_symm I a).comp_of_eq _ (by simp only [zero_add]),
    exact continuous_at_id.add continuous_at_const,
  },
  simp only [continuous_at, zero_add, local_equiv.left_inv _ (mem_ext_chart_source _ _)] at gc,
  refine (gc.eventually n).mp (eventually_of_forall _),
  intros x h, rw h,
end

-- Close enough to a, f c a stays within (ext_chart_at I a).source
lemma super.stays_in_chart (s : super f d a) (c : ℂ)
    : ∀ᶠ p : ℂ × S in 𝓝 (c,a), f p.1 p.2 ∈ (ext_chart_at I a).source := begin
  apply continuous_at.eventually_mem_nhd,
  exact (s.fa.continuous.comp continuous_id).continuous_at,
  simp only [s.f0, function.comp.right_id, function.uncurry_apply_pair, ext_chart_at_source_mem_nhds I a],
end

-- There is a open set around the attractor in ext_chart I a where things are nice
lemma super.fr_prop (s : super f d a) (c : ℂ)
    : ∃ r, r > 0 ∧ analytic_on ℂ (uncurry s.fl) (ball (c,0) r) ∧
        ∀ p : ℂ × S, p ∈ (ext_chart_at II (c,a)).source →
          ext_chart_at II (c,a) p ∈ ball (ext_chart_at II (c,a) (c,a)) r →
          f p.1 p.2 ∈ (ext_chart_at I a).source := begin
  rcases (s.fla c).ball with ⟨r0,r0p,fla⟩,
  rcases eventually_nhds_iff.mp (s.stays_in_chart c) with ⟨t,tp,ot,ta⟩,
  set ch := ext_chart_at II (c,a),
  set s := ch.target ∩ ch.symm ⁻¹' t,
  have os : is_open s :=
    (continuous_on_ext_chart_at_symm II (c,a)).preimage_open_of_open
      (ext_chart_at_open_target II (c,a)) ot,
  rcases metric.is_open_iff.mp os (ch (c,a)) _ with ⟨r1,r1p,rs⟩, {
    use [min r0 r1, by bound],
    use fla.mono (metric.ball_subset_ball (by bound)),
    intros p ps pr, apply tp p,
    rw [←ch.left_inv ps, ←set.mem_preimage],
    exact set.mem_of_mem_inter_right (rs (metric.ball_subset_ball (by bound) pr)),
  }, {
    apply set.mem_inter (mem_ext_chart_target _ _),
    rw [set.mem_preimage, ch.left_inv (mem_ext_chart_source _ _)],
    exact ta, apply_instance, apply_instance, apply_instance,
  },
end

-- A radius around (c,0) on which f and fl are nice
def super.fr (s : super f d a) (c : ℂ) : ℝ := classical.some (s.fr_prop c)
lemma super.frp (s : super f d a) (c : ℂ) : s.fr c > 0 := (classical.some_spec (s.fr_prop c)).1
lemma super.fla_on (s : super f d a) (c : ℂ) : analytic_on ℂ (uncurry s.fl) (ball (c,0) (s.fr c)) :=
  (classical.some_spec (s.fr_prop c)).2.1
lemma super.fr_stays (s : super f d a) (c : ℂ) (p : ℂ × S) (ps : p ∈ (ext_chart_at II (c,a)).source)
    (pr : ext_chart_at II (c,a) p ∈ ball (ext_chart_at II (c,a) (c,a)) (s.fr c))
    : f p.1 p.2 ∈ (ext_chart_at I a).source :=
  (classical.some_spec (s.fr_prop c)).2.2 p ps pr
def super.fls (s : super f d a) : set (ℂ × ℂ) := ⋃ c, ball (c,(0:ℂ)) (s.fr c)
def super.fls_open (s : super f d a) : is_open s.fls := is_open_Union (λ _, is_open_ball)

-- b ∈ ball 0 r → (b,0) ∈ ball 0 r
lemma prod_zero_mem_ball {c b : ℂ} {r : ℝ} (m : b ∈ ball c r) : (b,(0 : ℂ)) ∈ ball (c, (0 : ℂ)) r := begin
  simp only [metric.mem_ball] at m, simpa only [metric.mem_ball, dist_prod_same_right],
end

-- super → super_at_c and super_near_c
lemma super.super_at_c (s : super f d a) : super_at_c s.fl d univ := {
  o := is_open_univ,
  fa := λ c m, s.fla _, 
  s := λ c m, { d2 := s.d2, fd := s.fd _, fc := s.fc _, fa0 := (s.fla c).in2 },
}
lemma super.exists_super_near_c (s : super f d a) : ∃ t, t ⊆ s.fls ∧ super_near_c s.fl d univ t := begin
  refine s.super_at_c.super_near_c' s.fls_open (λ c m, _),
  rw [super.fls, set.mem_Union], use c, exact mem_ball_self (s.frp c),
end

-- A set on which bottcher_near is defined
def super.near' (s : super f d a) : set (ℂ × ℂ) := classical.some s.exists_super_near_c
lemma super.near_subset' (s : super f d a) : s.near' ⊆ s.fls := (classical.some_spec s.exists_super_near_c).1
def super.near (s : super f d a) : set (ℂ × S) :=
  (ext_chart_at II ((0:ℂ),a)).source ∩
    ext_chart_at II ((0:ℂ),a) ⁻¹' {p : ℂ × ℂ | (p.1, p.2 - ext_chart_at I a a) ∈ s.near'}
lemma super.super_near_c (s : super f d a) : super_near_c s.fl d univ s.near' :=
  (classical.some_spec s.exists_super_near_c).2
lemma super.is_open_near' (s : super f d a) : is_open s.near' := s.super_near_c.o
lemma super.is_open_near (s : super f d a) : is_open s.near := begin
  apply (continuous_on_ext_chart_at _ _).preimage_open_of_open (is_open_ext_chart_at_source _ _),
  exact is_open.preimage (continuous_fst.prod (continuous_snd.sub continuous_const)) s.is_open_near',
end
lemma super.mem_near (s : super f d a) (c : ℂ) : (c,a) ∈ s.near := begin
  simp only [super.near, ext_chart_at_prod, local_equiv.prod_source, set.mem_prod, set.mem_inter_iff,
    mem_ext_chart_source, ext_chart_at_eq_refl, local_equiv.refl_source, set.mem_univ, true_and, set.mem_preimage,
    local_equiv.prod_coe, local_equiv.refl_coe, id, set.mem_set_of_eq, sub_self],
  exact (s.super_near_c.s (set.mem_univ _)).t0,
end 
lemma super.near_subset_chart (s : super f d a) {c : ℂ} {z : S} (m : (c,z) ∈ s.near)
    : z ∈ (ext_chart_at I a).source := begin
  have h := set.mem_of_mem_inter_left m,
  simp only [ext_chart_at_prod, local_equiv.prod_source, set.mem_prod_eq] at h,
  exact h.2,
end
lemma super.mem_near_to_near' (s : super f d a) {p : ℂ × S} (m : p ∈ s.near)
    : (p.1, ext_chart_at I a p.2 - ext_chart_at I a a) ∈ s.near' := begin
  have h := set.mem_of_mem_inter_right m,
  simp only [set.mem_preimage, ext_chart_at_prod, local_equiv.prod_coe, ext_chart_at_eq_refl,
    local_equiv.refl_coe, id] at h,
  exact h,
end 

-- Once we're in s.near, we stay there
lemma super.stays_near (s : super f d a) {c : ℂ} {z : S} (m : (c,z) ∈ s.near) : (c, f c z) ∈ s.near := begin
  simp only [super.near, ext_chart_at_prod, local_equiv.prod_source, set.mem_prod, set.mem_inter_iff,
    mem_ext_chart_source, ext_chart_at_eq_refl, local_equiv.refl_source, set.mem_univ, true_and, set.mem_preimage,
    local_equiv.prod_coe, local_equiv.refl_coe, id, set.mem_set_of_eq, sub_self] at ⊢ m,
  rcases set.mem_Union.mp (s.near_subset' m.2) with ⟨b,mb⟩,
  simp only [mem_ball_iff_norm, prod.norm_def, max_lt_iff, prod.fst_sub, prod.snd_sub, sub_zero] at mb,
  constructor, {
    apply s.fr_stays b (c,z),
    simp only [m.1, super.near, ext_chart_at_prod, local_equiv.prod_source, set.mem_prod, set.mem_inter_iff,
      mem_ext_chart_source, ext_chart_at_eq_refl, local_equiv.refl_source, set.mem_univ, true_and, set.mem_preimage,
      local_equiv.prod_coe, local_equiv.refl_coe, id, set.mem_set_of_eq, sub_self],
    simp only [m.1, mb.1, mb.2, super.near, ext_chart_at_prod, local_equiv.prod_source, set.mem_prod,
      set.mem_inter_iff, mem_ext_chart_source, ext_chart_at_eq_refl, local_equiv.refl_source, set.mem_univ, true_and,
      set.mem_preimage, local_equiv.prod_coe, local_equiv.refl_coe, id, set.mem_set_of_eq, sub_self,
      mem_ball_iff_norm, prod.norm_def, max_lt_iff, prod.fst_sub, prod.snd_sub, sub_zero],
  }, {
    have h := (s.super_near_c.s (set.mem_univ c)).ft m.2,
    simp only [super.fl, fl, function.comp, sub_add_cancel, local_equiv.left_inv _ m.1] at h,
    exact h,
  },
end

-- Once we're in s.near, we stay there forever
lemma super.iter_stays_near (s : super f d a) {c : ℂ} {z : S} (m : (c,z) ∈ s.near) (n : ℕ)
    : (c, f c^[n] z) ∈ s.near := begin
  induction n with n h, simp only [function.iterate_zero, id, m],
  simp only [nat.add_succ, function.iterate_succ', s.stays_near h],
end

-- More iterations stay in s.near
lemma super.iter_stays_near' (s : super f d a) {a b : ℕ} (m : (c, f c^[a] z) ∈ s.near)
  (ab : a ≤ b) : (c, f c^[b] z) ∈ s.near := begin
  rw [←nat.sub_add_cancel ab, function.iterate_add_apply], exact s.iter_stays_near m _,
end

 -- If z attracts, it eventually reaches s.near
lemma super.reaches_near (s : super f d a) {z : S} (a : attracts (f c) z a)
    : ∀ᶠ n in at_top, (c, f c^[n] z) ∈ s.near := begin
  rw [attracts, filter.tendsto_iff_forall_eventually_mem] at a,
  have e := a {z | (c,z) ∈ s.near} _, exact e,
  apply is_open.mem_nhds, apply is_open.snd_preimage s.is_open_near, exact s.mem_near c,
end

-- If z reaches near, it attracts to a
lemma super.attracts (s : super f d a) {n : ℕ} (r : (c, f c^[n] z) ∈ s.near) : attracts (f c) z a := begin
  have m := s.mem_near_to_near' r,
  have t := iterates_tendsto (s.super_near_c.s (set.mem_univ c)) m,
  generalize hg : (λ x : ℂ, (ext_chart_at I a).symm (x + ext_chart_at I a a)) = g,
  have gc : continuous_at g 0, {
    rw ←hg, 
    refine (continuous_at_ext_chart_at_symm'' I a _).comp (continuous_id.add continuous_const).continuous_at,
    simp only [zero_add], exact mem_ext_chart_target I a,
  },
  have g0 : g 0 = a, {
    simp only [←hg], simp only [zero_add], exact local_equiv.left_inv _ (mem_ext_chart_source _ _),
  },
  have h := gc.tendsto.comp t, clear t gc m,
  simp only [function.comp, g0] at h,
  rw ←attracts_shift n,
  refine filter.tendsto.congr _ h, clear h,
  intro k, simp only [←hg], induction k with k h,
  simp only [function.iterate_zero_apply], rw sub_add_cancel,
  exact local_equiv.left_inv _ (s.near_subset_chart r),
  simp only [function.iterate_succ_apply'],
  generalize hx : s.fl c^[k] (ext_chart_at I a (f c^[n] z) - ext_chart_at I a a) = x, rw hx at h,
  simp only [super.fl, fl, function.comp, sub_add_cancel, h, ←function.iterate_succ_apply' (f c)],
  apply local_equiv.left_inv _ (s.near_subset_chart (s.iter_stays_near r _)),
end

-- The basin of points that attract to a
def super.basin (s : super f d a) : set (ℂ × S) := {p : ℂ × S | ∃ n, (p.1, f p.1^[n] p.2) ∈ s.near}

-- s.basin is open
lemma super.is_open_preimage (s : super f d a) (n : ℕ)
    : is_open {p : ℂ × S | (p.1, f p.1^[n] p.2) ∈ s.near } :=
  is_open.preimage (continuous_fst.prod (s.continuous_iter continuous_fst continuous_snd)) s.is_open_near
lemma super.is_open_basin (s : super f d a) : is_open s.basin := begin
  simp only [super.basin, set_of_exists], exact is_open_Union (λ n, s.is_open_preimage n),
end

-- Anything in basin is eventually in near
lemma super.basin_stays (s : super f d a) (m : (c,z) ∈ s.basin)
    : ∀ᶠ n in at_top, (c, f c^[n] z) ∈ s.near := begin
  simp only [super.basin, set.mem_set_of] at m,
  rcases m with ⟨n,m⟩,
  rw filter.eventually_at_top, use n, intros k kn,
  rw [←nat.sub_add_cancel kn, function.iterate_add_apply],
  exact s.iter_stays_near m _,
end

-- Anything in basin attracts
lemma super.basin_attracts (s : super f d a) (m : (c,z) ∈ s.basin) : attracts (f c) z a := begin
  rcases m with ⟨n,m⟩, exact s.attracts m,
end
lemma super.basin_iff_attracts (s : super f d a) : (c,z) ∈ s.basin ↔ attracts (f c) z a := begin
  constructor, exact s.basin_attracts, intro h,
  rcases tendsto_at_top_nhds.mp h {z | (c,z) ∈ s.near} (s.mem_near c) (s.is_open_near.snd_preimage c) with ⟨n,h⟩, 
  use [n, h _ (le_refl _)],
end

-- f acting on and returning pairs
def super.fp (s : super f d a) : ℂ × S → ℂ × S := λ p : ℂ × S, (p.1, f p.1 p.2)
lemma super.fpa (s : super f d a) : holomorphic II II s.fp := λ _, holomorphic_at_fst.prod (s.fa _)
lemma super.fp1 (s : super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).1 = p.1 := begin
  simp only [super.fp], induction n with n h, simp only [function.iterate_zero_apply],
  simp only [function.iterate_succ_apply', h],
end
lemma super.fp2 (s : super f d a) (n : ℕ) (p : ℂ × S) : (s.fp^[n] p).2 = (f p.1^[n] p.2) := begin
  simp only [super.fp], induction n with n h, simp only [function.iterate_zero_apply],
  have c := s.fp1 n p, simp only [super.fp] at c,
  simp only [function.iterate_succ_apply', c, h],
end
 
-- bottcher_near on the manifold
def super.bottcher_near (s : super f d a) (c : ℂ) (z : S) : ℂ := 
  bottcher_near (s.fl c) d (ext_chart_at I a z - ext_chart_at I a a)
def super.bottcher_nearp (s : super f d a) : ℂ × S → ℂ := uncurry s.bottcher_near

-- s.bottcher_near is analytic
lemma super.bottcher_near_holomorphic (s : super f d a)
    : holomorphic_on II I (uncurry s.bottcher_near) s.near := begin
  intros p m,
  simp only [uncurry, super.bottcher_near],
  have e : (λ p : ℂ × S, bottcher_near (s.fl p.1) d (ext_chart_at I a p.2 - ext_chart_at I a a)) =
           (λ p : ℂ × ℂ, bottcher_near (s.fl p.1) d p.2) ∘
             (λ p : ℂ × S, (p.1, ext_chart_at I a p.2 - ext_chart_at I a a)) := rfl, 
  rw e, clear e,
  have h1 := (bottcher_near_analytic s.super_near_c _ (s.mem_near_to_near' m)).holomorphic_at II I,
  have h2 : holomorphic_at II II (λ p : ℂ × S, (p.1, ext_chart_at I a p.2 - ext_chart_at I a a)) p, {
    apply holomorphic_at_fst.prod, apply holomorphic_at.sub,
    exact (holomorphic_at.ext_chart_at (s.near_subset_chart m)).comp holomorphic_at_snd,
    exact holomorphic_at_const,
  },
  exact holomorphic_at.comp h1 h2,
end

-- bottcher_near after some iterations of f
def super.bottcher_near_iter (s : super f d a) (n : ℕ) : ℂ → S → ℂ := λ c z, s.bottcher_near c (f c^[n] z)
lemma super.bottcher_near_iter_holomorphic (s : super f d a) {n : ℕ} (r : (c, f c^[n] z) ∈ s.near)
    : holomorphic_at II I (uncurry (s.bottcher_near_iter n)) (c,z) := begin
  refine (s.bottcher_near_holomorphic _ _).curry_comp holomorphic_at_fst (s.holomorphic_iter _), exact r,
end

-- s.bottcher_near satisfies the defining equation
lemma super.bottcher_near_eqn (s : super f d a) (m : (c,z) ∈ s.near)
    : s.bottcher_near c (f c z) = (s.bottcher_near c z)^d := begin
  simp only [super.bottcher_near],
  have e : ext_chart_at I a (f c z) - ext_chart_at I a a =
           s.fl c (ext_chart_at I a z - ext_chart_at I a a) :=
    by simp only [function.comp, super.fl, fl, sub_add_cancel, local_equiv.left_inv _ (s.near_subset_chart m)],
  rw [e, bottcher_near_eqn (s.super_near_c.s (set.mem_univ c)) (s.mem_near_to_near' m)],
end

-- s.bottcher_near_eqn iterated
lemma super.bottcher_near_eqn_iter (s : super f d a) (m : (c,z) ∈ s.near) {n : ℕ} 
    : s.bottcher_near c (f c^[n] z) = (s.bottcher_near c z)^d^n := begin
  induction n with n h, simp only [function.iterate_zero_apply, pow_zero, pow_one],
  simp only [function.iterate_succ_apply', s.bottcher_near_eqn (s.iter_stays_near m n), h, ←pow_mul, ←pow_succ'],
end
 
-- The defining equation in terms of s.bottcher_nearp and s.fp
lemma super.bottcher_nearp_eqn (s : super f d a) (m : p ∈ s.near)
    : s.bottcher_nearp (s.fp p) = (s.bottcher_nearp p)^d := begin
  rcases p with ⟨c,z⟩, exact s.bottcher_near_eqn m, 
end
 
-- abs (s.bottcher_near c z) < 1
lemma super.bottcher_near_lt_one (s : super f d a) (m : (c,z) ∈ s.near) : abs (s.bottcher_near c z) < 1 :=
  by simp only [super.bottcher_near,
    bottcher_near_lt_one (s.super_near_c.s (set.mem_univ c)) (s.mem_near_to_near' m)]

-- s.bottcher_near = 0 only at a
lemma super.bottcher_near_eq_zero (s : super f d a) (m : (c,z) ∈ s.near) : s.bottcher_near c z = 0 ↔ z = a := begin
  simp only [super.bottcher_near], constructor, {
    intro za, contrapose za,
    apply bottcher_near_ne_zero (s.super_near_c.s (set.mem_univ _)) (s.mem_near_to_near' m),
    simp only [sub_ne_zero],
    exact (ext_chart_at I a).inj_on.ne (s.near_subset_chart m) (mem_ext_chart_source I a) za,
  }, {
    intro za, simp only [za, sub_self, bottcher_near_zero],
  },
end

-- bottcher_near a = 0
lemma super.bottcher_near_a (s : super f d a) : s.bottcher_near c a = 0 :=
  by simp only [super.bottcher_near, sub_self, bottcher_near_zero]

-- s.bottcher_near' ≠ 0 at 0
lemma super.bottcher_near_mfderiv_ne_zero (s : super f d a) (c : ℂ) : mfderiv I I (s.bottcher_near c) a ≠ 0 := begin
  apply mderiv_comp_ne_zero', {
    simp only [sub_self, mfderiv_eq_fderiv,
      (bottcher_near_monic (s.super_near_c.s (set.mem_univ c))).has_fderiv_at.fderiv],
    by_contradiction,
    have b := continuous_linear_map.ext_iff.mp h 1,
    simp only [continuous_linear_map.smul_right_apply, continuous_linear_map.one_apply, algebra.id.smul_eq_mul,
      mul_one, continuous_linear_map.zero_apply, one_ne_zero] at b,
    exact b,
  }, {
    have u : (λ z : S, ext_chart_at I a z - ext_chart_at I a a) =
              ext_chart_at I a - λ y : S, ext_chart_at I a a := rfl,
    rw [u, mfderiv_sub, mfderiv_const, sub_zero],
    exact ext_chart_at_mderiv_ne_zero a,
    exact (holomorphic_at.ext_chart_at (mem_ext_chart_source I a)).mdifferentiable_at,
    apply mdifferentiable_at_const,
  },
end

-- bottcher_near is invertible near any (c,a)
lemma super.bottcher_near_has_inv (s : super f d a) (c : ℂ)
    : ∃ bi : ℂ → ℂ → S, holomorphic_at II I (uncurry bi) (c,0) ∧
        (∀ᶠ p : ℂ × S in 𝓝 (c,a), bi p.1 (s.bottcher_near p.1 p.2) = p.2) ∧
        (∀ᶠ p : ℂ × ℂ in 𝓝 (c,0), s.bottcher_near p.1 (bi p.1 p.2) = p.2) := begin
  have h := complex_inverse_fun (s.bottcher_near_holomorphic _ (s.mem_near c)) (s.bottcher_near_mfderiv_ne_zero c),
  simp only [s.bottcher_near_a] at h, exact h,
end

-- The potential function if z reaches s.near after n iterations
def super.potential' (s : super f d a) (c : ℂ) (z : S) (n : ℕ) : ℝ :=
  (abs (s.bottcher_near c ((f c)^[n] z)))^((d : ℝ)^n)⁻¹

-- potential' doesn't depend on n, for large n
lemma super.potential_eq' (s : super f d a) {c : ℂ} {z : S} {n0 n1 : ℕ}
    (n0s : (c, f c^[n0] z) ∈ s.near) (n1s : (c, f c^[n1] z) ∈ s.near)
    : s.potential' c z n0 = s.potential' c z n1 := begin
  wlog n01 : n0 ≤ n1, exact (this s n1s n0s (le_of_lt (not_le.mp n01))).symm,
  clear n1s, rw ←nat.sub_add_cancel n01,
  have m : ∀ k, (c, f c^[n0+k] z) ∈ s.near, {
    intro k, rw nat.add_comm, simp only [function.iterate_add, s.iter_stays_near n0s k],
  },
  generalize hk : n1 - n0 = k, rw nat.add_comm, clear hk,
  induction k with k h, simp only [add_zero],
  simp only [nat.add_succ, function.iterate_succ', super.potential'],
  rw s.bottcher_near_eqn (m k),
  rw [pow_succ _ (n0 + k), mul_inv, complex.abs.map_pow, real.rpow_mul, ←real.rpow_nat_cast _ d],
  rw [←real.rpow_mul (complex.abs.nonneg _) _ d⁻¹, mul_inv_cancel (s.super_at_c.s (set.mem_univ c)).drz,
    real.rpow_one],
  exact h, bound,
end

-- The potential function measures how quickly z attracts to a under f c.
def super.potential (s : super f d a) (c : ℂ) (z : S) : ℝ :=
  @dite _ (∃ n, (c, f c^[n] z) ∈ s.near) (classical.dec _)
    (λ q, s.potential' c z (@nat.find _ (classical.dec_pred _) q))
    (λ _, 1)

-- potential = potential' for large n
lemma super.potential_eq (s : super f d a) {k : ℕ} (ks : (c, f c^[k] z) ∈ s.near)
    : s.potential c z = s.potential' c z k := begin
  have h := exists.intro k ks,
  simp only [super.potential, h, dif_pos],
  exact s.potential_eq' (@nat.find_spec _ (classical.dec_pred _) h) ks,
end

-- abs bottcher_near in terms of potential
lemma super.abs_bottcher_near (s : super f d a) {n : ℕ} (r : (c, f c^[n] z) ∈ s.near)
    : abs (s.bottcher_near c (f c^[n] z)) = s.potential c z ^ d^n := begin
  simp only [s.potential_eq r, super.potential'],
  rw [←real.rpow_nat_cast, ←real.rpow_mul (complex.abs.nonneg _), nat.cast_pow, inv_mul_cancel, real.rpow_one],
  exact pow_ne_zero _ (nat.cast_ne_zero.mpr s.d0),
end

-- potential a = 0
lemma super.potential_a (s : super f d a) : s.potential c a = 0 := begin
  have r : (c, f c^[0] a) ∈ s.near := by simp only [function.iterate_zero, s.mem_near, id.def],
  simp only [s.potential_eq r, super.potential', function.iterate_zero, id.def, s.bottcher_near_a,
    complex.abs.map_zero, pow_zero, inv_one, real.rpow_one],
end

-- If z doesn't reach near, potential = 1
lemma super.potential_eq_one (s : super f d a) (a : ∀ n, (c, f c^[n] z) ∉ s.near) : s.potential c z = 1 :=
  by simp only [super.potential, not_exists.mpr a, not_false_iff, dif_neg, and_false]

-- If z reaches near, potential < 1
lemma super.potential_lt_one (s : super f d a) (a : ∃ n, (c, f c^[n] z) ∈ s.near) : s.potential c z < 1 := begin
  simp only [super.potential, a, dif_pos, super.potential'],
  refine real.rpow_lt_one (complex.abs.nonneg _) _ (by bound [s.dp]),
  exact s.bottcher_near_lt_one (@nat.find_spec _ (classical.dec_pred _) a),
end

-- z reaches near iff potential < 1
lemma super.potential_lt_one_iff (s : super f d a) : s.potential c z < 1 ↔ ∃ n, (c, f c^[n] z) ∈ s.near := begin
  refine ⟨_, s.potential_lt_one⟩,
  intro h, contrapose h, simp only [not_exists] at h,
  simp only [s.potential_eq_one h, lt_self_iff_false, not_false_iff],
end

-- potential ≤ 1
lemma super.potential_le_one (s : super f d a) : s.potential c z ≤ 1 := begin
  by_cases a : ∃ n, (c, f c^[n] z) ∈ s.near,
  exact le_of_lt (s.potential_lt_one a),
  exact le_of_eq (s.potential_eq_one (not_exists.mp a)),
end

-- potential ≥ 0
lemma super.potential_nonneg (s : super f d a) : 0 ≤ s.potential c z := begin
  by_cases r : ∃ n, (c, f c^[n] z) ∈ s.near,
  rcases r with ⟨n,r⟩, simp only [s.potential_eq r, super.potential'], bound,
  simp only [s.potential_eq_one (not_exists.mp r), zero_le_one],
end 

-- The defining equation of potential
lemma super.potential_eqn (s : super f d a) : s.potential c (f c z) = s.potential c z ^ d := begin
  by_cases a : ∃ n, (c, f c^[n] z) ∈ s.near, {
    rcases a with ⟨n,a⟩, 
    have a' : (c, f c^[n] (f c z)) ∈ s.near :=
      by simp only [←function.iterate_succ_apply, function.iterate_succ', s.stays_near a],
    simp only [s.potential_eq a, s.potential_eq a', super.potential', ←function.iterate_succ_apply,
      function.iterate_succ', s.bottcher_near_eqn a, complex.abs.map_pow, ←real.rpow_nat_cast,
      ←real.rpow_mul (complex.abs.nonneg _), mul_comm],
  }, {
    have a' : ∀ n, (c, f c^[n] (f c z)) ∉ s.near, {
      contrapose a, simp only [not_forall, not_not, ←function.iterate_succ_apply] at a ⊢,
      rcases a with ⟨n,a⟩, use [n+1, a],
    },
    simp only [s.potential_eq_one (not_exists.mp a), s.potential_eq_one a', one_pow],
  },
end

-- The potential equation, iterated
lemma super.potential_eqn_iter (s : super f d a) (n : ℕ)
    : s.potential c (f c^[n] z) = s.potential c z ^ (d^n) := begin
  induction n with n h, simp only [function.iterate_zero, id.def, pow_zero, pow_one],
  simp only [function.iterate_succ', super.potential_eqn, h, ←pow_mul, ←pow_succ'],
end

-- Our standard iteration is analytic
lemma super.iter_holomorphic' (s : super f d a) (n : ℕ)
    : holomorphic II I (λ p : ℂ × S, f p.1^[n] p.2) := begin
  intro p, induction n with n h, simp [function.iterate_zero, holomorphic_at_snd],
  simp only [function.iterate_succ', function.comp],
  exact (s.fa _).curry_comp holomorphic_at_fst h,
end
lemma super.iter_holomorphic (s : super f d a) (n : ℕ)
    : holomorphic II II (λ p : ℂ × S, (p.1, f p.1^[n] p.2)) := begin
  intro p, apply holomorphic_at_fst.prod, apply s.iter_holomorphic',
end

-- potential is continuous if we attract
lemma continuous_at.potential_of_reaches (s : super f d a) (a : ∃ n, (c, f c^[n] z) ∈ s.near)
    : continuous_at (uncurry s.potential) (c,z) := begin
  rcases a with ⟨n,a⟩, 
  have e : uncurry s.potential =ᶠ[𝓝 (c,z)] (λ p : ℂ × S, s.potential' p.1 p.2 n), {
    have a' : ∀ᶠ p : ℂ × S in 𝓝 (c,z), (p.1, f p.1^[n] p.2) ∈ s.near :=
      (s.iter_holomorphic n _).continuous_at.eventually_mem s.is_open_near a,
    refine a'.mp (eventually_of_forall (λ p h, _)),
    funext p, simp only [uncurry, s.potential_eq h],
  },
  simp only [continuous_at_congr e, super.potential'],
  refine continuous_at.rpow _ continuous_at_const _, {
    apply complex.continuous_abs.continuous_at.comp,
    refine ((s.bottcher_near_holomorphic _ _).comp (s.iter_holomorphic n (c,z))).continuous_at,
    exact a,
  }, {
    right, bound [s.dp],
  },
end

-- s.potential = 0 exactly on s.preimages
lemma super.potential_eq_zero (s : super f d a) : s.potential c z = 0 ↔ ∃ n, f c^[n] z = a := begin
  constructor, {
    intro h,
    by_cases r : ∃ n, (c, f c^[n] z) ∈ s.near, {
      rcases r with ⟨n,r⟩,
      simp only [s.potential_eq r, super.potential', real.rpow_eq_zero_iff_of_nonneg (complex.abs.nonneg _),
        complex.abs.eq_zero, s.bottcher_near_eq_zero r] at h,
      use [n, h.1],
    }, {
      rw not_exists at r, simp only [s.potential_eq_one r, one_ne_zero] at h, exfalso, exact h,
    },
  }, {
    intro p, rcases p with ⟨n,p⟩, 
    have nz : d^n > 0 := pow_pos s.dp _,
    rw [←pow_eq_zero_iff nz, ←s.potential_eqn_iter n, p, s.potential_a],
    apply_instance,
  },
end

-- potential is upper semicontinuous unconditionally
lemma upper_semicontinuous.potential (s : super f d a) : upper_semicontinuous (uncurry s.potential) := begin
  rintro ⟨c,z⟩,
  by_cases r : ∃ n, (c, f c^[n] z) ∈ s.near, {
    exact (continuous_at.potential_of_reaches s r).upper_semicontinuous_at,
  }, {
    simp only [uncurry, upper_semicontinuous_at, s.potential_eq_one (not_exists.mp r)],
    exact λ y y1, eventually_of_forall (λ p, lt_of_le_of_lt s.potential_le_one y1),
  },
end

-- I only know how to prove that potential is everywhere continuous using an additional assumption.  The
-- most general version is that the set of preimages is closed, but for the Mandelbrot set we have the
-- simpler case that a is the only preimage of a.
@[class] structure one_preimage (s : super f d a) : Prop :=
  (eq_a : ∀ c z, f c z = a → z = a)
lemma super.preimage_eq' (s : super f d a) [o : one_preimage s] : f c z = a ↔ z = a := begin
  have e := o.eq_a c z, refine ⟨e,_⟩, intro e, simp only [e, s.f0],
end
lemma super.preimage_eq (s : super f d a) [o : one_preimage s] {n : ℕ} : f c^[n] z = a ↔ z = a := begin
  induction n with n h, simp only [function.iterate_zero_apply],
  simp only [function.iterate_succ_apply', s.preimage_eq', h],
end
lemma super.potential_eq_zero_of_one_preimage (s : super f d a) [one_preimage s]
    (c : ℂ) : s.potential c z = 0 ↔ z = a := begin
  constructor, {
    intro h, rw s.potential_eq_zero at h, rcases h with ⟨n,h⟩, rw s.preimage_eq at h, exact h, 
  }, {
    intros h, simp only [h, s.potential_a],
  },
end
lemma super.potential_ne_zero (s : super f d a) [one_preimage s] (c : ℂ) : s.potential c z ≠ 0 ↔ z ≠ a :=
  by simp only [ne.def, s.potential_eq_zero_of_one_preimage]
lemma super.potential_pos (s : super f d a) [one_preimage s] (c : ℂ) : 0 < s.potential c z ↔ z ≠ a := begin
  rw ←s.potential_ne_zero c, use [ne_of_gt, λ ne, ne.symm.lt_of_le s.potential_nonneg],
end

-- f can't get from far from (c,a) to arbitrarily close to (c,a) in one step
lemma super.no_jump (s : super f d a) [one_preimage s] (c : ℂ) (n : set (ℂ × S)) (no : is_open n) (na : (c,a) ∈ n)
    : ∀ᶠ p : ℂ × S in 𝓝 (c,a), ∀ q, p = s.fp q → q ∈ n := begin
  have h : ∀ q : ℂ × S, f q.1 q.2 = a → q.2 = a := λ _, by simp only [s.preimage_eq', imp_self],
  contrapose h,
  simp only [filter.not_eventually, not_forall, exists_prop] at h,
  set t := s.fp '' ((closed_ball c 1 ×ˢ univ) ∩ nᶜ),
  have tc : is_closed t, {
    refine (is_compact.image _ s.fpa.continuous).is_closed,
    exact ((is_compact_closed_ball _ _).prod is_compact_univ).inter_right no.is_closed_compl,
  },
  have th : ∃ᶠ p in 𝓝 (c,a), p ∈ t, {
    have mb : ∀ᶠ p : ℂ × S in 𝓝 (c,a), p.1 ∈ closed_ball c 1 :=
      continuous_at_fst.eventually_mem_nhd (metric.closed_ball_mem_nhds _ zero_lt_one),
    refine (h.and_eventually mb).mp (eventually_of_forall (λ p i, _)), rcases i with ⟨⟨q,qp,m⟩,b⟩,
    simp only [prod.ext_iff] at qp, simp only [qp.1] at b,
    simp only [set.mem_image, set.mem_compl_iff, set.mem_inter_iff, set.mem_prod_eq, set.mem_univ, and_true,
      prod.ext_iff],
    use [q,⟨b,m⟩,qp.1.symm,qp.2.symm],
  },
  have m := th.mem_of_closed tc,
  rcases (set.mem_image _ _ _).mp m with ⟨p,m,pa⟩,
  simp only [super.fp, prod.mk.inj_iff] at pa,
  simp only [not_forall], use [p,pa.2],
  contrapose m, simp only [not_not, set.mem_compl_iff] at ⊢ m,
  rw [←@prod.mk.eta _ _ p, pa.1, m],
  simp only [set.mem_inter_iff, set.prod_mk_mem_set_prod_eq, metric.mem_closed_ball, dist_self, zero_le_one,
    set.mem_univ, set.mem_compl_iff, true_and, set.not_not_mem, not_not, na],
end

-- A barrier is a compact, annular region around a (but not containing it) such that
-- outside points must pass through it to reach a.
structure barrier (s : super f d a) (c : ℂ) (n t : set (ℂ × S)) : Prop :=
  (compact : is_compact t)
  (tn : t ⊆ n)
  (near : t ⊆ s.near)
  (hole : ∀ e, (e,a) ∉ t)
  (barrier : ∀ᶠ e in 𝓝 c, ∀ z, (e,z) ∉ n → attracts (f e) z a → ∃ n, (e, f e^[n] z) ∈ t)

-- f can't get from far from (c,a) to close to (c,a) without passing through a barrier
lemma super.barrier (s : super f d a) [one_preimage s] (n : set (ℂ × S)) (no : is_open n) (na : (c,a) ∈ n)
    : ∃ t : set (ℂ × S), barrier s c n t := begin
  set n' := n ∩ s.near,
  have nn' : n' ∈ 𝓝 (c,a) := filter.inter_mem (no.mem_nhds na) (s.is_open_near.mem_nhds (s.mem_near c)), 
  rcases (filter.has_basis_iff.mp (compact_basis_nhds (c,a)) n').mp nn' with ⟨u,⟨un,uc⟩,us⟩,
  simp only [set.subset_inter_iff] at us,
  rcases eventually_nhds_iff.mp (s.no_jump c (interior u) is_open_interior (mem_interior_iff_mem_nhds.mpr un))
    with ⟨i,ih,io,ia⟩,
  rcases mem_nhds_prod_iff'.mp (filter.inter_mem un (io.mem_nhds ia)) with ⟨i0,i1,i0o,i0m,i1o,i1m,ii⟩,
  simp only [set.subset_inter_iff] at ii,
  set t := u \ (univ ×ˢ i1),
  have ta : ∀ e, (e,a) ∉ t := λ e, set.not_mem_diff_of_mem (set.mk_mem_prod (set.mem_univ _) i1m),
  use t, refine ⟨uc.diff (is_open_univ.prod i1o), trans (set.diff_subset _ _) us.1,
    trans (set.diff_subset _ _) us.2, ta, _⟩,
  rw eventually_nhds_iff, use i0, refine ⟨_, i0o, i0m⟩,
  intros e em z zm za,
  rcases tendsto_at_top_nhds.mp za i1 i1m i1o with ⟨m,mh⟩,
  have en : ∃ n, f e^[n] z ∈ i1 := ⟨m, mh m (le_refl _)⟩,
  set n := @nat.find _ (classical.dec_pred _) en,
  use n-1,
  have ni1 : (f e^[n] z) ∈ i1 := @nat.find_spec _ (classical.dec_pred _) en,
  have n0 : n ≠ 0, {
    contrapose zm, simp only [set.not_not_mem],
    simp only [nat.sub, ne.def, nat.find_eq_zero, function.iterate_zero, id.def, set.not_not_mem] at zm,
    exact us.1 (ii.1 (set.mk_mem_prod em zm)),
  },
  have nt : (f e^[n-1] z) ∉ i1 := @nat.find_min _ (classical.dec_pred _) en _ (nat.pred_lt n0),
  apply set.mem_diff_of_mem, {
    apply interior_subset, apply ih (e, f e^[n] z) (ii.2 (set.mk_mem_prod em ni1)),
    simp only [super.fp], rw ←function.iterate_succ_apply' (f e) (n-1),
    simp only [nat.succ_eq_add_one, nat.sub_add_cancel (nat.one_le_of_lt (nat.pos_of_ne_zero n0))],
  }, {
    contrapose nt,
    simp only [set.prod_mk_mem_set_prod_eq, not_and, not_forall, set.not_not_mem, exists_prop] at nt ⊢,
    exact nt.2,
  },
end

-- potential is large on barriers (because they are compact)
lemma barrier.potential_large {s : super f d a} [one_preimage s] {n t : set (ℂ × S)} (b : barrier s c n t)
    : ∃ r : ℝ, r > 0 ∧ ∀ e z, (e,z) ∈ t → r ≤ s.potential e z := begin
  by_cases t0 : t = ∅, {
    use [1, zero_lt_one], simp only [t0, gt_iff_lt, set.mem_empty_iff_false, is_empty.forall_iff, forall_const,
      implies_true_iff, and_true],
  },
  simp only [←ne.def, ←set.nonempty_iff_ne_empty] at t0,
  have pc : continuous_on (uncurry s.potential) t, {
    refine continuous_on.mono _ b.near,
    rintros ⟨c,z⟩ m, apply continuous_at.continuous_within_at,
    apply continuous_at.potential_of_reaches s, use 0, simpa only [function.iterate_zero_apply],
  },
  rcases pc.compact_min b.compact t0 with ⟨⟨e,z⟩,ps,pm⟩,
  use s.potential e z, constructor, {
    have h := b.hole e, contrapose h, simp only [not_lt] at h,
    have h' := le_antisymm h s.potential_nonneg,
    simp only [s.potential_eq_zero, s.preimage_eq, exists_const] at h',
    simp only [not_not, ←h', ps],
  }, {
    intros e z m, simp only [is_min_on_iff, uncurry] at ⊢ pm, exact pm _ m,
  },
end

-- The first n preimages of a barrier
def barrier.fast {s : super f d a} {n t : set (ℂ × S)} (b : barrier s c n t) (m : ℕ) : set (ℂ × S) :=
  ⋃ k : fin m, (λ p : ℂ × S, (p.1, f p.1^[k] p.2)) ⁻¹' t
lemma barrier.closed_fast {s : super f d a} {n t : set (ℂ × S)} (b : barrier s c n t) (m : ℕ)
    : is_closed (b.fast m) := begin
  apply is_closed_Union, intro k, refine is_closed.preimage _ b.compact.is_closed,
  apply continuous_fst.prod, generalize hn : (k : ℕ) = n, clear' k hn, induction n with n h,
  simp only [function.iterate_zero_apply], exact continuous_snd,
  simp only [function.iterate_succ_apply'], exact s.fa.continuous.comp (continuous_fst.prod h),
end
lemma barrier.mem_fast {s : super f d a} {n t : set (ℂ × S)} (b : barrier s c n t) {m : ℕ}
    {e : ℂ} {z : S} : (e,z) ∈ b.fast m ↔ ∃ n, n < m ∧ (e, f e^[n] z) ∈ t := begin
  simp only [barrier.fast, set.mem_Union, set.mem_preimage], constructor,
  intro h, rcases h with ⟨n,h⟩, use [n, fin.is_lt _, h],
  intro h, rcases h with ⟨n,nm,h⟩, use [⟨n,nm⟩, h],
end
lemma barrier.fast_reaches {s : super f d a} {n t : set (ℂ × S)} (b : barrier s c n t) {m : ℕ}
    {e : ℂ} {z : S} (q : (e,z) ∈ b.fast m) : ∃ n, (e, f e^[n] z) ∈ s.near := begin
  rw b.mem_fast at q, rcases q with ⟨n,nm,q⟩, use [n, b.near q],
end 

-- potential is also lower semicontinuous (and thus continuous) if one_preimage s
lemma continuous.potential (s : super f d a) [one_preimage s] : continuous (uncurry s.potential) := begin
  -- Reduce to showing that nearby bounded potential means reaches
  refine continuous_iff_lower_upper_semicontinuous.mpr ⟨_, upper_semicontinuous.potential s⟩, 
  rintro ⟨c,z⟩,
  by_cases re : ∃ n, (c, f c^[n] z) ∈ s.near,
  exact (continuous_at.potential_of_reaches s re).lower_semicontinuous_at,
  simp only [not_exists] at re,
  intros y y1,
  simp only [continuous_at, uncurry, s.potential_eq_one re] at ⊢ y1,
  contrapose re,
  simp only [filter.not_eventually, not_lt] at re,
  simp only [not_forall, not_not] at re ⊢,
  -- Construct a barrier separating (c,z) from (c,a)
  by_cases za : z = a, { use 0, simp only [za, function.iterate_zero_apply, s.mem_near c] }, 
  have sn : {(c,a)}ᶜ ∈ 𝓝 (c,z) :=
    compl_singleton_mem_nhds (by simp only [za, ne.def, prod.mk.inj_iff, and_false, not_false_iff]),
  rcases (filter.has_basis_iff.mp (compact_basis_nhds (c,z)) {(c,a)}ᶜ).mp sn with ⟨u,⟨un,uc⟩,ua⟩,
  simp only [set.subset_compl_singleton_iff] at ua,
  rcases s.barrier uᶜ uc.is_closed.is_open_compl (set.mem_compl ua) with ⟨t,b⟩,
  rcases b.potential_large with ⟨r,rp,rt⟩,
  -- potential ≤ y → reaches the barrier quickly
  have en : ∃ n, ∀ᶠ e in 𝓝 c, ∀ z, (e,z) ∈ u → s.potential e z ≤ y → (e,z) ∈ b.fast n, {
    -- Find n s.t. y ^ (d^n) < r
    rcases exists_pow_lt_of_lt_one rp y1 with ⟨k,ky⟩,
    rcases filter.exists_le_of_tendsto_at_top (nat.tendsto_pow_at_top_at_top_of_one_lt s.d1) 0 k with ⟨n,np,nk⟩,
    simp only at nk,
    use n,
    -- Our upper bound on potential e z, plus on our lower bound on t, implies that z reaches near quickly
    refine b.barrier.mp (eventually_of_forall (λ e h z m py, _)),
    rcases h z (set.not_mem_compl_iff.mpr m) _ with ⟨o,oh⟩, {
      by_cases no : n ≤ o, {
        have pyo : s.potential e z ^ d^o ≤ y ^ d^o := by bound [s.potential_nonneg],
        rw ←s.potential_eqn_iter o at pyo,
        have ryo : r ≤ y^d^o := trans (rt _ _ oh) pyo,
        have kdo : k ≤ d^o := trans nk (nat.pow_le_pow_of_le_right s.dp no),
        have ryk : r ≤ y^k := trans ryo (pow_le_pow_of_le_one (trans s.potential_nonneg py) (le_of_lt y1) kdo),
        linarith,
      }, {
        simp only [not_le] at no, rw b.mem_fast, use [o,no,oh],
      },
    }, {
      by_cases r : ∃ n, (e, f e^[n] z) ∈ s.near, 
      rcases r with ⟨n,r⟩, exact s.attracts r,
      simp only [not_exists] at r, rw s.potential_eq_one r at py, linarith,
    },
  },
  -- Now that we've bounded n, (c,z) must reach near
  rcases en with ⟨n,h⟩,
  rcases eventually_nhds_iff.mp h with ⟨v,vh,vo,vc⟩,
  have ev : ∀ᶠ p : ℂ × S in 𝓝 (c,z), p ∈ u ∩ (v ×ˢ univ), {
    simp only [filter.eventually_iff, set.set_of_mem_eq],
    exact filter.inter_mem un ((vo.prod is_open_univ).mem_nhds (set.mk_mem_prod vc (set.mem_univ _))),
  },
  have ef : ∃ᶠ p in 𝓝 (c,z), p ∈ b.fast n, {
    refine (re.and_eventually ev).mp (eventually_of_forall _),
    rintros ⟨e,z⟩ ⟨zy,m⟩, simp only [set.mem_inter_iff, set.mem_prod, set.mem_univ, and_true] at m,
    exact vh e m.2 z m.1 zy,
  },
  rcases b.mem_fast.mp (ef.mem_of_closed (b.closed_fast _)) with ⟨n,_,r⟩,
  use [n, b.near r],
end

-- potential levelsets form a neighborhood basis at a
lemma super.potential_basis (s : super f d a) [one_preimage s] (c : ℂ) {t : set S} (n : t ∈ 𝓝 a)
    : ∃ p, 0 < p ∧ {z | s.potential c z < p} ⊆ t := begin
  wlog o : is_open t, {
    rcases mem_nhds_iff.mp n with ⟨t',tt,o,m⟩,
    rcases this c (o.mem_nhds m) o with ⟨p,pp,sub⟩,
    use [p, pp, trans sub tt],
  },
  by_cases ne : tᶜ = ∅, { use [1, zero_lt_one], simp only [compl_empty_iff] at ne, rw ne, exact subset_univ _ },
  replace ne := set.nonempty.image (s.potential c) (nonempty_iff_ne_empty.mpr ne),
  have pos : ∀ p : ℝ, p ∈ s.potential c '' tᶜ → 0 ≤ p, {
    intros p m, simp only [mem_image] at m, rcases m with ⟨z,_,e⟩, rw ←e, exact s.potential_nonneg,
  },
  have below : bdd_below (s.potential c '' tᶜ) := bdd_below_def.mpr ⟨0,pos⟩, 
  generalize hq : Inf (s.potential c '' tᶜ) = q,
  have qt : ∀ z, s.potential c z < q → z ∈ t, {
    intros z i, contrapose i, simp only [not_lt, ←hq], apply cInf_le below,
    simp only [mem_image], use [z,i],
  },
  have qp : 0 < q, {
    simp only [←hq],
    have mc := cInf_mem_closure ne below,
    rw is_closed.closure_eq at mc, {
      simp only [mem_image] at mc, rcases mc with ⟨z,m,e⟩,
      rw ←e, contrapose m,
      replace m := le_antisymm (not_lt.mp m) s.potential_nonneg,
      rw s.potential_eq_zero_of_one_preimage at m, simp only [m, not_mem_compl_iff],
      exact mem_of_mem_nhds n,
    }, {
      exact (o.is_closed_compl.is_compact.image (continuous.potential s).in2).is_closed,
    },
  },
  use [q,qp,qt],
end 

-- f is locally noncritical near (but not at) a.
-- This is a depressingly long proof for a very simple conceptual argument.
lemma super.f_noncritical_near_a (s : super f d a) (c : ℂ)
    : ∀ᶠ p : ℂ × S in 𝓝 (c,a), critical (f p.1) p.2 ↔ p.2 = a := begin
  have t : continuous_at (λ p : ℂ × S, (p.1, ext_chart_at I a p.2 - ext_chart_at I a a)) (c,a), {
    refine continuous_at_fst.prod (continuous_at.sub _ continuous_at_const),
    exact (continuous_at_ext_chart_at I a).comp_of_eq continuous_at_snd rfl,
  },
  simp only [continuous_at, sub_self] at t,
  apply (in_chart_critical (s.fa (c,a))).mp,
  apply (t.eventually (df_ne_zero s.super_near_c (set.mem_univ c))).mp,
  have am := mem_ext_chart_source I a,
  have em := ((is_open_ext_chart_at_source I a).eventually_mem am).prod_inr (𝓝 c),
  simp only [←nhds_prod_eq] at em, apply em.mp,
  have ezm : ∀ᶠ p : ℂ × S in 𝓝 (c,a), f p.1 p.2 ∈ (ext_chart_at I a).source, {
    apply (s.fa _).continuous_at.eventually_mem (is_open_ext_chart_at_source I a),
    simp only [uncurry, s.f0, mem_ext_chart_source I a],
  },
  apply ezm.mp,
  apply eventually_of_forall, clear t em,
  rintros ⟨e,z⟩ ezm zm d0 m0, simp only at ⊢ ezm zm d0 m0,
  simp only [super.fl, fl, sub_eq_zero, (local_equiv.inj_on _).eq_iff zm am] at d0,
  simp only [critical, m0, in_chart, ←d0], clear m0 d0,
  generalize hg : (λ w, ext_chart_at I (f c a) (f e (((ext_chart_at I a).symm) w))) = g,
  have hg' : ext_chart_at I a ∘ f e ∘ (ext_chart_at I a).symm = g, { rw ←hg, simp only [function.comp, s.f0], },
  rw hg', clear hg', rw iff.comm,
  have dg : differentiable_at ℂ g (ext_chart_at I a z), {
    rw ←hg, apply analytic_at.differentiable_at, apply holomorphic_at.analytic_at I I, simp only [s.f0],
    apply (holomorphic_at.ext_chart_at _).comp, apply (s.fa _).in2.comp,
    exact holomorphic_at.ext_chart_at_symm (local_equiv.map_source _ zm),
    simp only [local_equiv.left_inv _ zm, s.f0], exact ezm,
  },
  have d0 : ∀ z, differentiable_at ℂ (λ z, z - ext_chart_at I a a) z :=
    λ z, differentiable_at_id.sub (differentiable_at_const _),
  have d1 : differentiable_at ℂ (g ∘ λ (z : ℂ), z + ext_chart_at I a a)
      (ext_chart_at I a z - ext_chart_at I a a), {
    apply differentiable_at.comp, simp only [sub_add_cancel, dg],
    exact differentiable_at_id.add (differentiable_at_const _),
  },
  simp only [deriv.comp _ (d0 _) d1, deriv_sub_const, deriv_id''],
  rw deriv.comp _ _ _,
  simp only [deriv_add_const, deriv_id'', mul_one, sub_add_cancel],
  simp only [sub_add_cancel, dg], exact differentiable_at_id.add (differentiable_at_const _),
end

-- Critical points that are not a are closed (because a is an isolated critical point w.r.t. z)
lemma super.is_closed_critical_not_a (s : super f d a)
    : is_closed {p : ℂ × S | critical (f p.1) p.2 ∧ p.2 ≠ a} := begin
  rw ←is_open_compl_iff, rw is_open_iff_eventually, rintros ⟨c,z⟩ m, 
  by_cases za : z = a, {
    rw za, refine (s.f_noncritical_near_a c).mp (eventually_of_forall _), rintros ⟨e,w⟩ h,
    simp only [mem_compl_iff, mem_set_of, not_and, not_not] at ⊢ h, exact h.1,
  }, {
    have o := is_open_iff_eventually.mp (is_open_noncritical s.fa),
    simp only [za, mem_compl_iff, mem_set_of, not_and, not_not, imp_false] at m o ⊢,
    refine (o (c,z) m).mp (eventually_of_forall _), rintros ⟨e,w⟩ a b, exfalso, exact a b,
  },
end

-- If z ∈ s.basin, iterating enough takes us to a noncritical point of bottcher_near
lemma super.eventually_noncritical (s : super f d a) (m : (c,z) ∈ s.basin)
    : ∀ᶠ n in at_top, mfderiv I I (s.bottcher_near c) (f c^[n] z) ≠ 0 :=
  (s.basin_attracts m).eventually (mfderiv_ne_zero_eventually
    (s.bottcher_near_holomorphic _ (s.mem_near c)).in2 (s.bottcher_near_mfderiv_ne_zero c))

-- bottcher_near_iter is noncritical given noncriticality of the two parts
lemma super.bottcher_near_iter_mfderiv_ne_zero (s : super f d a)
    (b0 : mfderiv I I (s.bottcher_near c) (f c^[n] z) ≠ 0) (f0 : ¬precritical (f c) z)
    : mfderiv I I (s.bottcher_near_iter n c) z ≠ 0 := begin
  apply mderiv_comp_ne_zero' b0, contrapose f0, simp only [not_not] at ⊢ f0, exact critical_iter s.fa.in2 f0,
end

-- f c^[n] is nontrivial at a
lemma super.iter_nontrivial_a (s : super f d a)
    : nontrivial_holomorphic_at (λ z, f c^[n] z) a := begin
  induction n with n h, simp only [function.iterate_zero_apply], apply nontrivial_holomorphic_at_id,
  simp only [function.iterate_succ_apply'], refine nontrivial_holomorphic_at.comp _ h,
  simp only [s.iter_a], exact s.f_nontrivial c,
end

-- s.bottcher_near_iter is nontrivial at a
lemma super.bottcher_near_iter_nontrivial_a (s : super f d a)
    : nontrivial_holomorphic_at (s.bottcher_near_iter n c) a := begin
  have b : nontrivial_holomorphic_at (s.bottcher_near c) (f c^[n] a), {
    simp only [s.iter_a],
    exact nontrivial_holomorphic_at_of_mfderiv_ne_zero (s.bottcher_near_holomorphic _ (s.mem_near c)).in2
      (s.bottcher_near_mfderiv_ne_zero c),
  },
  exact b.comp s.iter_nontrivial_a,
end

-- Fix c, and let p < 1.  Then u = s.potential c ⁻¹' Icc 0 p is closed, and thus compact, and thus there
-- is a fixed n s.t. f c^[n] '' u ⊆ s.near.  This lets us work with fixed n more of the time.
def super.is_nice_n (s : super f d a) (c : ℂ) (p : ℝ) (n : ℕ) :=
  ∀ z, s.potential c z ≤ p → (c, f c^[n] z) ∈ s.near ∧
    ∀ k, n ≤ k → mfderiv I I (s.bottcher_near c) (f c^[k] z) ≠ 0
lemma super.is_nice_zero (s : super f d a) (c : ℂ) [one_preimage s] : s.is_nice_n c 0 0 := begin
  intros z zp,
  have za := le_antisymm zp s.potential_nonneg, simp only [s.potential_eq_zero_of_one_preimage] at za,
  rw [za, function.iterate_zero_apply], use s.mem_near c,
  intros k k0, rw s.iter_a, exact s.bottcher_near_mfderiv_ne_zero c,
end
lemma super.is_nice_n_mono (s : super f d a) {c : ℂ} {p : ℝ} {n0 n1 : ℕ}
    (nice : s.is_nice_n c p n0) (n01 : n0 ≤ n1) : s.is_nice_n c p n1 := begin
  intros z zp, rcases nice z zp with ⟨m,nc⟩,
  use [s.iter_stays_near' m n01, λ k n1k, nc k (trans n01 n1k)],
end
lemma super.has_nice_n (s : super f d a) (c : ℂ) {p : ℝ} (p1 : p < 1) [one_preimage s]
    : ∃ n, s.is_nice_n c p n := begin
  have et : ∀ᶠ z in 𝓝 a, (c,z) ∈ s.near ∧ mfderiv I I (s.bottcher_near c) z ≠ 0, {
    apply (mfderiv_ne_zero_eventually (s.bottcher_near_holomorphic _ (s.mem_near c)).in2
      (s.bottcher_near_mfderiv_ne_zero c)).mp,
    apply ((s.is_open_near.snd_preimage c).eventually_mem (s.mem_near c)).mp,
    refine (eventually_of_forall (λ z m nc, _)), use [m,nc],
  },
  rcases et.exists_mem with ⟨t,m,h⟩,
  rcases s.potential_basis c m with ⟨q,qp,qt⟩, clear et m,
  rcases exists_pow_lt_of_lt_one qp p1 with ⟨n,pq⟩,
  use n, intros z m,
  replace m : ∀ k, n ≤ k → s.potential c (f c^[k] z) < q, {
    intros k nk, refine lt_of_le_of_lt _ pq, simp only [s.potential_eqn_iter],
    have dn := le_of_lt (nat.lt_pow_self s.d1 k),
    apply trans (pow_le_pow_of_le_one s.potential_nonneg s.potential_le_one dn),
    refine trans (pow_le_pow_of_le_left s.potential_nonneg m _) _,
    exact pow_le_pow_of_le_one (trans s.potential_nonneg m) (le_of_lt p1) nk,
  },
  use [(h _ (qt (m n (le_refl _)))).1, λ k nk, (h _ (qt (m k nk))).2],
end
def super.np (s : super f d a) (c : ℂ) (p : ℝ) : ℕ :=
  @dite _ (p < 1 ∧ one_preimage s) (classical.dec _)
    (λ q, @nat.find _ (classical.dec_pred _) (@super.has_nice_n _ _ _ _ _ _ _ _ s c p q.1 q.2))
    (λ _, 0)
lemma super.nice_np (s : super f d a) (c : ℂ) {p : ℝ} (p1 : p < 1) [op : one_preimage s]
    : s.is_nice_n c p (s.np c p) := begin
  have q : p < 1 ∧ one_preimage s := ⟨p1,op⟩, 
  simp only [super.np, q, true_and, dif_pos],
  exact @nat.find_spec _ (classical.dec_pred _) (s.has_nice_n c p1),
end
lemma super.np_zero (s : super f d a) (c : ℂ) [op : one_preimage s] : s.np c 0 = 0 :=
  by simp only [super.np, zero_lt_one, op, true_and, dif_pos, nat.find_eq_zero, s.is_nice_zero]
lemma super.np_mono (s : super f d a) (c : ℂ) {p0 p1 : ℝ} (le : p0 ≤ p1) (p11 : p1 < 1) [op : one_preimage s]
    : s.np c p0 ≤ s.np c p1 := begin
  have p01 : p0 < 1 := lt_of_le_of_lt le p11,
  have e : s.np c p0 = @nat.find _ (classical.dec_pred _) (s.has_nice_n c p01) :=
    by simp only [super.np, p01, op, true_and, dif_pos],
  rw e, apply nat.find_min', exact λ z zp, s.nice_np c p11 _ (trans zp le),
end
def super.n (s : super f d a) (c : ℂ) (z : S) : ℕ := s.np c (s.potential c z)
def super.nice_n (s : super f d a) {c : ℂ} {z : S} (m : (c,z) ∈ s.basin) [one_preimage s]
    : s.is_nice_n c (s.potential c z) (s.n c z) := s.nice_np c (s.potential_lt_one m)