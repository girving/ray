-- Hartogs's theorem for two variables: separately analytic functions are jointly analytic
--   https://en.wikipedia.org/wiki/Hartogs's_theorem_on_separate_holomorphicity
--   https://www-users.cse.umn.edu/~garrett/m/complex/hartogs.pdf

import analysis.calculus.parametric_interval_integral
import analysis.complex.schwarz
import analysis.normed.group.basic
import analysis.normed_space.multilinear
import data.real.pi.bounds
import data.set.function
import measure_theory.measure.measure_space_def
import topology.algebra.module.multilinear
import topology.metric_space.baire

import analytic
import bounds
import max
import max_log
import multilinear
import osgood
import prod
import subharmonic
import tactics
import topology

open complex (abs exp I log)
open filter (at_top)
open function (curry uncurry)
open linear_order (min)
open measure_theory.measure_space (volume)
open metric (ball closed_ball sphere bounded is_open_ball)
open prod (swap)
open set (univ)
open topological_space (second_countable_topology)
open_locale real nnreal ennreal topology
noncomputable theory

section hartogs

variables {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [second_countable_topology E]
variable {f : ℂ × ℂ → E}
variable {s : set (ℂ × ℂ)}
variables {c0 c0' c1 z0 z1 w0 w1 : ℂ}
variables {r r0 r1 b e : ℝ}

structure har (f : ℂ × ℂ → E) (s : set (ℂ × ℂ)) : Prop :=
  (fa0 : ∀ (c0 c1), (c0,c1) ∈ s → analytic_at ℂ (λ z0, f (z0,c1)) c0)
  (fa1 : ∀ (c0 c1), (c0,c1) ∈ s → analytic_at ℂ (λ z1, f (c0,z1)) c1)

def har.flip (h : har f s) : har (f ∘ swap) (swap '' s) := {
  fa0 := begin
    intros c0 c1 cs, simp only [function.comp_app, prod.swap_prod_mk],
    rw swap_mem at cs, exact h.fa1 c1 c0 cs,
  end,
  fa1 := begin
    intros c0 c1 cs, simp only [function.comp_app, prod.swap_prod_mk],
    rw swap_mem at cs, exact h.fa0 c1 c0 cs,
  end,
}

lemma har.mono {s t : set (ℂ × ℂ)} (ts : t ⊆ s) (h : har f s) : har f t := {
  fa0 := λ c0 c1 m, h.fa0 _ _ (ts m),
  fa1 := λ c0 c1 m, h.fa1 _ _ (ts m),
}

lemma har.on0 (h : har f (closed_ball (c0,c1) r)) (rp : r > 0)
    (z1r : z1 ∈ closed_ball c1 r) : analytic_on ℂ (λ z0, f (z0,z1)) (closed_ball c0 r) := begin
  intros z0 z0s, apply h.fa0 z0 z1,
  rw ←closed_ball_prod_same,
  simp only [set.prod_mk_mem_set_prod_eq, metric.mem_closed_ball] at ⊢ z0s,
  exact ⟨z0s,z1r⟩,
end

lemma har.on1 (h : har f (closed_ball (c0,c1) r)) (rp : r > 0)
    (z0r : z0 ∈ closed_ball c0 r) : analytic_on ℂ (λ z1, f (z0,z1)) (closed_ball c1 r) := begin
  intros z1 z1s, apply h.fa1 z0 z1,
  rw ←closed_ball_prod_same,
  simp only [set.prod_mk_mem_set_prod_eq, metric.mem_closed_ball] at ⊢ z1s,
  exact ⟨z0r,z1s⟩
end

lemma bounded.dist0 (h : har f s) {z w : ℂ × ℂ} {b e r : ℝ}
    (bp : b > 0) (ep : e > 0) (rp : r > 0) (rs : ball z (r/2) ⊆ s)
    (zs : z ∈ s) (wz : dist w z < min (r/2) (e*r/b/24))
    (fb : ∀ z, z ∈ s → ‖f z‖ ≤ b) : dist (f w) (f (z.fst,w.snd)) ≤ e/4 := begin
  generalize hu : min (r/2) (e*r/b/24) = u, rw hu at wz,
  have up : u > 0, { rw ←hu, simp only [gt_iff_lt, lt_min_iff], exact ⟨by bound [h.rp], by bound [h.rp]⟩ },
  have ur : u ≤ r/2, { rw ←hu, exact min_le_left _ _ },
  have ue : 6 * b / r * u ≤ e/4, { rw ←hu,
    calc 6*b/r * min (r/2) (e*r/b/24) ≤ 6*b/r * (e*r/b/24) : by bound [bp, rp, min_le_right]
    ... = (b/b) * (r/r) * (e/4) : by ring
    ... = e/4 : by field_simp [ne_of_gt bp, ne_of_gt rp]
  },
  rw ball_prod_same' at rs,
  rw [←metric.mem_ball, ball_prod_same', set.mem_prod] at wz,
  have d : differentiable_on ℂ (λ t, f (t,w.snd)) (ball z.fst (r/2)), {
    intros t ts, refine (h.fa0 t w.snd _).differentiable_within_at,
    exact rs (set.mk_mem_prod ts (metric.ball_subset_ball ur wz.right))
  },
  have wf : w.fst ∈ ball z.fst (r/2) := metric.ball_subset_ball ur wz.left,
  have m : set.maps_to (λ t, f (t,w.snd)) (ball z.fst (r/2)) (ball (f (z.fst,w.snd)) (3*b)), {
    intros t ts, simp only [dist_eq_norm, metric.mem_ball], apply lt_of_le_of_lt (norm_sub_le _ _),
    have f0 : ‖f (t, w.snd)‖ ≤ b := by apply_rules [rs, set.mk_mem_prod, metric.ball_subset_ball ur, fb, wz.right],
    have f1 : ‖f (z.fst, w.snd)‖ ≤ b := by apply_rules [rs, set.mk_mem_prod, metric.ball_subset_ball ur, fb,
        metric.mem_ball_self up, wz.right],
    calc ‖f (t, w.snd)‖ + ‖f (z.fst, w.snd)‖ ≤ b + b : by bound
    ... = 2*b : by ring
    ... < 3*b : mul_lt_mul_of_pos_right (by norm_num) bp
  },
  have L := complex.dist_le_div_mul_dist_of_maps_to_ball d m wf, simp only [prod.mk.eta] at L,
  refine trans L (trans _ ue), simp only [metric.mem_ball] at wz,
  rw [div_eq_mul_inv _ (2 : ℝ), div_mul_eq_div_div], ring_nf,
  bound [h.rp, wz.left]
end

lemma bounded.dist1 (h : har f s) {z w : ℂ × ℂ} {b e r : ℝ}
    (bp : b > 0) (ep : e > 0) (rp : r > 0) (rs : ball z r ⊆ s)
    (zs : z ∈ s) (wz : dist w z < min (r/2) (e*r/b/24))
    (fb : ∀ z, z ∈ s → ‖f z‖ ≤ b) : dist (f (z.fst,w.snd)) (f z) ≤ e/4 := begin
  have wrs : ball w (r/2) ⊆ s, {
    refine trans _ rs, apply metric.ball_subset_ball',
    have rr := trans (le_of_lt wz) (min_le_left _ _),
    transitivity (r/2)+(r/2), bound, ring_nf
  },
  have ws : w ∈ s := wrs (metric.mem_ball_self (by bound)),
  have rs' : ball (swap w) (r/2) ⊆ swap '' s, { rw ball_swap, exact set.image_subset _ wrs },
  have zs' : swap w ∈ swap '' s, { rw swap_mem', simpa },
  have wz' : dist (swap z) (swap w) < min (r/2) (e*r/b/24) := by rwa [dist_swap, dist_comm],
  have fb' : ∀ z, z ∈ swap '' s → ‖(f ∘ swap) z‖ ≤ b := λ z zs, fb z.swap (swap_mem'.mp zs),
  have d' := bounded.dist0 h.flip bp ep rp rs' zs' wz' fb',
  simp only [function.comp_app, prod.swap_swap, prod.fst_swap, prod.snd_swap, prod.swap_prod_mk] at d',
  rwa dist_comm,
end

-- f is analytic if it's bounded
lemma of_bounded (h : har f s) (o : is_open s) {b : ℝ} (fb : ∀ z, z ∈ s → ‖f z‖ ≤ b) : analytic_on ℂ f s := begin
  suffices c : continuous_on f s, exact osgood o c h.fa0 h.fa1,
  by_cases bp : b ≤ 0, {
    have fz : ∀ z, z ∈ s → f z = 0 :=
      λ z zs, norm_eq_zero.mp (le_antisymm (trans (fb z zs) bp) (norm_nonneg (f z))),
    rw continuous_on_congr fz, exact continuous_on_const,
  },
  simp only [not_le] at bp,
  intros z zs,
  rcases metric.is_open_iff.mp o z zs with ⟨r,rp,rs⟩,
  rw metric.continuous_within_at_iff, intros e ep,
  have up : min (r/2) (e*r/b/24) > 0 := by bound [lt_min, h.rp],
  use [min (r/2) (e*r/b/24), up],
  intros w ws wz,
  have s0 : dist (f w) (f (z.fst,w.snd)) ≤ e/4 :=
    bounded.dist0 h bp ep rp (trans (metric.ball_subset_ball (by bound)) rs) zs wz fb,
  have s1 : dist (f (z.fst,w.snd)) (f z) ≤ e/4 :=
    bounded.dist1 h bp ep rp rs zs wz fb,
  calc dist (f w) (f z) ≤ dist (f w) (f (z.fst,w.snd)) + dist (f (z.fst,w.snd)) (f z) : dist_triangle _ _ _
  ... ≤ e/4 + e/4 : by bound
  ... = e/2 : by ring
  ... < e : by bound
end

-- I'm finding it very difficult to work with subtypes (sets coerced to Sort), so I'm going to instead
-- prove one of the variants of Baire's theorem for an open set
lemma nonempty_interior.nonempty_interior_of_Union_of_closed
    {A B : Type} [topological_space A] [baire_space A] [nonempty A] [encodable B] {f : B → set A}
    (hc : ∀ k, is_closed (f k)) (hU : (interior ⋃ k, f k).nonempty)
    : ∃ k, (interior (f k)).nonempty := begin
  set s := interior ⋃ k, f k,
  set f' : option B → set A := λ k, match k with none := sᶜ | some k := f k end,
  have hc' : ∀ k, is_closed (f' k), { rw option.forall, exact ⟨is_open_interior.is_closed_compl, λ k, hc k⟩ },
  have hU' : (⋃ k, f' k) = set.univ, {
    apply set.ext, intro x, refine ⟨(λ _, set.mem_univ _), _⟩, intro xu, rw set.mem_Union,
    by_cases m : x ∈ s, {
      rcases set.mem_Union.mp (interior_subset m) with ⟨k,mk⟩,
      use some k, simpa only,
    }, {
      use none,
    }
  },
  have d := dense_Union_interior_of_closed hc' hU',
  rcases dense.exists_mem_open d is_open_interior hU with ⟨x,xi,xs⟩,
  rcases set.mem_Union.mp xi with ⟨k,xk⟩,
  induction k with k, {
    have xc := subset_closure xs, finish,
  }, {
    exact ⟨k,set.nonempty_of_mem xk⟩,
  },
end

-- Special case of forall_and_distrib
lemma forall_const_and_distrib {A : Type} [nonempty A] {p : Prop} {q : A → Prop} : (∀ x, p ∧ q x) ↔ p ∧ ∀ x, q x := begin
  have d := @forall_and_distrib A (λ _, p) q, simp only [forall_const] at d, exact d
end

-- Version of is_closed_le for continuous_on
lemma continuous_on.is_closed_le {A B : Type} [topological_space A] [topological_space B] [preorder B] [order_closed_topology B]
    {s : set A} {f g : A → B} (sc : is_closed s) (fc : continuous_on f s) (gc : continuous_on g s)
    : is_closed {x | x ∈ s ∧ f x ≤ g x} := begin
  rw set.set_of_and, simp only [set.set_of_mem_eq],
  set t := {p : B × B | p.fst ≤ p.snd},
  set fg := λ x, (f x, g x),
  have e : {x | f x ≤ g x} = fg⁻¹' t, { apply set.ext, intro x, simp only [set.preimage_set_of_eq] }, rw e,
  exact continuous_on.preimage_closed_of_closed (continuous_on.prod fc gc) sc order_closed_topology.is_closed_le',
end

-- If f is separately analytic on a polydisk, it is analytic on a subpolydisk that is full in one dimension
lemma on_subdisk (h : har f (closed_ball (c0,c1) r)) (rp : r > 0) (ep : e > 0)
    : ∃ c0' t, t > 0 ∧ c0' ∈ closed_ball c0 e ∧ analytic_on ℂ f (ball c0' t ×ˢ ball c1 r) := begin
  set re := min r e,
  have esub : closed_ball c0 re ⊆ closed_ball c0 r := metric.closed_ball_subset_closed_ball (by bound),
  generalize hS : (λ b : ℕ, {z0 | z0 ∈ closed_ball c0 re ∧ ∀ z1, z1 ∈ closed_ball c1 r → ‖f (z0,z1)‖ ≤ b}) = S,
  have hc : ∀ b, is_closed (S b), {
    intro b, rw ←hS, simp only [←forall_const_and_distrib],
    rw set.set_of_forall, apply is_closed_Inter, intro z1,
    by_cases z1r : z1 ∉ closed_ball c1 r, {
      simp only [z1r, false_implies_iff, and_true, set.set_of_mem_eq, metric.is_closed_ball]
    }, {
      rw set.not_not_mem at z1r,
      simp only [z1r, true_implies_iff],
      refine continuous_on.is_closed_le metric.is_closed_ball _ continuous_on_const,
      apply continuous_on.norm,
      exact continuous_on.mono (h.on0 rp z1r).continuous_on esub
    }
  },
  have hU : (interior ⋃ b, S b).nonempty, {
    refine set.nonempty_of_mem (mem_interior.mpr ⟨ball c0 re, _, metric.is_open_ball, metric.mem_ball_self (by bound)⟩),
    rw set.subset_def, intros z0 z0s, rw set.mem_Union,
    have z0s' := esub (mem_open_closed z0s),
    rcases (h.on1 rp z0s').continuous_on.bounded_norm (is_compact_closed_ball _ _) with ⟨b,bp,fb⟩,
    use nat.ceil b, rw ←hS, simp only [set.mem_set_of],
    refine ⟨mem_open_closed z0s, _⟩,
    simp only [metric.mem_closed_ball] at ⊢ fb, intros z1 z1r,
    exact trans (fb z1 z1r) (nat.le_ceil _),
  },
  rcases nonempty_interior.nonempty_interior_of_Union_of_closed hc hU with ⟨b,bi⟩, simp only at bi,
  rcases bi with ⟨c0',c0's⟩, use c0',
  rcases mem_interior.mp c0's with ⟨s',s's,so,c0s'⟩,
  rcases metric.is_open_iff.mp so c0' c0s' with ⟨t,tp,ts⟩,
  have tr : ball c0' t ⊆ closed_ball c0 re, {
    rw set.subset_def, intros z0 z0t,
    have z0b := trans ts s's z0t,
    rw ←hS at z0b, simp only [set.set_of_and, set.set_of_mem_eq, set.mem_inter_iff] at z0b,
    exact z0b.left,
  },
  have c0e : c0' ∈ closed_ball c0 e := trans tr (metric.closed_ball_subset_closed_ball (by bound)) (metric.mem_ball_self tp),
  have fb : ∀ z, z ∈ ball c0' t ×ˢ ball c1 r → ‖f z‖ ≤ b, {
    intros z zs, rw set.mem_prod at zs,
    have zb := trans ts s's zs.left,
    rw ←hS at zb,
    simp only [metric.mem_ball, metric.mem_closed_ball, le_min_iff, set.mem_set_of_eq] at zb zs,
    have zb' := zb.right z.snd (le_of_lt zs.right),
    simp only [prod.mk.eta] at zb', exact zb',
  },
  use [t, tp, c0e],
  refine of_bounded (h.mono _) (is_open.prod is_open_ball is_open_ball) fb,
  rw ←closed_ball_prod_same, exact set.prod_mono (trans tr esub) metric.ball_subset_closed_ball
end

-- Separate analyticity on a polydisk, full analyticity on a polydisk smaller in one direction
structure uneven (f : ℂ × ℂ → E) (c0 c1 : ℂ) (r0 r1 : ℝ) : Prop :=
  (r0p : r0 > 0)
  (r1p : r1 > 0)
  (r01 : r0 ≤ r1)
  (h : har f (closed_ball (c0,c1) r1))
  (a : analytic_on ℂ f (ball c0 r0 ×ˢ ball c1 r1))

-- Exact diameter of complex ball
lemma diam_ball_eq {c : ℂ} {r : ℝ} (rp : r ≥ 0) : metric.diam (ball c r) = 2*r := begin
  by_cases r0 : 0 = r, { simp only [←r0, metric.ball_zero, metric.diam_empty, mul_zero] },
  have rp' := ne.lt_of_le r0 rp, clear r0,
  apply le_antisymm (metric.diam_ball rp),
  apply le_of_forall_small_le_add rp', intros e ep er,
  have m : ∀ t : ℝ, |t| ≤ 1 → c + t*(r - e/2) ∈ ball c r, {
    intros t t1,
    simp only [complex.dist_eq, metric.mem_ball, add_sub_cancel', absolute_value.map_mul, complex.abs_of_real],
    have re : r - e/2 ≥ 0 := by bound [trans (half_lt_self ep) er],
    calc |t| * abs (↑r - ↑e/2 : ℂ) = |t| * abs (↑(r - e/2) : ℂ)
        : by simp only [complex.of_real_sub, complex.of_real_div, complex.of_real_bit0, complex.of_real_one]
    ... = |t| * (r - e/2) : by rw [complex.abs_of_real, abs_of_nonneg re]
    ... ≤ 1 * (r - e/2) : by bound
    ... = r - e/2 : by ring
    ... < r - 0 : sub_lt_sub_left (by bound) r
    ... = r : by ring
  },
  have lo := metric.dist_le_diam_of_mem metric.bounded_ball (m 1 (by norm_num)) (m (-1) (by norm_num)),
  have e : abs (2*↑r - ↑e : ℂ) = 2*r - e, {
    have re : 2*r - e ≥ 0, { transitivity r - e, bound, transitivity 1 * r, simp only [one_mul], bound, bound },
    calc abs (2*↑r - ↑e : ℂ) = abs (↑(2*r - e) : ℂ)
        : by simp only [complex.of_real_sub, complex.of_real_mul, complex.of_real_bit0, complex.of_real_one]
    ... = 2*r - e : by rw [complex.abs_of_real, abs_of_nonneg re]
  },
  simp only [complex.dist_eq, complex.of_real_one, one_mul, complex.of_real_neg, neg_mul, neg_sub, add_sub_add_left_eq_sub] at lo,
  ring_nf at lo, rw e at lo, linarith,
end

-- Exact diameter of complex closed ball
lemma diam_closed_ball_eq {c : ℂ} {r : ℝ} (rp : r ≥ 0) : metric.diam (closed_ball c r) = 2*r := begin
  apply le_antisymm (metric.diam_closed_ball rp),
  transitivity metric.diam (ball c r),
  rw diam_ball_eq rp,
  exact metric.diam_mono metric.ball_subset_closed_ball metric.bounded_closed_ball
end

lemma le_of_ball_subset_closed_ball {z0 z1 : ℂ} {r0 r1 : ℝ} (r0p : r0 ≥ 0) (r1p : r1 ≥ 0)
    : ball z0 r0 ⊆ closed_ball z1 r1 → r0 ≤ r1 := begin
  intro s,
  have m := metric.diam_mono s metric.bounded_closed_ball,
  rw [diam_ball_eq r0p, diam_closed_ball_eq r1p] at m, linarith,
end

-- Given separate analyticity on a polydisk, find an uneven subpolydisk s.t. fixing the unevenness covers the center
lemma to_uneven (h : har f (closed_ball (c0,c1) r)) (rp : r > 0)
    : ∃ c0' r0 r1, ball c0' r1 ⊆ closed_ball c0 r ∧ c0 ∈ ball c0' r1 ∧ uneven f c0' c1 r0 r1 := begin
  have r4p : r/4 > 0 := by bound,
  rcases on_subdisk h rp r4p with ⟨c0',r0,r0p,m,a⟩,
  simp only [metric.mem_closed_ball] at m,
  have sub : closed_ball c0' (r/2) ⊆ closed_ball c0 r, {
    apply metric.closed_ball_subset_closed_ball',
    calc r/2 + dist c0' c0 ≤ r/2 + r/4 : by bound
    ... = (3/4)*r : by ring
    ... ≤ 1*r : by bound
    ... = r : by ring
  },
  have r01 : min r0 (r/2) ≤ r/2 := by bound,
  have c0m : c0 ∈ ball c0' (r/2), {
    simp only [metric.mem_ball], rw dist_comm, apply lt_of_le_of_lt m, bound [div_lt_div_of_lt_left],
  },
  have h' : har f (closed_ball (c0',c1) (r/2)), {
    refine har.mono _ h, simp only [←closed_ball_prod_same], apply set.prod_mono,
    assumption, apply metric.closed_ball_subset_closed_ball, bound
  },
  have a' : analytic_on ℂ f (ball c0' (min r0 (r/2)) ×ˢ ball c1 (r/2)), {
    apply a.mono, apply set.prod_mono,
    apply metric.ball_subset_ball',
    simp only [dist_self, add_zero, min_le_iff, le_refl, true_or],
    apply metric.ball_subset_ball, bound,
  },
  use [c0', min r0 (r/2), r/2, trans (metric.ball_subset_closed_ball) sub, c0m], exact {
    r0p := by bound, r1p := by bound, r01 := r01, h := h', a := a',
  },
end

def uneven_term' (u : uneven f c0 c1 r0 r1) (r : ℝ) (z1 : ℂ) (n : ℕ) : E :=
  (2*π*I : ℂ)⁻¹ • ∮ z0 in C(c0, r), (z0 - c0)⁻¹^n • (z0 - c0)⁻¹ • f (z0,z1)

def uneven_term (u : uneven f c0 c1 r0 r1) := uneven_term' u r1

def uneven_series' (u : uneven f c0 c1 r0 r1) (r : ℝ) (z1 : ℂ) : formal_multilinear_series ℂ ℂ E :=
  λ n, continuous_multilinear_map.mk_pi_field ℂ _ (uneven_term' u r z1 n)

def uneven_series (u : uneven f c0 c1 r0 r1) := uneven_series' u r1

lemma uneven_series_apply (u : uneven f c0 c1 r0 r1) (r : ℝ) (z1 : ℂ) (n : ℕ)
    : uneven_series' u r z1 n (λ _, 1) = uneven_term' u r z1 n :=
  by simp only [uneven_series', continuous_multilinear_map.mk_pi_field_apply, finset.prod_const_one, one_smul]

lemma uneven_is_cauchy {u : uneven f c0 c1 r0 r1} {r : ℝ}
    : uneven_series' u r z1 = cauchy_power_series (λ z0, f (z0,z1)) c0 r := begin
  funext, rw [uneven_series', cauchy_power_series], refl,
end

lemma uneven.has_series (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr1 : s ≤ r1)
    (z1s : z1 ∈ closed_ball c1 r1)
    : has_fpower_series_on_ball (λ z0, f (z0,z1)) (uneven_series' u s z1) c0 (ennreal.of_real s) := begin
  set sn := s.to_nnreal,
  have sns : s = sn, { simp only [real.coe_to_nnreal', le_of_lt sp, max_eq_left] },
  have snp : sn > 0 := real.to_nnreal_pos.mpr sp,
  rw uneven_is_cauchy,
  rw [sns, ←ennreal.coe_nnreal_eq],
  refine differentiable_on.has_fpower_series_on_ball _ snp,
  rw ←sns,
  refine differentiable_on.mono _ (metric.closed_ball_subset_closed_ball sr1),
  exact analytic_on.differentiable_on (u.h.on0 u.r1p z1s),
end

lemma uneven_term_eq (u : uneven f c0 c1 r0 r1) {r : ℝ} (rp : r > 0) (rr1 : r ≤ r1) {z1 : ℂ}
    : z1 ∈ closed_ball c1 r1 → uneven_term' u r z1 = uneven_term u z1 := begin
  intro z1s, funext,
  have p0 := u.has_series rp rr1 z1s,
  have p1 := u.has_series u.r1p (by refl) z1s,
  have h := has_fpower_series_at.eq_formal_multilinear_series p0.has_fpower_series_at p1.has_fpower_series_at,
  clear p0 p1, simp only [uneven_term, ←uneven_series_apply], rwa h,
end

lemma uneven_series_eq (u : uneven f c0 c1 r0 r1) {r : ℝ} (rp : r > 0) (rr1 : r ≤ r1) {z1 : ℂ}
    : z1 ∈ closed_ball c1 r1 → uneven_series' u r z1 = uneven_series u z1 := begin
  intro z1s, funext,
  simp_rw [uneven_series, uneven_series', uneven_term_eq u rp rr1 z1s, uneven_term_eq u u.r1p (le_refl _) z1s],
end

lemma uneven_series_norm (u : uneven f c0 c1 r0 r1) {n : ℕ} : ‖uneven_series u z1 n‖ = ‖uneven_term u z1 n‖ :=
  by rw [uneven_series, uneven_series', uneven_term, continuous_multilinear_map.norm_mk_pi_field]

-- Our power series terms are uniformly bounded (away from the edges)
lemma uneven_series_uniform_bound (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1)
    : ∃ c a : ℝ, c > 0 ∧ a > 0 ∧ ∀ n z1, z1 ∈ closed_ball c1 s → ‖uneven_series u z1 n‖ ≤ c * a^n := begin
  have fc : continuous_on f (sphere c0 (r0/2) ×ˢ closed_ball c1 s), {
    suffices fa' : analytic_on ℂ f (sphere c0 (r0/2) ×ˢ closed_ball c1 s), exact fa'.continuous_on,
    refine u.a.mono (set.prod_mono _ _),
    have rh : r0/2 < r0 := by bound [u.r0p],
    exact trans metric.sphere_subset_closed_ball (metric.closed_ball_subset_ball rh),
    exact metric.closed_ball_subset_ball (by bound [u.r1p]),
  },
  rcases fc.bounded_norm (is_compact.prod (is_compact_sphere _ _) (is_compact_closed_ball _ _))
    with ⟨b,bp,fb⟩,
  use [b + 1, (r0/2)⁻¹, lt_of_le_of_lt bp (lt_add_one _), by bound [u.r0p]],
  intros n z1 z1s,
  have r0hp : r0 / 2 > 0 := by bound [u.r0p],
  have r0hr1 : r0 / 2 ≤ r1 := trans (by bound [u.r0p]) u.r01,
  set g := λ z0, f (z0,z1),
  have gc : continuous_on g (sphere c0 (r0/2)) :=
    continuous_on.comp fc (continuous_on.prod continuous_on_id continuous_on_const) (λ z0 z0s, set.mk_mem_prod z0s z1s),
  have gb : ∀ z0, z0 ∈ sphere c0 (r0/2) → ‖g z0‖ ≤ b := λ z0 z0s, fb (z0,z1) (set.mk_mem_prod z0s z1s),
  have cb := cauchy1_bound' r0hp bp gc gb n, clear bp gc gb,
  have e : (2*π*I : ℂ)⁻¹ • ∮ z0 in C(c0, r0/2), (z0 - c0)⁻¹^n • (z0 - c0)⁻¹ • g z0 = uneven_term' u (r0/2) z1 n := rfl,
  rw e at cb, clear e g,
  rw uneven_term_eq u r0hp r0hr1 (metric.closed_ball_subset_closed_ball (le_of_lt sr) z1s) at cb,
  rwa uneven_series_norm u, apply trans cb,
  bound [le_of_lt (lt_add_one b)],
end

-- Our power series terms are nonuniformly bounded as O(s⁻¹^n) for any s < r1
lemma uneven_series_nonuniform_bound (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr1 : s < r1)
    (z1s : z1 ∈ closed_ball c1 r1)
    : ∃ c : ℝ, c > 0 ∧ ∀ n, ‖uneven_series u z1 n‖ ≤ c * s⁻¹^n := begin
  have h := (uneven.has_series u u.r1p (le_refl _) z1s).r_le,
  rw [formal_multilinear_series.radius, le_supr_iff] at h,
  have sr := not_le_of_lt ((ennreal.of_real_lt_of_real_iff_of_nonneg (le_of_lt sp)).mpr sr1),
  specialize h (ennreal.of_real s), rw imp_iff_not sr at h,
  simp only [not_forall, not_le, lt_supr_iff] at h,
  rcases h with ⟨t,c,th,st⟩,
  have st' : s < ↑t, {
    rw [←ennreal.of_real_coe_nnreal, ennreal.of_real_lt_of_real_iff_of_nonneg (le_of_lt sp)] at st, exact st,
  },
  have cp : c ≥ 0 := trans (th 0) (by bound),
  use [max 1 c, lt_of_lt_of_le (by norm_num) (le_max_left 1 c)],
  intro n, specialize th n, rw uneven_series_eq u u.r1p (le_refl _) z1s at th,
  generalize hy : ‖uneven_series u z1 n‖ = y, rw hy at th, have yp : y ≥ 0, { rw ←hy, bound },
  have tnz : (t : ℝ)^n ≠ 0 := pow_ne_zero _ (ne_of_gt (trans sp st')),
  calc y = y * (↑t^n * (↑t^n)⁻¹) : by simp only [mul_inv_cancel tnz, mul_one]
  ... = y * ↑t^n * (↑t^n)⁻¹ : by ring
  ... ≤ c * (↑t^n)⁻¹ : by bound
  ... ≤ c * (s^n)⁻¹ : by bound
  ... = c * s⁻¹^n : by simp only [inv_pow]
  ... ≤ (max 1 c) * s⁻¹^n : by bound,
end

-- λ z0, (z0, 0)
def id_zero_lm : ℂ →L[ℂ] (ℂ × ℂ) := continuous_linear_map.prod (continuous_linear_map.id ℂ ℂ) (0 : ℂ →L[ℂ] ℂ)

-- Given a continuous multilinear map on two complex numbers, restrict to the slice along just the first
def continuous_multilinear_map.along0 {n : ℕ} (p : continuous_multilinear_map ℂ (λ _ : fin n, ℂ × ℂ) E)
    : continuous_multilinear_map ℂ (λ _: fin n, ℂ) E := p.comp_continuous_linear_map (λ _, id_zero_lm)

-- along0 reduces norms
lemma along0.norm {n : ℕ} (p : continuous_multilinear_map ℂ (λ _ : fin n, ℂ × ℂ) E) : ‖p.along0‖ ≤ ‖p‖ := begin
  have pp : 0 ≤ ‖p‖ := by bound,
  apply @continuous_multilinear_map.op_norm_le_bound ℂ (fin n) (λ _, ℂ) E _ _ _ _ _ _ p.along0 _ pp,
  intro m,
  simp only [continuous_multilinear_map.along0, continuous_multilinear_map.comp_continuous_linear_map_apply, complex.norm_eq_abs],
  have e : ∀ i : fin n, abs (m i) = ‖id_zero_lm (m i)‖, {
    intro i,
    simp only [id_zero_lm, prod.norm_def, continuous_linear_map.prod_apply, continuous_linear_map.coe_id', id.def,
      continuous_linear_map.zero_apply, complex.norm_eq_abs, absolute_value.map_zero, max_eq_left, map_nonneg],
  },
  simp_rw e,
  exact @continuous_multilinear_map.le_op_norm ℂ (fin n) (λ _, ℂ × ℂ) E _ _ _ _ _ _ p _,
end

-- along0 is linear
def along0.linear_map (n : ℕ)
    : continuous_multilinear_map ℂ (λ _ : fin n, ℂ × ℂ) E →ₗ[ℂ]
      continuous_multilinear_map ℂ (λ _: fin n, ℂ) E := {
  to_fun := λ p, p.along0,
  map_add' := begin
    intros p q, simp_rw continuous_multilinear_map.along0,
    apply continuous_multilinear_map.ext, intro m,
    simp only [continuous_multilinear_map.comp_continuous_linear_map_apply, continuous_multilinear_map.add_apply],
  end,
  map_smul' := begin
    intros s p, simp_rw continuous_multilinear_map.along0,
    apply continuous_multilinear_map.ext, intro m,
    simp only [continuous_multilinear_map.comp_continuous_linear_map_apply, continuous_multilinear_map.smul_apply, ring_hom.id_apply],
  end
}

-- along0 is continuous linear
def along0.continuous_linear_map (n : ℕ)
    : continuous_multilinear_map ℂ (λ _ : fin n, ℂ × ℂ) E →L[ℂ]
      continuous_multilinear_map ℂ (λ _: fin n, ℂ) E := begin
  refine linear_map.mk_continuous (along0.linear_map n) 1 _,
  intro p, simp only [one_mul, along0.linear_map], exact along0.norm p,
end

-- along0 for a whole power series
def formal_multilinear_series.along0 (p : formal_multilinear_series ℂ (ℂ × ℂ) E) : formal_multilinear_series ℂ ℂ E :=
  λ n, (p n).along0

-- along0 increases radius of convergence
lemma along0.radius (p : formal_multilinear_series ℂ (ℂ × ℂ) E) : p.radius ≤ p.along0.radius := begin
  simp_rw formal_multilinear_series.radius,
  refine supr_mono _, intro r,
  refine supr_mono _, intro C,
  refine supr_mono' _, intro h,
  have h' : ∀ n, ‖p.along0 n‖ * ↑r ^ n ≤ C := λ n, trans (by bound [along0.norm (p n)]) (h n),
  use h', simp only [le_refl],
end

-- If f : ℂ × ℂ → E is analytic with series p, (λ z0, f (z0,z1)) is analytic with series p.along0
lemma has_fpower_series_at.along0 {f : ℂ × ℂ → E} {c0 c1 : ℂ} {p : formal_multilinear_series ℂ (ℂ × ℂ) E}
    (fp : has_fpower_series_at f p (c0,c1)) : has_fpower_series_at (λ z0, f (z0,c1)) p.along0 c0 := begin
  rcases fp with ⟨r,fpr⟩,
  suffices h : has_fpower_series_on_ball (λ z0, f (z0,c1)) p.along0 c0 r, exact h.has_fpower_series_at,
  refine {
    r_le := trans fpr.r_le (along0.radius p),
    r_pos := fpr.r_pos,
    has_sum := _,
  }, {
    intros w0 w0r,
    simp_rw [formal_multilinear_series.along0, continuous_multilinear_map.along0, id_zero_lm],
    simp only [continuous_multilinear_map.comp_continuous_linear_map_apply, continuous_linear_map.prod_apply,
      continuous_linear_map.coe_id', id.def, continuous_linear_map.zero_apply],
    have w01r : (w0, (0 : ℂ)) ∈ emetric.ball (0 : ℂ × ℂ) r, {
      simp only [prod.edist_eq, emetric.mem_ball, prod.fst_zero, prod.snd_zero, edist_self, ennreal.max_zero_right] at ⊢ w0r,
      exact w0r,
    },
    have hs := fpr.has_sum w01r, simp only [prod.mk_add_mk, add_zero] at ⊢ hs, exact hs,
  }
end

-- The map p → p.along0 is analytic
lemma along0.analytic_at (n : ℕ) : ∀ {p}, analytic_at ℂ (λ p : continuous_multilinear_map ℂ (λ _ : fin n, ℂ × ℂ) E, p.along0) p :=
  λ p, (@along0.continuous_linear_map E _ _ _ _ n).analytic_at p

-- uneven_series u r1 z1 is analytic as a function of z1
lemma uneven_series_analytic (u : uneven f c0 c1 r0 r1) (n : ℕ)
    : analytic_on ℂ (λ z1, uneven_series u z1 n) (ball c1 r1) := begin
  intros z1 z1s,
  rcases u.a (c0,z1) (set.mk_mem_prod (metric.mem_ball_self u.r0p) z1s) with ⟨p,r,hp⟩,
  have pa := (p.has_fpower_series_on_ball_change_origin n (lt_of_lt_of_le hp.r_pos hp.r_le)).analytic_at,
  set g := λ w1, ((0 : ℂ), w1-z1),
  have ga : analytic_on ℂ g univ, {
    rw ←differentiable.entire, exact (differentiable_const _).prod (differentiable_id.sub (differentiable_const _)),
  },
  have g0 : 0 = g z1 := by simp only [prod.ext_iff, prod.fst_zero, prod.snd_zero, sub_self, and_self],
  rw g0 at pa,
  have ta := pa.comp (ga z1 (set.mem_univ _)),
  simp_rw function.comp at ta, clear pa ga g0,
  have pu : ∀ᶠ w1 in nhds z1, uneven_series u w1 n = (p.change_origin (g w1)).along0 n, {
    rw eventually_nhds_iff,
    set s' := r1 - dist z1 c1,
    set s := min r (ennreal.of_real s'),
    have s'p : s' > 0, { simp only [metric.mem_ball] at z1s, bound },
    have s'r1 : s' ≤ r1 := sub_le_self r1 (by bound),
    have sp : s > 0 := by bound [hp.r_pos, ennreal.of_real_pos.mpr s'p],
    have sr : s ≤ r := min_le_left _ _,
    have sr1 : s ≤ ennreal.of_real r1 := trans (min_le_right _ _) (ennreal.of_real_le_of_real s'r1),
    have sb : emetric.ball z1 s ⊆ ball c1 r1, {
      rw set.subset_def, intros x xs,
      simp only [metric.mem_ball, emetric.mem_ball, lt_min_iff, edist_lt_of_real] at ⊢ xs z1s,
      calc dist x c1 ≤ dist x z1 + dist z1 c1 : by bound
      ... < s' + dist z1 c1 : add_lt_add_right xs.right _
      ... = r1 - dist z1 c1 + dist z1 c1 : rfl
      ... = r1 : by ring_nf
    },
    use emetric.ball z1 s,
    refine ⟨_, emetric.is_open_ball, emetric.mem_ball_self sp⟩,
    intros w1 w1s,
    have p0 : has_fpower_series_at (λ z0, f (z0,w1)) (uneven_series u w1) c0, {
      have w1c : w1 ∈ closed_ball c1 r1 := mem_open_closed (sb w1s),
      refine (uneven.has_series u u.r1p (le_refl _) w1c).has_fpower_series_at,
    },
    have p1 : has_fpower_series_at (λ z0, f (z0,w1)) (p.change_origin (g w1)).along0 c0, {
      have wz : ↑‖((0 : ℂ), w1 - z1)‖₊ < r, {
        simp only [emetric.mem_ball, edist_dist, complex.dist_eq] at w1s,
        simp only [prod.nnnorm_def', nnnorm_zero, max_eq_right, zero_le', ←edist_eq_coe_nnnorm, edist_dist, complex.dist_eq, sub_zero],
        exact lt_of_lt_of_le w1s sr,
      },
      have co := (hp.change_origin wz).has_fpower_series_at,
      simp only [prod.mk_add_mk, add_zero, add_sub_cancel'_right] at co, exact co.along0,
    },
    rw has_fpower_series_at.eq_formal_multilinear_series p0 p1,
  },
  have clm := @continuous_multilinear_map.complete_space ℂ (fin n) (λ _, ℂ) E _ _ _ _ _ _ _,
  rw @analytic_at_congr ℂ _ _ _ _ _ (continuous_multilinear_map ℂ (λ _ : fin n, ℂ) E)
      _ _ clm _ _ _ pu, clear pu clm,
  exact (along0.analytic_at _).comp ta,
end

-- uneven_term u z1 n is analytic as a function of z1
lemma uneven_term.analytic (u : uneven f c0 c1 r0 r1) (n : ℕ)
    : analytic_on ℂ (λ z1, uneven_term u z1 n) (ball c1 r1) := begin
  have e : ∀ z1, uneven_term u z1 n = (cmmap_apply_cmap ℂ (λ _ : fin n, ℂ) E (λ _, 1)) (uneven_series u z1 n), {
    intro z1, simp only [uneven_term, ←uneven_series_apply, cmmap_apply_cmap, uneven_series, continuous_linear_map.coe_mk',
  linear_map.coe_mk],
  },
  simp_rw e,
  exact continuous_linear_map.comp_analytic_on _ (uneven_series_analytic u n),
end

-- The subharmonic functions we'll apply Hartogs's lemma to
def uneven_log (u : uneven f c0 c1 r0 r1) (n : ℕ) (z1 : ℂ) : ℝ := (↑n)⁻¹ * max_log (-1) (‖r1^n • uneven_term u z1 n‖)

-- Uniform bound on uneven_term in terms of uneven_log
lemma uneven_log_uniform_bound (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1)
    : ∃ b : ℝ, ∀ n z1, z1 ∈ closed_ball c1 s → uneven_log u n z1 ≤ b := begin
  rcases uneven_series_uniform_bound u sp sr with ⟨c,a,cp,ap,h⟩,
  use max_log 0 (r1 * (max 1 c * a)), intros n z zs, specialize h n z zs,
  simp_rw uneven_series_norm at h, rw uneven_log,
  by_cases n0 : n = 0, { simp only [n0, algebra_map.coe_zero, inv_zero, zero_mul, le_max_log] },
  have np : n ≥ 1 := nat.one_le_of_lt (nat.pos_of_ne_zero n0),
  rw inv_mul_le_iff (nat.cast_pos.mpr (nat.pos_of_ne_zero n0) : 0 < (n : ℝ)),
  apply max_log_le, transitivity (0 : ℝ), norm_num, simp only, bound [le_max_log],
  simp only [norm_smul, abs_of_pos u.r1p, norm_pow, real.norm_eq_abs],
  transitivity r1^n * (c * a^n), bound [u.r1p],
  rw real.exp_nat_mul,
  transitivity (r1 * (max 1 c * a))^n, simp only [mul_pow], bound [u.r1p],
  transitivity (max 1 c)^1, simp only [pow_one, le_max_iff, le_refl, or_true], exact pow_le_pow (le_max_left 1 c) np,
  bound [le_exp_max_log, u.r1p, le_max_of_le_right (le_of_lt cp)],
end

 -- Nonuniform bound on uneven_term in terms of uneven_log
lemma uneven_log_nonuniform_bound (u : uneven f c0 c1 r0 r1) (z1s : z1 ∈ closed_ball c1 r1)
    : ∀ d, d > 0 → ∀ᶠ n in at_top, uneven_log u n z1 ≤ d := begin
  intros d dp,
  rcases exists_between dp with ⟨e,ep,ed⟩,
  set s := r1 / e.exp,
  have sp : s > 0 := by bound [u.r1p, real.exp_pos],
  have sr : s < r1 := by bound [u.r1p, real.exp_pos, div_lt_self, real.one_lt_exp_iff.mpr],
  rcases uneven_series_nonuniform_bound u sp sr z1s with ⟨c,cp,us⟩,
  -- Choose m large enough to make c negligible
  rcases exists_nat_gt (max 1 (c.log / (d-e))) with ⟨m,mb⟩,
  have mp : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one (trans (by bound) (le_of_lt mb)),
  rw filter.eventually_at_top, use m, intros n mn, specialize us n,
  generalize ht : ‖uneven_term u z1 n‖ = t,
  have tp : t ≥ 0, { rw ←ht, bound },
  rw [uneven_series_norm, ht] at us,
  clear z1s,
  -- Prove the desired bound
  rw [uneven_log, inv_mul_le_iff (lt_of_lt_of_le mp (nat.cast_le.mpr mn))],
  apply max_log_le, transitivity (0 : ℝ), norm_num, bound,
  have nb : c.log / (d-e) ≤ n := trans (trans (by bound) (le_of_lt mb)) (nat.cast_le.mpr mn),
  calc ‖r1^n • uneven_term u z1 n‖ = r1^n * t : by simp only [←ht, norm_smul, abs_of_pos u.r1p, norm_pow, real.norm_eq_abs, mul_eq_mul_left_iff,
                                                              eq_self_iff_true, true_or, abs_pow]
  ... ≤ r1^n * (c * s⁻¹^n) : by bound [u.r1p]
  ... = r1^n * (c * (e.exp^n / r1^n)) : by rw [inv_div, div_pow]
  ... = r1^n / r1^n * c * e.exp^n : by ring
  ... = c * e.exp^n : by field_simp [ne_of_gt (pow_pos u.r1p _)]
  ... = c * (↑n*e).exp : by rw real.exp_nat_mul
  ... = c * (↑n*d - ↑n*(d-e)).exp : by ring_nf
  ... = c.log.exp * ((↑n*d).exp / (↑n*(d-e)).exp) : by rw [real.exp_sub, real.exp_log cp]
  ... = c.log.exp / (↑n*(d-e)).exp * (↑n*d).exp : by ring_nf
  ... = (c.log - ↑n*(d-e)).exp * (↑n*d).exp : by rw real.exp_sub
  ... ≤ (c.log - c.log/(d-e)*(d-e)).exp * (↑n*d).exp : by bound [real.exp_le_exp.mpr, le_of_lt (real.exp_pos _)]
  ... ≤ (↑n*d).exp : by field_simp [ne_of_gt (sub_pos.mpr ed)],
end

-- Our max_log function is subharmonic
lemma uneven_nonuniform_subharmonic (u : uneven f c0 c1 r0 r1) (n : ℕ) : subharmonic_on (uneven_log u n) (ball c1 r1) := begin
  refine subharmonic_on.const_mul _ (by bound),
  apply analytic_on.max_log_norm_subharmonic_on _ (-1),
  apply_instance, apply_instance, apply_instance,
  rw ←differentiable_iff_analytic metric.is_open_ball,
  apply differentiable_on.const_smul, rw differentiable_iff_analytic metric.is_open_ball,
  apply uneven_term.analytic u, apply_instance, apply_instance,
end

-- The nonuniform bound holds uniformly
lemma uneven_series_strong_bound (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1)
    : ∀ᶠ n in at_top, ∀ z1, z1 ∈ closed_ball c1 s → ‖uneven_series u z1 n‖ ≤ s⁻¹^n := begin
  rcases exists_between sr with ⟨t,ts,tr⟩,
  have tp : t > 0 := trans ts sp,
  have trs : closed_ball c1 t ⊆ ball c1 r1 := metric.closed_ball_subset_ball tr,
  have cs : closed_ball c1 t ⊆ closed_ball c1 r1 := metric.closed_ball_subset_closed_ball (le_of_lt tr),
  have ks : closed_ball c1 s ⊆ interior (closed_ball c1 t), {
    rw interior_closed_ball _ (ne_of_gt tp), exact metric.closed_ball_subset_ball ts, apply_instance,
  },
  rcases uneven_log_uniform_bound u tp tr with ⟨b,fb⟩,
  have H := subharmonic_on.hartogs (λ n, (uneven_nonuniform_subharmonic u n).mono trs) fb
      (λ z zs, uneven_log_nonuniform_bound u (cs zs)) (is_compact_closed_ball _ _) ks,
  specialize H (r1/s).log (by bound [real.log_pos, (one_lt_div _).mpr]),
  refine H.mp ((filter.eventually_gt_at_top 0).mp (filter.eventually_of_forall _)),
  intros n np h z zs, specialize h z zs, simp only at h,
  rw uneven_series_norm,
  rw [uneven_log, inv_mul_le_iff (nat.cast_pos.mpr np : 0 < (n : ℝ))] at h,
  simp only [norm_smul, abs_of_pos u.r1p, norm_pow, real.norm_eq_abs] at h,
  have a := le_of_max_log_le h,
  rw [real.exp_nat_mul, real.exp_log (div_pos u.r1p sp), div_eq_mul_inv, mul_pow, abs_pow, abs_of_pos u.r1p] at a,
  exact (mul_le_mul_left (by bound [u.r1p])).mp a,
end

-- The nonuniform bound holds uniformly, without ∀ᶠ
lemma uneven_series_strong_bound' (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1)
    : ∃ c, c ≥ 0 ∧ ∀ n, ∀ z1, z1 ∈ closed_ball c1 s → ‖uneven_series u z1 n‖ ≤ c * s⁻¹^n := begin
  rcases filter.eventually_at_top.mp (uneven_series_strong_bound u sp sr) with ⟨n,h⟩,
  set g := λ z1, partial_sups (λ k, s^k * ‖uneven_series u z1 k‖) n,
  have gc : continuous_on g (closed_ball c1 s), {
    apply continuous_on.partial_sups, intro n, apply continuous_on.mul continuous_on_const, apply continuous_on.norm,
    exact (uneven_series_analytic u n).continuous_on.mono (metric.closed_ball_subset_ball sr), apply_instance,
  },
  rcases gc.bounded (is_compact_closed_ball _ _) with ⟨b,bp,gb⟩,
  simp_rw partial_sups_le_iff at gb,
  use [max 1 b, le_max_of_le_right bp], intros k z zs,
  by_cases kn : k ≤ n, {
    specialize gb z zs k kn,
    calc ‖uneven_series u z k‖
        = s⁻¹^k * (s^k * ‖uneven_series u z k‖) : by { ring_nf, field_simp [ne_of_gt (pow_pos sp _)] }
    ... ≤ s⁻¹^k * b : by bound
    ... = b * s⁻¹^k : by ring_nf
    ... ≤ max 1 b * s⁻¹^k : by bound,
  }, {
    simp only [not_le] at kn, apply trans (h k (le_of_lt kn) z zs),
    calc s⁻¹^k = 1 * s⁻¹^k : by simp only [one_mul]
    ... ≤ max 1 b * s⁻¹^k : by bound,
  },
end

-- This should go somewhere else
lemma fst_snd_eq {A B : Type} (p : A × B) : (p.fst,p.snd) = p := by simp only [prod.mk.eta]

-- f is bounded away from the (now even!) edges
lemma uneven_bounded (u : uneven f c0 c1 r0 r1) {s : ℝ} (sp : s > 0) (sr : s < r1)
    : ∃ b, b ≥ 0 ∧ ∀ z, z ∈ ball (c0,c1) s → ‖f z‖ ≤ b := begin
  rcases exists_between sr with ⟨t,ts,tr⟩,
  have tp : t > 0 := trans ts sp,
  rcases uneven_series_strong_bound' u tp tr with ⟨c,cp,ch⟩,
  use [c * (1 - s/t)⁻¹, by bound], intros z zs,
  simp only [prod.dist_eq, metric.mem_ball, max_lt_iff] at zs,
  have z1t : z.2 ∈ closed_ball c1 t, { simp only [metric.mem_closed_ball], exact trans (le_of_lt zs.2) (le_of_lt ts) },
  have z1r : z.2 ∈ closed_ball c1 r1 := metric.closed_ball_subset_closed_ball (le_of_lt tr) z1t,
  have ds : z.1-c0 ∈ metric.ball (0 : ℂ) s, {
    simp only [complex.dist_eq] at zs,
    simp only [zs.1, mem_ball_zero_iff, complex.norm_eq_abs],
  },
  have ds' : z.1-c0 ∈ emetric.ball (0 : ℂ) (ennreal.of_real s) := by rwa metric.emetric_ball,
  have hs := (u.has_series sp (le_of_lt sr) z1r).has_sum ds',
  simp only [uneven_series_eq u sp (le_of_lt sr) z1r, formal_multilinear_series.apply_eq_pow_smul_coeff, add_sub_cancel'_right,
    prod.mk.eta] at hs,
  set g := λ n : ℕ, c * (s/t)^n, 
  have gs : has_sum g (c * (1 - s/t)⁻¹) :=
    has_sum.mul_left _ (has_sum_geometric_of_lt_1 (by bound) (by bound [(div_lt_one _).mpr])),
  apply has_sum.norm_le_of_bounded hs gs,
  intro n,
  simp only [mem_ball_zero_iff, complex.norm_eq_abs] at ds,
  simp only [norm_smul, complex.norm_eq_abs, complex.abs_pow, ←formal_multilinear_series.norm_apply_eq_norm_coef],
  calc abs (z.1-c0)^n * ‖uneven_series u z.2 n‖ ≤ s^n * (c * t⁻¹^n) : by bound [ch n _ z1t]
  ... = c * (s^n * t⁻¹^n) : by ring_nf
  ... = c * (s / t)^n : by rw [←mul_pow, ←div_eq_mul_inv],
end 
  
end hartogs

-- Hartogs's theorem on ℂ × ℂ: separately analytic functions are jointly analytic
theorem pair.hartogs {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [second_countable_topology E]
    {f : ℂ × ℂ → E} {s : set (ℂ × ℂ)} (so : is_open s)
    (fa0 : ∀ (c0 c1), (c0,c1) ∈ s → analytic_at ℂ (λ z0, f (z0,c1)) c0)
    (fa1 : ∀ (c0 c1), (c0,c1) ∈ s → analytic_at ℂ (λ z1, f (c0,z1)) c1)
    : analytic_on ℂ f s  := begin
  have h : har f s := ⟨fa0,fa1⟩,
  intros c cs,
  rcases metric.is_open_iff.mp so c cs with ⟨r,rp,rs⟩,
  rcases exists_between rp with ⟨t,tp,tr⟩,
  have bs : closed_ball (c.1,c.2) t ⊆ s, { refine trans _ rs, simp only [fst_snd_eq], exact metric.closed_ball_subset_ball tr },
  rcases to_uneven (h.mono bs) tp with ⟨c0',r0,r1,us,c0s,u⟩,
  have cr : abs (c.1 - c0') < r1, { simp only [complex.dist_eq, metric.mem_ball] at c0s, exact c0s },
  rcases exists_between cr with ⟨v,vc,vr⟩,
  rcases uneven_bounded u (lt_of_le_of_lt (complex.abs.nonneg _) vc) vr with ⟨b,bp,fb⟩,
  have fa := of_bounded (h.mono _) metric.is_open_ball fb, {
    apply fa,
    simp only [prod.dist_eq, complex.dist_eq, metric.mem_ball, sub_self, absolute_value.map_zero, max_eq_left, map_nonneg, vc],
  }, {
    refine trans _ bs,
    simp_rw [←ball_prod_same, ←closed_ball_prod_same, set.prod_subset_prod_iff], apply or.inl,
    use [trans (metric.ball_subset_ball (le_of_lt vr)) us],
    have r1t := le_of_ball_subset_closed_ball (le_of_lt u.r1p) (le_of_lt tp) us,
    exact trans metric.ball_subset_closed_ball (metric.closed_ball_subset_closed_ball (trans (le_of_lt vr) r1t)),
  },
end

-- Hartog's theorem near a point
theorem pair.hartogs_at {E : Type} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E] [second_countable_topology E]
    {f : ℂ × ℂ → E} {c : ℂ × ℂ}
    (fa0 : ∀ᶠ p : ℂ × ℂ in 𝓝 c, analytic_at ℂ (λ z0, f (z0,p.2)) p.1)
    (fa1 : ∀ᶠ p : ℂ × ℂ in 𝓝 c, analytic_at ℂ (λ z1, f (p.1,z1)) p.2)
    : analytic_at ℂ f c := begin
  rcases eventually_nhds_iff.mp (fa0.and fa1) with ⟨s,fa,o,cs⟩,
  exact pair.hartogs o (λ c0 c1 m, (fa _ m).1) (λ c0 c1 m, (fa _ m).2) c cs,
end