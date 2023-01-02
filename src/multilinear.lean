-- Multilinear functions on pairs

import algebra.algebra.basic
import analysis.complex.basic
import analysis.normed.field.basic
import analysis.normed_space.basic
import analysis.normed_space.multilinear
import data.complex.basic
import topology.algebra.module.multilinear

import tactics

open_locale complex_conjugate
noncomputable theory
variables {n : ℕ}
variables {𝕜 : Type} [nontrivially_normed_field 𝕜]
variables {R A B E : Type} [semiring R]

lemma continuous_multilinear_map.to_fun_eq_coe {R A B : Type} [semiring R]
    [add_comm_monoid A] [module R A] [topological_space A]
    [add_comm_monoid B] [module R B] [topological_space B]
    (f : continuous_multilinear_map R (λ _ : fin n, A) B) : f.to_fun = ⇑f := begin
  rw multilinear_map.to_fun_eq_coe, simp
end

-- A version of curry0 that doesn't assume commutativity
def curry0 (R A : Type) {B : Type} [semiring R]
    [add_comm_monoid A] [module R A] [topological_space A]
    [add_comm_monoid B] [module R B] [topological_space B]
    (b : B) : continuous_multilinear_map R (λ _ : fin 0, A) B := {
  to_fun := λ _, b,
  map_add' := by simp,
  map_smul' := by simp,
  cont := by continuity
}

lemma curry0_apply [add_comm_monoid A] [module R A] [topological_space A] [add_comm_monoid B] [module R B] [topological_space B]
    (b : B) (a : Π _ : fin 0, A) : curry0 R A b a = b := by rw [curry0, ←continuous_multilinear_map.to_fun_eq_coe]

lemma curry0_norm [normed_add_comm_group A] [normed_space 𝕜 A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (b : B) : ∥curry0 𝕜 A b∥ = ∥b∥ := begin
  apply le_antisymm, {
    apply continuous_multilinear_map.op_norm_le_bound,
    simp, intro a, rw [curry0_apply b a, finset.univ_eq_empty, finset.prod_empty], simp
  }, {
    have lo := continuous_multilinear_map.unit_le_op_norm (curry0 𝕜 A b) fin.elim0 _,
    rw curry0_apply at lo, assumption,
    rw pi.norm_def, simp
  }
end

-- fst as a continuous_multilinear_map
def fst_cmmap (R : Type) (A B : Type) [semiring R]
    [add_comm_monoid A] [module R A] [topological_space A]
    [add_comm_monoid B] [module R B] [topological_space B]
    : continuous_multilinear_map R (λ _ : fin 1, A × B) A := {
  -- Once we upgrade mathlib, this can be
  --   (continuous_linear_map.fst R A B).comp_continuous_multilinear_map
  --     (continuous_multilinear_map.of_subsingleton R (A × B) (0 : fin 1))
  -- and similarly for snd_cmmap.
  to_fun := λ z, (z 0).fst,
  map_add' := begin intros z i x y, have i0 : i = 0 := by simp, rw i0, simp end,
  map_smul' := begin intros z i s x, have i0 : i = 0 := by simp, rw i0, simp end,
  cont := by continuity
}

-- snd as a continuous_multilinear_map
def snd_cmmap (R : Type) (A B : Type) [semiring R]
    [add_comm_monoid A] [module R A] [topological_space A]
    [add_comm_monoid B] [module R B] [topological_space B]
    : continuous_multilinear_map R (λ _ : fin 1, A × B) B := {
  to_fun := λ z, (z 0).snd,
  map_add' := begin intros z i x y, have i0 : i = 0 := by simp, rw i0, simp end,
  map_smul' := begin intros z i s x, have i0 : i = 0 := by simp, rw i0, simp end,
  cont := by continuity
}

lemma fst_cmmap_apply [add_comm_monoid A] [module R A] [topological_space A] [add_comm_monoid B] [module R B] [topological_space B]
    (a : A) (b : B) : fst_cmmap R A B (λ _, (a,b)) = a := by rw [fst_cmmap, ←continuous_multilinear_map.to_fun_eq_coe]

lemma snd_cmmap_apply [add_comm_monoid A] [module R A] [topological_space A] [add_comm_monoid B] [module R B] [topological_space B]
    (a : A) (b : B) : snd_cmmap R A B (λ _, (a,b)) = b := by rw [snd_cmmap, ←continuous_multilinear_map.to_fun_eq_coe]

lemma fst_cmmap_norm [normed_ring A] [normed_algebra 𝕜 A] [norm_one_class A] [normed_ring B] [normed_algebra 𝕜 B] [norm_one_class B]
    : ∥fst_cmmap 𝕜 A B∥ = 1 := begin
  apply le_antisymm, {
    apply @continuous_multilinear_map.op_norm_le_bound 𝕜 _ (λ _ : fin 1, A × B) _ _ _ _ _ _ _ _ (fst_cmmap 𝕜 A B) (1 : ℝ) (by norm_num),
    intro z, simp,
    have e : z = (λ _, ((z 0).fst, (z 0).snd)), { apply funext, intro i, rw fin.eq_zero i, simp }, rw e,
    rw fst_cmmap_apply, simp, exact norm_fst_le (z 0)
  }, {
    have lo := @continuous_multilinear_map.unit_le_op_norm 𝕜 _ (λ _ : fin 1, A × B) A _ _ _ _ _ _ _ (fst_cmmap 𝕜 A B) (λ _, (1,1)) _,
    rw [fst_cmmap_apply, norm_one] at lo, assumption,
    rw pi_norm_le_iff, intro i, rw prod.norm_def, simp, norm_num
  }
end

lemma snd_cmmap_norm [normed_ring A] [normed_algebra 𝕜 A] [norm_one_class A] [normed_ring B] [normed_algebra 𝕜 B] [norm_one_class B]
    : ∥snd_cmmap 𝕜 A B∥ = 1 := begin
  apply le_antisymm, {
    apply @continuous_multilinear_map.op_norm_le_bound 𝕜 _ (λ _ : fin 1, A × B) _ _ _ _ _ _ _ _ (snd_cmmap 𝕜 A B) (1 : ℝ) (by norm_num),
    intro z, simp,
    have e : z = (λ _, ((z 0).fst, (z 0).snd)), { apply funext, intro i, rw fin.eq_zero i, simp }, rw e,
    rw snd_cmmap_apply, simp, exact norm_snd_le (z 0)
  }, {
    have lo := @continuous_multilinear_map.unit_le_op_norm 𝕜 _ (λ _ : fin 1, A × B) B _ _ _ _ _ _ _ (snd_cmmap 𝕜 A B) (λ _, (1,1)) _,
    rw [snd_cmmap_apply, norm_one] at lo, assumption,
    rw pi_norm_le_iff, intro i, rw prod.norm_def, simp, norm_num
  }
end

-- Lemmas for smul_cmmap
lemma update_0_0 (z : fin (n+1) → A) (x : A) : function.update (λ _ : fin 1, z 0) 0 x = (λ _ : fin 1, x) := begin
  apply funext, intro i,
  have i0 : i = 0 := by simp,
  rw i0, simp
end
lemma update_0_succ (f : fin (n+1) → A) (x : A) (i : fin n) : function.update f 0 x i.succ = f i.succ := begin
  rw function.update_apply, simp,
  have i0 := fin.succ_ne_zero i,
  finish
end
lemma update_nz_0 (f : fin (n+1) → A) {x : A} {i : fin (n+1)} (i0 : i ≠ 0) : function.update f i x 0 = f 0 :=
  by rw function.update_noteq i0.symm
lemma update_nz_succ (f : fin (n+1) → A) (x : A) {i : fin (n+1)} (i0 : i ≠ 0)
    : (λ j : fin n, function.update f i x j.succ) = function.update (λ j : fin n, f j.succ) (i.pred i0) x := begin
  apply funext, intro k,
  by_cases ki : k.succ = i, {
    have ki' : k = i.pred i0 := by simp_rw [←ki, fin.pred_succ],
    rw [ki,ki'], rw function.update_same, rw function.update_same
  }, {
    rw function.update_noteq ki,
    rw function.update_noteq _,
    by_contradiction,
    rw [h,fin.succ_pred _] at ki,
    finish
  }
end

-- Raw cons of two continuous multilinear maps
def smul_cmmap_fn [add_comm_monoid A] [module 𝕜 A] [topological_space A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    : (Π _ : fin (n+1), A) → B := 
  λ z, (x.to_fun (λ _, z 0)) • (xs.to_fun (λ i, z i.succ))

-- smul_cmmap_fn is multiadditive
lemma smul_cmmap_add [add_comm_monoid A] [module 𝕜 A] [topological_space A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    : ∀ (z : Π _ : fin (n+1), A) (i : fin (n+1)) (u v : A),
      smul_cmmap_fn x xs (function.update z i (u + v)) =
      smul_cmmap_fn x xs (function.update z i u) + smul_cmmap_fn x xs (function.update z i v) := begin
  intros z i u v,
  rw smul_cmmap_fn,
  by_cases i0 : i = 0, {
    rw i0, simp, simp_rw update_0_succ z _ _,
    have uv := x.map_add (λ _, z 0) 0 u v,
    rw update_0_0 z _ at uv,
    rw update_0_0 z _ at uv,
    rw update_0_0 z _ at uv,
    rw [uv, add_smul]
  }, {
    simp,
    simp_rw update_nz_0 z i0,
    rw update_nz_succ z _ i0,
    rw update_nz_succ z _ i0,
    rw update_nz_succ z _ i0,
    have uv := xs.map_add (λ j, z j.succ) (i.pred i0) u v,
    rw [uv, smul_add]
  }
end

-- smul_cmmap_fn commutes with scalars
lemma smul_cmmap_smul [add_comm_monoid A] [module 𝕜 A] [topological_space A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    : ∀ (z : Π _ : fin (n+1), A) (i : fin (n+1)) (s : 𝕜) (u : A),
      smul_cmmap_fn x xs (function.update z i (s • u)) = s • smul_cmmap_fn x xs (function.update z i u) := begin
  intros z i s u,
  rw smul_cmmap_fn,
  by_cases i0 : i = 0, {
    rw i0, simp, simp_rw update_0_succ z _ _,
    have su := x.map_smul (λ _, z 0) 0 s u,
    rw update_0_0 z _ at su,
    rw update_0_0 z _ at su,
    rw [su, smul_assoc]
  }, {
    simp,
    simp_rw update_nz_0 z i0,
    rw update_nz_succ z _ i0,
    rw update_nz_succ z _ i0,
    have su := xs.map_smul (λ j, z j.succ) (i.pred i0) s u,
    rw [su, smul_comm]
  }
end

-- smul_cmmap_fn is continuous
lemma smul_cmmap_cont [add_comm_monoid A] [module 𝕜 A] [topological_space A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    : continuous (smul_cmmap_fn x xs) := begin
  rw smul_cmmap_fn, continuity,
  exact x.cont, exact xs.cont
end

-- Cons two continuous_multilinear_maps together
def smul_cmmap (𝕜 A B : Type) [nontrivially_normed_field 𝕜]
    [add_comm_monoid A] [module 𝕜 A] [topological_space A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    : continuous_multilinear_map 𝕜 (λ _ : fin (n+1), A) B := {
  to_fun := smul_cmmap_fn x xs,
  map_add' := smul_cmmap_add x xs,
  map_smul' := smul_cmmap_smul x xs,
  cont := smul_cmmap_cont x xs,
}

lemma smul_cmmap_apply [add_comm_monoid A] [module 𝕜 A] [topological_space A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    (z : Π _ : fin (n+1), A)
    : smul_cmmap _ _ _ x xs z = x (λ _, z 0) • xs (λ i, z i.succ) := begin
  rw [smul_cmmap, ←continuous_multilinear_map.to_fun_eq_coe],
  simp, rw smul_cmmap_fn, simp
end

lemma smul_cmmap_norm [normed_add_comm_group A] [normed_space 𝕜 A] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : continuous_multilinear_map 𝕜 (λ _ : fin 1, A) 𝕜)
    (xs : continuous_multilinear_map 𝕜 (λ _ : fin n, A) B)
    : ∥smul_cmmap 𝕜 A B x xs∥ ≤ ∥x∥ * ∥xs∥ := begin
  apply continuous_multilinear_map.op_norm_le_bound, bound,
  intro z, rw smul_cmmap_apply,
  have xb := continuous_multilinear_map.le_op_norm x (λ _ : fin 1, z 0),
  have xsb := continuous_multilinear_map.le_op_norm xs (λ i : fin n, z i.succ),
  simp at xb xsb,
  have e0 := fin.prod_cons (∥z 0∥) (λ i : fin n, ∥z i.succ∥),
  simp at e0,
  have e1 : ∥z 0∥ = (λ i : fin (n+1), ∥z i∥) 0 := rfl,
  have e2 : (λ (i : fin n), ∥z i.succ∥) = fin.tail (λ i : fin (n+1), ∥z i∥) := rfl,
  nth_rewrite 0 e1 at e0, nth_rewrite 0 e2 at e0, rw fin.cons_self_tail at e0,
  calc ∥x (λ _ : fin 1, z 0) • xs (λ i : fin n, z i.succ)∥
      ≤ ∥x∥ * ∥z 0∥ * (∥xs∥ * finset.univ.prod (λ (i : fin n), ∥z i.succ∥)) : by { rw norm_smul, bound }
  ... = ∥x∥ * ∥xs∥ * (∥z 0∥ * finset.univ.prod (λ (i : fin n), ∥z i.succ∥)) : by ring
  ... = ∥x∥ * ∥xs∥ * finset.univ.prod (λ (i : fin (n + 1)), ∥z i∥) : by rw ←e0
end

-- A term of the general n-linear map on ℂ × ℂ, equal to z0^k * z1^(n-k) when applied to (λ _, (z0,z1))
noncomputable def term_cmmap (𝕜 : Type) [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
    : Π (n : ℕ), ℕ → E → continuous_multilinear_map 𝕜 (λ _ : fin n, 𝕜 × 𝕜) E
| 0 := λ _ x, curry0 _ _ x
| (n+1) := λ k x, smul_cmmap _ _ _ (if n < k then fst_cmmap 𝕜 𝕜 𝕜 else snd_cmmap 𝕜 𝕜 𝕜) (term_cmmap n k x)

lemma term_cmmap_apply [normed_add_comm_group E] [normed_space 𝕜 E] [smul_comm_class 𝕜 𝕜 E] [is_scalar_tower 𝕜 𝕜 E]
    (n k : ℕ) (a b : 𝕜) (x : E) : term_cmmap 𝕜 n k x (λ _, (a,b)) = a^(min k n) • b^(n-k) • x := begin
  induction n with n h, {
    rw term_cmmap, rw curry0_apply, simp
  }, {
    rw [term_cmmap, smul_cmmap_apply, h],
    by_cases nk : n < k, {
      simp [nk],
      rw fst_cmmap_apply,
      have nsk : n.succ ≤ k := nat.succ_le_iff.mpr nk,
      rw [min_eq_right (le_of_lt nk), min_eq_right nsk, nat.sub_eq_zero_of_le (le_of_lt nk), nat.sub_eq_zero_of_le nsk],
      simp, rw [←smul_assoc, smul_eq_mul, ←pow_succ]
    }, {
      simp [nk], simp at nk,
      rw snd_cmmap_apply,
      have nsk : k ≤ n.succ := nat.le_succ_of_le nk,
      rw [min_eq_left nk, min_eq_left nsk],
      rw [smul_comm b _, ←smul_assoc b _ _, smul_eq_mul, ←pow_succ, ←nat.sub_add_comm nk],
      assumption, assumption
    }
  }
end

lemma term_cmmap_norm (𝕜 : Type) [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
    (n k : ℕ) (x : E) : ∥term_cmmap 𝕜 n k x∥ ≤ ∥x∥ := begin
  induction n with n nh, {
    rw [term_cmmap, curry0_norm]
  }, {
    rw term_cmmap, simp,
    generalize ht : term_cmmap 𝕜 n k x = t, rw ht at nh,
    have tn := smul_cmmap_norm (ite (n < k) (fst_cmmap 𝕜 𝕜 𝕜) (snd_cmmap 𝕜 𝕜 𝕜)) t,
    by_cases nk : n < k, {
      simp [nk] at ⊢ tn, rw fst_cmmap_norm at tn, simp at tn, exact trans tn nh
    }, {
      simp [nk] at ⊢ tn, rw snd_cmmap_norm at tn, simp at tn, exact trans tn nh
    }
  }
end

-- conj as a continuous_linear_map
def conj_clm : ℂ →L[ℝ] ℂ := {
  to_fun := λ z, conj z,
  map_add' := by simp,
  map_smul' := by simp,
}
lemma conj_clm_apply (z : ℂ) : conj_clm z = conj z := rfl

-- The continuous linear map that evaluates a continuous multilinear map at a point
def cmmap_apply_cmap (𝕜 : Type) {I : Type} (A : I → Type) (B : Type)
    [fintype I] [decidable_eq I] [nontrivially_normed_field 𝕜]
    [Π i, normed_add_comm_group (A i)] [Π i, normed_space 𝕜 (A i)] [normed_add_comm_group B] [normed_space 𝕜 B]
    (x : Π i, A i) : continuous_multilinear_map 𝕜 A B →L[𝕜] B := {
  to_fun := λ f, f x,
  map_add' := by simp,
  map_smul' := by simp,
  cont := by simp [continuous_multilinear_map.continuous_eval_left],
}