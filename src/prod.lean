-- Facts about products

import analysis.calculus.fderiv
import analysis.normed.field.basic
import data.prod.basic
import data.set.basic
import topology.basic

open function (uncurry curry)
open metric (ball)
open prod (swap)
open_locale topological_space
noncomputable theory

variables {A B C : Type}
variables {𝕜 : Type} [nontrivially_normed_field 𝕜]

lemma flip_flip (f : A → B → C) : flip (flip f) = f := rfl

lemma swap_swap (s : set (A × B)) : swap '' (swap '' s) = s := begin
  nth_rewrite 1 set.image_swap_eq_preimage_swap,
  exact set.image_preimage_eq s prod.swap_surjective
end

lemma flip_swap (f : A → B → C) : uncurry (flip f) = (uncurry f) ∘ swap := rfl

lemma differentiable.swap
    [normed_add_comm_group A] [normed_add_comm_group B] [normed_space 𝕜 A] [normed_space 𝕜 B]
    : differentiable 𝕜 (swap : A × B → B × A) :=
  λ p, differentiable_at.prod (differentiable_snd _) (differentiable_fst _)

lemma differentiable_on.swap {s : set (A × B)}
    [normed_add_comm_group A] [normed_add_comm_group B] [normed_space 𝕜 A] [normed_space 𝕜 B]
    : differentiable_on 𝕜 swap s :=
  differentiable.differentiable_on differentiable.swap

lemma swap_is_open {s : set (A × B)} [topological_space A] [topological_space B]
    : is_open s → is_open (swap '' s) := begin
  rw set.image_swap_eq_preimage_swap, exact is_open.preimage continuous_swap
end

lemma swap_mem {a : A} {b : B} {s : set (A × B)} : (b,a) ∈ swap '' s ↔ (a,b) ∈ s := begin
  constructor, {
    intro m, simp at m, rcases m with ⟨a',b',m,hb,ha⟩, rwa [←ha, ←hb]
  }, {
    intro m, exact set.mem_image_of_mem swap m
  }
end

lemma swap_mem' {x : A × B} {s : set (B × A)} : x ∈ swap '' s ↔ swap x ∈ s := begin
  have h := @swap_mem _ _ x.snd x.fst s, simp at ⊢ h, exact h
end

lemma ball_prod_same' [pseudo_metric_space A] [pseudo_metric_space B]
    (x : A × B) (r : ℝ) : ball x r = ball x.fst r ×ˢ ball x.snd r := begin
  have s := ball_prod_same x.fst x.snd r, simp at s, exact s.symm
end

lemma ball_swap [pseudo_metric_space A] [pseudo_metric_space B]
    {x : A × B} {r : ℝ} : ball x.swap r = swap '' ball x r := begin
  apply set.ext, intro y,
  rw [swap_mem', metric.mem_ball, metric.mem_ball, prod.dist_eq, prod.dist_eq],
  simp, finish
end

lemma dist_swap [pseudo_metric_space A] [pseudo_metric_space B]
    {x y : A × B} : dist x.swap y.swap = dist x y := begin
  rw [prod.dist_eq, prod.dist_eq], simp, rw max_comm
end