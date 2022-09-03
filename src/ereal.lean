-- ereal facts

import analysis.special_functions.log.basic
import data.real.basic
import data.real.ennreal
import data.real.ereal
import topology.instances.ereal

import simple

open linear_order (min)
open_locale nnreal ennreal
noncomputable theory

-- log : ereal → ereal, turning nonpositives to -∞ and preserving ∞
def ereal.log : ereal → ereal
| ⊥ := ⊥
| (x : ℝ) := if x ≤ 0 then ⊥ else ↑(x.log)
| ⊤ := ⊤

-- exp : ereal → ereal, turning -∞ into 0 and preserving ∞
def ereal.exp : ereal → ereal
| ⊥ := 0
| (x : ℝ) := ↑(x.exp)
| ⊤ := ⊤

-- Is an ereal finite?
def ereal.is_finite (x : ereal) := ∃ y : ℝ, x = ↑y

@[simp] lemma ereal.coe_finite {x : ℝ} : ereal.is_finite (x : ereal) := by simp [ereal.is_finite]
lemma ereal.bot_infinite : ¬ereal.is_finite ⊥ := by simp [ereal.is_finite]
lemma ereal.top_infinite : ¬ereal.is_finite ⊤ := by simp [ereal.is_finite]
lemma ereal.is_finite.ne_bot {x : ereal} : ereal.is_finite x → x ≠ ⊥ := begin
  intro f, by_contradiction, rw h at f, have nf := ereal.bot_infinite, finish
end

instance : densely_ordered ereal := ⟨begin
  intros x y xy,
  induction x using ereal.rec,
  induction y using ereal.rec, finish,
  existsi ↑(y - 1), simp, apply_instance,
  existsi (0 : ereal), simp,
  induction y using ereal.rec, finish,
  simp at xy, rcases exists_between xy with ⟨a,lo,hi⟩, existsi ↑a, simp, finish, apply_instance,
  existsi ↑(x + 1), rw ereal.coe_lt_coe_iff, simp, rw ←ereal.coe_one, exact ereal.coe_lt_top _,
  simp at xy, finish,
end⟩

@[simp] lemma ereal.log_zero : ereal.log 0 = ⊥ := by { rw [←ereal.coe_zero, ereal.log], simp }
@[simp] lemma ereal.log_bot : ereal.log ⊥ = ⊥ := by simp [ereal.log]
@[simp] lemma ereal.log_top : ereal.log ⊤ = ⊤ := by simp [ereal.log]
@[simp] lemma ereal.exp_bot : ereal.exp ⊥ = 0 := by simp [ereal.exp]
@[simp] lemma ereal.exp_top : ereal.exp ⊤ = ⊤ := by simp [ereal.exp]
@[simp] lemma ereal.log_coe {x : ℝ} (h : x > 0) : ereal.log x = ↑(x.log) := begin rw ereal.log, simp, exact not_le_of_gt h end
@[simp] lemma ereal.exp_coe {x : ℝ} : ereal.exp x = ↑(x.exp) := rfl

@[simp] lemma ereal.log_exp {x : ereal} : x.exp.log = x := begin
  induction x using ereal.rec, simp, simp [ereal.log], apply not_le_of_gt, exact real.exp_pos _, simp,
end

@[simp] lemma ereal.exp_log {x : ereal} (h : x ≥ 0) : x.log.exp = x := begin
  induction x using ereal.rec, simp at h, finish, swap, simp,
  simp at h, rw [←ereal.coe_zero, ereal.coe_le_coe_iff] at h,
  by_cases z : x = 0, { rw z, simp },
  simp [lt_of_le_of_ne h (ne.symm z), real.exp_log],
end

lemma ereal.log_lt_top_iff {x : ereal} : x.log < ⊤ ↔ x < ⊤ := begin
  induction x using ereal.rec, simp, simp [ereal.log], by_cases x0 : x ≤ 0, simp [x0], simp [x0], simp,
end

lemma ereal.exp_pos_iff {x : ereal} : 0 < x.exp ↔ ⊥ < x := begin
  induction x using ereal.rec,
  simp, simp, rw [←ereal.coe_zero, ereal.coe_lt_coe_iff], simp [real.exp_pos], simp,
end

lemma ereal.log_eq_iff_eq_exp {x y : ereal} (h : x ≥ 0) : x.log = y ↔ x = y.exp := begin
  constructor, { intro e, rw ←e, simp [h] }, { intro e, rw e, simp }
end

lemma ereal.log_lt_iff_lt_exp {x y : ereal} (h : x ≥ 0) : x.log < y ↔ x < y.exp := begin
  induction x using ereal.rec, finish, swap, simp,
  rw ←ereal.coe_zero at h,
  have h' := ereal.coe_le_coe_iff.mp h,
  by_cases x0 : x = 0, { rw x0, simp [real.exp_pos], exact ereal.exp_pos_iff.symm },
  have xp := lt_of_le_of_ne h' (ne.symm x0),
  induction y using ereal.rec, simp, assumption,
  simp [ereal.exp_coe, ereal.coe_lt_coe_iff],
  rw [ereal.log_coe xp, ereal.coe_lt_coe_iff],
  exact real.log_lt_iff_lt_exp xp,
  rw ereal.log_coe xp, simp,
end

lemma ereal.log_le_iff_le_exp {x y : ereal} (h : x ≥ 0) : x.log ≤ y ↔ x ≤ y.exp := begin
  by_cases e : x = y.exp, { rw e, simp },
  constructor, {
    intro w, rw ←ereal.log_eq_iff_eq_exp h at e,
    have s := lt_of_le_of_ne w e,
    rw ereal.log_lt_iff_lt_exp h at s,
    exact le_of_lt s,
  }, {
    intro w,
    have s := lt_of_le_of_ne w e,
    rw ←ereal.log_lt_iff_lt_exp h at s,
    exact le_of_lt s,
  }
end

lemma ereal.coe_sub {x y : ℝ} : ((x - y : ℝ) : ereal) = (x : ereal) - (y : ereal) := rfl

lemma monotone_ereal_log : monotone ereal.log := begin
  intros x y,
  induction x using ereal.rec, simp,
  induction y using ereal.rec, simp,
  simp [ereal.log], intro xy,
  by_cases y0 : y ≤ 0, { simp [y0], exact not_lt_of_ge (trans y0 xy) },
  by_cases x0 : x ≤ 0, { simp [x0] },
  simp [x0, y0], simp at x0 y0, rwa real.log_le_log x0 y0,
  simp, simp, intro e, rw e, simp,
end

lemma ereal.log_surjective : function.surjective ereal.log := begin
  rw function.surjective, intro x, existsi x.exp, simp,
end

lemma continuous_ereal_log : continuous ereal.log :=
  monotone_ereal_log.continuous_of_surjective ereal.log_surjective

-- Clamp x into the interval [lo, hi]
def clamp {X : Type} [linear_order X] (x lo hi : X) : X := max lo (min hi x)

-- Simple facts about clamp
@[simp] lemma clamp_bot {X : Type} [linear_order X] [order_bot X] {lo hi : X} : clamp ⊥ lo hi = lo := by simp [clamp]
@[simp] lemma clamp_top {X : Type} [linear_order X] [order_top X] {lo hi : X} : clamp ⊤ lo hi = max lo hi := by simp [clamp]
lemma le_clamp {X : Type} [linear_order X] (x lo hi : X) : lo ≤ clamp x lo hi := by simp [clamp, le_max_left]
lemma clamp_le {X : Type} [linear_order X] (x lo hi : X) : clamp x lo hi ≤ max lo hi := by simp [clamp]
lemma monotone.clamp {X : Type} [linear_order X] (lo hi : X) : monotone (λ x, clamp x lo hi) :=
  monotone.comp (monotone.max monotone_const monotone_id) (monotone.min monotone_const monotone_id)
lemma le_clamp_of_le_hi {X : Type} [linear_order X] (x lo hi : X) : x ≤ hi → x ≤ clamp x lo hi := λ h, by simp [clamp, h]
lemma clamp_le_lox {X : Type} [linear_order X] (x lo hi : X) : clamp x lo hi ≤ max lo x := by simp [clamp, max_le_iff]

-- Clamp is the identity inside the bounds
lemma clamp_inv {X : Type} [linear_order X] (x y : X) {lo hi : X} (y0 : lo < y) (y1 : y < hi) : clamp x lo hi = y ↔ x = y := begin
  rw clamp, constructor, {
    intro h,
    by_cases x1 : x < hi, {
      simp [le_of_lt x1] at h,
      by_cases x0 : lo < x, simp [le_of_lt x0] at h, exact h, simp at x0, simp [x0] at h, rw h at y0, finish, 
    }, {
      simp at x1, simp [x1] at h, rw ←h at y1, simp at y1, finish,
    }
  }, {
    intro h, rw h, simp [le_of_lt y0, le_of_lt y1],
  },
end

-- Clamp is continuous
lemma continuous_clamp {X : Type} [linear_order X] [topological_space X] [order_topology X]
    (lo hi : X) : continuous (λ x, clamp x lo hi) :=
  continuous.comp (continuous.max continuous_const continuous_id) (continuous.min continuous_const continuous_id)
 
-- Simple facts about min, max, and ereal coe
@[simp] lemma ereal.min_coe {x y : ℝ} : min (x : ereal) y = ↑(min x y) := begin
  by_cases h : x ≤ y, simp [h], simp at h, simp [le_of_lt h],
end
@[simp] lemma ereal.max_coe {x y : ℝ} : max (x : ereal) y = ↑(max x y) := begin
  by_cases h : x ≤ y, simp [h], simp at h, simp [le_of_lt h],
end
@[simp] lemma clamp_ereal_coe {x lo hi : ℝ} : clamp (x : ereal) lo hi = ↑(clamp x lo hi) := by simp [clamp]
@[simp] lemma ereal.min_coe_finite {x y : ℝ} : (min (x : ereal) y).is_finite := ⟨min x y, by simp⟩
@[simp] lemma ereal.max_coe_finite {x y : ℝ} : (max (x : ereal) y).is_finite := ⟨max x y, by simp⟩

-- Clamping ereals produces reals for real intervals
lemma ereal_clamp_finite (x : ereal) (lo hi : ℝ) : (clamp x ↑lo ↑hi).is_finite := begin
  rw clamp, induction x using ereal.rec, simp, simp, simp,
end
@[simp] lemma ereal.clamp_ne_bot {x : ereal} {lo hi : ℝ} : clamp x lo hi ≠ ⊥ :=
  ne_of_gt (lt_of_lt_of_le (by simp) (le_clamp x lo hi))
@[simp] lemma ereal.clamp_ne_top {x : ereal} {lo hi : ℝ} : clamp x lo hi ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (clamp_le x lo hi) (by simp))

-- Clamp an ereal to be between two real values
def ereal.clamp (x : ereal) (lo hi : ℝ) : ℝ := (clamp x ↑lo ↑hi).to_real

-- Facts about ereal.clamp
@[simp] lemma ereal.clamp_bot {lo hi : ℝ} : ereal.clamp ⊥ lo hi = lo := by simp [ereal.clamp]
@[simp] lemma ereal.clamp_top {lo hi : ℝ} : ereal.clamp ⊤ lo hi = max lo hi := by simp [ereal.clamp]
@[simp] lemma ereal.clamp_coe {x lo hi : ℝ} : ereal.clamp x lo hi = clamp x lo hi := by simp [ereal.clamp]
lemma ereal.le_clamp {x : ereal} {lo hi : ℝ} : lo ≤ x.clamp lo hi :=
  ereal.to_real_le_to_real (le_clamp x lo hi) (by simp) (by simp)
lemma ereal.clamp_le (x : ereal) (lo hi : ℝ) : x.clamp lo hi ≤ max lo hi :=
  ereal.to_real_le_to_real (clamp_le x lo hi) (by simp) (by simp)
lemma monotone.ereal_clamp (lo hi : ℝ) : monotone (λ x, ereal.clamp x lo hi) :=
  λ x y xy, ereal.to_real_le_to_real (monotone.clamp (lo : ereal) hi xy) (by simp) (by simp)
lemma ereal.le_clamp_of_le_hi (x : ereal) (lo hi : ℝ) : x ≤ hi → x ≤ x.clamp lo hi := begin
  intro h, rw ereal.clamp,
  rcases ereal_clamp_finite x lo hi with ⟨y,hy⟩, rw hy, simp, rw ←hy,
  exact le_clamp_of_le_hi x lo hi h,
end
lemma ereal.clamp_le_lox (x : ereal) (lo hi : ℝ) : ↑(x.clamp lo hi) ≤ max ↑lo x := begin
  rw ereal.clamp, have h := clamp_le_lox x lo hi,
  rcases ereal_clamp_finite x lo hi with ⟨y,hy⟩, rw hy at ⊢ h, exact trans (by simp) h,
end

-- ereal.clamp is the identity inside the bounds
lemma ereal.clamp_inv {x : ereal} {lo hi y : ℝ} (y0 : lo < y) (y1 : y < hi) : x.clamp lo hi = y ↔ x = y := begin
  have h := clamp_inv x y (ereal.coe_lt_coe_iff.mpr y0) (ereal.coe_lt_coe_iff.mpr y1),
  simp [ereal.clamp], rcases ereal_clamp_finite x lo hi with ⟨z,cz⟩, simp [cz] at h ⊢, assumption,
end

-- ereal.clamp is continuous in x
lemma continuous.ereal_clamp {lo hi : ℝ} : continuous (λ x, ereal.clamp x lo hi) := begin
  simp_rw ereal.clamp,
  apply ereal.continuous_on_to_real.comp_continuous (continuous_clamp _ _),
  simp,
end

-- Convert from ereal to ennreal, clamping negative values to 0
def ereal.to_ennreal : ereal → ennreal
| ⊤ := ⊤
| (x : ℝ) := ennreal.of_real x
| ⊥ := 0

lemma ereal.to_ennreal_neg {x : ereal} (h : x ≤ 0) : x.to_ennreal = 0 := begin
  induction x using ereal.rec,
  simp [ereal.to_ennreal],
  simp [ereal.to_ennreal],
  have e : (0 : ereal) = ((0 : ℝ) : ereal) := by simp,
  rw [e, ereal.coe_le_coe_iff] at h, exact h,
  simp at h, finish,
end

@[simp] lemma ereal.to_real_to_ennreal {x : ereal} : x.to_ennreal.to_real = max 0 x.to_real := begin
  by_cases h : x < 0, {
    simp [ereal.to_ennreal_neg (le_of_lt h)],
    induction x using ereal.rec, simp,
    have e : (0 : ereal) = ((0 : ℝ) : ereal) := by simp,
    rw [e, ereal.coe_lt_coe_iff] at h, simp [le_of_lt h],
    simp,
  }, {
    simp at h,
    induction x using ereal.rec,
    simp [ereal.to_ennreal], swap, simp [ereal.to_ennreal],
    simp [ereal.to_ennreal],
    have e : (0 : ereal) = ((0 : ℝ) : ereal) := by simp,
    rw [e, ereal.coe_le_coe_iff] at h, simp [ennreal.to_real_of_real h, h],
  }
end

lemma ereal.to_ennreal_ne_top_iff {x : ereal} : x.to_ennreal ≠ ⊤ ↔ x ≠ ⊤ := begin
  induction x using ereal.rec, simp [ereal.to_ennreal], simp [ereal.to_ennreal], simp [ereal.to_ennreal],
end

@[simp] lemma ereal.to_ennreal_coe {x : ennreal} : (x : ereal).to_ennreal = x := begin
  induction x using with_top.rec_top_coe,
  simp [ereal.to_ennreal],
  rw ←ennreal.to_real_eq_to_real,
  simp, swap, simp,
  rw ereal.to_ennreal_ne_top_iff, simp,
end

lemma ereal.coe_to_ennreal {x : ereal} (h : x ≥ 0) : ↑(x.to_ennreal) = x := begin
  induction x using ereal.rec,
  simp at h, simp [h], swap, simp [ereal.to_ennreal],
  simp [ereal.to_ennreal],
  have e : (0 : ereal) = ((0 : ℝ) : ereal) := by simp,
  have h' := simple.ge_to_le h,
  rw [e, ereal.coe_le_coe_iff] at h',
  rw ←real.coe_to_nnreal _ h',
  generalize hy : x.to_nnreal = y,
  rw ←ereal.coe_nnreal_eq_coe_real,
  simp,
end