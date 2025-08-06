import Interval.Box.Basic
import Ray.Dynamics.Mandelbrot

/-!
## Mandelbrot iteration

We iterate until either a cutoff is reached or we exceed a given radius, recording why we stopped.
-/

open Complex (abs)
open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-- Why we exited out of an iteration -/
inductive Exit : Type
  | count
  | large
  | nan
  deriving DecidableEq, Repr

/-- An iteration result -/
structure Iter where
  /-- The final value after iteration -/
  z : Box
  /-- Number of steps taken -/
  n : ℕ
  /-- Why we stopped iterating -/
  exit : Exit
  deriving Repr

/-- Helper for `iterate` -/
def iterate' (c z : Box) (rs : Floating) (k n : ℕ) : Iter := match n with
  | 0 => ⟨z, k, .count⟩
  | n + 1 =>
    -- Conveniently, `z.re.sqr` and `z.im.sqr` are needed by both iteration and squared magnitude
    let zr2 := z.re.sqr
    let zi2 := z.im.sqr
    let z2 := zr2.lo.add zi2.lo false
    if z2 = nan then ⟨z, k, .nan⟩ else  -- We hit nan, so stop computing
    if rs < z2 then ⟨z, k, .large⟩ else  -- Early exit if we know that `r ≤ |z|`
    let zri := z.re * z.im
    let w := ⟨zr2 - zi2, zri.scaleB 1⟩ + c
    iterate' c w rs (k+1) n

/-- Iterate until we reach a given count or definitely exceed a given squared radius.
    Returns the final iterate, and the number of steps taken. -/
def iterate (c z : Box) (rs : Floating) (n : ℕ) : Iter :=
  if rs = nan then ⟨z, 0, .nan⟩ else
  iterate' c z rs 0 n

/-- All correctness properties of `iterate'` in a single lemma -/
lemma iterate'_correct {c z : Box} {rs : Floating} {c' z' : ℂ} {rs' : ℝ}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (rsm : rs' ≤ rs.val) (k n : ℕ) :
    let i := iterate' c z rs k n
    let w' := (f' 2 c')^[i.n - k] z'
    k ≤ i.n ∧ w' ∈ approx i.z ∧ (i.exit = .large → rs' < ‖w'‖ ^ 2) := by
  induction' n with n h generalizing k z z'
  · simpa only [iterate', le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq, reduceCtorEq,
      false_implies, and_true, true_and]
  · simp only [iterate', Floating.val_lt_val]
    generalize hzr2 : z.re.sqr = zr2
    generalize hzi2 : z.im.sqr = zi2
    generalize hz2 : zr2.lo.add zi2.lo false = z2
    generalize hw : (⟨zr2 - zi2, (z.re * z.im).scaleB 1⟩ : Box) + c = w
    have we : w = z.sqr + c := by rw [←hw, Box.sqr, hzr2, hzi2]
    have wa : f' 2 c' z' ∈ approx w := by rw [we, f']; approx
    generalize hw' : f' 2 c' z' = w' at wa
    by_cases z2n : z2 = nan
    · simpa only [z2n, ↓reduceIte, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq,
        reduceCtorEq, false_implies, and_true, true_and]
    by_cases rz : rs.val < z2.val
    · simp only [z2n, rz, ite_true, le_refl, tsub_eq_zero_of_le, Function.iterate_zero, id_eq, zm,
      forall_true_left, true_and, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _),
      if_false]
      refine lt_of_le_of_lt rsm (lt_of_lt_of_le rz ?_)
      simp only [Complex.normSq_apply, ←sq, ←hz2, ←hzr2, ←hzi2] at z2n ⊢
      rcases Floating.ne_nan_of_add z2n with ⟨nr, ni⟩
      simp only [ne_eq, Interval.lo_eq_nan] at nr ni
      refine le_trans (Floating.add_le z2n) (add_le_add ?_ ?_)
      · apply Interval.lo_le nr; approx
      · apply Interval.lo_le ni; approx
    · simp only [rz, ite_false, z2n]
      generalize hi : iterate' c w rs (k + 1) n = i
      specialize h wa (k+1)
      simp only [hi] at h
      refine ⟨by omega, ?_⟩
      have ie : i.n - k = (i.n - (k + 1)) + 1 := by omega
      rw [ie, Function.iterate_succ_apply, hw']
      exact h.2

/-- `iterate` produces a correct iterate -/
@[approx] lemma mem_approx_iterate {c z : Box} {rs : Floating} {c' z' : ℂ}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (n : ℕ) :
    (f' 2 c')^[(iterate c z rs n).n] z' ∈ approx (iterate c z rs n).z := by
  rw [iterate]
  by_cases rsn : rs = nan
  · simpa only [rsn, ite_true, Function.iterate_zero, id_eq]
  · simp only [rsn, ite_false]
    exact (iterate'_correct cm zm (le_refl _) 0 n).2.1

/-- If `iterate` claims the result is large, it is` -/
lemma iterate_large {c z : Box} {rs : Floating} {n : ℕ} {c' z' : ℂ}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (l : (iterate c z rs n).exit = .large) :
    rs.val < ‖(f' 2 c')^[(iterate c z rs n).n] z'‖ ^ 2 := by
  rw [iterate] at l ⊢
  by_cases rsn : rs = nan
  · simp only [rsn, ↓reduceIte, reduceCtorEq] at l
  · simp only [rsn, ite_false] at l ⊢
    simpa only [not_lt, Nat.sub_zero] using (iterate'_correct cm zm (le_refl _) 0 n).2.2 l

/-- Iterate exits with `.nan` when `rs = nan` -/
@[simp] lemma iterate_nan {c z : Box} {n : ℕ} : (iterate c z nan n).exit = .nan := by
  rw [iterate]; simp only [ite_true]

/-- Iterate exits with `.nan` when `rs = nan` -/
@[simp] lemma ne_nan_of_iterate {c z : Box} {rs : Floating} {n : ℕ}
    (e : (iterate c z rs n).exit ≠ .nan) : rs ≠ nan := by
  contrapose e; simp only [ne_eq, not_not] at e
  simp only [e, iterate_nan, ne_eq, not_true_eq_false, not_false_eq_true]
