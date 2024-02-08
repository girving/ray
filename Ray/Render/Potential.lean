import Ray.Approx.Box
import Ray.Approx.Floating.Conversion
import Ray.Approx.Series
import Ray.Dynamics.Mandelbrot
import Ray.Dynamics.Multibrot.PotentialLower
import Ray.Render.Color
import Ray.Render.Iterate

/-!
## Approximate computation of the Mandelbrot potential function

Fix `c`, and let `p z = potential 2 c z` be the potential function for the `c`-Julia set.  Say we
iterate `n` times to get `w = f^[n] z`.  There are two cases

#### Case 1: `abs w ≤ 4`

By `le_potential`, we have

  `0.216 ≤ p w`
  `0.216 ^ (2^n)⁻¹ ≤ p z`.

Not very many iterations will give us a lower bound very close to `1`.

#### Case 2: `4 ≤ abs w`

Increasing `n` by 1 if necessary, we have `6 ≤ abs w`.  By `potential_approx` and
`potential_error_le_of_z6`, we have

  `|p w - 1/abs w| ≤ 0.8095 / abs w ^ 1.927`

Here is an `abs w : 1/abs w, RHS` table for various `abs w` values:

  `w    6: 1/w 0.16667, error 2.563e-2, ratio 0.153`
  `w   32: 1/w 0.03125, error 1.018e-3, ratio 0.032`
  `w 1020: 1/w 0.00098, error 1.290e-6, ratio 0.001`

We then finish with

  `p z = p w ^ (2^n)⁻¹`
-/

open Complex (abs)
open Real (log)
open Set

private local instance : Fact (2 ≤ 2) := ⟨by norm_num⟩

/-!
### Potential approximation routines
-/

/-- Repeated square roots: `x ^ (2 ^ -n)` -/
@[irreducible, pp_dot] def Interval.iter_sqrt (x : Interval) (n : ℕ) : Interval :=
  exp ((log x).scaleB' (-.ofNat0 n))

/-- Approximate the potential of a large `z`.
    The estimate is independent of `c`, but is only valid if `6, abs c ≤ abs z` -/
@[irreducible] def Box.potential_large (z : Box) : Interval :=
  let s := z.normSq
  -- We have `|p j.z - s ^ (-1/2)| ≤ 0.8095 * s ^ -0.9635`
  -- `s ^ a = exp (a * log s)`, so we'll CSE the `log s`
  let log_s := s.log
  (-log_s.div2).exp.grow (0.8095 * (log_s * -0.9635).exp).hi

/-- Approximate the potential of a small `z` (valid for `abs c, abs z ≤ 4`) -/
@[irreducible] def Box.potential_small : Interval :=
  0.216 ∪ 1

/-- Approximate the Mandelbrot potential function at any point -/
@[irreducible] def Box.potential (c z : Box) (n : ℕ) (r : Floating) : Interval :=
  let cs := c.normSq.hi
  let i := iterate c z (cs.max 9) n
  match i.exit with
  | .nan => nan
  | .large =>
    -- We're outside radius `3` after `i.n` iterations.  Iterate a bit more to make `z` very large,
    -- then use our large `z` potential bound.  This should always work, so we use a large count.
    let rc := (r.mul r true).max (cs.max 36)  -- We need `6, abs c ≤ abs z`
    let j := iterate c i.z rc 1000
    match j.exit with
    | .large => (potential_large j.z).iter_sqrt (i.n + j.n)
    | _ => nan  -- If we fail to leave the large radius, give up
  | .count =>
    -- We know we're `≤ 3`.  Check that we're `≤ 4`, bail if not, and use the small bound if so.
    let zs := i.z.normSq.hi
    if zs = nan ∨ 16 < zs ∨ 16 < cs then nan else
    potential_small.iter_sqrt i.n

/-!
### Correctness proof
-/

/-- `Interval.iter_sqrt` is conservative -/
lemma Interval.mem_approx_iter_sqrt {a : ℝ} {x : Interval} {n : ℕ} (ax : a ∈ approx x) :
    a ^ (2 ^ (-n : ℝ) : ℝ) ∈ approx (x.iter_sqrt n) := by
  rw [iter_sqrt]
  by_cases a0 : a ≤ 0
  · simp only [log_nonpos a0 ax, nan_scaleB', exp_nan, approx_nan, mem_univ]
  · rw [Real.rpow_def_of_pos (not_le.mp a0)]
    mono

/-- `Interval.iter_sqrt` is conservative, more inferable version -/
@[mono] lemma Interval.mem_approx_iter_sqrt' {a : ℝ} {x : Interval} {n : ℕ}
    (a0 : 0 ≤ a) (ax : a^(2^n) ∈ approx x) : a ∈ approx (x.iter_sqrt n) := by
  generalize hb : a^(2^n) = b at ax
  have ab : a = b ^ (2 ^ (-n : ℝ) : ℝ) := by
    have e : (2:ℝ)^n = (2^n : ℕ) := by norm_num
    rw [←hb, Real.rpow_neg (by norm_num), Real.rpow_nat_cast, e,
      Real.pow_rpow_inv_natCast a0 (pow_ne_zero _ (by norm_num))]
  rw [ab]
  exact mem_approx_iter_sqrt ax

/-- `potential_small` covers all small values -/
lemma Box.approx_potential_small {c' z' : ℂ} (c4 : abs c' ≤ 4) (z4 : abs z' ≤ 4) :
    (superF 2).potential c' z' ∈ approx potential_small := by
  have ss : Icc 0.216 1 ⊆ approx potential_small := by
    rw [potential_small]
    apply Icc_subset_approx
    · exact Interval.approx_union_left (Interval.approx_ofScientific _ _ _)
    · exact Interval.approx_union_right Interval.mem_approx_one
  refine ss ⟨?_, ?_⟩
  · exact le_potential c4 z4
  · apply Super.potential_le_one

/-- `potential_large` covers all large values -/
lemma Box.approx_potential_large {c' z' : ℂ} {z : Box} (cz : abs c' ≤ abs z') (z6 : 6 ≤ abs z')
    (zm : z' ∈ approx z) : (superF 2).potential c' z' ∈ approx (potential_large z) := by
  rw [potential_large]
  apply Interval.approx_grow (potential_approx 2 (le_trans (by norm_num) z6) cz)
  · intro n
    rw [Ne.def, Interval.hi_eq_nan] at n
    refine le_trans (potential_error_le_of_z6 _ z6 cz) ?_
    apply Interval.le_hi n
    rw [div_eq_mul_inv, ←Real.rpow_neg (Complex.abs.nonneg _), Real.rpow_def_of_pos (by linarith)]
    have e : Real.log (Complex.abs z') * -1.927 = Real.log (Complex.abs z' ^ 2) * -0.9635 := by
      rw [Real.log_pow, Nat.cast_two, mul_comm (2:ℝ), mul_assoc]; norm_num
    rw [e]
    mono
  · have e : 1 / Complex.abs z' = Real.exp (-(Real.log (Complex.abs z' ^ 2) / 2)) := by
      simp only [one_div, Real.log_pow, Nat.cast_ofNat, neg_mul, Real.rpow_neg zero_le_two,
        Real.rpow_one, ←mul_assoc, mul_comm _ (2:ℝ)⁻¹]
      rw [mul_div_cancel_left _ two_ne_zero, Real.exp_neg, Real.exp_log (by linarith)]
    rw [e]
    mono

/-- `Box.potential` is conservative -/
@[mono] lemma Box.mem_approx_potential {c' z' : ℂ} {c z : Box}
    (cm : c' ∈ approx c) (zm : z' ∈ approx z) (n : ℕ) (r : Floating) :
    (superF 2).potential c' z' ∈ approx (Box.potential c z n r) := by
  set s := superF 2
  rw [Box.potential]
  generalize hcs : (normSq c).hi = cs
  generalize hi : iterate c z (cs.max 9) n = i
  by_cases csn : cs = nan
  · simp only [csn, Floating.nan_max, iterate_nan, Interval.approx_nan, mem_univ]
  simp only [hi, Interval.hi_eq_nan, Floating.val_lt_val]
  generalize hie : i.exit = ie
  induction ie
  · generalize hzs : (normSq i.z) = zs
    by_cases bad : zs = nan ∨ (16 : Floating).val < zs.hi.val ∨ (16 : Floating).val < cs.val
    · simp only [Floating.val_lt_val, bad, ↓reduceIte, Interval.approx_nan, mem_univ]
    · simp only [bad, ↓reduceIte]
      simp only [not_or, not_lt, ←hzs] at bad
      rcases bad with ⟨zsn, z4, c4⟩
      rw [Floating.val_ofNat] at c4 z4
      simp only [← hcs, Nat.cast_ofNat, Interval.hi_eq_nan] at c4 z4 csn zsn
      apply Interval.mem_approx_iter_sqrt' s.potential_nonneg
      simp only [←s.potential_eqn_iter, f_f'_iter]
      generalize hw' : (f' 2 c')^[i.n] z' = w'
      have le4 : Real.sqrt 16 ≤ 4 := by rw [Real.sqrt_le_iff]; norm_num
      apply approx_potential_small
      · exact le_trans (Box.abs_le_sqrt_normSq cm csn) (le_trans (Real.sqrt_le_sqrt c4) le4)
      · refine le_trans (Box.abs_le_sqrt_normSq ?_ zsn) (le_trans (Real.sqrt_le_sqrt z4) le4)
        rw [←hw', ←hi]
        exact mem_approx_iterate cm zm _
  · generalize hj : iterate c i.z ((r.mul r true).max (cs.max 36)) 1000 = j
    simp only [hj]
    generalize hje : j.exit = je
    induction je
    · simp only [Interval.approx_nan, mem_univ]
    · simp only
      generalize hn : i.n + j.n = n
      apply Interval.mem_approx_iter_sqrt' s.potential_nonneg
      simp only [←s.potential_eqn_iter, f_f'_iter, ←hj] at hje ⊢
      generalize hw' : (f' 2 c')^[n] z' = w'
      have izm : (f' 2 c')^[i.n] z' ∈ approx i.z := by rw [←hi]; exact mem_approx_iterate cm zm _
      have jl := iterate_large cm izm hje
      have jrn := ne_nan_of_iterate (hje.trans_ne (by decide))
      simp only [hj, ← Function.iterate_add_apply, add_comm _ i.n, hn, hw'] at jl
      simp only [ne_eq, Floating.max_eq_nan, not_or] at jrn
      rw [Floating.val_max jrn.1 (Floating.max_ne_nan.mpr jrn.2),
        Floating.val_max jrn.2.1 jrn.2.2, max_lt_iff, max_lt_iff, Floating.val_ofNat,
        Nat.cast_eq_ofNat] at jl
      apply approx_potential_large
      · refine le_trans ?_ (le_trans (Real.sqrt_le_sqrt jl.2.1.le) ?_)
        · simp only [← hcs, Interval.hi_eq_nan] at csn ⊢; exact abs_le_sqrt_normSq cm csn
        · simp only [map_nonneg, Real.sqrt_sq, le_refl]
      · refine le_trans ?_ (le_trans (Real.sqrt_le_sqrt jl.2.2.le) ?_)
        · have e : (36 : ℝ) = 6 ^ 2 := by norm_num
          rw [e, Real.sqrt_sq (by norm_num)]
        · simp only [map_nonneg, Real.sqrt_sq, le_refl]
      · rw [←hw', ←hn, add_comm _ j.n, Function.iterate_add_apply, ←hj]
        exact mem_approx_iterate cm izm _
    · simp only [Interval.approx_nan, mem_univ]
  · simp only [Interval.approx_nan, mem_univ]

/-- `Box.potential` is conservative, diagonal version -/
@[mono] lemma Box.mem_approx_potential' {c' : ℂ} {c : Box} (cm : c' ∈ approx c) (n : ℕ)
    (r : Floating) : _root_.potential 2 c' ∈ approx (Box.potential c c n r) := by
  simp only [_root_.potential, RiemannSphere.fill_coe, mem_approx_potential cm cm]
