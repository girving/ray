module
public import Ray.Multibrot.Isomorphism
import Ray.Misc.Bound
import Ray.Multibrot.Bottcher
import Ray.Multibrot.BottcherInv
import Ray.Multibrot.Isomorphism
import Ray.Multibrot.KoebeInf
import Ray.Multibrot.Rinv

/-!
## Effective bounds on `s.ray` for multibrot sets

`BottcherInv.lean` shows that `sbottcher_inv d c x` covers a large disk around the origin.
Inverted, this implies an upper bound on `s.ray` for small `x`.
-/

open RiemannSphere
open OneDimension
open Set
open scoped OnePoint RiemannSphere Topology
noncomputable section

-- We fix `d ≥ 2`
variable {d : ℕ} [Fact (2 ≤ d)]
variable {c x z : ℂ}

/-- A weak upper bound on `s.ray`, using the Koebe quarter theorem -/
lemma sray_le_weak (xc : ‖x‖ < rinv 4⁻¹ c / 4) :
    ‖((superF d).ray c x).toComplex‖ ≤ 1.24 * ‖x‖⁻¹ := by
  set s := superF d
  generalize hk : (1.24 : ℝ) = k
  have k0 : 0 < k := by bound
  obtain ⟨z,zm,_,zp,zx⟩ := sbottcher_inv_small_mem_preimage (d := d) xc
  have b := zx ▸ sbottcher_inv_approx_z d (z := z) (by linarith)
  nth_rw 1 [← zx]
  simp only [sbottcher_inv_def, s.ray_bottcher zp]
  simp only [toComplex_inv, toComplex_coe, norm_inv]
  refine le_trans ?_ (b := ‖(x / k)‖⁻¹) (by simp [div_eq_mul_inv, abs_of_pos k0])
  have z16 : ‖z‖ ≤ 4⁻¹ := by rw [lt_div_iff₀ (by norm_num), lt_rinv] at xc; linarith
  by_cases z0 : z = 0
  · simp [z0]
    bound
  by_cases x0 : x = 0
  · contrapose b
    simp only [x0, zero_sub, norm_neg, pow_two, ← mul_assoc, not_le]
    exact mul_lt_of_lt_one_left (by positivity) (by linarith)
  apply inv_anti₀ (by simp [x0, k0.ne'])
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos k0]
  calc ‖x‖ / k
    _ = ‖x - z + z‖ / k := by ring_nf
    _ ≤ (‖x - z‖ + ‖z‖) / k := by bound
    _ ≤ (0.943 * ‖z‖ ^ 2 + ‖z‖) / k := by bound
    _ = ‖z‖ * (0.943 * ‖z‖ + 1) / k := by ring
    _ ≤ ‖z‖ * (0.943 * 4⁻¹ + 1) / k := by bound
    _ ≤ ‖z‖ := by rw [← hk]; ring_nf; bound

/-- Bound the difference of inverses using a bound on the difference -/
lemma norm_inv_sub_inv_le {a b : ℝ} {z w : ℂ} (za : ‖z‖ < a⁻¹) (b0 : 0 ≤ b)
    (near : ‖w - z‖ ≤ a * ‖z‖ ^ 2) (weak : ‖z‖ ≤ b / a * ‖w‖) : ‖z⁻¹ - w⁻¹‖ ≤ b := by
  have a0 : 0 < a := inv_pos.mp (lt_of_le_of_lt (norm_nonneg _) za)
  have za' : a * ‖z‖ < 1 := lt_of_lt_of_le (mul_lt_mul_of_pos_left za a0) (by simp [a0.ne'])
  by_cases z0 : z = 0
  · simp only [z0, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, norm_le_zero_iff] at near
    simp only [z0, inv_zero, near, sub_self, norm_zero, b0]
  by_cases w0 : w = 0
  · contrapose near
    simp only [w0, zero_sub, norm_neg, pow_two, ← mul_assoc, not_le]
    exact mul_lt_of_lt_one_left (by positivity) za'
  have zw0 : 0 < ‖w * z‖ := by simp; positivity
  rw [← mul_le_mul_iff_left₀ zw0]
  simp only [← norm_mul, sub_mul]
  field_simp [w0, z0]
  refine le_trans near ?_
  simp only [norm_mul]
  have wn0 : 0 < ‖w‖ := norm_pos_iff.mpr w0
  have zn0 : 0 < ‖z‖ := norm_pos_iff.mpr z0
  simp only [pow_two, ← mul_assoc, mul_right_comm _ ‖z‖]
  refine mul_le_mul_of_nonneg_right ?_ (by bound)
  refine le_trans (mul_le_mul_of_nonneg_left weak a0.le) ?_
  simp only [← mul_assoc, mul_div_cancel₀ _ a0.ne', le_refl]

/-- A strong bound on `s.ray`, using the Böttcher approximation to boost the weak bound -/
public lemma sray_le (xc : ‖x‖ < rinv 4⁻¹ c / 4) :
    ‖((superF d).ray c x).toComplex - x⁻¹‖ ≤ 4 := by
  set s := superF d
  obtain ⟨z,zx,zc,zp,szx⟩ := sbottcher_inv_small_mem_preimage (d := d) xc
  have b := szx ▸ sbottcher_inv_approx_z d (z := z) (by linarith)
  nth_rw 1 [← szx]
  simp only [sbottcher_inv_def, s.ray_bottcher zp, toComplex_inv, toComplex_coe]
  have z4 : ‖z‖ ≤ 4⁻¹ := by
    rw [lt_div_iff₀ (by norm_num), lt_rinv] at xc
    linarith
  exact norm_inv_sub_inv_le (by linarith) (by norm_num) b (le_trans zx (by bound))

/-- A strong bound on `ray d`, using the Böttcher approximation and the Koebe quarter theorem -/
public lemma ray_le (z8 : ‖z‖ < 16⁻¹) : ‖(ray d z).toComplex - z⁻¹‖ ≤ 4 := by
  set s := superF d
  obtain ⟨c,cz,cm,cx⟩ := bottcher_inv_small_mem_preimage (d := d) (z := z) (by linarith)
  by_cases c0 : c = 0
  · simp only [c0, bottcher_inv_zero] at cx
    simp [← cx]
  have c4 : ‖c‖ < 4⁻¹ := by linarith
  have ci4 : 4 < ‖c⁻¹‖ := by
    rw [norm_inv, lt_inv_comm₀ (by norm_num) (norm_pos_iff.mpr c0)]
    exact lt_of_le_of_lt cz (by linarith)
  have cx' : bottcher' d c⁻¹ = z := by
    simp only [← cx, bottcher_inv_def, bottcher, inv_coe c0, fill_coe]
  have b := bottcher_approx d (by linarith)
  simp only [inv_inv, norm_inv, cx'] at b
  nth_rw 1 [← cx]
  rw [bottcher_inv_def, ray_bottcher cm, inv_coe c0, toComplex_coe]
  exact norm_inv_sub_inv_le (by linarith) (by bound) b (le_trans cz (by bound))
