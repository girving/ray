import Ray.Dynamics.Multibrot.BottcherInv
import Ray.Dynamics.Multibrot.Isomorphism
import Ray.Dynamics.Multibrot.KoebeInf

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
lemma sray_le_weak (c16 : 16 < ‖c‖) (xc : ‖x‖ < ‖c‖⁻¹ / 4) :
    ‖((superF d).ray c x).toComplex‖ ≤ 2 * ‖x‖⁻¹ := by
  set s := superF d
  obtain ⟨z,zm,_,zp,zx⟩ := sbottcher_inv_small_mem_preimage (d := d) c16 xc
  have b := zx ▸ sbottcher_inv_approx_z d c16 (z := z) (by linarith)
  nth_rw 1 [← zx]
  simp only [sbottcher_inv, s.ray_bottcher zp]
  simp only [toComplex_inv, toComplex_coe, norm_inv]
  refine le_trans ?_ (b := ‖(x / 2)‖⁻¹) (by simp [div_eq_mul_inv])
  have z16 : ‖z‖ < 16⁻¹ := lt_of_lt_of_le zm (inv_anti₀ (by norm_num) c16.le)
  by_cases z0 : z = 0
  · simp [z0]
    bound
  by_cases x0 : x = 0
  · contrapose b
    simp only [x0, zero_sub, norm_neg, pow_two, ← mul_assoc, not_le]
    exact mul_lt_of_lt_one_left (by positivity) (by linarith)
  apply inv_anti₀ (by simp [x0])
  simp only [Complex.norm_div, Complex.norm_ofNat]
  calc ‖x‖ / 2
    _ = ‖x - z + z‖ / 2 := by ring_nf
    _ ≤ (‖x - z‖ + ‖z‖) / 2 := by bound
    _ ≤ (16 * ‖z‖ ^ 2 + ‖z‖) / 2 := by bound
    _ = ‖z‖ * (16 * ‖z‖ + 1) / 2 := by ring
    _ ≤ ‖z‖ * (16 * 16⁻¹ + 1) / 2 := by bound
    _ = ‖z‖ := by ring

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
lemma sray_le (c16 : 16 < ‖c‖) (xc : ‖x‖ < ‖c‖⁻¹ / 4) :
    ‖((superF d).ray c x).toComplex - x⁻¹‖ ≤ 64 := by
  set s := superF d
  obtain ⟨z,zc,zx,zp,szx⟩ := sbottcher_inv_small_mem_preimage (d := d) c16 xc
  have b := szx ▸ sbottcher_inv_approx_z d c16 (z := z) (by linarith)
  nth_rw 1 [← szx]
  simp only [sbottcher_inv, s.ray_bottcher zp, toComplex_inv, toComplex_coe]
  have ci : ‖c‖⁻¹ ≤ 16⁻¹ := inv_anti₀ (by norm_num) c16.le
  exact norm_inv_sub_inv_le (by linarith) (by norm_num) b (by linarith)

/-- A strong bound on `ray d`, using the Böttcher approximation and the Koebe quarter theorem -/
lemma ray_le (z8 : ‖z‖ < 64⁻¹) : ‖(ray d z).toComplex - z⁻¹‖ ≤ 64 := by
  set s := superF d
  obtain ⟨c,cz,cm,cx⟩ := bottcher_inv_small_mem_preimage (d := d) (z := z) (by linarith)
  by_cases c0 : c = 0
  · simp only [c0, bottcher_inv_zero] at cx
    simp [← cx]
  have c16 : ‖c‖ < 16⁻¹ := by linarith
  have ci16 : 16 < ‖c⁻¹‖ := by
    rw [norm_inv, lt_inv_comm₀ (by norm_num) (norm_pos_iff.mpr c0)]
    exact lt_of_le_of_lt cz (by linarith)
  have cx' : bottcher' d c⁻¹ = z := by
    simp only [← cx, bottcher_inv, bottcher, inv_coe c0, fill_coe]
  have b := bottcher_approx d ci16
  simp only [inv_inv, norm_inv, cx'] at b
  nth_rw 1 [← cx]
  rw [bottcher_inv, ray_bottcher cm, inv_coe c0, toComplex_coe]
  apply norm_inv_sub_inv_le c16 (by bound) b (by linarith)
