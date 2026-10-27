import Step2.D2.D2S01
import Step2.D2.D2Bv1

/-!
# Sharp line 3, part 1: the profile `Φ` of `-(λ+m²)² ∂_λ ĉ_T`

With `f(w) = w² ψ(w) + 2Ψ₁(w)` (`f' = w² ψ'`, `f(0) = 2c₀`):

* `PhiH z = 1 - (2c₀)⁻¹ ∑_i ω_i f(z/2^i)`, `PhiH' z = -(2c₀)⁻¹ ∑_i ω_i f'(z/2^i)/2^i`;
* `PhiE y = PhiH (y/κ)`;
* `PhiE_decay`: `|1 - Φ(y)| + |yΦ'(y)| ≤ K (1+y)^{-3}`;
* `PhiE_profile`: `Φ` is a profile `0 → 1`;
* `PhiE_small`: `|Φ(y)| ≤ K y⁴`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- `f(w) = w² ψ(w) + 2Ψ₁(w)`. -/
def fP (w : ℝ) : ℝ := w ^ 2 * ψ w + 2 * Psi1 w

/-- `f'(w) = w² ψ'(w)`. -/
def fP' (w : ℝ) : ℝ := w ^ 2 * ψd w

theorem hasDerivAt_fP (w : ℝ) : HasDerivAt fP (fP' w) w := by
  have h1 := ((hasDerivAt_id w).pow 2).mul (hasDerivAt_ψ w)
  have h2 := (hasDerivAt_Psi1 w).const_mul 2
  convert h1.add h2 using 1
  simp [fP']; ring

theorem fP_zero : fP 0 = 2 * c0 := by simp [fP, Psi1_zero]

theorem fP_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ fP w := by
  have := ψ_nonneg w; have := Psi1_nonneg hw; unfold fP; positivity

theorem abs_w3_ψd_le {w : ℝ} (hw : 0 ≤ w) : w ^ 3 * |ψd w| ≤ Cd * ((1 + w) ^ 3)⁻¹ := by
  have h := ψd_le w
  rw [abs_of_nonneg hw] at h
  have hCd := Cd_nonneg
  have h1 : w ^ 3 ≤ (1 + w) ^ 3 := pow_le_pow_left₀ hw (by linarith) 3
  calc w ^ 3 * |ψd w| ≤ (1 + w) ^ 3 * (Cd / (1 + w) ^ 8) :=
        mul_le_mul h1 h (abs_nonneg _) (by positivity)
    _ = Cd * ((1 + w) ^ 5)⁻¹ := by field_simp
    _ ≤ Cd * ((1 + w) ^ 3)⁻¹ := by
        gcongr
        · exact le_add_of_nonneg_right hw
        · norm_num

theorem abs_w2_ψd_le {w : ℝ} (hw : 0 ≤ w) : w ^ 2 * |ψd w| ≤ Cd := by
  have h := ψd_le w
  rw [abs_of_nonneg hw] at h
  have hCd := Cd_nonneg
  have h1 : w ^ 2 ≤ (1 + w) ^ 8 := by
    calc w ^ 2 ≤ (1 + w) ^ 2 := pow_le_pow_left₀ hw (by linarith) 2
      _ ≤ (1 + w) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  calc w ^ 2 * |ψd w| ≤ (1 + w) ^ 8 * (Cd / (1 + w) ^ 8) :=
        mul_le_mul h1 h (abs_nonneg _) (by positivity)
    _ = Cd := by field_simp

/-- The decay constant of `f`. -/
def Cfp : ℝ := Cψ2 + 2 * CΨ

theorem Cfp_nonneg : 0 ≤ Cfp := by have := Cψ2_nonneg; have := CΨ_nonneg; unfold Cfp; positivity

theorem fP_le {w : ℝ} (hw : 0 ≤ w) : fP w ≤ Cfp * ((1 + w) ^ 3)⁻¹ := by
  have h1 := sq_ψ_le w
  rw [abs_of_nonneg hw] at h1
  have h2 := Psi1_le hw
  unfold fP Cfp; linarith

theorem abs_fP_sub_le {w : ℝ} (hw : 0 ≤ w) : |2 * c0 - fP w| ≤ M2 * w ^ 4 := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fP) (f' := fP')
    (s := Icc 0 w) (C := M2 * w ^ 3)
    (fun t _ => (hasDerivAt_fP t).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, fP', abs_mul, abs_of_nonneg (sq_nonneg t)]
      have h1 := abs_ψd_le t
      rw [abs_of_nonneg ht.1] at h1
      have hM := M2_nonneg
      calc t ^ 2 * |ψd t| ≤ t ^ 2 * (M2 * t) := by gcongr
        _ = M2 * t ^ 3 := by ring
        _ ≤ M2 * w ^ 3 := by gcongr; exact ht.1; exact ht.2)
    (convex_Icc 0 w) ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, fP_zero, sub_zero, abs_of_nonneg hw, abs_sub_comm] at h
  calc _ ≤ M2 * w ^ 3 * w := h
    _ = M2 * w ^ 4 := by ring

/-! ### `Φ` in the angle variable -/

/-- `Φ_H(z) = 1 - (2c₀)⁻¹ ∑ ω_i f(z/2^i)`. -/
def PhiH (z : ℝ) : ℝ := 1 - (2 * c0)⁻¹ * ∑' i, om i * fP (z / 2 ^ i)

/-- `Φ_H'(z) = -(2c₀)⁻¹ ∑ ω_i f'(z/2^i)/2^i`. -/
def PhiH' (z : ℝ) : ℝ := -((2 * c0)⁻¹ * ∑' i, om i * (fP' (z / 2 ^ i) / 2 ^ i))

theorem summable_om_fP {z : ℝ} (hz : 0 ≤ z) : Summable fun i => om i * fP (z / 2 ^ i) := by
  refine (tsum_om_le (A := Cfp) (r := 1) zero_le_one fun i => ?_).1
  have hz' : 0 ≤ z / 2 ^ i := by positivity
  rw [abs_of_nonneg (fP_nonneg hz'), one_pow, mul_one]
  refine (fP_le hz').trans ?_
  have := Cfp_nonneg
  have : ((1 + z / 2 ^ i) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  nlinarith

theorem hasDerivAt_PhiH {z : ℝ} (hz : 0 < z) : HasDerivAt PhiH (PhiH' z) z := by
  set g : ℕ → ℝ → ℝ := fun i y => om i * fP (y / 2 ^ i)
  set g' : ℕ → ℝ → ℝ := fun i y => om i * (fP' (y / 2 ^ i) / 2 ^ i)
  have hg : ∀ i y, HasDerivAt (g i) (g' i y) y := by
    intro i y
    have h1 := (hasDerivAt_fP (y / 2 ^ i)).comp y ((hasDerivAt_id y).div_const (2 ^ i))
    have h2 := h1.const_mul (om i)
    convert h2 using 1
    simp only [g']; field_simp
  -- a uniform bound on `|f'| = w²|ψ'|` (all `w`)
  have hb : ∀ w, |fP' w| ≤ Cd := by
    intro w
    rw [fP', abs_mul, abs_of_nonneg (sq_nonneg w)]
    rcases le_total 0 w with hw | hw
    · exact abs_w2_ψd_le hw
    · have h := abs_w2_ψd_le (w := -w) (by linarith)
      have e : ψd (-w) = -ψd w := by
        have h1 := hasDerivAt_ψ (-w)
        have h2 : HasDerivAt (fun r => ψ (-r)) (-ψd (-w)) w := by
          have := (hasDerivAt_ψ (-w)).comp w (hasDerivAt_neg w)
          convert this using 1; ring
        have h3 : (fun r => ψ (-r)) = ψ := funext ψ_neg
        rw [h3] at h2
        have := (hasDerivAt_ψ w).unique h2
        linarith
      rw [e, abs_neg, neg_sq] at h
      exact h
  have hg' : ∀ i y, ‖g' i y‖ ≤ om i * Cd := by
    intro i y
    have h2 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
    simp only [g', Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (om_pos i), abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ i)]
    refine mul_le_mul_of_nonneg_left ?_ (om_pos i).le
    calc |fP' (y / 2 ^ i)| / 2 ^ i ≤ Cd / 1 := by
          gcongr
          · exact Cd_nonneg
          · exact hb _
      _ = Cd := div_one _
  have hs0 : Summable fun i => g i 0 := by
    simp only [g, zero_div, fP_zero]
    exact summable_om.mul_right _
  have hsum : Summable fun i => om i * Cd := summable_om.mul_right _
  have h := hasDerivAt_tsum hsum hg hg' hs0 z
  have := (h.const_mul (2 * c0)⁻¹).const_sub 1
  unfold PhiH PhiH'
  convert this using 1

/-! ### Bounds -/

/-- The decay constant of `Φ_H`. -/
def KPhi : ℝ := (2 * c0)⁻¹ * (Cfp + Cd) * Som 8

theorem KPhi_nonneg : 0 ≤ KPhi := by
  have := c0_pos; have := Cfp_nonneg; have := Cd_nonneg; have := Som_nonneg (r := 8) (by norm_num)
  unfold KPhi; positivity

theorem one_sub_PhiH_le {z : ℝ} (hz : 0 ≤ z) :
    |1 - PhiH z| ≤ (2 * c0)⁻¹ * Cfp * Som 8 * ((1 + z) ^ 3)⁻¹ := by
  have hc0 := c0_pos
  have e : 1 - PhiH z = (2 * c0)⁻¹ * ∑' i, om i * fP (z / 2 ^ i) := by unfold PhiH; ring
  rw [e]
  have h := (tsum_om_le (f := fun i => fP (z / 2 ^ i)) (A := Cfp * ((1 + z) ^ 3)⁻¹) (r := 8)
    (by norm_num) (fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      rw [abs_of_nonneg (fP_nonneg hz')]
      have h2 := inv_one_add_div_pow_le hz i 3
      norm_num at h2
      calc fP (z / 2 ^ i) ≤ Cfp * ((1 + z / 2 ^ i) ^ 3)⁻¹ := fP_le hz'
        _ ≤ Cfp * (8 ^ i * ((1 + z) ^ 3)⁻¹) := by gcongr; exact Cfp_nonneg
        _ = Cfp * ((1 + z) ^ 3)⁻¹ * 8 ^ i := by ring)).2
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (2 * c0)⁻¹ * |∑' i, om i * fP (z / 2 ^ i)| ≤ (2 * c0)⁻¹ * (Cfp * ((1 + z) ^ 3)⁻¹ * Som 8) := by
        gcongr
    _ = _ := by ring

theorem z_PhiH'_le {z : ℝ} (hz : 0 ≤ z) :
    |z * PhiH' z| ≤ (2 * c0)⁻¹ * Cd * Som 8 * ((1 + z) ^ 3)⁻¹ := by
  have hc0 := c0_pos
  have e : z * PhiH' z = -((2 * c0)⁻¹ * ∑' i, om i * ((z / 2 ^ i) * fP' (z / 2 ^ i))) := by
    unfold PhiH'
    rw [mul_neg, ← mul_assoc, mul_comm z, mul_assoc, ← tsum_mul_left]
    congr 3; funext i
    have : (2 : ℝ) ^ i ≠ 0 := by positivity
    field_simp
  rw [e, abs_neg]
  have h := (tsum_om_le (f := fun i => (z / 2 ^ i) * fP' (z / 2 ^ i)) (A := Cd * ((1 + z) ^ 3)⁻¹)
    (r := 8) (by norm_num) (fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      rw [fP', abs_mul, abs_mul, abs_of_nonneg hz', abs_of_nonneg (sq_nonneg _)]
      have h2 := inv_one_add_div_pow_le hz i 3
      norm_num at h2
      calc z / 2 ^ i * ((z / 2 ^ i) ^ 2 * |ψd (z / 2 ^ i)|) =
            (z / 2 ^ i) ^ 3 * |ψd (z / 2 ^ i)| := by ring
        _ ≤ Cd * ((1 + z / 2 ^ i) ^ 3)⁻¹ := abs_w3_ψd_le hz'
        _ ≤ Cd * (8 ^ i * ((1 + z) ^ 3)⁻¹) := by gcongr; exact Cd_nonneg
        _ = Cd * ((1 + z) ^ 3)⁻¹ * 8 ^ i := by ring)).2
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (2 * c0)⁻¹ * |∑' i, om i * (z / 2 ^ i * fP' (z / 2 ^ i))| ≤
      (2 * c0)⁻¹ * (Cd * ((1 + z) ^ 3)⁻¹ * Som 8) := by gcongr
    _ = _ := by ring

theorem PhiH_decay : DecayProfile PhiH PhiH' KPhi 3 := by
  intro y hy
  have h1 := one_sub_PhiH_le hy.le
  have h2 := z_PhiH'_le hy.le
  rw [one_add_rpow_neg_three hy.le, KPhi]
  nlinarith

/-- `|Φ_H(z)| ≤ (2c₀)⁻¹ M₂ z⁴`. -/
theorem abs_PhiH_le {z : ℝ} (hz : 0 ≤ z) : |PhiH z| ≤ (2 * c0)⁻¹ * M2 * z ^ 4 := by
  have hc0 := c0_pos
  have hs := summable_om_fP hz
  have e : PhiH z = (2 * c0)⁻¹ * ∑' i, om i * (2 * c0 - fP (z / 2 ^ i)) := by
    have h1 : ∑' i, om i * (2 * c0 - fP (z / 2 ^ i)) =
        2 * c0 - ∑' i, om i * fP (z / 2 ^ i) := by
      have e1 : (fun i => om i * (2 * c0 - fP (z / 2 ^ i))) =
          fun i => om i * (2 * c0) - om i * fP (z / 2 ^ i) := by funext i; ring
      rw [e1, Summable.tsum_sub (summable_om.mul_right _) hs, tsum_mul_right, tsum_om, one_mul]
    rw [h1, PhiH]; field_simp
  rw [e]
  have h := (tsum_om_le (f := fun i => 2 * c0 - fP (z / 2 ^ i)) (A := M2 * z ^ 4) (r := 1)
    zero_le_one (fun i => by
      have hz' : 0 ≤ z / 2 ^ i := by positivity
      have h2 : z / 2 ^ i ≤ z := div_le_self hz (one_le_pow₀ (by norm_num))
      refine (abs_fP_sub_le hz').trans ?_
      rw [one_pow, mul_one]
      have := M2_nonneg
      gcongr)).2
  rw [Som_one, mul_one] at h
  rw [abs_mul, abs_of_pos (by positivity)]
  calc (2 * c0)⁻¹ * |∑' i, om i * (2 * c0 - fP (z / 2 ^ i))| ≤ (2 * c0)⁻¹ * (M2 * z ^ 4) := by
        gcongr
    _ = _ := by ring

/-! ### `Φ` in the momentum variable `y = κ z` -/

/-- `Φ(y) = Φ_H(y/κ)`. -/
def PhiE (y : ℝ) : ℝ := PhiH (y / kap)

def PhiE' (y : ℝ) : ℝ := PhiH' (y / kap) / kap

theorem hasDerivAt_PhiE {y : ℝ} (hy : 0 < y) : HasDerivAt PhiE (PhiE' y) y := by
  have hk := kap_pos
  have := (hasDerivAt_PhiH (z := y / kap) (by positivity)).comp y ((hasDerivAt_id y).div_const kap)
  convert this using 1
  simp [PhiE', div_eq_mul_inv]

def KPhiE : ℝ := KPhi * kap ^ 3

theorem KPhiE_nonneg : 0 ≤ KPhiE := by
  have := KPhi_nonneg; have := kap_pos; unfold KPhiE; positivity

theorem PhiE_decay : DecayProfile PhiE PhiE' KPhiE 3 := by
  intro y hy
  have hk := kap_pos
  have hk1 := one_le_kap
  have h := PhiH_decay (y / kap) (by positivity)
  have e : y * PhiE' y = y / kap * PhiH' (y / kap) := by unfold PhiE'; field_simp
  rw [PhiE, e]
  refine h.trans ?_
  rw [one_add_rpow_neg_three (by positivity), one_add_rpow_neg_three hy.le, KPhiE]
  have h1 : (1 + y) ≤ kap * (1 + y / kap) := by
    rw [mul_add, mul_div_cancel₀ _ hk.ne']; linarith
  have h2 : ((1 + y / kap) ^ 3)⁻¹ ≤ kap ^ 3 * ((1 + y) ^ 3)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
      div_le_iff₀ (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h1 3
  have := KPhi_nonneg
  calc KPhi * ((1 + y / kap) ^ 3)⁻¹ ≤ KPhi * (kap ^ 3 * ((1 + y) ^ 3)⁻¹) := by gcongr
    _ = _ := by ring

theorem abs_PhiE_le {y : ℝ} (hy : 0 ≤ y) : |PhiE y| ≤ (2 * c0)⁻¹ * M2 * y ^ 4 := by
  have hk := kap_pos
  have hk1 := one_le_kap
  refine (abs_PhiH_le (by positivity)).trans ?_
  have := c0_pos; have := M2_nonneg
  have h : (y / kap) ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ (by positivity) (div_le_self hy hk1) 4
  gcongr

theorem abs_PhiE_bound {y : ℝ} (hy : 0 < y) : |PhiE y| ≤ 1 + KPhiE := by
  have h := PhiE_decay y hy
  have hd : (1 + y) ^ (-(3 : ℝ)) ≤ 1 := rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have := KPhiE_nonneg
  have h1 : |1 - PhiE y| ≤ KPhiE := by
    have : KPhiE * (1 + y) ^ (-(3 : ℝ)) ≤ KPhiE := mul_le_of_le_one_right this hd
    linarith [abs_nonneg (y * PhiE' y)]
  have := abs_sub_abs_le_abs_sub (PhiE y) 1
  rw [abs_one] at this
  have := abs_sub_comm (PhiE y) 1
  linarith

theorem PhiE_profile : Profile PhiE 0 1 where
  cont := fun y hy => (hasDerivAt_PhiE hy).continuousAt.continuousWithinAt
  bound := by
    refine ⟨max (1 + KPhiE) ((2 * c0)⁻¹ * M2 + KPhiE), 3, by norm_num, fun y hy => ⟨?_, ?_, ?_⟩⟩
    · exact (abs_PhiE_bound hy).trans (le_max_left _ _)
    · intro hy1
      rw [sub_zero]
      refine (abs_PhiE_le hy.le).trans ?_
      have h1 : y ^ 4 ≤ y ^ (3 : ℝ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact pow_le_pow_of_le_one hy.le hy1 (by norm_num)
      have := c0_pos; have := M2_nonneg; have := KPhiE_nonneg
      calc (2 * c0)⁻¹ * M2 * y ^ 4 ≤ (2 * c0)⁻¹ * M2 * y ^ (3 : ℝ) := by gcongr
        _ ≤ max (1 + KPhiE) ((2 * c0)⁻¹ * M2 + KPhiE) * y ^ (3 : ℝ) := by
            gcongr
            exact (le_add_of_nonneg_right this).trans (le_max_right _ _)
    · intro hy1
      have h := PhiE_decay y hy
      have h2 : (1 + y) ^ (-(3 : ℝ)) ≤ y ^ (-(3 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hy (by linarith) (by norm_num)
      have := KPhiE_nonneg
      have h3 : |PhiE y - 1| ≤ KPhiE * (1 + y) ^ (-(3 : ℝ)) := by
        rw [abs_sub_comm]; linarith [abs_nonneg (y * PhiE' y)]
      refine h3.trans ?_
      calc KPhiE * (1 + y) ^ (-(3 : ℝ)) ≤ KPhiE * y ^ (-(3 : ℝ)) := by gcongr
        _ ≤ max (1 + KPhiE) ((2 * c0)⁻¹ * M2 + KPhiE) * y ^ (-(3 : ℝ)) := by
            gcongr
            exact (le_add_of_nonneg_left (by norm_num)).trans (le_max_left _ _)

end

end Step2.D2
