import Step2.D2.D2Ehat

/-!
# The scaling profile of `C_{j+1}` and the values `C_{j+1}(0,0)`, `C_{j+1}(0,e₁)` (`prop:d2`)

For the concrete family `Pc` and the profile `E = Ep` of `D2Profile`:

* `angle_compare`: the main term of `ehat_repr`, in the angle variable `ρ = 2√2 π x`, versus the
  same function of `√(λ + m²)` (mean value theorem; error `O((1 + c|p|)^{-α})`);
* `chat_pointwise`: `|ĉ_{j+1}(p) - (E(L^{j+1}s) - E(L^j s))/s²| ≤ K₁ (1 + 2L^j|p|/π²)^{-3} + 2 C_rem L^{-2j}`
  with `s = √(λ(p) + m²)`;
* `mass_pointwise`: `|f_c(λ + m²) - f_c(λ)| ≤ M c⁴ m² (1 + 2c|p|/π)^{-β}`;
* `chat_profile_error` (**(R1)**): `∫_{[-π,π]²} |ĉ_{j+1} - (E_{j+1} - E_j)/λ| = O(L^{-2j} + m² L^{2j}(1 + L²))`;
* `Cj_succ_diag_value`, `Cj_succ_e1_value`: `C_{j+1}(0,0)` and `C_{j+1}(0,e₁)` equal
  `(1/2π) log L + O(L^{-2j} + m² L^{2j}(1 + L²))`, with constants independent of `L, j, m, n`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

/-- The constant of `angle_compare`. -/
def Cmv : ℝ := π ^ 2 / 32 + π / 2 * (π ^ 2 / 32 + 1 / 4)

theorem Cmv_nonneg : 0 ≤ Cmv := by have := pi_pos; unfold Cmv; positivity

/-- **The angle variable versus `√(λ + m²)`.** Let `D` satisfy `|D| + |yD'| ≤ K₂ (1+y)^{-α}`,
`0 < x ≤ 1/2`, `ρ = 2√2 π x` and `S = (4 + m²) 2 sin²(πx) ≥ m²`. Then
`|D(cρ)/((4+m²) 2π² x²) - D(c√S)/S| ≤ K₂ C_mv (1 + (2c/π) ρ)^{-α}`. -/
theorem angle_compare {D D' : ℝ → ℝ} {K2 α c x msq S : ℝ}
    (hd : ∀ y, 0 < y → HasDerivAt D (D' y) y)
    (hb : ∀ y, 0 < y → |D y| + |y * D' y| ≤ K2 * (1 + y) ^ (-α)) (hα : 0 ≤ α) (hc : 0 < c)
    (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hm : 0 ≤ msq) (hS : (4 + msq) * (2 * sin (π * x) ^ 2) = S)
    (hmS : msq ≤ S) :
    |D (c * (2 * √2 * π * x)) / ((4 + msq) * (2 * π ^ 2 * x ^ 2)) - D (c * √S) / S| ≤
      K2 * Cmv * (1 + c * (2 / π) * (2 * √2 * π * x)) ^ (-α) := by
  have hpi := pi_pos
  have hK2 := K_nonneg_of_bound hb
  set ρ := 2 * √2 * π * x with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ2 : ρ ^ 2 = 8 * π ^ 2 * x ^ 2 := by
    rw [hρdef]; ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
  -- trigonometric facts
  have hsin_lo : 2 * x ≤ sin (π * x) := by
    have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
    rwa [show 2 / π * (π * x) = 2 * x by field_simp] at this
  have hsin_hi : sin (π * x) ≤ π * x := (Real.sin_lt (by positivity)).le
  have hsin0 : 0 < sin (π * x) := by linarith
  have hd4 := sq_sub_sin_sq_le (π * x)
  have hd0 : 0 ≤ (π * x) ^ 2 - sin (π * x) ^ 2 := by nlinarith
  have hS32 : 32 * x ^ 2 ≤ S := by rw [← hS]; nlinarith
  have hSpos : 0 < S := by nlinarith
  have hsqS : 2 / π * ρ ≤ √S := by
    rw [Real.le_sqrt (by positivity) hSpos.le, mul_pow, hρ2]
    have : (2 / π) ^ 2 * (8 * π ^ 2 * x ^ 2) = 32 * x ^ 2 := by field_simp; ring
    linarith
  have hsqS0 : 0 < √S := Real.sqrt_pos.2 hSpos
  set ℓ := c * (2 / π) * ρ with hℓ
  have hℓ0 : 0 < ℓ := by positivity
  have hℓρ : ℓ ≤ c * ρ := by
    rw [hℓ, mul_assoc]
    gcongr
    calc 2 / π * ρ ≤ 1 * ρ := by gcongr; rw [div_le_one hpi]; linarith [pi_gt_three]
      _ = ρ := one_mul ρ
  have hℓS : ℓ ≤ c * √S := by rw [hℓ, mul_assoc]; gcongr
  set A := (4 + msq) * (2 * π ^ 2 * x ^ 2)
  have hA : 0 < A := by positivity
  -- error 1: the prefactor
  have e1 : |1 / A - 1 / S| ≤ π ^ 2 / 32 := by
    have hSA : A - S = (4 + msq) * 2 * ((π * x) ^ 2 - sin (π * x) ^ 2) := by
      rw [← hS]; ring
    rw [div_sub_div _ _ hA.ne' hSpos.ne', abs_div, abs_of_pos (by positivity : 0 < A * S)]
    rw [show 1 * S - A * 1 = -(A - S) by ring, abs_neg, hSA,
      abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : (4 + msq) * 2 * ((π * x) ^ 2 - sin (π * x) ^ 2) ≤ (4 + msq) * 2 * (π * x) ^ 4 := by
      gcongr
    have h2 : π ^ 2 / 32 * (A * S) ≥ π ^ 2 / 32 * (A * (32 * x ^ 2)) := by gcongr
    have h3 : π ^ 2 / 32 * (A * (32 * x ^ 2)) = (4 + msq) * 2 * (π * x) ^ 4 := by
      simp only [A]; ring
    linarith
  have hD1 : |D (c * ρ)| ≤ K2 * (1 + ℓ) ^ (-α) := by
    have := hb (c * ρ) (by positivity)
    have h2 := decay_antitone hα hℓ0.le hℓρ
    have : |D (c * ρ)| ≤ K2 * (1 + c * ρ) ^ (-α) := by linarith [abs_nonneg (c * ρ * D' (c * ρ))]
    exact this.trans (mul_le_mul_of_nonneg_left h2 hK2)
  -- error 2: the mean value theorem between `cρ` and `c√S`
  have hmv : |D (c * √S) - D (c * ρ)| ≤ K2 * (1 + ℓ) ^ (-α) / ℓ * |c * √S - c * ρ| := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := D) (f' := D')
      (s := uIcc (c * ρ) (c * √S)) (C := K2 * (1 + ℓ) ^ (-α) / ℓ)
      (fun t ht => by
        have : ℓ ≤ t := le_trans (le_min hℓρ hℓS) ht.1
        exact (hd t (hℓ0.trans_le this)).hasDerivWithinAt)
      (fun t ht => by
        have hlt : ℓ ≤ t := le_trans (le_min hℓρ hℓS) ht.1
        have ht0 : 0 < t := hℓ0.trans_le hlt
        have h1 := hb t ht0
        have h2 : |t * D' t| ≤ K2 * (1 + ℓ) ^ (-α) := by
          have := decay_antitone hα hℓ0.le hlt
          have : |t * D' t| ≤ K2 * (1 + t) ^ (-α) := by linarith [abs_nonneg (D t)]
          exact this.trans (mul_le_mul_of_nonneg_left (decay_antitone hα hℓ0.le hlt) hK2)
        rw [abs_mul, abs_of_pos ht0] at h2
        rw [Real.norm_eq_abs, le_div_iff₀ hℓ0]
        calc |D' t| * ℓ ≤ |D' t| * t := by gcongr
          _ = t * |D' t| := mul_comm _ _
          _ ≤ _ := h2)
      (convex_uIcc _ _) left_mem_uIcc right_mem_uIcc
    simpa only [Real.norm_eq_abs] using this
  have hdiffS : |√S - ρ| ≤ (8 * (π * x) ^ 4 + 2 * msq * (π * x) ^ 2) / ρ := by
    rw [le_div_iff₀ hρ0]
    have h1 : |√S - ρ| * (√S + ρ) = |S - ρ ^ 2| := by
      rw [← abs_of_pos (by positivity : 0 < √S + ρ), ← abs_mul]
      congr 1
      rw [show (√S - ρ) * (√S + ρ) = √S ^ 2 - ρ ^ 2 by ring, Real.sq_sqrt hSpos.le]
    have h2 : S - ρ ^ 2 = -(8 * ((π * x) ^ 2 - sin (π * x) ^ 2)) + 2 * msq * sin (π * x) ^ 2 := by
      rw [← hS, hρ2]; ring
    have h3 : |S - ρ ^ 2| ≤ 8 * (π * x) ^ 4 + 2 * msq * (π * x) ^ 2 := by
      rw [h2]
      refine (abs_add_le _ _).trans ?_
      rw [abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      have : sin (π * x) ^ 2 ≤ (π * x) ^ 2 := by
        exact pow_le_pow_left₀ hsin0.le hsin_hi 2
      have : 2 * msq * sin (π * x) ^ 2 ≤ 2 * msq * (π * x) ^ 2 := by gcongr
      linarith
    have h4 : |√S - ρ| * ρ ≤ |√S - ρ| * (√S + ρ) := by
      gcongr; linarith
    linarith
  have e2 : |D (c * ρ) - D (c * √S)| / S ≤ K2 * (1 + ℓ) ^ (-α) * (π / 2 * (π ^ 2 / 32 + 1 / 4)) := by
    rw [abs_sub_comm]
    have hcS : |c * √S - c * ρ| = c * |√S - ρ| := by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
    rw [hcS] at hmv
    have hB : 0 ≤ K2 * (1 + ℓ) ^ (-α) := by positivity
    rw [div_le_iff₀ hSpos]
    calc |D (c * √S) - D (c * ρ)| ≤ K2 * (1 + ℓ) ^ (-α) / ℓ * (c * |√S - ρ|) := hmv
      _ ≤ K2 * (1 + ℓ) ^ (-α) / ℓ * (c * ((8 * (π * x) ^ 4 + 2 * msq * (π * x) ^ 2) / ρ)) := by
          gcongr
      _ = K2 * (1 + ℓ) ^ (-α) * (π / 2 * (π ^ 2 * x ^ 2 + msq / 4)) := by
          rw [hℓ]
          field_simp
          rw [hρ2]
          ring
      _ ≤ K2 * (1 + ℓ) ^ (-α) * (π / 2 * (π ^ 2 / 32 + 1 / 4)) * S := by
          rw [mul_assoc (K2 * (1 + ℓ) ^ (-α))]
          refine mul_le_mul_of_nonneg_left ?_ hB
          have h1 : π ^ 2 * x ^ 2 ≤ π ^ 2 / 32 * S := by nlinarith
          have h2 : msq / 4 ≤ 1 / 4 * S := by linarith
          have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : (0:ℝ) ≤ π / 2)
          nlinarith
  have key : D (c * ρ) / A - D (c * √S) / S =
      D (c * ρ) * (1 / A - 1 / S) + (D (c * ρ) - D (c * √S)) / S := by ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_div, abs_of_pos hSpos]
  have hB : 0 ≤ (1 + ℓ) ^ (-α) := by positivity
  calc |D (c * ρ)| * |1 / A - 1 / S| + |D (c * ρ) - D (c * √S)| / S
      ≤ K2 * (1 + ℓ) ^ (-α) * (π ^ 2 / 32) +
          K2 * (1 + ℓ) ^ (-α) * (π / 2 * (π ^ 2 / 32 + 1 / 4)) := by
        exact add_le_add (mul_le_mul hD1 e1 (abs_nonneg _) (by positivity)) e2
    _ = K2 * Cmv * (1 + ℓ) ^ (-α) := by rw [Cmv]; ring

/-- The decay constant of `D(y) = E(Ly) - E(y)` (`DecayProfile.diff`). -/
def K2c : ℝ := 2 * (KH * kap ^ (3 : ℝ))

theorem K2c_nonneg : 0 ≤ K2c := by
  have := KH_nonneg; have := kap_pos; unfold K2c; positivity

theorem uhatC_eq (msq : ℝ) (p : ℂ) : uhatC msq p = (lamC p + msq) / (4 + msq) := by
  rw [uhatC]; norm_num

theorem rho_lower {msq x : ℝ} {p : ℂ} (hp : p ∈ BZ) (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (hx0 : 0 < x)
    (hx1 : x ≤ 1 / 2) (hSx : (4 + msq) * (2 * Real.sin (π * x) ^ 2) = lamC p + msq) :
    ‖p‖ / π ≤ 2 * √2 * π * x := by
  have hpi := pi_pos
  have h1 : 4 / π ^ 2 * ‖p‖ ^ 2 ≤ lamC p := lamC_ge hp
  have h2 : Real.sin (π * x) ≤ π * x := (Real.sin_lt (by positivity)).le
  have hsin0 : 0 ≤ Real.sin (π * x) := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    (by nlinarith)
  have h3 : (2 * √2 * π * x) ^ 2 = 8 * (π * x) ^ 2 := by
    ring_nf; rw [Real.sq_sqrt (by norm_num)]; ring
  have h4 : Real.sin (π * x) ^ 2 ≤ (π * x) ^ 2 := pow_le_pow_left₀ hsin0 h2 2
  have h5 : lamC p ≤ 10 * Real.sin (π * x) ^ 2 := by nlinarith [sq_nonneg (Real.sin (π * x))]
  have h6 : (‖p‖ / π) ^ 2 = ‖p‖ ^ 2 / π ^ 2 := by rw [div_pow]
  have h7 : ‖p‖ ^ 2 / π ^ 2 ≤ lamC p / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have : ‖p‖ ^ 2 = π ^ 2 / 4 * (4 / π ^ 2 * ‖p‖ ^ 2) := by field_simp
    nlinarith
  have h8 : (‖p‖ / π) ^ 2 ≤ (2 * √2 * π * x) ^ 2 := by
    rw [h6, h3]; nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 h8

theorem half_mul_eq_kap (T x : ℝ) : T / 2 * x = T * (2 * √2 * π * x) / kap := by
  rw [kap]
  have : (√2 : ℝ) ≠ 0 := by positivity
  have := pi_pos
  field_simp
  ring

theorem main_term_eq {L c x msq S : ℝ} (j : ℕ) (hc : c = L ^ j) (hx0 : 0 < x)
    (hSx : (4 + msq) * (2 * Real.sin (π * x) ^ 2) = S) (hm : 0 ≤ msq)
    (hsin : Real.sin (π * x) ≠ 0) :
    sinc2 x * (Hp (L ^ (j + 1) / 2 * x) - Hp (c / 2 * x)) / S =
      (Ep (L * (c * (2 * √2 * π * x))) - Ep (c * (2 * √2 * π * x))) /
        ((4 + msq) * (2 * π ^ 2 * x ^ 2)) := by
  have hpi := pi_pos
  rw [half_mul_eq_kap, half_mul_eq_kap, Ep, Ep, ← mul_assoc L c, hc, ← pow_succ', sinc2, ← hSx]
  have : (π * x) ≠ 0 := by positivity
  have : 4 + msq ≠ 0 := by linarith
  field_simp

/-- **Pointwise profile error of `ĉ_{j+1}`.** For `p ∈ [-π,π]² ∖ {0}`, `0 ≤ m² ≤ 1`, `L ≥ 1`,
with `s = √(λ(p) + m²)`:
`|ĉ_{j+1}(p) - (E(L^{j+1}s) - E(L^j s))/s²| ≤ K₂ C_mv (1 + 2L^j|p|/π²)^{-3} + 2 C_rem L^{-2j}`. -/
theorem chat_pointwise {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (hL : 1 ≤ L) (j : ℕ) {p : ℂ}
    (hp : p ∈ BZ) (hp0 : p ≠ 0) :
    |chat Pc msq (Ioc (L ^ j / 2) (L ^ (j + 1) / 2)) p -
        (Ep (L ^ (j + 1) * √(lamC p + msq)) - Ep (L ^ j * √(lamC p + msq))) / (lamC p + msq)| ≤
      K2c * Cmv * (1 + 2 * L ^ j / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) + 2 * Crem / (L ^ j) ^ 2 := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  set c := L ^ j with hcdef
  have hc : 0 < c := by positivity
  have hlam : 0 < lamC p := lamC_pos hp hp0
  set S := lamC p + msq with hSdef
  have hS : 0 < S := by positivity
  set u := uhatC msq p with hudef
  have hu : u = S / (4 + msq) := uhatC_eq msq p
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu2 : u ∈ Icc (0 : ℝ) 2 := uhatC_mem hm p
  set x := xu u with hxdef
  have hx0 : 0 < x := xu_pos hu0
  have hx1 : x ≤ 1 / 2 := xu_le u
  have hsin := u_eq_two_sin_sq hu2
  rw [← hxdef] at hsin
  have hSx : (4 + msq) * (2 * Real.sin (π * x) ^ 2) = S := by
    rw [← hsin, hu]; field_simp
  have hsin0 : 0 < Real.sin (π * x) := by
    have := Real.mul_le_sin (x := π * x) (by positivity) (by nlinarith)
    have : 0 < 2 / π * (π * x) := by positivity
    linarith
  -- `ĉ` in terms of `ê`
  have ha : (0 : ℝ) ≤ c / 2 := by positivity
  have hcb : c ≤ L ^ (j + 1) := by rw [pow_succ]; nlinarith
  have hab : c / 2 ≤ L ^ (j + 1) / 2 := by linarith
  rw [chat_eq_ehat Pc hm ha hab hS]
  have r1 := ehat_repr hm (T := L ^ (j + 1) / 2) (by positivity) hu0
  have r2 := ehat_repr hm (T := c / 2) (by positivity) hu0
  rw [← hudef, ← hxdef] at r1 r2
  set ρ := 2 * √2 * π * x with hρdef
  have hmain := main_term_eq j hcdef hx0 hSx hm hsin0.ne'
  rw [← hρdef] at hmain
  have hD := angle_compare (D := fun y => Ep (L * y) - Ep y)
    (D' := fun y => L * Ep' (L * y) - Ep' y) (K2 := K2c)
    (α := 3) (c := c) (fun y hy => hasDerivAt_scale_diff (fun y _ => hasDerivAt_Ep y) hL0 hy)
    (fun y hy => by
      have := Ep_decay.diff (by norm_num) hL hy
      simpa [K2c, mul_assoc] using this) (by norm_num) hc hx0 hx1 hm hSx (by linarith)
  rw [← hρdef] at hD
  have hρp : ‖p‖ / π ≤ ρ := rho_lower hp hm hm1 hx0 hx1 hSx
  have hdec : (1 + c * (2 / π) * ρ) ^ (-(3 : ℝ)) ≤ (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) := by
    apply decay_antitone (by norm_num) (by positivity)
    calc 2 * c / π ^ 2 * ‖p‖ = c * (2 / π) * (‖p‖ / π) := by field_simp
      _ ≤ c * (2 / π) * ρ := by gcongr
  set eb := ehat Pc msq (L ^ (j + 1) / 2) p - (1 - sinc2 x * (1 - Hp (L ^ (j + 1) / 2 * x)))
  set ea := ehat Pc msq (c / 2) p - (1 - sinc2 x * (1 - Hp (c / 2 * x)))
  have herr : |eb - ea| / S ≤ 2 * Crem / c ^ 2 := by
    rw [div_le_iff₀ hS]
    refine (abs_sub _ _).trans ((add_le_add r1 r2).trans ?_)
    have hC := Crem_nonneg
    have hb2 : 1 / (L ^ (j + 1) / 2) ^ 2 ≤ 4 / c ^ 2 := by
      rw [div_pow, one_div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have e : Crem * u / (L ^ (j + 1) / 2) ^ 2 + Crem * u / (c / 2) ^ 2 =
        Crem * u * (1 / (L ^ (j + 1) / 2) ^ 2 + 4 / c ^ 2) := by field_simp; ring
    rw [e, hu]
    have h1 : Crem * (S / (4 + msq)) ≤ Crem * (S / 4) := by gcongr; linarith
    have h2 : 1 / (L ^ (j + 1) / 2) ^ 2 + 4 / c ^ 2 ≤ 8 / c ^ 2 := by
      have : 8 / c ^ 2 = 4 / c ^ 2 + 4 / c ^ 2 := by ring
      linarith
    calc _ ≤ Crem * (S / 4) * (8 / c ^ 2) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * Crem / c ^ 2 * S := by ring
  have hsplit : (ehat Pc msq (L ^ (j + 1) / 2) p - ehat Pc msq (c / 2) p) / S -
      (Ep (L ^ (j + 1) * √S) - Ep (c * √S)) / S =
      (sinc2 x * (Hp (L ^ (j + 1) / 2 * x) - Hp (c / 2 * x)) / S -
        (Ep (L * (c * √S)) - Ep (c * √S)) / S) + (eb - ea) / S := by
    rw [← mul_assoc L c, hcdef, ← pow_succ']
    simp only [eb, ea]; ring
  rw [hsplit, hmain]
  refine (abs_add_le _ _).trans (add_le_add (hD.trans ?_) ?_)
  · exact mul_le_mul_of_nonneg_left hdec (mul_nonneg K2c_nonneg Cmv_nonneg)
  · rw [abs_div, abs_of_pos hS]; exact herr

/-! ### The mass shift -/

/-- **Pointwise mass error.** If `|Φ_h(y)| ≤ M y⁴ (1+y)^{-β}`, then on `[-π,π]² ∖ {0}`,
`|f_c(λ + m²) - f_c(λ)| ≤ M c⁴ m² (1 + 2c|p|/π)^{-β}`, `f_c(s) = h(c√s)/s`. -/
theorem mass_pointwise {h h' : ℝ → ℝ} {M β c msq : ℝ} (hd : ∀ y, 0 < y → HasDerivAt h (h' y) y)
    (hΦ : ∀ y, 0 < y → |Phi h h' y| ≤ M * y ^ 4 * (1 + y) ^ (-β)) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (hc : 0 < c) (hm : 0 ≤ msq) {z : ℂ} (hz : z ∈ BZ) (hz0 : z ≠ 0) :
    |fc h c (lamC z + msq) - fc h c (lamC z)| ≤ M * c ^ 4 * msq * (1 + 2 * c / π * ‖z‖) ^ (-β) := by
  have hpi : 0 < π := pi_pos
  have hl := lamC_pos hz hz0
  have hb : ∀ t, 0 < t → |-Phi h h' (c * √t) / t ^ 2| ≤ M * c ^ 4 * (1 + c * √t) ^ (-β) :=
    fun t ht => fc_deriv_bound_mass hΦ hc ht
  have hdec : (1 + c * √(lamC z)) ^ (-β) ≤ (1 + 2 * c / π * ‖z‖) ^ (-β) :=
    decay_antitone hβ (by positivity) (by
      have := sqrt_lamC_ge hz
      calc 2 * c / π * ‖z‖ = c * (2 / π * ‖z‖) := by ring
        _ ≤ c * √(lamC z) := by gcongr)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fc h c)
    (f' := fun t => -Phi h h' (c * √t) / t ^ 2)
    (s := Icc (lamC z) (lamC z + msq)) (C := M * c ^ 4 * (1 + c * √(lamC z)) ^ (-β))
    (fun t ht => (hasDerivAt_fc hd hc (hl.trans_le ht.1)).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      refine (hb t (hl.trans_le ht.1)).trans (mul_le_mul_of_nonneg_left
        (decay_antitone hβ (by positivity) (by gcongr; exact ht.1)) (by positivity)))
    (convex_Icc _ _) ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  simp only [add_sub_cancel_left, Real.norm_eq_abs] at this
  rw [abs_of_nonneg hm] at this
  refine this.trans ?_
  calc M * c ^ 4 * (1 + c * √(lamC z)) ^ (-β) * msq
      = M * c ^ 4 * msq * (1 + c * √(lamC z)) ^ (-β) := by ring
    _ ≤ M * c ^ 4 * msq * (1 + 2 * c / π * ‖z‖) ^ (-β) := by gcongr

theorem Phi_Ep_le' {y : ℝ} (hy : 0 < y) :
    |Phi Ep Ep' y| ≤ MPhi * y ^ 4 * (1 + y) ^ (-(4 : ℝ)) := Phi_Ep_le hy.le

/-! ### The integrated profile error (R1) -/

theorem volume_real_BZ : volume.real BZ = (2 * π) ^ 2 := by
  have h := integral_ex_BZ 0
  simp only [ex_zero, if_true, setIntegral_const] at h
  rw [Complex.real_smul, mul_one] at h
  exact_mod_cast h

/-- The constant `A` of `chat_profile_error`. -/
def ErrA : ℝ := K2c * Cmv * Ia 3 * (π ^ 4 / 4) + 2 * Crem * (2 * π) ^ 2

/-- The constant `B` of `chat_profile_error`. -/
def ErrB : ℝ := MPhi * Ia 4 * (π ^ 2 / 4)

theorem ErrA_nonneg : 0 ≤ ErrA := by
  have := K2c_nonneg; have := Cmv_nonneg; have := Ia_nonneg 3; have := Crem_nonneg
  have := pi_pos; unfold ErrA; positivity

theorem ErrB_nonneg : 0 ≤ ErrB := by
  have := MPhi_nonneg; have := Ia_nonneg 4; have := pi_pos; unfold ErrB; positivity

theorem integral_BZ_decay_le {α a : ℝ} (hα : 2 < α) (ha : 0 < a) :
    ∫ z in BZ, (1 + a * ‖z‖) ^ (-α) ≤ Ia α / a ^ 2 := by
  rw [← integral_decay_scale α ha]
  exact setIntegral_le_integral (integrable_decay_scale hα ha)
    (Eventually.of_forall fun z => by positivity)

/-- **(R1) The scaling profile.** For the concrete decomposition, `0 ≤ m² ≤ 1` and `L ≥ 1`,
`∫_{[-π,π]²} |ĉ_{j+1} - (E(L^{j+1}√λ) - E(L^j√λ))/λ| ≤ A L^{-2j} + B m² (L^{2j} + L^{2(j+1)})`,
with constants `A = ErrA`, `B = ErrB` independent of `L, j, m`. -/
theorem chat_profile_error {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1) (hL : 1 ≤ L) (j : ℕ) :
    ∫ p in BZ, |chat Pc msq (Ioc (L ^ j / 2) (L ^ (j + 1) / 2)) p -
        (Ep (L ^ (j + 1) * √(lamC p)) - Ep (L ^ j * √(lamC p))) / lamC p| ≤
      ErrA / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2) := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  set c := L ^ j with hcdef
  set c1 := L ^ (j + 1) with hc1def
  have hc : 0 < c := by positivity
  have hc1 : 0 < c1 := by positivity
  have hM := MPhi_nonneg
  set G : ℂ → ℝ := fun p => K2c * Cmv * (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) +
    2 * Crem / c ^ 2 + (MPhi * c1 ^ 4 * msq * (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) +
      MPhi * c ^ 4 * msq * (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ)))
  have hne : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := ae_iff.2 (by simp)
  have hpt : ∀ᵐ p ∂(volume.restrict BZ), |chat Pc msq (Ioc (c / 2) (c1 / 2)) p -
      (Ep (c1 * √(lamC p)) - Ep (c * √(lamC p))) / lamC p| ≤ G p := by
    filter_upwards [ae_restrict_mem measurableSet_BZ, ae_restrict_of_ae hne] with p hp hp0
    have h1 := chat_pointwise hm hm1 hL j hp hp0
    have m1 := mass_pointwise (h := Ep) (h' := Ep') (M := MPhi) (β := 4) (c := c1)
      (fun y _ => hasDerivAt_Ep y) (fun y hy => Phi_Ep_le' hy) MPhi_nonneg (by norm_num) hc1 hm hp hp0
    have m2 := mass_pointwise (h := Ep) (h' := Ep') (M := MPhi) (β := 4) (c := c)
      (fun y _ => hasDerivAt_Ep y) (fun y hy => Phi_Ep_le' hy) MPhi_nonneg (by norm_num) hc hm hp hp0
    simp only [fc] at m1 m2
    rw [← hcdef, ← hc1def] at h1
    have hsq : √(lamC p) ^ 2 = lamC p := Real.sq_sqrt (lamC_nonneg p)
    set a := chat Pc msq (Ioc (c / 2) (c1 / 2)) p
    have e : a - (Ep (c1 * √(lamC p)) - Ep (c * √(lamC p))) / lamC p =
        (a - (Ep (c1 * √(lamC p + msq)) - Ep (c * √(lamC p + msq))) / (lamC p + msq)) +
        ((Ep (c1 * √(lamC p + msq)) / (lamC p + msq) - Ep (c1 * √(lamC p)) / lamC p) -
          (Ep (c * √(lamC p + msq)) / (lamC p + msq) - Ep (c * √(lamC p)) / lamC p)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add h1 ((abs_sub _ _).trans (add_le_add m1 m2)))
  have i3 : Integrable fun p : ℂ => (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  have i41 : Integrable fun p : ℂ => (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  have i42 : Integrable fun p : ℂ => (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ)) :=
    integrable_decay_scale (by norm_num) (by positivity)
  haveI : IsFiniteMeasure (volume.restrict BZ) :=
    isFiniteMeasure_restrict.2 isCompact_BZ.measure_lt_top.ne
  have iC : IntegrableOn (fun _ : ℂ => 2 * Crem / c ^ 2) BZ := integrableOn_const (by
    exact isCompact_BZ.measure_lt_top.ne)
  have hGi : IntegrableOn G BZ :=
    (((i3.const_mul _).integrableOn.add iC).add
      ((i41.const_mul _).integrableOn.add (i42.const_mul _).integrableOn))
  refine (integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _) hGi hpt).trans ?_
  -- integrate the bound
  have hI : ∫ p in BZ, G p = K2c * Cmv * (∫ p in BZ, (1 + 2 * c / π ^ 2 * ‖p‖) ^ (-(3 : ℝ))) +
      2 * Crem / c ^ 2 * (2 * π) ^ 2 +
      (MPhi * c1 ^ 4 * msq * (∫ p in BZ, (1 + 2 * c1 / π * ‖p‖) ^ (-(4 : ℝ))) +
        MPhi * c ^ 4 * msq * ∫ p in BZ, (1 + 2 * c / π * ‖p‖) ^ (-(4 : ℝ))) := by
    simp only [G]
    have a1 := (i3.const_mul (K2c * Cmv)).integrableOn (s := BZ)
    have a2 := (i41.const_mul (MPhi * c1 ^ 4 * msq)).integrableOn (s := BZ)
    have a3 := (i42.const_mul (MPhi * c ^ 4 * msq)).integrableOn (s := BZ)
    have b1 := integral_add (a1.add iC) (a2.add a3)
    have b2 := integral_add a1 iC
    have b3 := integral_add a2 a3
    simp only [Pi.add_apply] at b1 b2 b3
    rw [b1, b2, b3, integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const,
      volume_real_BZ, smul_eq_mul]
    ring
  rw [hI]
  have j3 := integral_BZ_decay_le (α := 3) (a := 2 * c / π ^ 2) (by norm_num) (by positivity)
  have j41 := integral_BZ_decay_le (α := 4) (a := 2 * c1 / π) (by norm_num) (by positivity)
  have j42 := integral_BZ_decay_le (α := 4) (a := 2 * c / π) (by norm_num) (by positivity)
  have hK := mul_nonneg K2c_nonneg Cmv_nonneg
  have hm4 : 0 ≤ MPhi * c1 ^ 4 * msq := by positivity
  have hm4' : 0 ≤ MPhi * c ^ 4 * msq := by positivity
  calc _ ≤ K2c * Cmv * (Ia 3 / (2 * c / π ^ 2) ^ 2) + 2 * Crem / c ^ 2 * (2 * π) ^ 2 +
        (MPhi * c1 ^ 4 * msq * (Ia 4 / (2 * c1 / π) ^ 2) +
          MPhi * c ^ 4 * msq * (Ia 4 / (2 * c / π) ^ 2)) := by
        gcongr
    _ = ErrA / c ^ 2 + ErrB * msq * (c ^ 2 + c1 ^ 2) := by
        rw [ErrA, ErrB]; field_simp; ring

/-! ### The values of `C_{j+1}(0,0)` and `C_{j+1}(0,e₁)` -/

/-- The constant of the `L^{-2j}` term of `Cj_succ_diag_value` (before the factor `(2π)^{-2}`). -/
def ErrC : ℝ := (π ^ 6 / 256 + 1 / π ^ 2) * Ia 3 * (2 * (KH * kap ^ (3 : ℝ))) + ErrA

/-- The constant of `Cj_succ_e1_value`. -/
def ErrC1 : ℝ := (π ^ 6 / 256 + 1 / π ^ 2 + π ^ 4 / 32) * Ia 3 * (2 * (KH * kap ^ (3 : ℝ))) + ErrA

/-- **`C_{j+1}(0,0)` for the concrete decomposition (`prop:d2`, `ζ = 0`).** On the torus of side
`n`, for `j ≥ 1`, `L ≥ 1`, `L^{j+1}/2 < n` and `0 ≤ m² ≤ 1`:
`|C_{j+1}(x,x) - (1/2π) log L| ≤ (2π)^{-2} (C L^{-2j} + B m² (L^{2j} + L^{2(j+1)}))`
with constants `C = ErrC`, `B = ErrB` independent of `L, j, m, n`. -/
theorem Cj_succ_diag_value {n : ℕ} [NeZero n] {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1)
    (hL : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) (x : Grassmann.Torus 2 n) (hn : L ^ (j + 1) / 2 < n) :
    |FRD.Cj Pc msq L (j + 1) x x - Real.log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * (ErrC / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
  have h := Cj_succ_diag_sub_log Pc hm hL hj x hn Ep_profile (fun y _ => hasDerivAt_Ep y)
    Ep_decay (by norm_num)
  have h2 := chat_profile_error hm hm1 hL j
  have hp : (0 : ℝ) ≤ (2 * π)⁻¹ ^ 2 := by positivity
  refine h.trans ?_
  have := mul_le_mul_of_nonneg_left h2 hp
  have e : (2 * π)⁻¹ ^ 2 * (ErrC / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) =
      (2 * π)⁻¹ ^ 2 * ((π ^ 6 / 256 + 1 / π ^ 2) * Ia 3 * (2 * (KH * kap ^ (3 : ℝ))) / (L ^ j) ^ 2) +
      (2 * π)⁻¹ ^ 2 * (ErrA / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
    rw [ErrC]; ring
  rw [e]
  exact add_le_add le_rfl this

/-- **`C_{j+1}(0,e₁)` for the concrete decomposition (`prop:d2`, `ζ = 0`).** If `(1, 0) ∈ ℤ²`
lifts `x - y` and `L^{j+1}/2 + 1 < n`, then
`|C_{j+1}(x,y) - (1/2π) log L| ≤ (2π)^{-2} (C₁ L^{-2j} + B m² (L^{2j} + L^{2(j+1)}))`. -/
theorem Cj_succ_e1_value {n : ℕ} [NeZero n] {msq L : ℝ} (hm : 0 ≤ msq) (hm1 : msq ≤ 1)
    (hL : 1 ≤ L) {j : ℕ} (hj : 1 ≤ j) (x y : Grassmann.Torus 2 n)
    (hr : ∀ i, (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ZMod n) = ((x - y : Grassmann.Torus 2 n) :
      Fin 2 → ZMod n) i)
    (hn : L ^ (j + 1) / 2 + 1 < n) :
    |FRD.Cj Pc msq L (j + 1) x y - Real.log L / (2 * π)| ≤
      (2 * π)⁻¹ ^ 2 * (ErrC1 / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
  have hpi := pi_pos
  have hL0 : 0 < L := by linarith
  have hc : 0 < L ^ j := by positivity
  have hCj := Cj_eq_integral_BZ Pc hm hL0.le (j + 1) x y ![1, 0] hr (by simpa using hn)
  rw [FRD.lowEnd_succ L hj] at hCj
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_zero, one_mul,
    zero_mul, add_zero] at hCj
  set S := Ioc (L ^ j / 2) (L ^ (j + 1) / 2)
  set F := fun z : ℂ => (Ep (L ^ (j + 1) * √(lamC z)) - Ep (L ^ j * √(lamC z))) / lamC z
  have hi : IntegrableOn (fun y => (Ep (L * y) - Ep y) / y) (Ioi 0) := by
    have := Ep_profile.integrableOn one_pos hL
    simpa using this
  have hF : IntegrableOn F BZ := by
    have := lattice_integrableOn (h := fun y => Ep (L * y) - Ep y)
      (h' := fun y => L * Ep' (L * y) - Ep' y)
      (fun y hy => hasDerivAt_scale_diff (fun y _ => hasDerivAt_Ep y) hL0 hy)
      (fun y hy => Ep_decay.diff (by norm_num) hL hy) hi (by norm_num : (2 : ℝ) < 3) hc
    simpa only [pow_succ_mul_eq] using this
  have hch : IntegrableOn (chat Pc msq S) BZ :=
    integrableOn_chat Pc hm (by positivity) (by
      rw [pow_succ]; gcongr; nlinarith)
  have hcos : ∀ g : ℂ → ℝ, IntegrableOn g BZ → IntegrableOn (fun z => g z * Real.cos z.re) BZ :=
    fun g hg => Integrable.mul_bdd (c := 1) hg (by fun_prop) (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  have h1 := lattice_Ce1 Ep_profile (fun y _ => hasDerivAt_Ep y) Ep_decay (by norm_num) hL j
  have h2 := chat_profile_error hm hm1 hL j
  have hsplit : (∫ p in BZ, chat Pc msq S p * Real.cos p.re) =
      (∫ p in BZ, Real.cos p.re * F p) + ∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re := by
    rw [← integral_add ((hcos F hF).congr_fun (fun z _ => mul_comm _ _) measurableSet_BZ)
      (by
        have := (hcos _ hch).sub (hcos _ hF)
        exact this.congr_fun (fun z _ => by simp only [Pi.sub_apply]; ring) measurableSet_BZ)]
    refine setIntegral_congr_fun measurableSet_BZ fun z _ => ?_
    simp only [F]; ring
  have h3 : |∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re| ≤
      ∫ p in BZ, |chat Pc msq S p - F p| := by
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (hch.sub hF).abs
      (Eventually.of_forall fun z => ?_))
    simp only [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hp : (0 : ℝ) < (2 * π)⁻¹ ^ 2 := by positivity
  rw [hCj, ← inv_pow, hsplit, mul_add]
  have e : (2 * π)⁻¹ ^ 2 * ∫ p in BZ, Real.cos p.re * F p = (2 * π)⁻¹ ^ 2 * (∫ z in BZ, Real.cos z.re *
      ((Ep (L ^ (j + 1) * √(lamC z)) - Ep (L ^ j * √(lamC z))) / lamC z)) := rfl
  have h4 : |(2 * π)⁻¹ ^ 2 * ∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re| ≤
      (2 * π)⁻¹ ^ 2 * (ErrA / (L ^ j) ^ 2 + ErrB * msq * ((L ^ j) ^ 2 + (L ^ (j + 1)) ^ 2)) := by
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left (h3.trans h2) hp.le
  have h5 := (abs_add_le _ _).trans (add_le_add h1 h4)
  rw [← e] at h5
  calc _ = |((2 * π)⁻¹ ^ 2 * (∫ p in BZ, Real.cos p.re * F p) - Real.log L / (2 * π)) +
        (2 * π)⁻¹ ^ 2 * ∫ p in BZ, (chat Pc msq S p - F p) * Real.cos p.re| := by
        congr 1; ring
    _ ≤ _ := h5
    _ = _ := by rw [ErrC1]; ring

end

end Step2.D2
