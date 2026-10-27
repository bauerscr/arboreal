import Step2.D2.D2Sh11

/-!
# Sharp line 3 of `prop:d2` at `ζ = 0`

`frakBT_sharp`: for `L ≥ 7`, `1 ≤ j`, `j + 1 < N`, `0 < m² ≤ L^{-2(N-1)}`:

  `‖𝔅(w_{j+1}) - 𝔅(w_j) - log L/(2π)‖ ≤ C_sh (L^{-2j} + m² L^{2(j+1)})`,

with an absolute constant `C_sh`.
-/

namespace Step2.D2

noncomputable section

open MeasureTheory Set Filter Topology Real FRD FRD.PtF

theorem hPhi_profile : Profile hPhi 0 1 := by
  have := PhiE_profile.mul PhiE_profile
  norm_num at this
  exact this

theorem hPhi_decay : DecayProfile hPhi hPhi' (2 * (1 + KPhiE) * KPhiE) 3 :=
  PhiE_decay.sq (by norm_num)

theorem bdd_fc_hPhi {c : ℝ} (hc : 0 < c) : Bdd fun p => fc hPhi c (lamC p) := by
  have hl := continuous_lamC
  have hc4 := c4_nonneg
  refine ⟨?_, c4 ^ 2 * c ^ 8 * 8 ^ 3, fun p => ?_⟩
  · have hcont : Continuous fun p => PhiE (c * √(lamC p)) :=
      continuous_PhiE_comp (by fun_prop) (fun p => by positivity)
    simp only [fc, hPhi]
    exact (hcont.measurable.mul hcont.measurable).div hl.measurable
  · simp only [fc, hPhi]
    have h0 := lamC_nonneg p
    have h8 := lamC_le_eight p
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; simp; positivity
    · have hb := abs_PhiE_le (y := c * √(lamC p)) (by positivity)
      rw [abs_div, abs_mul, abs_of_pos h]
      have e : (c * √(lamC p)) ^ 4 = c ^ 4 * lamC p ^ 2 := by
        rw [mul_pow, show √(lamC p) ^ 4 = (√(lamC p) ^ 2) ^ 2 by ring, Real.sq_sqrt h0]
      rw [e] at hb
      rw [div_le_iff₀ h]
      calc |PhiE (c * √(lamC p))| * |PhiE (c * √(lamC p))| ≤
          (c4 * (c ^ 4 * lamC p ^ 2)) * (c4 * (c ^ 4 * lamC p ^ 2)) := by
            unfold c4; gcongr
        _ = c4 ^ 2 * c ^ 8 * lamC p ^ 3 * lamC p := by ring
        _ ≤ c4 ^ 2 * c ^ 8 * 8 ^ 3 * lamC p := by gcongr

/-- The lattice constant of `lattice_C` for `Φ²`. -/
def Klat : ℝ := (π ^ 6 / 256 + 1 / π ^ 2) * Ia 3 * (2 * (2 * (1 + KPhiE) * KPhiE))

/-- The sharp constant. -/
def Csh : ℝ := ((2 * π) ^ 2)⁻¹ * (8 * CJ + 4 * CS + Klat + Cms)

theorem floor_cond {L N : ℕ} (hL : 7 ≤ L) {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ N) :
    2 * (⌊(L : ℝ) ^ k / 2⌋₊ + 4) < L ^ N := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have h1 : (⌊(L : ℝ) ^ k / 2⌋₊ : ℝ) ≤ (L : ℝ) ^ k / 2 := Nat.floor_le (by positivity)
  have h2 : (L : ℝ) ^ k * L ≤ (L : ℝ) ^ N := by
    rw [← pow_succ]; exact pow_le_pow_right₀ hL1 hk
  have h7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
  have h3 : (7 : ℝ) ≤ (L : ℝ) ^ k := by
    calc (7 : ℝ) ≤ L := h7
      _ = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hL1 hk1
  have h4 : ((2 * (⌊(L : ℝ) ^ k / 2⌋₊ + 4) : ℕ) : ℝ) < ((L ^ N : ℕ) : ℝ) := by
    push_cast; nlinarith
  exact_mod_cast h4

set_option maxHeartbeats 1000000 in
/-- **Sharp line 3 of `prop:d2` (`ζ = 0`).** -/
theorem frakBT_sharp {L N j : ℕ} [NeZero L] (hL : 7 ≤ L) (hj : 1 ≤ j) (hjN : j + 1 < N)
    {msq : ℝ} (hm : 0 < msq) (hmN : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) :
    ‖frakBT L N msq ((L : ℝ) ^ (j + 1) / 2) - frakBT L N msq ((L : ℝ) ^ j / 2) -
      ((Real.log L / (2 * π) : ℝ) : ℂ)‖ ≤
      Csh * (((L : ℝ) ^ j) ^ 2)⁻¹ + Csh * (msq * ((L : ℝ) ^ (j + 1)) ^ 2) := by
  have hpi := pi_pos
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL7 : (7 : ℝ) ≤ L := by exact_mod_cast hL
  have hm1 : msq ≤ 1 := msq_le_one (by omega) (by omega) hmN
  set T := (L : ℝ) ^ j / 2
  set T' := (L : ℝ) ^ (j + 1) / 2
  have hLj : (L : ℝ) ≤ (L : ℝ) ^ j := by
    calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hL1 hj
  have hT : 1 ≤ T := by simp only [T]; linarith
  have hTT : T ≤ T' := by
    simp only [T, T']; rw [pow_succ]; nlinarith
  have hT' : 1 ≤ T' := le_trans hT hTT
  have hmT' : msq * T' ^ 2 ≤ 1 := msq_mul_sq_le (by omega) hjN hm.le hmN
  -- the representations
  rw [frakBT_JS hm hm1 hT' (floor_cond hL (by omega) (by omega)),
    frakBT_JS hm hm1 hT (floor_cond hL hj (by omega)),
    ← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  -- the pieces
  have h1 := JT_sub_JPhi hm hm1 hT
  have h1' := JT_sub_JPhi hm hm1 hT'
  have h2 := JPhi_sub_J0 hm hT
  have h2' := JPhi_sub_J0 hm hT'
  have h3 := ST_sub_le hm hm1 hT hTT
  have hlat := lattice_C hPhi_profile (fun y hy => hasDerivAt_hPhi hy) hPhi_decay (by norm_num)
    hL1 j
  have hJ0 : J0 T' - J0 T = ∫ z in BZ, (hPhi ((L : ℝ) ^ (j + 1) * √(lamC z)) -
      hPhi ((L : ℝ) ^ j * √(lamC z))) / lamC z := by
    unfold J0
    rw [← integral_sub (bdd_fc_hPhi (by positivity)).integrableOn
      (bdd_fc_hPhi (by positivity)).integrableOn]
    refine setIntegral_congr_fun measurableSet_BZ fun z _ => ?_
    simp only [fc, T, T']
    rw [sub_div]; ring_nf
  rw [← hJ0] at hlat
  -- bounds in terms of `L^j`
  have hT2 : (T ^ 2)⁻¹ = 4 * (((L : ℝ) ^ j) ^ 2)⁻¹ := by
    simp only [T]; field_simp; ring
  have hT'2 : (T' ^ 2)⁻¹ ≤ 4 * (((L : ℝ) ^ j) ^ 2)⁻¹ := by
    rw [← hT2]; exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hTT 2)
  have hmT2 : msq * T ^ 2 ≤ msq * ((L : ℝ) ^ (j + 1)) ^ 2 / 4 := by
    have : T ^ 2 ≤ T' ^ 2 := pow_le_pow_left₀ (by positivity) hTT 2
    have e : T' ^ 2 = ((L : ℝ) ^ (j + 1)) ^ 2 / 4 := by simp only [T']; ring
    nlinarith
  have hmT'2 : msq * T' ^ 2 = msq * ((L : ℝ) ^ (j + 1)) ^ 2 / 4 := by simp only [T']; ring
  have hCJ : 0 ≤ CJ := by
    have := Ca_nonneg; have := A0_nonneg; have := KPhiE_nonneg; have := Ia_nonneg 3
    unfold CJ; positivity
  have hCS : 0 ≤ CS := by
    have := CE1_nonneg; have := A0_nonneg; have := Ca_nonneg; have := KPhiE_nonneg
    have := Ia_nonneg 3
    unfold CS; positivity
  have hCms : 0 ≤ Cms := by
    have := Qm_nonneg; have := Ia_nonneg 4; have := Mh_nonneg
    unfold Cms; positivity
  have hKlat : 0 ≤ Klat := by
    have := KPhiE_nonneg; have := Ia_nonneg 3
    unfold Klat; positivity
  set P := (2 * π) ^ 2
  have hP : 0 < P := by positivity
  -- assemble
  have key : P⁻¹ * (JT msq T' + ST msq T') - P⁻¹ * (JT msq T + ST msq T) - Real.log L / (2 * π) =
      P⁻¹ * ((JT msq T' - JPhi msq T') - (JT msq T - JPhi msq T) +
        (JPhi msq T' - J0 T') - (JPhi msq T - J0 T) + (ST msq T' - ST msq T)) +
      (P⁻¹ * (J0 T' - J0 T) - Real.log L / (2 * π)) := by ring
  rw [key]
  have hlat' : |P⁻¹ * (J0 T' - J0 T) - Real.log L / (2 * π)| ≤
      P⁻¹ * (Klat * (((L : ℝ) ^ j) ^ 2)⁻¹) := by
    have e : P⁻¹ = (2 * π)⁻¹ ^ 2 := by simp only [P]; rw [inv_pow]
    rw [e]
    refine hlat.trans (le_of_eq ?_)
    unfold Klat; field_simp
  have hX : |(JT msq T' - JPhi msq T') - (JT msq T - JPhi msq T) +
        (JPhi msq T' - J0 T') - (JPhi msq T - J0 T) + (ST msq T' - ST msq T)| ≤
      CJ / T' ^ 2 + CJ / T ^ 2 + Cms * msq * T' ^ 2 + Cms * msq * T ^ 2 + CS / T ^ 2 := by
    have := abs_add_le ((JT msq T' - JPhi msq T') - (JT msq T - JPhi msq T) +
        (JPhi msq T' - J0 T') - (JPhi msq T - J0 T)) (ST msq T' - ST msq T)
    have := abs_sub (JT msq T' - JPhi msq T' - (JT msq T - JPhi msq T) + (JPhi msq T' - J0 T'))
      (JPhi msq T - J0 T)
    have := abs_add_le (JT msq T' - JPhi msq T' - (JT msq T - JPhi msq T)) (JPhi msq T' - J0 T')
    have := abs_sub (JT msq T' - JPhi msq T') (JT msq T - JPhi msq T)
    linarith
  set I := (((L : ℝ) ^ j) ^ 2)⁻¹
  set M := msq * ((L : ℝ) ^ (j + 1)) ^ 2
  have hI : 0 ≤ I := by positivity
  have hM : 0 ≤ M := by positivity
  have hsum : CJ / T' ^ 2 + CJ / T ^ 2 + Cms * msq * T' ^ 2 + Cms * msq * T ^ 2 + CS / T ^ 2 +
      Klat * I ≤ (8 * CJ + 4 * CS + Klat + Cms) * (I + M) := by
    have a1 : CJ / T' ^ 2 ≤ 4 * CJ * I := by
      rw [div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_left hT'2 hCJ
      linarith
    have a2 : CJ / T ^ 2 = 4 * CJ * I := by rw [div_eq_mul_inv, hT2]; ring
    have a3 : Cms * msq * T' ^ 2 = Cms * M / 4 := by
      rw [mul_assoc, hmT'2]; ring
    have a4 : Cms * msq * T ^ 2 ≤ Cms * M / 4 := by
      rw [mul_assoc]
      have := mul_le_mul_of_nonneg_left hmT2 hCms
      linarith
    have a5 : CS / T ^ 2 = 4 * CS * I := by rw [div_eq_mul_inv, hT2]; ring
    have b1 : 0 ≤ CJ * M := by positivity
    have b2 : 0 ≤ CS * M := by positivity
    have b3 : 0 ≤ Klat * M := by positivity
    have b4 : 0 ≤ Cms * I := by positivity
    have e : (8 * CJ + 4 * CS + Klat + Cms) * (I + M) = 8 * (CJ * I) + 4 * (CS * I) + Klat * I +
        Cms * I + 8 * (CJ * M) + 4 * (CS * M) + Klat * M + Cms * M := by ring
    have e2 : 4 * CJ * I = 4 * (CJ * I) := by ring
    have e3 : 4 * CS * I = 4 * (CS * I) := by ring
    have hCmsM : 0 ≤ Cms * M := by positivity
    rw [e]
    linarith only [a1, a2, a3, a4, a5, b1, b2, b3, b4, e2, e3, hCmsM]
  calc |P⁻¹ * ((JT msq T' - JPhi msq T') - (JT msq T - JPhi msq T) +
        (JPhi msq T' - J0 T') - (JPhi msq T - J0 T) + (ST msq T' - ST msq T)) +
        (P⁻¹ * (J0 T' - J0 T) - Real.log L / (2 * π))|
      ≤ P⁻¹ * (CJ / T' ^ 2 + CJ / T ^ 2 + Cms * msq * T' ^ 2 + Cms * msq * T ^ 2 + CS / T ^ 2) +
        P⁻¹ * (Klat * I) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ hlat')
        rw [abs_mul, abs_of_pos (inv_pos.2 hP)]
        exact mul_le_mul_of_nonneg_left hX (inv_pos.2 hP).le
    _ = P⁻¹ * (CJ / T' ^ 2 + CJ / T ^ 2 + Cms * msq * T' ^ 2 + Cms * msq * T ^ 2 + CS / T ^ 2 +
        Klat * I) := by ring
    _ ≤ P⁻¹ * ((8 * CJ + 4 * CS + Klat + Cms) * (I + M)) :=
        mul_le_mul_of_nonneg_left hsum (inv_pos.2 hP).le
    _ = Csh * I + Csh * M := by unfold Csh; simp only [P]; ring

end

end Step2.D2
