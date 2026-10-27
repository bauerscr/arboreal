import Step2.Flow.ZetaSharp4
import Step2.Flow.FlowBase

/-!
# One step of `log |Z|` along regular histories (assembly)

`zs_step`: the per-step estimate `|log|Z_{k+2}| - log|Z_{k+1}| + (β/3) ǧ_k| ≤ A_Z ǧ_k² +
A_Z ǧ_k a_k` from the sharp coupling (`zeta_sharp_hist`), the coordinate change
(`stGr_sub_le`), the bound `|Z_{k+1}C_k(e₁,0)| ≤ K_z` (`Zcov_hist`), `M_z(k+1) ≤ 2 c_z ǧ_k`, and
for `k ≥ 1` the value of `C'_{k+1}(e₁, 0)` (`X_value_hist`). Here
`A_Z = 7(2c_E + (8/7)K_z)² + 2c_E + (8/7)K_z + |β/3| + (32/7) c_μ ℓ² K_z + K 2c_z +
(2π)^{-2}(E_{C1} + 2E_B)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2.D2

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 1000000 in
theorem zs_step {ℓ ρ cEz Kz KCp cmuv cz AZ κ cg cm cT ε C₂ Cqζ Clζ cSζ : ℝ} {k : ℕ}
    {t : Hist.Seq (Xs R)} (hRℓ : R.ℓ = ℓ) (hRρ : R.ρ = ρ) (hm0 : 0 < R.msq) (hρ0 : 0 < ρ)
    (hρ8 : ρ ≤ 1 / 8) (hcEz0 : 0 ≤ cEz) (hKz : 0 ≤ Kz) (hKCp : 0 ≤ KCp) (hcz : 0 ≤ cz)
    (hVk1 : ∀ i < k + 1, ValidAt R i) (hcmud : cmuv = cmu ((L : ℝ) ^ 2) cm) (hcmu : 0 ≤ cmuv)
    (hAZd : AZ = 7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 8 / 7 * Kz +
      |betaL L / 3| + 32 / 7 * cmuv * ℓ ^ 2 * Kz + KCp * (2 * cz) +
      (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB))
    (hε1 : ε ≤ 1) (hcEzR : cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cqζ Clζ cSζ = cEz)
    (hζs : ‖stZeta R (rawHist R (k + 1) t) + stGr R k (rawHist R k t) (t k).1 (t k).2.1 *
          (stZ' R (rawHist R k t) * stCov R k (rawHist R k t) (dirVec (Sum.inl 0)) 0)‖ ≤
        2 * cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cqζ Clζ cSζ * (t k).1 ^ 2)
    (hX : ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) (dirVec (Sum.inl 0)) 0‖ ≤ Kz)
    (hMz : (dData L N R.msq (zh R k t)).Mz (k + 1) ≤ 2 * cz * (t k).1)
    (ht : InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε (k + 1) t)
    (hXv : 1 ≤ k →
      ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) (dirVec (Sum.inl 0)) 0 -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ k) ^ 2 +
            ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
          KCp * (dData L N R.msq (zh R k t)).Mz (k + 1)) :
    |Real.log ‖(rawHist R (k + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k + 1) t).Z‖ +
        betaL L / 3 * (t k).1| ≤ AZ * (t k).1 ^ 2 + AZ * (t k).1 * zA L R.msq k := by
  obtain ⟨hg, hgε, hμ, -⟩ := ht.1 k (by omega)
  have hg1 : (t k).1 ≤ 1 := hgε.trans hε1
  have hρ0' : 0 ≤ R.ρ := by rw [hRρ]; exact hρ0.le
  have hρ8' : R.ρ ≤ 1 / 8 := by rw [hRρ]; exact hρ8
  rw [logZ_succ R hρ0' hρ8' hVk1 t]
  have hζ4 : ‖stZeta R (rawHist R (k + 1) t)‖ ≤ 1 / 4 :=
    (norm_stZeta_le hρ0' _).trans (by linarith only [hρ8'])
  have hgr' : ‖stGr R k (rawHist R k t) (t k).1 (t k).2.1‖ ≤ 8 / 7 * (t k).1 := by
    have := norm_stGr_le R k (rawHist R k t) (t k).1 (t k).2.1
    rwa [abs_of_pos hg] at this
  have hw := norm_Zw1_le R hρ0' k hVk1 t
  have hgr0 := stGr_sub_le R k (rawHist R k t) (μ := (t k).2.1) hg.le hw
  rw [hRℓ] at hgr0
  have hgr : ‖stGr R k (rawHist R k t) (t k).1 (t k).2.1 - (t k).1‖ ≤
      32 / 7 * cmuv * ℓ ^ 2 * (t k).1 ^ 2 := by
    have hμ' : |(t k).2.1| ≤ cmuv * (t k).1 := by rw [hcmud]; exact hμ
    have := mul_le_mul_of_nonneg_right hμ' (by positivity : (0 : ℝ) ≤ 32 / 7 * ℓ ^ 2 * (t k).1)
    have e1 : 32 / 7 * |(t k).2.1| * ℓ ^ 2 * (t k).1 = |(t k).2.1| * (32 / 7 * ℓ ^ 2 * (t k).1) := by
      ring
    have e2 : 32 / 7 * cmuv * ℓ ^ 2 * (t k).1 ^ 2 = cmuv * (t k).1 * (32 / 7 * ℓ ^ 2 * (t k).1) := by
      ring
    linarith only [hgr0, this, e1, e2]
  rw [hcEzR] at hζs
  have hP0 : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 := by positivity
  have hErr1 := ErrC1_nonneg
  have hErrB := ErrB_nonneg
  set g := (t k).1 with hgdef
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have h := logZ_step_crude (ℓ0 := betaL L / 3) hg.le hg1 hζ4 hζs hgr' hX (by positivity) hKz
    rw [zA_zero, mul_one]
    have hco : 7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 8 / 7 * Kz + |betaL L / 3| ≤ AZ := by
      rw [hAZd]
      have : 0 ≤ 32 / 7 * cmuv * ℓ ^ 2 * Kz + KCp * (2 * cz) +
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) := by positivity
      linarith only [this]
    have h2 := mul_le_mul_of_nonneg_right hco hg.le
    have h3 : 0 ≤ AZ * g ^ 2 := mul_nonneg (le_trans (by positivity) hco) hg2
    linarith only [h, h2, h3]
  · have hXv' := hXv hk1
    have eℓ : betaL L / 3 = Real.log L / (2 * Real.pi) := by unfold betaL; ring
    rw [eℓ]
    have h := logZ_step_num (cn := 32 / 7 * cmuv * ℓ ^ 2) hg.le hg1 hζ4 hζs hgr hgr' hX hXv'
      (by positivity) hKz
    rw [zA_pos L R.msq hk1]
    set a := (((L : ℝ) ^ k) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (k + 1)) ^ 2 with ha
    have hLk : ((L : ℝ) ^ k) ^ 2 ≤ ((L : ℝ) ^ (k + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity)
        (pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
          (Nat.le_succ k)) 2
    have hA1 : ErrC1 / ((L : ℝ) ^ k) ^ 2 + ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 +
        ((L : ℝ) ^ (k + 1)) ^ 2) ≤ (ErrC1 + 2 * ErrB) * a := by
      rw [ha, div_eq_mul_inv]
      have hi : 0 ≤ (((L : ℝ) ^ k) ^ 2)⁻¹ := by positivity
      have hb : 0 ≤ R.msq * ((L : ℝ) ^ (k + 1)) ^ 2 := by positivity
      have h1 : ErrB * R.msq * ((L : ℝ) ^ k) ^ 2 ≤ ErrB * R.msq * ((L : ℝ) ^ (k + 1)) ^ 2 :=
        mul_le_mul_of_nonneg_left hLk (by positivity)
      have h2 : 0 ≤ 2 * ErrB * (((L : ℝ) ^ k) ^ 2)⁻¹ := by positivity
      have h3 : 0 ≤ ErrC1 * (R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) := by positivity
      have e : (ErrC1 + 2 * ErrB) * ((((L : ℝ) ^ k) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) =
          ErrC1 * (((L : ℝ) ^ k) ^ 2)⁻¹ + 2 * ErrB * (((L : ℝ) ^ k) ^ 2)⁻¹ +
            ErrC1 * (R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) +
            2 * (ErrB * R.msq * ((L : ℝ) ^ (k + 1)) ^ 2) := by ring
      have e2 : ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2) =
          ErrB * R.msq * ((L : ℝ) ^ k) ^ 2 + ErrB * R.msq * ((L : ℝ) ^ (k + 1)) ^ 2 := by ring
      rw [e, e2]
      linarith only [h1, h2, h3]
    have hεX : (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ k) ^ 2 +
        ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
        KCp * (dData L N R.msq (zh R k t)).Mz (k + 1) ≤
        (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) * a + KCp * (2 * cz) * g := by
      have h1 := mul_le_mul_of_nonneg_left hA1 hP0
      have h2 := mul_le_mul_of_nonneg_left hMz hKCp
      have e : KCp * (2 * cz * g) = KCp * (2 * cz) * g := by ring
      linarith only [h1, h2, e]
    have hgε := mul_le_mul_of_nonneg_left hεX hg.le
    have hco : 7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 32 / 7 * cmuv * ℓ ^ 2 * Kz + KCp * (2 * cz) ≤
        AZ := by
      rw [hAZd]
      have : 0 ≤ 8 / 7 * Kz + |betaL L / 3| + (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) := by
        positivity
      linarith only [this]
    have hco2 : (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) ≤ AZ := by
      rw [hAZd]
      have : 0 ≤ 7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 8 / 7 * Kz + |betaL L / 3| +
          32 / 7 * cmuv * ℓ ^ 2 * Kz + KCp * (2 * cz) := by positivity
      linarith only [this]
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have h4 := mul_le_mul_of_nonneg_right hco hg2
    have h5 := mul_le_mul_of_nonneg_right hco2 (mul_nonneg hg.le ha0)
    have e1 : g * ((2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) * a + KCp * (2 * cz) * g) =
        (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) * (g * a) + KCp * (2 * cz) * g ^ 2 := by ring
    have e2 : (7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 32 / 7 * cmuv * ℓ ^ 2 * Kz) * g ^ 2 +
        KCp * (2 * cz) * g ^ 2 =
        (7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 32 / 7 * cmuv * ℓ ^ 2 * Kz + KCp * (2 * cz)) * g ^ 2 := by
      ring
    have e3 : AZ * g * a = AZ * (g * a) := by ring
    linarith only [h, hgε, h4, h5, e1, e2, e3]

end

end Step2
