import PtCorr2.Zero.OnePt

/-!
# The Ward identity and positivity at either sign of `h` (route (a1), task 3, model part)

`ward2`, `suscept2`, `ward2_onept` are stated for `h ≥ 0` (`b ≤ μ₀ + m²`), where positivity gives
`⟨Z_0⟩_C ≠ 0`. On the windowed trajectories of route (a1) `h` may be negative. Here:

* **`ward2_of_Zne`**: the susceptibility formula and the Ward identity along a trajectory for any
  sign of `h`, given `⟨Z_0⟩ ≠ 0` (in the form `omegaC (Γh R 0 t) (Zh R 0 t) ≠ 0`);
  **`omegaZh_ne_of`**: `⟨Z_0⟩ ≠ 0` from the nonvanishing of the factors of `hist_omega_traj`
  (`∏ c_j`, `det`, `1 + ũ`);
* **`ward_V0_real`**: the Ward identity for real `r = 1 - b⟨ψ̄_0ψ_0⟩` and `χ = ∑_x⟨ψ̄_0ψ_x⟩`;
* positivity: **`chi_mem_of_h_nonneg`** (`h ≥ 0` ⟹ `χ` real, `0 ≤ χ ≤ |Λ|/b`),
  **`h_neg_of_chi_out`** (a susceptibility outside `[0, |Λ|/b]` forces `h < 0`),
  **`h_neg_of_Zb_eq_zero`** (`⟨Z_0⟩ = 0` forces `h < 0`);
* the sign of `h` from the one-point function: **`h_nonneg_of_onept`** (`⟨Z_0⟩ ≠ 0`, `r ≥ 0`,
  `χ > 0` ⟹ `h ≥ 0`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

variable {L N : ℕ} [NeZero L]

/-- **The Ward identity in real form**: `(μ₀ + m² - b) χ = r`. -/
theorem ward_V0_real {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hZ : Obs.Zb (Suscept.Cov 2 L N msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0)
    {r χ : ℝ} (hr : 1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0) = r)
    (hχ : ∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x) = χ) :
    (μ₀ + msq - b) * χ = r := by
  have hw := ward_V0 (L := L) (N := N) hb hm0 hZ
  rw [hr, hχ, ← Complex.ofReal_mul] at hw
  exact_mod_cast hw.symm

/-- **Positivity**: for `h ≥ 0` the susceptibility `χ = ∑_x ⟨ψ̄_0ψ_x⟩` is real and
`0 ≤ χ ≤ |Λ|/b`. -/
theorem chi_mem_of_h_nonneg {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq) (hh : b ≤ μ₀ + msq) :
    ∃ χ : ℝ, 0 ≤ χ ∧ χ ≤ (Fintype.card (Lam 2 L N) : ℝ) / b ∧
      ∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x) = χ := by
  choose p hp0 hp1 hpe using fun x : Lam 2 L N => onept_avg0_two_mem (L := L) (N := N) hb hm0 hh x
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb.ne'
  have he : ∀ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x) = ((p x / b : ℝ) : ℂ) := by
    intro x
    have := hpe x
    rw [Complex.ofReal_div, eq_div_iff hb', mul_comm]
    exact this
  refine ⟨(∑ x, p x) / b, div_nonneg (sum_nonneg fun x _ => hp0 x) hb.le, ?_, ?_⟩
  · refine div_le_div_of_nonneg_right ?_ hb.le
    calc ∑ x, p x ≤ ∑ _x : Lam 2 L N, (1 : ℝ) := sum_le_sum fun x _ => hp1 x
      _ = (Fintype.card (Lam 2 L N) : ℝ) := by simp
  · rw [sum_congr rfl fun x _ => he x, ← Complex.ofReal_sum, sum_div]

/-- **A susceptibility outside the positivity range forces `h < 0`.** -/
theorem h_neg_of_chi_out {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hout : ¬ ∃ χ : ℝ, 0 ≤ χ ∧ χ ≤ (Fintype.card (Lam 2 L N) : ℝ) / b ∧
      ∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x) = χ) :
    μ₀ + msq < b := by
  by_contra h
  push Not at h
  exact hout (chi_mem_of_h_nonneg hb hm0 h)

/-- **The sign of `h` from the one-point function**: `⟨Z_0⟩ ≠ 0`, `r = 1 - b⟨ψ̄_0ψ_0⟩ ≥ 0` and
`χ > 0` give `h ≥ 0`. -/
theorem h_nonneg_of_onept {b μ₀ msq : ℝ} (hb : 0 < b) (hm0 : 0 < msq)
    (hZ : Obs.Zb (Suscept.Cov 2 L N msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0)
    {r χ : ℝ} (hr0 : 0 ≤ r) (hχ0 : 0 < χ)
    (hr : 1 - (b : ℂ) * avg0 L N msq b μ₀ (psibar 0 * psi 0) = r)
    (hχ : ∑ x : Lam 2 L N, avg0 L N msq b μ₀ (psibar 0 * psi x) = χ) :
    b ≤ μ₀ + msq := by
  have hw := ward_V0_real hb hm0 hZ hr hχ
  by_contra h
  push Not at h
  have : (μ₀ + msq - b) * χ < 0 := mul_neg_of_neg_of_pos (by linarith) hχ0
  linarith

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **`⟨Z_0⟩ ≠ 0` from the flow** (any sign of `h`): the factors of `hist_omega_traj` do not
vanish. -/
theorem omegaZh_ne_of {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Step2.Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c))
    (hch : ∏ j ∈ range (Nh + 1), ch R j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ≠ 0)
    (hdet : detStep R (Nh + 1) (histOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).st ≠ 0)
    (hu : 1 + uFin (Nh + 1) (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (zmRaw R (Nh + 1) (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).ζ) ≠ 0) :
    omegaC (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (Zh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) ≠ 0 := by
  rw [hist_omega_traj R hN hρ1 hspl hm0 hm hV hVL b μ₀ hVN]
  exact mul_ne_zero hch (mul_ne_zero (mul_ne_zero hdet (Complex.exp_ne_zero _)) hu)

/-- **The Ward step along a trajectory at any sign of `h`** (`ward2` without `b ≤ μ₀ + m²`,
given `⟨Z_0⟩ ≠ 0`): the dressed susceptibility formula and the Ward identity. -/
theorem ward2_of_Zne {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) {b μ₀ : ℝ} (hb : 0 < b)
    (hVN : ∀ c ∈ blockIdx (L := L) (N := N) (Nh + 1),
      ((lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).V c : Alg 2 L N) =
        Step2.Vcoup (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ (blockSet (Nh + 1) c))
    (hZ : omegaC (Γh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (Zh R 0 (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : Alg 2 L N) ≠ 0) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    Obs.Zb (Suscept.Cov 2 L N R.msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 ∧
    ∑ x : Lam 2 L N, avg0 L N R.msq b μ₀ (psibar 0 * psi x) =
      1 / (R.msq : ℂ) - (1 / (R.msq : ℂ)) ^ 2 *
        (aFin (Nh + 1) (lastOut R Nh t) * πh R (Nh + 2) t /
            (1 + uFin (Nh + 1) (lastOut R Nh t) (zmRaw R (Nh + 1) (lastOut R Nh t).ζ)) +
          ∑ j ∈ range (Nh + 2), ch₀ R j t * πh R j t / ρh R j t) ∧
    ((μ₀ + R.msq - b : ℝ) : ℂ) * ∑ x : Lam 2 L N, avg0 L N R.msq b μ₀ (psibar 0 * psi x) =
      1 - (b : ℂ) * avg0 L N R.msq b μ₀ (psibar 0 * psi 0) := by
  intro t
  have hL7 : 7 ≤ L := by have := hVL.1; norm_num at this; omega
  have ht := traj_zero_eq R b μ₀
  have hsum := sum_avg0_eq R hL7 hm0 (by omega) t ht
  have hZb : Obs.Zb (Suscept.Cov 2 L N R.msq) (VE (V0c b μ₀) (univ : Finset (Lam 2 L N))) ≠ 0 := by
    have := omega_Zh_zero_eq R hL7 hm0 (by omega) t hb ht
    rw [Vh_eq_V0 hb] at this
    rw [← this]; exact hZ
  refine ⟨hZb, ?_, (ward_V0 hb hm0 hZb).symm⟩
  rw [hsum]
  exact suscept2 R hL7 hN hρ1 hspl hm0 hm hV hVL b μ₀ hVN hZ

end

end PtCorr2
