import Step2.Lip.FlowLipScale

/-!
# The inputs of the normalised step (Lipschitz bounds, part 8)

* `Kflat_lip`: `K♭ = e^{Δ} K` is Lipschitz in `(Δ, K)`, with the weight `A e^{-2δ}`:
  `‖K♭' - K♭‖ ≤ e^{2^d δ} ‖K' - K‖ + 4 e^{2^{d+1} δ} ‖K‖ ‖Δ' - Δ‖/δ`;
* `Fnorm_VfamL_sub_le`: the norm of the difference of two coupling polynomials.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem Knorm_mono_wt {j : ℕ} {ℓ A A' : ℝ} (hA : 0 ≤ A) (hAA : A ≤ A') (K : Act d L N) :
    Knorm j ℓ A K ≤ Knorm j ℓ A' K := by
  unfold Knorm
  gcongr

theorem Kflat_sub_K (j : ℕ) (Δ : Fam d L N) (K K' : Act d L N) :
    Kflat j Δ K' - Kflat j Δ K = Kflat j Δ (K' - K) := by
  funext Y
  simp only [Kflat, Pi.sub_apply, mul_sub]

set_option maxHeartbeats 1000000 in
/-- **`K♭` is Lipschitz in `(Δ, K)`.** -/
theorem Kflat_lip (j : ℕ) {ℓ A δ : ℝ} (hℓ : 0 < ℓ) (hA : 0 < A) (hδ : 0 < δ)
    {Δ Δ' : Fam d L N} (hΔ0 : ∀ b, ε (Δ b : Alg d L N) = 0)
    (hΔ0' : ∀ b, ε (Δ' b : Alg d L N) = 0) (hΔ : Fnorm j ℓ Δ ≤ ENNReal.ofReal δ)
    (hΔ' : Fnorm j ℓ Δ' ≤ ENNReal.ofReal δ) {K K' : Act d L N} {k c a : ℝ} (hk : 0 ≤ k)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hK : Knorm j ℓ A K ≤ ENNReal.ofReal k)
    (hdK : Knorm j ℓ A (K' - K) ≤ ENNReal.ofReal c) (hda : Fnorm j ℓ (Δ' - Δ) ≤ ENNReal.ofReal a) :
    Knorm j ℓ (A * Real.exp (-(2 * δ))) (Kflat j Δ' K' - Kflat j Δ K) ≤
      ENNReal.ofReal (Real.exp (2 ^ d * δ) * c +
        4 * (Real.exp (2 ^ d * (2 * δ)) * k) * (a / δ)) := by
  have hb : ∀ {F : Fam d L N} {t : ℝ}, Fnorm j ℓ F ≤ ENNReal.ofReal t →
      ∀ b ∈ blockIdx (L := L) (N := N) j, Tj d (L : ℝ) j ℓ (F b : Alg d L N) ≤ ENNReal.ofReal t :=
    fun h b hb => (Tj_le_Fnorm _ hb).trans h
  have hw : A * Real.exp (-(2 * δ)) ≤ A * Real.exp (-δ) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hA.le
  have hw0 : 0 ≤ A * Real.exp (-(2 * δ)) := by positivity
  have e1 : Kflat j Δ' K' - Kflat j Δ K = Kflat j Δ' (K' - K) + (Kflat j Δ' K - Kflat j Δ K) := by
    rw [← Kflat_sub_K]; abel
  rw [e1]
  refine (Knorm_add_le j ℓ _ _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  refine add_le_add ?_ ?_
  · -- the linear part
    refine (Knorm_mono_wt hw0 hw _).trans ?_
    have h := Knorm_Kflat_le j hℓ hA.le hδ.le Δ' hΔ0' (hb hΔ') (K' - K)
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right hdK _
  · -- the dependence on `Δ`
    set B := Real.exp (2 ^ d * (2 * δ)) * k with hB
    have hB0 : 0 ≤ B := by positivity
    have hbound : ∀ z : ℂ, ‖z‖ * a ≤ δ →
        Knorm j ℓ (A * Real.exp (-(2 * δ))) (Kflat j (Δ + z • (Δ' - Δ)) K) ≤ ENNReal.ofReal B := by
      intro z hz
      have hΔz : Fnorm j ℓ (Δ + z • (Δ' - Δ)) ≤ ENNReal.ofReal (2 * δ) := by
        refine (Fnorm_add_le' _ _).trans ?_
        rw [Fnorm_smul']
        calc Fnorm j ℓ Δ + ENNReal.ofReal ‖z‖ * Fnorm j ℓ (Δ' - Δ)
            ≤ ENNReal.ofReal δ + ENNReal.ofReal ‖z‖ * ENNReal.ofReal a := by gcongr
          _ = ENNReal.ofReal (δ + ‖z‖ * a) := by
            rw [← ENNReal.ofReal_mul (norm_nonneg _), ← ENNReal.ofReal_add hδ.le (by positivity)]
          _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
      have h := Knorm_Kflat_le j hℓ hA.le (by positivity : (0 : ℝ) ≤ 2 * δ) (Δ + z • (Δ' - Δ))
        (eps_line hΔ0 hΔ0' z) (hb hΔz) K
      refine h.trans ?_
      rw [hB, ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_right hK _
    have hs0 : 0 ≤ a / δ := div_nonneg ha hδ.le
    refine cauchy_lip hB0 hs0 ?_ ?_
    · have hend : ∀ {D : Fam d L N}, (∀ b, ε (D b : Alg d L N) = 0) →
          Fnorm j ℓ D ≤ ENNReal.ofReal δ →
          Knorm j ℓ (A * Real.exp (-(2 * δ))) (Kflat j D K) ≤ ENNReal.ofReal B := by
        intro D hD0 hD
        refine (Knorm_mono_wt hw0 hw _).trans ((Knorm_Kflat_le j hℓ hA.le hδ.le D hD0 (hb hD) K).trans ?_)
        rw [hB, ENNReal.ofReal_mul (Real.exp_pos _).le]
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) hK
        have : (0 : ℝ) ≤ 2 ^ d * δ := by positivity
        nlinarith
      refine Step.Knorm_le_of_wnorm fun U hU => ?_
      refine (wnorm_sub_le' _ _ _ _ _ _).trans ?_
      refine (add_le_add ((wnorm_le_Knorm hU).trans (hend hΔ0' hΔ'))
        ((wnorm_le_Knorm hU).trans (hend hΔ0 hΔ))).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add hB0 hB0]; ring_nf
    · intro R hR2 hRs
      have hR0 : 0 < R := by linarith
      have hRa : R * a ≤ δ := by
        rw [div_eq_mul_inv, ← mul_assoc, mul_inv_le_iff₀ hδ] at hRs; linarith
      refine Step.Knorm_le_of_wnorm fun U hU => ?_
      have hF : HolE (fun z : ℂ => Kflat j (Δ + z • (Δ' - Δ)) K U) :=
        holE_Kflat j (fun b => (HolE.const _).add (HolE.smul differentiable_id (HolE.const _)))
          (fun z b => eps_line hΔ0 hΔ0' z b) (fun X => HolE.const _) U
      have h := wnorm_sub_le_of_hol (j := j) hℓ (by positivity) U hF (by linarith : (1 : ℝ) < R) hB0
        fun z hz => (wnorm_le_Knorm hU).trans (hbound z (by rw [hz]; exact hRa))
      simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at h
      exact h

end

end Step2
