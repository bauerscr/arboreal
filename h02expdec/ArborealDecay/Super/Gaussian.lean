module

public import ArborealDecay.Super.Localization

/-!
# The supersymmetric Gaussian

`e^{-γ S}` (`Egam γ`, `γ > 0`) satisfies the hypotheses of the localization theorem, and
`∫_{ℝ^{2N|2N}} e^{-γ S} = 1` (`superIntegral_Egam`).  This is the normalisation check of BCHS
Theorem 2.8: with `∫ dx dy ∂_η ∂_ξ / (2π)` per pair, `∫ e^{-(x²+y²)/2 + ξη} = 1`.
-/

@[expose] public section

namespace ArborealDecay.Super

noncomputable section

open MeasureTheory CliffordAlgebra Grassmann

set_option linter.unusedSectionVars false

variable {N P : Type*} [Fintype N] [DecidableEq N] [Fintype P] [DecidableEq P]

theorem norm_le_one_add_sfun (p : Pt N) : ‖p‖ ≤ 1 + sfun p := by
  have hs := sfun_nonneg p
  refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun k => ?_
  rw [Real.norm_eq_abs]
  have h1 : p k ^ 2 / 2 ≤ sfun p :=
    Finset.single_le_sum (f := fun k => p k ^ 2 / 2) (fun _ _ => by positivity)
      (Finset.mem_univ k)
  have h2 : p k ^ 2 ≤ (1 + sfun p) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq h2 (by linarith)

theorem rdec_gauss {γ : ℝ} (hγ : 0 < γ) : RDec (gauss γ : Pt N → ℝ) := by
  refine ⟨(differentiable_gauss γ).continuous, fun k => ⟨(γ⁻¹) ^ k * k.factorial *
    Real.exp (2 * γ), fun p => ?_⟩⟩
  set u := sfun p
  have hu : 0 ≤ u := sfun_nonneg p
  have h1 : (1 + ‖p‖) ^ k ≤ (2 + u) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith [norm_le_one_add_sfun p]) k
  have h2 : (γ * (2 + u)) ^ k / k.factorial ≤ Real.exp (γ * (2 + u)) :=
    Real.pow_div_factorial_le_exp _ (by positivity) k
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have h3 : (2 + u) ^ k ≤ (γ⁻¹) ^ k * k.factorial * Real.exp (γ * (2 + u)) := by
    rw [div_le_iff₀ hf, mul_pow] at h2
    have hγk : 0 < γ ^ k := pow_pos hγ k
    rw [show (γ⁻¹) ^ k * k.factorial * Real.exp (γ * (2 + u)) =
      (Real.exp (γ * (2 + u)) * k.factorial) / γ ^ k by rw [inv_pow]; field_simp]
    rw [le_div_iff₀ hγk]; linarith
  rw [abs_of_pos (gauss_pos γ p), gauss]
  calc (1 + ‖p‖) ^ k * Real.exp (-γ * u)
      ≤ ((γ⁻¹) ^ k * k.factorial * Real.exp (γ * (2 + u))) * Real.exp (-γ * u) := by
        gcongr; exact h1.trans h3
    _ = (γ⁻¹) ^ k * k.factorial * Real.exp (2 * γ) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem decay_gauss {γ : ℝ} (hγ : 0 < γ) : Decay (gauss γ : Pt N → ℝ) := by
  refine ⟨(temp_gauss hγ.le).1, rdec_gauss hγ, fun v => ?_⟩
  have e : (fun p => fderiv ℝ (gauss γ) p v) =
      fun p => (-γ * fderiv ℝ sfun p v) * gauss γ p := by
    funext p; rw [fderiv_gauss]; ring
  rw [e]
  refine (rdec_gauss hγ).mul (continuous_const.mul
    ((temp_sfun.continuous_fderiv v))) ((PolyBd.const (-γ)).mul (temp_sfun.2.2 v))

theorem sdecay_Egam {γ : ℝ} (hγ : 0 < γ) : SDecay (Egam γ : Pt N → SG N P) := fun ℓ => by
  simp only [Egam, map_smul, smul_eq_mul]
  simpa [mul_comm] using (decay_gauss hγ).const_mul (ℓ (W γ))

theorem pi0_aa (i : N) : pi0 (aa i : SG N P) = 0 := by
  rw [aa, map_mul, pi0, ξ, killA_gen_of_mem (S := Set.range Sum.inl)
    (o := (Sum.inl (Sum.inl i) : (N ⊕ N) ⊕ P)) ⟨Sum.inl i, rfl⟩, zero_mul]

theorem pi0_WL (γ : ℝ) (l : List N) : pi0 (WL γ l : SG N P) = 1 := by
  induction l with
  | nil => simp
  | cons i l ih => rw [WL_cons, map_mul, ih, wpair, map_add, map_smul, pi0_aa]; simp

/-- **Normalisation**: `∫_{ℝ^{2N|2N}} e^{-γ S} = 1` for `γ > 0`. -/
theorem superIntegral_Egam {γ : ℝ} (hγ : 0 < γ) :
    superIntegral (Egam γ : Pt N → SG N P) = 1 := by
  rw [superIntegral_eq_pi0 (sdecay_Egam hγ) (Q_Egam γ), Egam, map_smul, W, pi0_WL, gauss]
  simp [sfun]

end

end ArborealDecay.Super

end
