import Step.SymGeom
import FRD

/-!
# The covariances of the finite range decomposition satisfy `GoodCov`

For `j + 1 < N`, the covariance `C_{j+1}` of Section `sec:frd` (constructed with the family
`FRD.stdPt`) satisfies the hypotheses `GoodCov` of Section `sec:step` once
`ℓ_0^2 ≥ K L^{d-2+2p_Φ}` (`e:Cleq1`): it is positive semidefinite (`Cj_posSemidef`), invariant
under the lattice automorphisms (`Cj_translate`, `Cj_symm`), has range `L^{j+1}/2`
(`Cj_finiteRange`), and `‖C_{j+1}‖_{Φ_{j+1}(ℓ_{j+1})} ≤ 1` (`Cj_bound`, `covNormj_le_one`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

/-- `C_{j+1}` on `Λ_N`. -/
abbrev Cfrd (d L N : ℕ) [NeZero L] (msq : ℝ) (j : ℕ) : Matrix (Lam d L N) (Lam d L N) ℝ :=
  Cj stdPt msq (L : ℝ) (j + 1)

/-- `C_{j+1}` is invariant under the generated lattice automorphisms. -/
theorem Cfrd_inv {d L N : ℕ} [NeZero L] (msq : ℝ) (j : ℕ) (T : AffAut d L N) (hT : IsGen T)
    (x y : Lam d L N) : Cfrd d L N msq j (T.E x) (T.E y) = Cfrd d L N msq j x y := by
  obtain ⟨π, s, t, h⟩ := hT.exists_form
  rw [h, h]
  change Cj stdPt msq (L : ℝ) (j + 1) (symm π s x + t) (symm π s y + t) =
    Cj stdPt msq (L : ℝ) (j + 1) x y
  rw [Cj_translate, Cj_symm]

/-- **`e:Cleq1`** and the other properties: `C_{j+1}` satisfies `GoodCov` for `j + 1 < N` and
`ℓ_0^2 ≥ K L^{d-2+2p_Φ}`. -/
theorem goodCov_Cfrd {d : ℕ} (hd : 3 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℕ) [NeZero L], 1 ≤ L → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
      K * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
      ∀ (N j : ℕ), j + 1 < N → ∀ msq : ℝ, 0 ≤ msq →
        GoodCov (d := d) (L := L) (N := N) j ℓ₀ (Cfrd d L N msq j) := by
  obtain ⟨K, hK⟩ := Cj_bound stdPt hd 0 le_rfl (pPhi d)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨max K 0 * (2 * (d : ℝ))⁻¹, by positivity, ?_⟩
  intro L _ hL ℓ₀ hℓ₀ hKℓ N j hjN msq hmsq
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLn : (L : ℝ) ^ (j + 1) ≤ ((L ^ N : ℕ) : ℝ) := by
    push_cast; exact pow_le_pow_right₀ hL1 hjN.le
  refine ⟨Cj_posSemidef stdPt hmsq (by positivity) _, fun T hT x y => Cfrd_inv msq j T hT x y,
    fun _ x y h => Cj_finiteRange stdPt hmsq hL1 _ h, ?_⟩
  refine covNormj_le_one hL1 hℓ₀ (by positivity) j (fun α₁ α₂ h₁ h₂ x y => ?_) hKℓ
  refine (hK (L ^ N) (L : ℝ) hL1 j hLn msq hmsq α₁ α₂ h₁ h₂ x y).trans ?_
  rw [neg_zero, Real.rpow_zero, mul_one]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc K * (2 * (d : ℝ) + msq)⁻¹ ≤ max K 0 * (2 * (d : ℝ) + msq)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (2 * (d : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) (le_max_right _ _)

/-! ### The last step -/

/-- `C_N` on `Λ_N` (the covariance of the last renormalisation group step). -/
abbrev CfrdN (d L M : ℕ) [NeZero L] (msq : ℝ) : Matrix (Lam d L (M + 1)) (Lam d L (M + 1)) ℝ :=
  CN stdPt msq (L : ℝ) (M + 1)

theorem symmDual_zero' {n : ℕ} [NeZero n] (π : Equiv.Perm (Fin d)) (s : Fin d → ℤˣ) :
    symmDual π s (0 : Torus d n) = 0 := by
  funext i
  show _ * (0 : Fin d → ZMod n) _ = (0 : Fin d → ZMod n) i
  simp

theorem CfrdN_inv {d L M : ℕ} [NeZero L] (msq : ℝ) (T : AffAut d L (M + 1)) (hT : IsGen T)
    (x y : Lam d L (M + 1)) : CfrdN d L M msq (T.E x) (T.E y) = CfrdN d L M msq x y := by
  obtain ⟨π, s, t, h⟩ := hT.exists_form
  rw [h, h]
  change CN stdPt msq (L : ℝ) (M + 1) (symm π s x + t) (symm π s y + t) =
    CN stdPt msq (L : ℝ) (M + 1) x y
  rw [CN, fmat_translate]
  refine fmat_symm_invariant π s (fun m => ?_) x y
  have h0 : symmDual π s m = 0 ↔ m = 0 :=
    ⟨fun hm => (symmDual_bijective π s).1 (hm.trans (symmDual_zero' π s).symm),
      fun hm => hm ▸ symmDual_zero' π s⟩
  simp only [h0, wt, uhat_symmDual]

/-- `C_N` satisfies `GoodCov` for the last step `j + 1 = N` (with `N = M + 1`). -/
theorem goodCov_CfrdN {d : ℕ} (hd : 3 ≤ d) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (L : ℕ) [NeZero L], 1 ≤ L → ∀ (ℓ₀ : ℝ), 0 < ℓ₀ →
      K * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) ≤ ℓ₀ ^ 2 →
      ∀ (M : ℕ) (msq : ℝ), 0 ≤ msq →
        GoodCov (d := d) (L := L) (N := M + 1) M ℓ₀ (CfrdN d L M msq) := by
  obtain ⟨K, hK⟩ := CN_bound stdPt hd 0 le_rfl (pPhi d)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine ⟨max K 0 * (2 * (d : ℝ))⁻¹, by positivity, ?_⟩
  intro L _ hL ℓ₀ hℓ₀ hKℓ M msq hmsq
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  refine ⟨CN_posSemidef stdPt hmsq (by positivity) _, fun T hT x y => CfrdN_inv msq T hT x y,
    fun h => absurd h (lt_irrefl _), ?_⟩
  refine covNormj_le_one hL1 hℓ₀ (by positivity) M (fun α₁ α₂ h₁ h₂ x y => ?_) hKℓ
  refine (hK L hL (M + 1) (by omega) msq hmsq α₁ α₂ h₁ h₂ x y).trans ?_
  rw [neg_zero, Real.rpow_zero, mul_one, show M + 1 - 1 = M by omega]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc K * (2 * (d : ℝ) + msq)⁻¹ ≤ max K 0 * (2 * (d : ℝ) + msq)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (2 * (d : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) (le_max_right _ _)

end

end Step
