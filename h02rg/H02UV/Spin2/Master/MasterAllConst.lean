import Spin2.Master.MasterAllCore

/-!
# `MasterCore`: signs of the derived constants
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 4000000 in
/-- Signs of the derived constants of the consolidated master construction. -/
theorem MasterCore.consts_nonneg {L : ℕ} [NeZero L] (D : MasterCore L) :
    0 ≤ D.cRel ∧ 0 ≤ D.cw ∧ 0 ≤ D.cWL ∧ 0 ≤ D.cKL ∧ 0 ≤ D.cρ ∧ 1 ≤ D.cWo ∧ 0 ≤ D.Bk ∧ 0 ≤ D.cδ ∧ 0 ≤ D.cGB ∧ 1 ≤ D.ιW := by
  obtain
    ⟨Cq, Cl, cS, hCq, hCl, hcS, hNu, Cpf, εpf, hCpf, hPB, C₀o, ηo, hC₀o, hηo, Kw, hKw, C₀u, ηu,
      hC₀u, hηu, Cw, hCw, hWw, Lo, Lu, hLo, hLuL, hLc, hLb, hL49, hLpl, hlog, ℓ, A, ρ, κ, cg, cm,
      cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hA2, hAx, hAu, hAJ, hVC, hLV, hZT, C₀x,
      ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hXm, c, hc, ζbar, K, cS2, hζ0, hK, hcS2, hLc',
      hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp, ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁,
      hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab, ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, htopR⟩ := D
  dsimp only [MasterCore.ce, MasterCore.B₁, MasterCore.B₂, MasterCore.B₃, MasterCore.cq, MasterCore.B', MasterCore.Bk, MasterCore.cgb, MasterCore.cP, MasterCore.cδ, MasterCore.cRel, MasterCore.cw, MasterCore.cGB, MasterCore.cWL, MasterCore.cKL, MasterCore.cρ, MasterCore.cWo, MasterCore.ιW]
  have hLr : (Lo : ℝ) ≤ L := by exact_mod_cast hLo
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (by omega : 2 ≤ L)
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, hCN⟩ := id hC2
  obtain ⟨-, hθ⟩ := hAx hLo
  set ce := ceff L c with hce
  set B' := c2Bp Cq Cl cS L K cS2 c (cx κ cT) with hB'
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hθ0 : 0 ≤ kθ0 L A C₀o ηo := by
    unfold kθ0
    exact mul_nonneg hC₀o (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  have hLwk : Kw / L ≤ 1 / 12 := by
    rw [div_le_iff₀ hL0]; linarith
  have hcx : 0 ≤ cx κ cT := by
    obtain ⟨-, -, -, -, hκ0, hκ1, -, -, hcT, -⟩ := id hC2
    unfold cx; exact div_nonneg (by linarith) (by linarith)
  set Bk := kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT) with hBk
  have hBk0 : 0 ≤ Bk := by
    have h1 := mul_nonneg hθ0 (by positivity : (0 : ℝ) ≤ 8 * cx κ cT)
    have h2 := mul_nonneg hC₁k
      (by positivity : (0 : ℝ) ≤ 8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    show 0 ≤ kθ0 L A C₀o ηo * (8 * cx κ cT) + C₁k * (8 + 2 * (8 * cx κ cT) + (8 * cx κ cT) ^ 2)
    linarith
  set cgb := c2gF B' c with hcgb
  set cP := prodCP2 L (Cpf L) with hcP
  set cδ := c2dF L (Cpf L) B' C₁w Bk c with hcδd
  have hcm2 : (2 : ℝ) ≤ max c 2 := le_max_right _ _
  have hB0' : (0 : ℝ) ≤ max B' 0 := le_max_right _ _
  have hcgb0 : 0 ≤ cgb := div_nonneg (by linarith) (by linarith)
  have hce2 : 0 ≤ ceff L (max c 2) := by unfold ceff; linarith
  have hcP0 : 0 ≤ cP := by
    show 0 ≤ (cbnC : ℝ) * Cpf L * (6 / 5 * L + 3072 * Obs2.locK 2 ^ 2)
    have := hCpf L; positivity
  set Xc := 16 * (8 * (csN 2 : ℝ)) * (3 * C₁w + 1) * Bk + 3 * cP * (3 * C₁w + 1) +
    4 * ceff L (max c 2) * cgb * (1 + cgb) with hXc
  have hcδX : cδ = 3 * Xc := rfl
  have hX0 : 0 ≤ Xc := by positivity
  have hcδ0 : 0 ≤ cδ := by rw [hcδX]; positivity
  have hq4 : (2 : ℝ) / L ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hL0 (by norm_num)]
    have : (49 : ℝ) ≤ L := by exact_mod_cast hL49
    linarith
  have hcδc : 0 ≤ cδ * c ^ 2 := mul_nonneg hcδ0 (sq_nonneg c)
  set Dℓ : ℝ := 9 / 8 * ℓ ^ 2 with hDℓ
  set Kw' : ℝ := 128 * (csN 2 : ℝ) * (3 * C₁w + 1) * Bk * (Dℓ + 1) +
    2 * (cBn : ℝ) * Q1 2 * (3 * C₁w + 1) * Dℓ with hKw'
  have hKw0 : 0 ≤ Kw' := by
    have hQ := one_le_Q1 (d := 2) (by norm_num)
    have : (0 : ℝ) ≤ csN 2 := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have : 0 ≤ Dℓ := by positivity
    have : 0 ≤ 3 * C₁w + 1 := by linarith
    have : 0 ≤ Q1 2 := by linarith
    positivity
  set cwF := max c 0 * Kw' with hcwF
  have hcw0 : 0 ≤ cwF := by rw [hcwF]; exact mul_nonneg (le_max_right _ _) hKw0
  have hW : (0 : ℝ) ≤ 3 * C₁w + 1 := by linarith
  have hm : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  have hρc : 0 ≤ (256 * (csN 2 : ℝ) * (3 * C₁w + 1) * Bk + 2 * (cBn : ℝ) * Q1 2 * (3 * C₁w + 1)) *
      (9 / 8 * ℓ ^ 2) + gbKb L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) := by
    have : (0 : ℝ) ≤ csN 2 := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ cBn := Nat.cast_nonneg _
    have : 0 ≤ Q1 2 := by have := one_le_Q1 (d := 2) (by norm_num); linarith
    have : 0 ≤ gbKb L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) :=
      gbKb_nonneg (le_max_right _ _) (by positivity)
    positivity
  have hKL : 0 ≤ 6 * Bk * (3 * C₁w + 1) * max c 0 := by positivity
  have hWL : 0 ≤ 2 * (3 * C₁w + 1) * max c 0 := by positivity
  have hGB : 0 ≤ gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) :=
    gbK_nonneg (le_max_right _ _) (by positivity)
  have hRes : 0 ≤ cδ * c ^ 2 ∧ 0 ≤ cwF ∧ 0 ≤ 2 * (3 * C₁w + 1) * max c 0 ∧
      0 ≤ 6 * Bk * (3 * C₁w + 1) * max c 0 ∧
      0 ≤ (256 * (csN 2 : ℝ) * (3 * C₁w + 1) * Bk + 2 * (cBn : ℝ) * Q1 2 * (3 * C₁w + 1)) *
        (9 / 8 * ℓ ^ 2) + gbKb L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) ∧
      1 ≤ 3 * C₁w + 1 ∧ 0 ≤ Bk ∧ 0 ≤ cδ ∧
      0 ≤ gbK L ℓ (max (cmu ((L : ℝ) ^ 2) cm) 0) (16 * ℓ ^ 2 / 49) ∧ 1 ≤ iotaW L Cw (3 * C₁w + 1) :=
    ⟨hcδc, hcw0, hWL, hKL, hρc, by linarith, hBk0, hcδ0, hGB, one_le_iotaW _ _ _⟩
  exact hRes

end

end Spin2
