import Step2.Lip.FlowLipStep

/-!
# The outputs of one normalised step (Lipschitz bounds, part 13)

Joint Lipschitz bounds for the outputs `K̂_{k+1}` (`oK_lip`), `𝒲̂^lin_{k+1}` (`oW_lip`),
`D̂_{k+1}` (`oD_lip`) of the normalised step for two step data `s, s'`, given bounds on the input
differences and the field scale `ℓ_Δ` of the difference of the covariances.
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **Lipschitz bound for `K̂_{k+1}`.** -/
theorem oK_lip : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (ℓi ℓo ℓC : ℝ),
      0 < ℓi → 0 < ℓo → 0 < ℓC → ℓo + 2 * ℓC ≤ 2 * ℓi → k + 1 < N →
      GoodCov2 k ℓC s.C → GoodCov2 k ℓC s'.C →
      ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 k ℓΔ (s'.C - s.C) →
      s.W + s.D ∈ BSub (L := L) (N := N) k → s'.W + s'.D ∈ BSub (L := L) (N := N) k →
      SD.V R k s ∈ BSub (L := L) (N := N) k → SD.V R k s' ∈ BSub (L := L) (N := N) k →
      SD.Kf R k s ∈ ASub (L := L) (N := N) k → SD.Kf R k s' ∈ ASub (L := L) (N := N) k →
      ∀ e : ℝ, 0 < e → e ≤ ε₁ →
      Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal e → Fnorm k ℓi (SD.V R k s') ≤ ENNReal.ofReal e →
      Fnorm k ℓi (s.W + s.D) ≤ ENNReal.ofReal (e ^ 2) →
      Fnorm k ℓi (s'.W + s'.D) ≤ ENNReal.ofReal (e ^ 2) →
      Knorm k ℓi (A / 2) (SD.Kf R k s) ≤ ENNReal.ofReal (e ^ 2) →
      Knorm k ℓi (A / 2) (SD.Kf R k s') ≤ ENNReal.ofReal (e ^ 2) →
      ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal a →
      Fnorm k ℓi ((s'.W + s'.D) - (s.W + s.D)) ≤ ENNReal.ofReal b →
      Knorm k ℓi (A / 2) (SD.Kf R k s' - SD.Kf R k s) ≤ ENNReal.ofReal c →
      Knorm (k + 1) ℓo A (SD.oK R k s' - SD.oK R k s) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η))) * e ^ 2 +
          16 * C₁ * e ^ 3) * relDist e a b c ℓΔ 1 ℓC) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := Kplus_lip_joint 2 le_rfl
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL
  refine ⟨2 * A₀, by linarith, fun A hA => ?_⟩
  obtain ⟨ε₁, C₁, hε₁, hC₁, h⟩ := h (A / 2) (by linarith)
  refine ⟨ε₁, C₁, hε₁, hC₁, ?_⟩
  intro N R k s s' ℓi ℓo ℓC hℓi hℓo hℓC hsum hkN hC hC' ℓΔ hℓΔ hΔ hWD hWD' hV hV' hK hK' e he he1
    hVe hVe' hWe hWe' hKe hKe' a b c ha hb hc hda hdb hdc
  refine Step.Knorm_le_of_wnorm fun U hU => ?_
  have hU' := hU
  have e1 : (SD.oK R k s' - SD.oK R k s) U = Kplus k s'.C (SD.V R k s') (s'.W + s'.D)
      (SD.Kf R k s') U - Kplus k s.C (SD.V R k s) (s.W + s.D) (SD.Kf R k s) U := by
    simp only [SD.oK, nK, Pi.sub_apply, Kconn, if_pos hU]
  rw [e1]
  have h1 := h N k hkN ℓi ℓo ℓC 1 hℓi hℓo hℓC one_pos (by linarith) s.C s'.C hC hC' ℓΔ hℓΔ hΔ
    (SD.V R k s) (SD.V R k s') (s.W + s.D) (s'.W + s'.D) (SD.Kf R k s) (SD.Kf R k s') hV.1 hV'.1
    hWD.1 hWD'.1 hK.1 hK'.1 (eps_VfamL k _) (eps_VfamL k _) e he he1 hVe hVe' hWe hWe' hKe hKe'
    a b c ha hb hc hda hdb hdc U hU
  rw [show 2 * (A / 2) = A by ring] at h1
  exact h1

set_option maxHeartbeats 1000000 in
/-- **Lipschitz bound for `𝒲̂^lin_{k+1}`**: source and transport separately. -/
theorem oW_lip : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (ℓi ℓo ℓC : ℝ),
      0 < ℓi → 0 < ℓo → 0 < ℓC → ℓo + 2 * ℓC ≤ 2 * ℓi → 2 * ℓC ≤ ℓi → k + 1 < N →
      GoodCov2 k ℓC s.C → GoodCov2 k ℓC s'.C → TInv s.C → TInv s'.C →
      ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 k ℓΔ (s'.C - s.C) →
      s.W ∈ BSub (L := L) (N := N) k → s'.W ∈ BSub (L := L) (N := N) k →
      SD.V R k s ∈ BSub (L := L) (N := N) k → SD.V R k s' ∈ BSub (L := L) (N := N) k →
      ∀ e w : ℝ, 0 < e → e ≤ 1 / 2 → 0 < w →
      Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal e → Fnorm k ℓi (SD.V R k s') ≤ ENNReal.ofReal e →
      Fnorm k ℓi s.W ≤ ENNReal.ofReal w → Fnorm k ℓi s'.W ≤ ENNReal.ofReal w →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal a →
      Fnorm k ℓi (s'.W - s.W) ≤ ENNReal.ofReal b →
      Fnorm (k + 1) ℓo (SD.oW R k s' - SD.oW R k s) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e a 0 0 ℓΔ 1 ℓC +
          4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * w) * (b / w + ℓΔ ^ 2 / (1 * ℓC) ^ 2)) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := TrL_lip_joint 2 le_rfl
  obtain ⟨L₂, hS⟩ := Src_lip_joint 2 le_rfl
  refine ⟨C₀, hC₀, max L₁ L₂, fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, hS⟩ := hS L ((le_max_right _ _).trans hL)
  refine ⟨C₂, hC₂, ?_⟩
  intro N R k s s' ℓi ℓo ℓC hℓi hℓo hℓC hsum hCℓ hkN hC hC' hCt hCt' ℓΔ hℓΔ hΔ hW hW' hV hV'
    e w he he1 hw hVe hVe' hWe hWe' a b ha hb hda hdb
  have h1 := hS N k hkN ℓi ℓo ℓC 1 hℓi hℓo hℓC one_pos (by linarith) (by linarith) s.C s'.C hC hC'
    hCt hCt' ℓΔ hℓΔ hΔ (SD.V R k s) (SD.V R k s') hV.1 hV'.1 (eps_VfamL k _) (eps_VfamL k _) e he
    he1 hVe hVe' a ha hda
  have h2 := hT L ((le_max_left _ _).trans hL) N k hkN ℓi ℓo ℓC 1 hℓi hℓo hℓC one_pos
    (by linarith) (by linarith) s.C s'.C hC hC' hCt hCt' ℓΔ hℓΔ hΔ s.W s'.W hW.1 hW'.1 hW.2.1
    hW'.2.1 w hw hWe hWe' b hb hdb
  have e1 : SD.oW R k s' - SD.oW R k s =
      (SrcL k s'.C (EthEL s'.C) (SD.V R k s') (SD.V R k s') -
        SrcL k s.C (EthEL s.C) (SD.V R k s) (SD.V R k s)) + (TrL k s'.C 1 s'.W - TrL k s.C 1 s.W) := by
    simp only [SD.oW, nWl, WlinNext]; abel
  rw [e1]
  refine (Fnorm_add_le' _ _).trans ?_
  have hr0 : 0 ≤ relDist e a 0 0 ℓΔ 1 ℓC :=
    relDist_nonneg (ℓΔ := ℓΔ) (τ := 1) (ℓC := ℓC) he ha le_rfl le_rfl
  have hc0 : 0 ≤ C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) := by positivity
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add h1 h2

set_option maxHeartbeats 1000000 in
/-- **Lipschitz bound for `D̂_{k+1}`.** -/
theorem oD_lip : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (ℓi ℓo ℓC : ℝ),
      0 < ℓi → 0 < ℓo → 0 < ℓC → ℓo + 2 * ℓC ≤ 2 * ℓi → 2 * ℓC ≤ ℓi → k + 1 < N →
      GoodCov2 k ℓC s.C → GoodCov2 k ℓC s'.C → TInv s.C → TInv s'.C →
      ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 k ℓΔ (s'.C - s.C) →
      s.W ∈ BSub (L := L) (N := N) k → s'.W ∈ BSub (L := L) (N := N) k →
      s.D ∈ BSub (L := L) (N := N) k → s'.D ∈ BSub (L := L) (N := N) k →
      SD.V R k s ∈ BSub (L := L) (N := N) k → SD.V R k s' ∈ BSub (L := L) (N := N) k →
      ∀ e : ℝ, 0 < e → e ≤ 1 / 4 →
      Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal e → Fnorm k ℓi (SD.V R k s') ≤ ENNReal.ofReal e →
      Fnorm k ℓi s.W ≤ ENNReal.ofReal (e ^ 2) → Fnorm k ℓi s'.W ≤ ENNReal.ofReal (e ^ 2) →
      Fnorm k ℓi s.D ≤ ENNReal.ofReal (e ^ 2) → Fnorm k ℓi s'.D ≤ ENNReal.ofReal (e ^ 2) →
      ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal a →
      Fnorm k ℓi (s'.W - s.W) ≤ ENNReal.ofReal b → Fnorm k ℓi (s'.D - s.D) ≤ ENNReal.ofReal c →
      Fnorm (k + 1) ℓo (SD.oD R k s' - SD.oD R k s) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * e ^ 2 + 64 * C₃ * e ^ 4) *
          relDist e a (b + c) c ℓΔ 1 ℓC) := by
  obtain ⟨C₀, hC₀, L₁, hT⟩ := Dnext_lip_joint 2 le_rfl
  refine ⟨C₀, hC₀, L₁, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, hT⟩ := hT L hL
  refine ⟨C₃, hC₃, ?_⟩
  intro N R k s s' ℓi ℓo ℓC hℓi hℓo hℓC hsum hCℓ hkN hC hC' hCt hCt' ℓΔ hℓΔ hΔ hW hW' hD hD' hV hV'
    e he he1 hVe hVe' hWe hWe' hDe hDe' a b c ha hb hc hda hdb hdc
  exact hT N k hkN ℓi ℓo ℓC 1 hℓi hℓo hℓC one_pos (by linarith) (by linarith) s.C s'.C hC hC'
    hCt hCt' ℓΔ hℓΔ hΔ (SD.V R k s) (SD.V R k s') s.W s'.W s.D s'.D hV.1 hV'.1 hW.1 hW'.1 hD.1
    hD'.1 hD.2.1 hD'.2.1 (eps_VfamL k _) (eps_VfamL k _) e he he1 hVe hVe' hWe hWe' hDe hDe' a b c
    ha hb hc hda hdb hdc

/-- The explicit part of the coupling map: `κ♭.shift(c₀, δ)`. -/
def SD.shv (R : RGPar 2 L N) (k : ℕ) (s : SD L N) : Fin 4 → ℂ :=
  ((Coup.ofVec (nVec R k s.zh s.yh s.g s.μ s.w)).shift 2 (c0C s.C) (dlC s.C)).toVec

theorem SD.kap_eq (R : RGPar 2 L N) (k : ℕ) (s : SD L N) :
    SD.kap R k s = coupRem k R.i₀ s.C (nVec R k s.zh s.yh s.g s.μ s.w) (s.W + s.D) (SD.Kf R k s) +
      SD.shv R k s := by
  simp only [coupRem, SD.shv, sub_add_cancel]
  rfl

set_option maxHeartbeats 1000000 in
/-- **Lipschitz bound for the coupling remainder of one normalised step.** -/
theorem oKap_rem_lip : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (k : ℕ) (s s' : SD L N) (ℓi ℓo ℓC : ℝ),
      0 < ℓi → 0 < ℓo → 0 < ℓC → ℓo + 2 * ℓC ≤ 2 * ℓi → k + 2 < N →
      GoodCov2 k ℓC s.C → GoodCov2 k ℓC s'.C → CSym s.C → CSym s'.C →
      (∀ x y, s.C x y = s.C y x) → (∀ x y, s'.C x y = s'.C y x) →
      ∀ ℓΔ : ℝ, 0 ≤ ℓΔ → GoodCov2 k ℓΔ (s'.C - s.C) →
      s.W + s.D ∈ BSub (L := L) (N := N) k → s'.W + s'.D ∈ BSub (L := L) (N := N) k →
      SD.Kf R k s ∈ ASub (L := L) (N := N) k → SD.Kf R k s' ∈ ASub (L := L) (N := N) k →
      ∀ A : ℝ, 1 ≤ A → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      Fnorm k ℓi (SD.V R k s) ≤ ENNReal.ofReal e → Fnorm k ℓi (SD.V R k s') ≤ ENNReal.ofReal e →
      Fnorm k ℓi (s.W + s.D) ≤ ENNReal.ofReal (e ^ 2) →
      Fnorm k ℓi (s'.W + s'.D) ≤ ENNReal.ofReal (e ^ 2) →
      Knorm k ℓi A (SD.Kf R k s) ≤ ENNReal.ofReal (e ^ 2) →
      Knorm k ℓi A (SD.Kf R k s') ≤ ENNReal.ofReal (e ^ 2) →
      ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c →
      Fnorm k ℓi (SD.V R k s' - SD.V R k s) ≤ ENNReal.ofReal a →
      Fnorm k ℓi ((s'.W + s'.D) - (s.W + s.D)) ≤ ENNReal.ofReal b →
      Knorm k ℓi A (SD.Kf R k s' - SD.Kf R k s) ≤ ENNReal.ofReal c →
      ∀ i : Fin 4, cwt L k i * ‖(SD.kap R k s' i - SD.kap R k s i) -
          (SD.shv R k s' i - SD.shv R k s i)‖ ≤
        4 * bRem L Cq Cl cS ℓi ℓo ((1 + 1) * ℓC) (2 * e) (2 * e ^ 2) (2 * e ^ 2) *
          relDist e a b c ℓΔ 1 ℓC := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupRem_lip_joint
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R k s s' ℓi ℓo ℓC hℓi hℓo hℓC hsum hkN hC hC' hCs hCs' hCsym hCsym' ℓΔ hℓΔ hΔ
    hWD hWD' hK hK' A hA e he he1 hVe hVe' hWe hWe' hKe hKe' a b c ha hb hc hda hdb hdc i
  have e1 : (SD.kap R k s' i - SD.kap R k s i) - (SD.shv R k s' i - SD.shv R k s i) =
      coupRem k R.i₀ s'.C (nVec R k s'.zh s'.yh s'.g s'.μ s'.w) (s'.W + s'.D) (SD.Kf R k s') i -
        coupRem k R.i₀ s.C (nVec R k s.zh s.yh s.g s.μ s.w) (s.W + s.D) (SD.Kf R k s) i := by
    rw [SD.kap_eq, SD.kap_eq, Pi.add_apply, Pi.add_apply]; ring
  rw [e1]
  exact h L hL8 hLp N k hkN R.i₀ ℓi ℓo ℓC 1 hℓi hℓo hℓC one_pos (by linarith) s.C s'.C hC hC'
    hCs hCs' hCsym hCsym' ℓΔ hℓΔ hΔ _ _ _ _ _ _ hWD hWD' hK hK' A hA e he he1 hVe hVe' hWe hWe'
    hKe hKe' a b c ha hb hc hda hdb hdc i

end

end Step2
