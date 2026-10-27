import Step2.Lip.FlowLipCmp

/-!
# Comparison of one step along two histories: the outputs (Lipschitz bounds, part 17)

Under `Cmp`, the outputs of step `k` of two histories differ by at most the joint Cauchy bounds
in terms of the input bounds `aIn`, `bWIn`, `bDIn`, `cIn` and the scale `ℓ_Δ`:
`cmp_K` (the activity), `cmp_W` (`𝒲^lin`), `cmp_D` (`D`), `cmp_kap` (the coupling remainder).
-/

namespace Step2

open Step

set_option linter.unusedSectionVars false

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The activities of two histories after step `k`.** -/
theorem cmp_K : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.A = A →
    ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ),
      Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ ε₁ → 2 ^ (2 + 3) + 8 * 2 < L →
      ∀ ℓo : ℝ, 0 < ℓo → ℓo + R.ℓ / 2 ≤ 7 / 4 * R.ℓ →
      Knorm (k + 1) ℓo R.A (nKH R k t' - nKH R k t) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-η))) * e ^ 2 +
          16 * C₁ * e ^ 3) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)) := by
  obtain ⟨C₀, η, L₀, hC₀, hη, h⟩ := oK_lip
  refine ⟨C₀, η, L₀, hC₀, hη, fun L _ hL => ?_⟩
  obtain ⟨A₀, hA₀, h⟩ := h L hL
  refine ⟨A₀, hA₀, fun A hA => ?_⟩
  obtain ⟨ε₁, C₁, hε₁, hC₁, h⟩ := h A hA
  refine ⟨ε₁, C₁, hε₁, hC₁, ?_⟩
  intro N R _ _ hRA k t t' Λ κ cm cT ε cz cw e ℓΔ H he1 hL8 ℓo hℓo hsum
  have hℓ := H.hℓ
  have hk := H.sOK.hk
  have h1 := h N R k (sdH R k t) (sdH R k t') (7 / 8 * R.ℓ) ℓo (R.ℓ / 4) (by positivity) hℓo
    (by positivity) (by linarith) (by omega) H.sOK.hC H.sOK'.hC ℓΔ H.hℓΔ H.hC
    (add_mem H.sOK.hW H.sOK.hD) (add_mem H.sOK'.hW H.sOK'.hD) (H.sOK.V_mem hL8)
    (H.sOK'.V_mem hL8) (H.sOK.Kf_mem hL8) (H.sOK'.Kf_mem hL8) e H.he he1 H.V_e H.V_e' H.WD_e
    H.WD_e' (by rw [← hRA]; exact H.Kf_e) (by rw [← hRA]; exact H.Kf_e') _ _ _
    H.aIn_nonneg (add_nonneg H.bWIn_nonneg H.bDIn_nonneg) H.cIn_nonneg H.dV H.dWD
    (by rw [← hRA]; exact H.dKf)
  rw [hRA]
  exact h1

set_option maxHeartbeats 1000000 in
/-- **`𝒲^lin` of two histories after step `k`.** -/
theorem cmp_W : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
      (k : ℕ) (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ),
      Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ 1 / 2 → 2 ^ (2 + 3) + 8 * 2 < L → 0 < ε →
      Fnorm (k + 1) R.ℓ (nWlH R k t' - nWlH R k t) ≤
        ENNReal.ofReal (4 * (4 * C₂ * e ^ 2) * relDist e (aIn R k t t') 0 0 ℓΔ 1 (R.ℓ / 4) +
          4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * ((cw + 1) * ε ^ 2)) *
            (bWIn R cw k t t' / ((cw + 1) * ε ^ 2) + ℓΔ ^ 2 / (1 * (R.ℓ / 4)) ^ 2)) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := oW_lip
  refine ⟨C₀, hC₀, L₀, fun L _ hL => ?_⟩
  obtain ⟨C₂, hC₂, h⟩ := h L hL
  refine ⟨C₂, hC₂, ?_⟩
  intro N R _ _ k t t' Λ κ cm cT ε cz cw e ℓΔ H he1 hL8 hε
  have hℓ := H.hℓ
  have hk := H.sOK.hk
  have hcw := H.hcw
  have hw : ∀ g : ℝ, 0 < g → g ≤ ε → cw * g ^ 2 ≤ (cw + 1) * ε ^ 2 := fun g hg hgε => by
    have : g ^ 2 ≤ ε ^ 2 := by gcongr
    nlinarith
  exact h N R k (sdH R k t) (sdH R k t') (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (by positivity) hℓ
    (by positivity) (by linarith) (by linarith) (by omega) H.sOK.hC H.sOK'.hC H.sOK.hCt H.sOK'.hCt
    ℓΔ H.hℓΔ H.hC H.sOK.hW H.sOK'.hW (H.sOK.V_mem hL8) (H.sOK'.V_mem hL8) e ((cw + 1) * ε ^ 2)
    H.he he1 (by positivity) H.V_e H.V_e'
    (H.sOK.hWn.trans (ENNReal.ofReal_le_ofReal (hw _ H.H.g_pos H.H.g_le)))
    (H.sOK'.hWn.trans (ENNReal.ofReal_le_ofReal (hw _ H.H'.g_pos H.H'.g_le))) _ _ H.aIn_nonneg
    H.bWIn_nonneg H.dV H.dW

set_option maxHeartbeats 1000000 in
/-- **`D` of two histories after step `k`.** -/
theorem cmp_D : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ C₃ : ℝ, 0 ≤ C₃ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
      (k : ℕ) (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ),
      Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ 1 / 4 → 2 ^ (2 + 3) + 8 * 2 < L →
      ∀ ℓo : ℝ, 0 < ℓo → ℓo + R.ℓ / 2 ≤ 7 / 4 * R.ℓ →
      Fnorm (k + 1) ℓo (nDH R k t' - nDH R k t) ≤
        ENNReal.ofReal (4 * (2 * (C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3)) * e ^ 2 + 64 * C₃ * e ^ 4) *
          relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (bDIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4)) := by
  obtain ⟨C₀, hC₀, L₀, h⟩ := oD_lip
  refine ⟨C₀, hC₀, L₀, fun L _ hL => ?_⟩
  obtain ⟨C₃, hC₃, h⟩ := h L hL
  refine ⟨C₃, hC₃, ?_⟩
  intro N R _ _ k t t' Λ κ cm cT ε cz cw e ℓΔ H he1 hL8 ℓo hℓo hsum
  have hℓ := H.hℓ
  have hk := H.sOK.hk
  have hWe : ∀ s : SD L N, SD.OK R k s (7 / 8 * R.ℓ) (R.ℓ / 4) R.A cz cw (cx κ cT) (cmu Λ cm) →
      0 < s.g → s.g ≤ ε → Fnorm k (7 / 8 * R.ℓ) s.W ≤ ENNReal.ofReal (e ^ 2) ∧
        Fnorm k (7 / 8 * R.ℓ) s.D ≤ ENNReal.ofReal (e ^ 2) := fun s hs hg hgε => by
    have hcw := H.hcw
    have hcx := H.hcx
    have h2 : s.g ^ 2 ≤ ε ^ 2 := by gcongr
    have h3 : s.g ^ 3 ≤ ε ^ 3 := by gcongr
    have := mul_le_mul_of_nonneg_left h2 hcw
    have := mul_le_mul_of_nonneg_left h3 hcx
    have hε0 : 0 ≤ ε := hg.le.trans hgε
    have h4 : 0 ≤ cx κ cT * ε ^ 3 := by positivity
    have h5 : 0 ≤ cw * ε ^ 2 := by positivity
    exact ⟨hs.hWn.trans (ENNReal.ofReal_le_ofReal (by linarith [H.he2])),
      hs.hDn.trans (ENNReal.ofReal_le_ofReal (by linarith [H.he2]))⟩
  obtain ⟨hW1, hD1⟩ := hWe _ H.sOK H.H.g_pos H.H.g_le
  obtain ⟨hW2, hD2⟩ := hWe _ H.sOK' H.H'.g_pos H.H'.g_le
  exact h N R k (sdH R k t) (sdH R k t') (7 / 8 * R.ℓ) ℓo (R.ℓ / 4) (by positivity) hℓo
    (by positivity) (by linarith) (by linarith) (by omega) H.sOK.hC H.sOK'.hC H.sOK.hCt H.sOK'.hCt
    ℓΔ H.hℓΔ H.hC H.sOK.hW H.sOK'.hW H.sOK.hD H.sOK'.hD (H.sOK.V_mem hL8) (H.sOK'.V_mem hL8) e
    H.he he1 H.V_e H.V_e' hW1 hW2 hD1 hD2 _ _ _ H.aIn_nonneg H.bWIn_nonneg H.bDIn_nonneg H.dV H.dW
    H.dD

set_option maxHeartbeats 1000000 in
/-- **The coupling remainders of two histories after step `k`.** -/
theorem cmp_kap : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], 2 ≤ R.A →
    ∀ (k : ℕ) (t t' : Hist.Seq (Xs R)) (Λ κ cm cT ε cz cw e ℓΔ : ℝ),
      Cmp R k t t' Λ κ cm cT ε cz cw e ℓΔ → e ≤ 1 / 2 →
      ∀ i : Fin 4, cwt L k i * ‖(kapH R k t' i - kapH R k t i) -
          (SD.shv R k (sdH R k t') i - SD.shv R k (sdH R k t) i)‖ ≤
        4 * bRem L Cq Cl cS (7 / 8 * R.ℓ) R.ℓ ((1 + 1) * (R.ℓ / 4)) (2 * e) (2 * e ^ 2)
          (2 * e ^ 2) * relDist e (aIn R k t t') (bWIn R cw k t t' + bDIn R (cx κ cT) k t t')
            (cIn R (cx κ cT) k t t') ℓΔ 1 (R.ℓ / 4) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := oKap_rem_lip
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R _ _ hA2 k t t' Λ κ cm cT ε cz cw e ℓΔ H he1 i
  have hℓ := H.hℓ
  have hk := H.sOK.hk
  exact h L hL8 hLp N R k (sdH R k t) (sdH R k t') (7 / 8 * R.ℓ) R.ℓ (R.ℓ / 4) (by positivity) hℓ
    (by positivity) (by linarith) hk H.sOK.hC H.sOK'.hC H.sOK.hCs H.sOK'.hCs H.sOK.hCsym
    H.sOK'.hCsym ℓΔ H.hℓΔ H.hC (add_mem H.sOK.hW H.sOK.hD) (add_mem H.sOK'.hW H.sOK'.hD)
    (H.sOK.Kf_mem hL8) (H.sOK'.Kf_mem hL8) (R.A / 2) (by linarith) e H.he he1 H.V_e H.V_e' H.WD_e
    H.WD_e' H.Kf_e H.Kf_e' _ _ _ H.aIn_nonneg (add_nonneg H.bWIn_nonneg H.bDIn_nonneg)
    H.cIn_nonneg H.dV H.dWD H.dKf i

end

end Step2
