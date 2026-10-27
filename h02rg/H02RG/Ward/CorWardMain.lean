import Ward.Macro

/-!
# `cor:ward` and `cor:macro` with the full quantifier prefix

`cor_ward` and `cor_macro` combine `PtCorr.setupW` (the common flow with reality) with
`cor_ward_i`, `cor_ward_ii`, `cor_macro_of`: for `d ≥ 3`, `L ≥ L₀` odd there are `A, ℓ₀` and an
initial coupling `V₀c` with `FlowDataW` for which the statements hold.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Psi4 Filter Topology

variable {d : ℕ}

/-- A choice of `(A, ℓ₀, V₀c)` with `FlowDataW` for every odd `L ≥ L₀`. -/
theorem exists_flowDataW (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ : ℝ), FlowDataW d L A ℓ₀ V₀c lbar C κ := by
  obtain ⟨L₀, Kℓ, hKℓ, H⟩ := setupW hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨A₀, hA₀, H'⟩ := H L hL hLodd
  set X := Kℓ * (L : ℝ) ^ ((d : ℝ) - 2 + 2 * pPhi d) with hX
  have hX0 : 0 ≤ X := mul_nonneg hKℓ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  set ℓ₀ := Real.sqrt X + 1 with hℓ₀
  have hℓ₀0 : 0 < ℓ₀ := by positivity
  have hℓ₀2 : X ≤ ℓ₀ ^ 2 := by
    have := Real.sq_sqrt hX0
    nlinarith [Real.sqrt_nonneg X]
  obtain ⟨V₀c, lbar, C, κ, HW⟩ := H' A₀ le_rfl ℓ₀ hℓ₀0 hℓ₀2
  exact ⟨A₀, ℓ₀, V₀c, lbar, C, κ, HW⟩

/-- **Corollary `cor:ward`** (i) and (ii). -/
theorem cor_ward (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ bbar K : ℝ),
      FlowDataW d L A ℓ₀ V₀c lbar C κ ∧ 0 < bbar ∧ bbar ≤ lbar ∧
      -- (i)
      (∀ b m, 0 < b → b ≤ bbar → 0 ≤ m →
        |hF V₀c b m - m * betaF V₀c b m| ≤ K * b * (m * betaF V₀c b m)) ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0) ∧
      (∀ b m, 0 < b → b ≤ bbar → 0 < m → 0 < hF V₀c b m) ∧
      -- (ii)
      ∃ (β₀ : ℝ) (bt mt : ℝ → ℝ → ℝ), 0 < β₀ ∧ ∀ β, β₀ ≤ β → ∀ h, 0 ≤ h →
        0 < bt β h ∧ bt β h ≤ bbar ∧ 0 ≤ mt β h ∧ (0 < h → 0 < mt β h) ∧
        betaF V₀c (bt β h) (mt β h) = β ∧ hF V₀c (bt β h) (mt β h) = h ∧
        mt β 0 = 0 ∧ Tendsto (mt β) (𝓝[≥] 0) (𝓝 0) ∧ Tendsto (bt β) (𝓝[≥] 0) (𝓝 (bt β 0)) ∧
        (∀ b, 0 < b → b ≤ bbar → betaF V₀c b 0 = β → b = bt β 0) := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
  obtain ⟨bbar, K, hb0, hb2, -, hK0, hKb, h48, hall, hh0, hpos⟩ := cor_ward_i hd HW
  refine ⟨A, ℓ₀, V₀c, lbar, C, κ, bbar, K, HW, hb0, by linarith [HW.lbar_pos], hall, hh0, hpos,
    cor_ward_ii hd HW hb0 hb2 hK0 hKb h48 hall hh0⟩

/-- **Corollary `cor:macro`** (with the corrected proof of `ã₀ > 0`, see `Ward/Macro.lean`). -/
theorem cor_macro (hd : 3 ≤ d) : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Odd L →
    ∃ (A ℓ₀ : ℝ) (V₀c : ℝ → ℂ → Vcoup) (lbar C κ bbar Cm : ℝ),
      FlowDataW d L A ℓ₀ V₀c lbar C κ ∧ 0 < bbar ∧ bbar ≤ lbar ∧ 0 ≤ Cm ∧
      (∀ b, 0 < b → b ≤ bbar → hF V₀c b 0 = 0) ∧
      ∀ N : ℕ, 1 ≤ N → ∀ b, 0 < b → b ≤ bbar →
        0 < atR d L V₀c N b ∧
        (∃ E₁ E₂ : ℝ, |E₁| ≤ Cm * b * (L : ℝ) ^ (-(κ * N)) ∧ |E₂| ≤ Cm * b * (L : ℝ) ^ (2 * N) ∧
          H02.expTree (nnW d L N (betaF V₀c b 0)) (nnW_symm _) 0 =
            c2F V₀c b 0 * (1 + E₁) / atR d L V₀c N b + E₂) ∧
        1 / atR d L V₀c N b ≤ Cm * Fintype.card (Lam d L N) / b := by
  obtain ⟨L₀, H⟩ := exists_flowDataW hd
  refine ⟨L₀, fun L _ hL hLodd => ?_⟩
  obtain ⟨A, ℓ₀, V₀c, lbar, C, κ, HW⟩ := H L hL hLodd
  obtain ⟨bbar, Cm, hb0, hb2, hCm, hh0, hmain⟩ := cor_macro_of hd HW
  exact ⟨A, ℓ₀, V₀c, lbar, C, κ, bbar, Cm, HW, hb0, by linarith [HW.lbar_pos], hCm, hh0, hmain⟩

end

end Ward
