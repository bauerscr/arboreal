import Step2.Flow.FlowF1d
import Step2.FlowCont.FlowCont3

/-!
# The step hypotheses for the concrete dressed decomposition

`validAt_concrete`: for the dressed decomposition of `FRD` (`d = 2`), `ValidAt R j` holds for all
`j + 2 < N` as soon as `ℓ ≥ ℓ₀` (independent of `N`, `m²`, `j`), `0 ≤ ρ ≤ ζ̄`, `L > 48`,
`0 < m² ≤ L^{-2(N-1)}`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L : ℕ} [NeZero L]

theorem ellDr_two (L : ℕ) (cS K M : ℝ) (j : ℕ) : ellDr 2 L cS K M j = ellDr 2 L cS K M 0 := by
  unfold ellDr; norm_num

/-- **`ValidAt` for the concrete dressed decomposition.** -/
theorem validAt_concrete (P : PtFamily) (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ℓ₀ ≤ R.ℓ → 0 ≤ R.ρ → R.ρ ≤ ζbar →
      ∀ j, j + 2 < N → ValidAt R j := by
  obtain ⟨cS, hcS, ζbar, hζ, hζ8, K, hK0, h⟩ := raw_family (d := 2) (L := L) P le_rfl (by omega)
  have hE0 : 0 ≤ ellDr 2 L cS K ζbar 0 := by unfold ellDr; positivity
  refine ⟨4 * ellDr 2 L cS K ζbar 0 + 1, by linarith, ζbar, hζ, hζ8, ?_⟩
  intro N R hP hN hm0 hm hℓ hρ0 hρ j hj
  refine ⟨hj, by norm_num, hL, hρ0, hρ.trans hζ8, by linarith, fun ζ hζb => ?_⟩
  set z : Fin (j + 1) → ℂ := fun i => ζ i
  set D₀ : DressedFRD.Data 2 (L ^ N) := ⟨L, N, R.msq, DressedFRD.frdC P R.msq L N, 0⟩
  have hz : ∀ i, ‖z i‖ ≤ ζbar := fun i => (hζb i).trans hρ
  have hg := h N R.msq hN hm0 hm j (by omega) z hz
  -- the raw covariance
  have hDζ : (⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ : DressedFRD.Data 2 (L ^ N)) =
      D₀.withζ ζ := by rw [hP]; rfl
  have hG : rawCov R j ζ = DressedFRD.kmat ((D₀.Dz z).Gint j) := by
    unfold rawCov
    rw [hDζ]
    have e : D₀.Dz z = (D₀.withζ ζ).withζ (DressedFRD.Data.ext z) := rfl
    rw [e, DressedFRD.Data.Gint_congr (D := D₀.withζ ζ) (ζ' := DressedFRD.Data.ext z)]
    intro i hi
    show ζ i = DressedFRD.Data.ext z i
    unfold DressedFRD.Data.ext
    rw [dif_pos (by omega)]
  have hZ : (D₀.Dz z).Z (j + 1) = ∏ i ∈ range (j + 1), (1 + ζ i) := by
    unfold DressedFRD.Data.Z
    refine prod_congr rfl fun i hi => ?_
    show 1 + DressedFRD.Data.ext z i = 1 + ζ i
    unfold DressedFRD.Data.ext
    rw [dif_pos (mem_range.1 hi)]
  have hC : ∀ k π s m, (D₀.Dz z).C k (symmDual π s m) = (D₀.Dz z).C k m :=
    fun k π s m => frdC_symm P _ _ _ _ π s m
  have hsym : DressedFRD.Data.Gint (D₀.Dz z) j ∈ symSub := DData.Gint_symMem hC j
  rw [hG]
  refine ⟨?_, TInv_kmat _, kmat_CSym ?_, kmat_symm ?_⟩
  · refine hg.mono ?_
    rw [hZ, ellDr_two, norm_inv]
    unfold fscale
    have : 0 ≤ Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ := Real.sqrt_nonneg _
    have h4 : ellDr 2 L cS K ζbar 0 ≤ R.ℓ / 4 := by linarith
    calc Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ * ellDr 2 L cS K ζbar 0 ≤
        Real.sqrt ‖∏ i ∈ range (j + 1), (1 + ζ i)‖⁻¹ * (R.ℓ / 4) := by gcongr
      _ = _ := by ring
  · exact hsym
  · exact hsym

end

end Step2
