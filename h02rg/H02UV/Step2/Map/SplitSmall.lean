import DressedFRD.FrdMain
import DressedFRD.EpsZero

/-!
# The splitting of the dressed decomposition for small couplings

`SplitSmall P L ρ`: for every `N ≥ 1`, `0 < m² ≤ L^{-2(N-1)}` and every dressed history `ζ` with
`|ζ_i| ≤ ρ`, the dressed decomposition of `FRD` (`d = 2`) has non-vanishing absorption
denominators and the exact splitting `Γ_j(1 + z_jAΓ_j)^{-1} = Γ^int_{j+1} + Γ_{j+1}` at every
`j < N` (`thm:main`(i), `DressedFRD.Data.Concl.den`, `.split`); moreover, with a constant `B ≥ 0`,
`|ζ'_jε_j(0)| ≤ 1/2` and `|ε_j(0)| ≤ B m² L^{2j}` (`DressedFRD.eps_zero_bound`).

`splitSmall_exists`: there is `ζ_F > 0` with `SplitSmall P L ρ` for all `0 ≤ ρ ≤ ζ_F`
(from `thm_main_frd` and `eps_zero_bound`).
-/

namespace Step2

noncomputable section

open DressedFRD

/-- The zero mode of `ε_j` for all histories with `|ζ_i| ≤ ρ`: `|ζ'_jε_j(0)| ≤ 1/2` and
`|ε_j(0)| ≤ B m² L^{2j}` (`DressedFRD.eps_zero_bound`). -/
def EpsZeroSmall (P : FRD.PtFamily) (L : ℕ) (ρ B : ℝ) : Prop :=
  ∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → ∀ j, j < N →
      ‖(⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).zp j *
          (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).eps j
            ((⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).tails j) 0‖ ≤ 1 / 2 ∧
      ‖(⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).eps j
          ((⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).tails j) 0‖ ≤
        B * msq * (L : ℝ) ^ (2 * j)

/-- The splitting hypotheses for all histories with `|ζ_i| ≤ ρ`, and the zero mode of `ε_j`
(`EpsZeroSmall`). -/
def SplitSmall (P : FRD.PtFamily) (L : ℕ) (ρ : ℝ) : Prop :=
  (∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ ζ : ℕ → ℂ, (∀ i, ‖ζ i‖ ≤ ρ) → ∀ j, j < N →
      (∀ m, 1 + (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).ζ j *
          (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).Z j * Asym msq m *
          (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).Gam j m ≠ 0) ∧
      ∀ m, (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).absorbed j m =
        (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).Gint j m +
          (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data 2 (L ^ N)).Gam (j + 1) m) ∧
  ∃ B : ℝ, 0 ≤ B ∧ EpsZeroSmall P L ρ B

theorem SplitSmall.mono {P : FRD.PtFamily} {L : ℕ} {ρ ρ' : ℝ} (h : SplitSmall P L ρ)
    (hρ : ρ' ≤ ρ) : SplitSmall P L ρ' := by
  obtain ⟨h1, B, hB, h2⟩ := h
  exact ⟨fun N msq hN hm0 hm ζ hζ j hj => h1 N msq hN hm0 hm ζ (fun i => (hζ i).trans hρ) j hj,
    B, hB, fun N msq hN hm0 hm ζ hζ j hj => h2 N msq hN hm0 hm ζ (fun i => (hζ i).trans hρ) j hj⟩

/-- **The splitting for small couplings** (from `thm_main_frd` and `eps_zero_bound`). -/
theorem splitSmall_exists (P : FRD.PtFamily) {L : ℕ} [NeZero L] (hL7 : 7 ≤ L) :
    ∃ ζF : ℝ, 0 < ζF ∧ SplitSmall P L ζF := by
  obtain ⟨ζbar, hζ, -, K, h⟩ := thm_main_frd P (d := 2) le_rfl (q := 2) le_rfl hL7
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull P (d := 2) le_rfl hL7 (q := 2) (M := 2 + 2 + 1) le_rfl
  obtain ⟨ζE, hζE, -, B, hB, hE⟩ := eps_zero_bound (q := 2) (M := 2 + 2 + 1) le_rfl hL7 le_rfl hcS
  refine ⟨min ζbar ζE, lt_min hζ hζE, fun N msq hN hm0 hm ζ hζb j hj => ?_, B, hB,
    fun N msq hN hm0 hm ζ hζb j hj => ?_⟩
  · have hc := (h (L ^ N) N msq ζ hN rfl hm0 hm).1 (fun i => (hζb i).trans (min_le_left _ _)) j hj
    exact ⟨hc.den, hc.split⟩
  · exact hE (L ^ N) ⟨L, N, msq, frdC P msq L N, ζ⟩ rfl rfl (hS (L ^ N) N msq hN rfl hm0) hm
      (fun i => (hζb i).trans (min_le_right _ _)) j hj

end

end Step2
