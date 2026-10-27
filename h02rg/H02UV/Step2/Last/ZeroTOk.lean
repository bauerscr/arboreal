import Step2.Last.ZeroMode
import Step2.D2.D2Ehat

/-!
# The zero-mode bound of `prop_last_d2` at a given `ρ`

`ZeroTOk L ρ`: with one constant `K ≥ 0`, for every `N`, `m² ∈ (0, L^{-2(N-1)}]`, `j + 1 = N` and
every dressed history `z` with `|z_i| ≤ ρ`, the normalised zero-mode variance
`t = Z_N Γ̂^int_N(0)` satisfies `|m² t - 1| ≤ K m² L^{2N}` (`prop_last_d2`).

`zeroTOk_of_d2`: `ZeroTOk L ρ` for every `ρ` below the `ζ̄` of `prop_last_d2`. This is the link
used by the master construction `flow_master_hyp0LZ` (`ρ` additionally below this `ζ̄`).
-/

namespace Step2

noncomputable section

open Finset Step2.D2

/-- **The zero-mode bound at `ρ`** (`prop_last_d2`, second item, for `|ζ_i| ≤ ρ`). -/
def ZeroTOk (L : ℕ) [NeZero L] (ρ : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq →
    msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ∀ j, j + 1 = N →
      ∀ z : Fin (j + 1) → ℂ, (∀ i, ‖z i‖ ≤ ρ) →
        ‖(msq : ℂ) *
            (((⟨L, N, msq, DressedFRD.frdC Pc msq L N, 0⟩ : DressedFRD.Data 2 (L ^ N)).Dz z).Z
                (j + 1) *
              ((⟨L, N, msq, DressedFRD.frdC Pc msq L N, 0⟩ : DressedFRD.Data 2 (L ^ N)).Dz z).Gint
                j 0) - 1‖ ≤
          K * msq * (L : ℝ) ^ (2 * N)

/-- `ZeroTOk` below the `ζ̄` of `prop_last_d2`. -/
theorem zeroTOk_of_d2 {L : ℕ} [NeZero L] (hL7 : 7 ≤ L) :
    ∃ ζT : ℝ, 0 < ζT ∧ ∀ ρ : ℝ, ρ ≤ ζT → ZeroTOk L ρ := by
  obtain ⟨ζbar, hζ, -, K, hK, h⟩ := prop_last_d2 (L := L) Pc hL7
  exact ⟨ζbar, hζ, fun ρ hρ => ⟨K, hK, fun N msq hN hm0 hm j hj z hz =>
    (h N msq hN hm0 hm j hj z fun i => (hz i).trans hρ).2⟩⟩

end

end Step2
