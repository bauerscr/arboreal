import Spin2.Pair.PairInitReq
import PtCorr2.Pair.SeedSplit2
import PtCorr2.Pair.SXOStepAB
import Spin2.Pair.PairVReq

/-!
# The requirements on `A` and `ε` of the reduced `ab` chain with per-scale weights

`PtCorr2.obs_histFromABL_wM` (the `K'`, `𝒲'` sizes of the reduced `ab` history in the weights
`wM(M_{a,j}, M_{b,j})`) needs the constants of `KObsBoundsABL` (`kobs_bounds_ABL`) and
`WObsBoundsAB` (`wobs_bounds_AB`), `θ₀ ≤ 1/72`, `K_w/L ≤ 1/12` and the smallness conditions
`hsm`, `hεε`, `hεk`, `hBr`, `hC₁ε`, `hε₁` at `ε`. They are fixed here with `c_k = 1`
(the seed condition `8k₀ ≤ c_k c_W m_{j₀}` is then met by the choice of `m`, which is only an upper
bound):

* **`abwAReq`** (`abwAReq_ev`): the constants of `KObsBoundsABL` exist at `(L, A)`, `θ₀ ≤ 1/72`;
* **`abwEReq`** (`abwEReq_ev`): the `ε`-conditions, with `c = c_R`, `c' = c_x`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Filter Topology

/-- The requirement on `A` of the reduced `ab` chain (`KObsBoundsABL`, `θ₀ ≤ 1/72`). -/
def abwAReq (C₀ η : ℝ) (La : ℕ) (L : ℕ) (A : ℝ) : Prop :=
  ∀ [NeZero L], La ≤ L →
    (∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsABL L A C₀ η ε₀ C₁) ∧ kθ0 L A C₀ η ≤ 1 / 72

theorem abwAReq_ev {C₀ η : ℝ} {L₀ La : ℕ} (hC₀ : 0 ≤ C₀) (hη : 0 < η)
    (hk : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
      ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsABL L A C₀ η ε₀ C₁)
    (hLa : L₀ ≤ La) (hLa' : 144 * C₀ + 1 ≤ (La : ℝ)) (L : ℕ) :
    ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → abwAReq C₀ η La L A := by
  by_cases hL : L ≠ 0 ∧ La ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    obtain ⟨A₀, -, hA⟩ := hk L (hLa.trans hL.2)
    refine ⟨max A₀ (2 * (144 * C₀ + 1) ^ η⁻¹), fun A hA' _ _ => ⟨hA A (le_of_max_le_left hA'),
      kθ0_le hC₀ hη (hLa'.trans (by exact_mod_cast hL.2)) (le_of_max_le_right hA')⟩⟩
  · exact ⟨0, fun A _ inst hLL => absurd ⟨inst.out, hLL⟩ hL⟩

/-- The requirement on `ε` of the reduced `ab` chain (`c = c_R`, `c' = c_x`, `c_k = 1`): the
smallness conditions of `obs_histFromABL_wM`. -/
def abwEReq (C₀ η Kw : ℝ) (La : ℕ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], La ≤ L → abwAReq C₀ η La L A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsABL L A C₀ η ε₀ C₁ ∧
      C₁ * (2 + 2 * (8 * c') + 1) * (c * ε) ≤ 1 / 72 ∧
      c * ε ≤ ε₀ ∧ (8 * c' + 1) * (c * ε) ≤ ε₀ ∧
      32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2 ≤ 1 ∧
    ∃ C₁w ε₁ : ℝ, 0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBoundsAB L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧
      c * ε ≤ ε₁

theorem abwEReq_ev {C₀ η Kw : ℝ} {L₀ La : ℕ}
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBoundsAB L Kw C₁ ε₁)
    (hLa : L₀ ≤ La) (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), abwEReq C₀ η Kw La L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ La ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : abwAReq C₀ η La L A
    · obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2
      obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLa.trans hL.2)
      filter_upwards [ev_lin (C₁ * (2 + 2 * (8 * c') + 1) * c) (by norm_num : (0 : ℝ) < 1 / 72),
        ev_lin c hε₀, ev_lin ((8 * c' + 1) * c) hε₀,
        ev_small (f := fun ε => 32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2) (c := 1)
          (by fun_prop) (by simp),
        ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁]
        with ε h1 h2 h3 h4 h5 h6
      intro _ _ _
      exact ⟨ε₀, C₁, hε₀, hC₁, hKB, by rw [← mul_assoc]; exact h1, h2,
        by rw [← mul_assoc]; exact h3, h4, C₁w, ε₁, hC₁w, hε₁, hWB,
        by rw [← mul_assoc]; exact h5, h6⟩
    · exact Eventually.of_forall fun _ _ _ hA' => absurd (fun (_ : NeZero L) => hA') hA
  · exact Eventually.of_forall fun _ inst hLL _ => absurd ⟨inst.out, hLL⟩ hL

/-! ### The `V`-step requirement (appended)

`abwEReqV` is `abwEReq` (same constants `C₁ = C₁k`, `C₁w`) together with the two `ε`-conditions of
the `V`-step of the joint induction (`Spin2/Pair/PairVStep*`): `16·vA2(L, C₁w)·cε ≤ 1` (the `S(B_+)` part
of the gradient of `V'_{ab}` is `≤ m̄/8`) and `32B(cε)² ≤ vck(C₁w)` (the `K'` sizes stay below
`vck·c_W m̄`, `kseqF_leL` with `c_k = vck`). It implies `abwEReq` (`abwEReq_of_V`). -/

/-- The requirement on `ε` of the `V`-step (`abwEReq` with the same constants plus the `V`-step
conditions). -/
def abwEReqV (C₀ η Kw : ℝ) (La : ℕ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  ∀ [NeZero L], La ≤ L → abwAReq C₀ η La L A →
    ∃ ε₀ C₁ : ℝ, 0 < ε₀ ∧ 0 ≤ C₁ ∧ KObsBoundsABL L A C₀ η ε₀ C₁ ∧
      C₁ * (2 + 2 * (8 * c') + 1) * (c * ε) ≤ 1 / 72 ∧
      c * ε ≤ ε₀ ∧ (8 * c' + 1) * (c * ε) ≤ ε₀ ∧
      32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2 ≤ 1 ∧
    ∃ C₁w ε₁ : ℝ, 0 ≤ C₁w ∧ 0 < ε₁ ∧ WObsBoundsAB L Kw C₁w ε₁ ∧ C₁w * (c * ε) ≤ 1 / 12 ∧
      c * ε ≤ ε₁ ∧
      16 * vA2 L C₁w * (c * ε) ≤ 1 ∧
      32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2 ≤ vck C₁w

theorem abwEReqV_ev {C₀ η Kw : ℝ} {L₀ La : ℕ}
    (hw : ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧ WObsBoundsAB L Kw C₁ ε₁)
    (hLa : L₀ ≤ La) (L : ℕ) (A c c' : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), abwEReqV C₀ η Kw La L A c c' ε := by
  by_cases hL : L ≠ 0 ∧ La ≤ L
  · haveI : NeZero L := ⟨hL.1⟩
    by_cases hA : abwAReq C₀ η La L A
    · obtain ⟨⟨ε₀, C₁, hε₀, hC₁, hKB⟩, -⟩ := hA hL.2
      obtain ⟨C₁w, ε₁, hC₁w, hε₁, hWB⟩ := hw L (hLa.trans hL.2)
      filter_upwards [ev_lin (C₁ * (2 + 2 * (8 * c') + 1) * c) (by norm_num : (0 : ℝ) < 1 / 72),
        ev_lin c hε₀, ev_lin ((8 * c' + 1) * c) hε₀,
        ev_small (f := fun ε => 32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2) (c := 1)
          (by fun_prop) (by simp),
        ev_lin (C₁w * c) (by norm_num : (0 : ℝ) < 1 / 12), ev_lin c hε₁,
        ev_lin (16 * vA2 L C₁w * c) (by norm_num : (0 : ℝ) < 1),
        ev_small (f := fun ε => 32 * kB (kθ0 L A C₀ η) C₁ (8 * c') * (c * ε) ^ 2) (c := vck C₁w)
          (by fun_prop) (by simpa using vck_pos hC₁w)]
        with ε h1 h2 h3 h4 h5 h6 h7 h8
      intro _ _ _
      exact ⟨ε₀, C₁, hε₀, hC₁, hKB, by rw [← mul_assoc]; exact h1, h2,
        by rw [← mul_assoc]; exact h3, h4, C₁w, ε₁, hC₁w, hε₁, hWB,
        by rw [← mul_assoc]; exact h5, h6, by rw [← mul_assoc]; exact h7, h8⟩
    · exact Eventually.of_forall fun _ _ _ hA' => absurd (fun (_ : NeZero L) => hA') hA
  · exact Eventually.of_forall fun _ inst hLL _ => absurd ⟨inst.out, hLL⟩ hL

end

end Spin2
