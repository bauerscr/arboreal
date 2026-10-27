import PtCorr2.Zero.Glue

/-!
# The raw zero mode `t_raw` and the `t` of `prop_last` along the flow

`ZtFin` integrates the raw zero mode `t_raw Q`, `t_raw = Γ̂^int_N(0)` of the dressed history `ζ` of
the last step (`zmRaw`). In normalised fields the zero-mode variance is `t = Z_N t_raw` with
`Z_N = ∏_{i<N} (1 + ζ_i)`: this is the `t = Z_N Γ̂^int_N(0)` of `prop_last` / `prop_last_d2`.

* `rawHist_struct`: along every history (no validity needed) `Z_j = ∏_{i<j}(1 + ζ_i)`,
  `ζ_i = 0` for `i ≥ j`, `|ζ_i| ≤ ρ`;
* `lastOut_struct`: the same for the final-scale object (`Z_N`, `ζ`) of `lastOut`;
* `zmRaw_eq_Dz`: `zmRaw` is the `Γ̂^int_N(0)` of the data `D₀.Dz z` of `prop_last` with
  `z_i = ζ_i`, and `Z_N = (D₀.Dz z).Z N`;
* **`zero_mode_t`**: with the constants `ζ̄, K` of `prop_last_d2` and `ρ ≤ ζ̄`, along every
  history, `t = Z_N t_raw` satisfies `|t - t_N| ≤ K L^{2N} ρ` and `|m² t - 1| ≤ K m² L^{2N}`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Step2 Step

variable {L N : ℕ} [NeZero L]

/-- **Structure of the raw history** (no validity needed). -/
theorem rawHist_struct (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ : 0 ≤ R.ρ) :
    ∀ (j : ℕ) (t : Hist.Seq (Xs R)),
      (rawHist R j t).Z = ∏ i ∈ range j, (1 + (rawHist R j t).ζ i) ∧
        (∀ i, j ≤ i → (rawHist R j t).ζ i = 0) ∧ ∀ i, ‖(rawHist R j t).ζ i‖ ≤ R.ρ
  | 0, _ => ⟨by simp [rawHist], fun _ _ => rfl, fun _ => by simpa [rawHist] using hρ⟩
  | j + 1, t => by
    obtain ⟨hZ, h0, hb⟩ := rawHist_struct R hρ j t
    set st := rawHist R j t
    have eζ : (rawHist R (j + 1) t).ζ = Function.update st.ζ j (absorbZeta R st.Z (st.z + st.y)) :=
      rfl
    have eZ : (rawHist R (j + 1) t).Z = st.Z * (1 + absorbZeta R st.Z (st.z + st.y)) := rfl
    refine ⟨?_, fun i hi => ?_, fun i => ?_⟩
    · rw [eZ, eζ, prod_range_succ, Function.update_self, hZ]
      congr 1
      refine prod_congr rfl fun i hi => ?_
      rw [Function.update_of_ne (by have := mem_range.1 hi; omega)]
    · rw [eζ, Function.update_of_ne (by omega), h0 i (by omega)]
    · rw [eζ]
      by_cases hi : i = j
      · subst hi; rw [Function.update_self]; exact absorb_le R hρ _ _
      · rw [Function.update_of_ne hi]; exact hb i

/-- The final-scale object of `lastOut` is the raw state at `N_h + 2`. -/
theorem lastOut_Z_ζ (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ)
    (t : Hist.Seq (Xs R)) :
    (lastOut R Nh t).Z = (rawHist R (Nh + 2) t).Z ∧ (lastOut R Nh t).ζ = (rawHist R (Nh + 2) t).ζ :=
  ⟨rfl, rfl⟩

/-- `zmRaw` with a finitely supported history is the zero mode of `prop_last`'s data. -/
theorem zmRaw_eq_Dz (R : RGPar 2 L N) (j : ℕ) (ζ : ℕ → ℂ) (hζ : ∀ i, j + 1 ≤ i → ζ i = 0) :
    let D₀ : DressedFRD.Data 2 (L ^ N) := ⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, 0⟩
    let z : Fin (j + 1) → ℂ := fun i => ζ i
    zmRaw R j ζ = (D₀.Dz z).Gint j 0 ∧
      ∏ i ∈ range (j + 1), (1 + ζ i) = (D₀.Dz z).Z (j + 1) := by
  intro D₀ z
  have e : DressedFRD.Data.ext z = ζ := by
    funext i
    unfold DressedFRD.Data.ext
    split_ifs with h
    · rfl
    · exact (hζ i (by omega)).symm
  have hD : D₀.Dz z = ⟨L, N, R.msq, DressedFRD.frdC R.P R.msq L N, ζ⟩ := by
    rw [← e]; rfl
  rw [hD]
  exact ⟨rfl, rfl⟩

/-- **The zero mode along the flow**: with the constants of `prop_last_d2` and `ρ ≤ ζ̄`, for every
history, the normalised zero-mode variance `t = Z_N t_raw` of the final-scale object satisfies
`|t - t_N| ≤ K L^{2N} ρ` and `|m² t - 1| ≤ K m² L^{2N}`. -/
theorem zero_mode_t (P : PtFamily) (hL7 : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = P → 0 ≤ R.ρ → R.ρ ≤ ζbar →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ (Nh : ℕ), Nh + 2 = N → ∀ t : Hist.Seq (Xs R),
      let out := lastOut R Nh t
      ‖out.Z * zmRaw R (Nh + 1) out.ζ - (tN P 2 R.msq (L : ℝ) N : ℂ)‖ ≤
          K * (L : ℝ) ^ (2 * N) * R.ρ ∧
        ‖(R.msq : ℂ) * (out.Z * zmRaw R (Nh + 1) out.ζ) - 1‖ ≤ K * R.msq * (L : ℝ) ^ (2 * N) := by
  obtain ⟨ζbar, hζ, hζ8, K, hK, h⟩ := prop_last_d2 (L := L) P hL7
  refine ⟨ζbar, hζ, hζ8, K, hK, fun R _ _ hP hρ0 hρ hm0 hm Nh hNh t => ?_⟩
  intro out
  obtain ⟨hZ, h0, hb⟩ := rawHist_struct R hρ0 (Nh + 2) t
  obtain ⟨eZ, eζ⟩ := lastOut_Z_ζ R Nh t
  have hsupp : ∀ i, Nh + 1 + 1 ≤ i → out.ζ i = 0 := fun i hi => by
    show (lastOut R Nh t).ζ i = 0
    rw [eζ]; exact h0 i (by omega)
  obtain ⟨e1, e2⟩ := zmRaw_eq_Dz R (Nh + 1) out.ζ hsupp
  have eZ' : out.Z = ∏ i ∈ range (Nh + 1 + 1), (1 + out.ζ i) := by
    show (lastOut R Nh t).Z = ∏ i ∈ range (Nh + 1 + 1), (1 + (lastOut R Nh t).ζ i)
    rw [eZ, eζ, hZ]
  have hz : ∀ i : Fin (Nh + 1 + 1), ‖out.ζ i‖ ≤ ζbar := fun i => by
    show ‖(lastOut R Nh t).ζ i‖ ≤ ζbar
    rw [eζ]; exact (hb i).trans hρ
  obtain ⟨h4, h5⟩ := h N R.msq (by omega) hm0 hm (Nh + 1) (by omega) (fun i => out.ζ i) hz
  rw [hP] at e1 e2
  set D₀ : DressedFRD.Data 2 (L ^ N) := ⟨L, N, R.msq, DressedFRD.frdC P R.msq L N, 0⟩
  have et : out.Z * zmRaw R (Nh + 1) out.ζ =
      (D₀.Dz fun i : Fin (Nh + 1 + 1) => out.ζ i).Z (Nh + 1 + 1) *
        (D₀.Dz fun i : Fin (Nh + 1 + 1) => out.ζ i).Gint (Nh + 1) 0 := by
    rw [eZ', e2, e1]
  rw [et]
  refine ⟨h4.trans ?_, h5⟩
  have hMz : (D₀.Dz fun i : Fin (Nh + 1 + 1) => out.ζ i).Mz (Nh + 1 + 1) ≤ R.ρ :=
    DressedFRD.Data.Mz_le hρ0 fun i hi => by
      show ‖DressedFRD.Data.ext (fun i : Fin (Nh + 1 + 1) => out.ζ i) i‖ ≤ R.ρ
      unfold DressedFRD.Data.ext; rw [dif_pos hi]
      show ‖(lastOut R Nh t).ζ i‖ ≤ R.ρ
      rw [eζ]; exact hb i
  have hP0 : 0 ≤ K * (L : ℝ) ^ (2 * N) := by positivity
  exact mul_le_mul_of_nonneg_left hMz hP0

end

end PtCorr2
