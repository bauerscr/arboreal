import PtCorr2.Pair.PairZero
import PtCorr2.Zero.ZeroT
import Step2.Last.ZeroTOk

/-!
# The last step, one-point items: the zero mode and `P₀` (PR6 items (a), (e))

* **`lastOut_zeroT`**: `ZeroTOk L ρ'` (the bound of `prop_last_d2` for `|ζ_i| ≤ ρ'`) and
  `R.ρ ≤ ρ'` give, along every history, `|m²t - 1| ≤ K m² L^{2N}` for `t = Z_N t_raw` of the
  final-scale object `lastOut` (same proof as `zero_mode_t`).
* `norm_tr_ge`: `|m²Z t_raw - 1| ≤ ½`, `m² > 0` give `|t_raw| ≥ 1/(2m²|Z|)`.
* **`eps_LS_le`**, **`eps_Wp_last_le`**: at the last scale (`j + 1 = N`, `n_B ≤ L^d` blocks) the
  localisation `Loc_{B_+,B}S(B_+)` has `ε(Loc_{B_+,B}S(B_+)) = ε(S(B_+))|B|/|B_+|`
  (`eps_LocXY`, `eps_Loc4sXY`), so `|ε S(B)| ≤ w` on every block gives `|ε𝒲_{j+1}(B)| ≤ (1 + L^d)w`
  for `𝒲_{j+1} = S - Loc S` (`Step2.Wp`). The observable last step uses `Wp` (with the `Loc`),
  the bulk final object `lastOut` uses `S(B)` (`rawStepN`): the two `P₀` differ, but both are
  `1 + O(ǧ²)`.
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step Loc Step2 Step2.LastN Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **The zero mode of `lastOut` from `ZeroTOk`** (copy of the proof of `zero_mode_t`). -/
theorem lastOut_zeroT {ρ' : ℝ} (hZ : ZeroTOk L ρ') :
    ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 0 ≤ R.ρ → R.ρ ≤ ρ' →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ (Nh : ℕ), Nh + 2 = N → ∀ t : Flow2.Hist.Seq (Xs R),
      ‖(R.msq : ℂ) * ((lastOut R Nh t).Z * zmRaw R (Nh + 1) (lastOut R Nh t).ζ) - 1‖ ≤
        K * R.msq * (L : ℝ) ^ (2 * N) := by
  obtain ⟨K, hK, h⟩ := hZ
  refine ⟨K, hK, fun N R _ _ hP hρ0 hρ hm0 hm Nh hNh t => ?_⟩
  set out := lastOut R Nh t
  obtain ⟨hZp, h0, hb⟩ := rawHist_struct R hρ0 (Nh + 2) t
  obtain ⟨eZ, eζ⟩ := lastOut_Z_ζ R Nh t
  have hsupp : ∀ i, Nh + 1 + 1 ≤ i → out.ζ i = 0 := fun i hi => by
    show (lastOut R Nh t).ζ i = 0
    rw [eζ]; exact h0 i (by omega)
  obtain ⟨e1, e2⟩ := zmRaw_eq_Dz R (Nh + 1) out.ζ hsupp
  have eZ' : out.Z = ∏ i ∈ range (Nh + 1 + 1), (1 + out.ζ i) := by
    show (lastOut R Nh t).Z = ∏ i ∈ range (Nh + 1 + 1), (1 + (lastOut R Nh t).ζ i)
    rw [eZ, eζ, hZp]
  have hz : ∀ i : Fin (Nh + 1 + 1), ‖out.ζ i‖ ≤ ρ' := fun i => by
    show ‖(lastOut R Nh t).ζ i‖ ≤ ρ'
    rw [eζ]; exact (hb i).trans hρ
  have h5 := h N R.msq (by omega) hm0 hm (Nh + 1) (by omega) (fun i => out.ζ i) hz
  rw [hP] at e1 e2
  have et : out.Z * zmRaw R (Nh + 1) out.ζ =
      ((⟨L, N, R.msq, DressedFRD.frdC Pc R.msq L N, 0⟩ : DressedFRD.Data 2 (L ^ N)).Dz
          fun i : Fin (Nh + 1 + 1) => out.ζ i).Z (Nh + 1 + 1) *
        ((⟨L, N, R.msq, DressedFRD.frdC Pc R.msq L N, 0⟩ : DressedFRD.Data 2 (L ^ N)).Dz
          fun i : Fin (Nh + 1 + 1) => out.ζ i).Gint (Nh + 1) 0 := by
    rw [eZ', e2, e1]
  rw [et]
  exact h5

/-- `|m²Z t_raw - 1| ≤ ½` and `m² > 0` give `1/(2m²|Z|) ≤ |t_raw|`. -/
theorem norm_tr_ge {m : ℝ} {Z tr : ℂ} (hm : 0 < m) (hZ : Z ≠ 0)
    (h : ‖(m : ℂ) * (Z * tr) - 1‖ ≤ 1 / 2) : 1 / (2 * m * ‖Z‖) ≤ ‖tr‖ := by
  have h1 : 1 / 2 ≤ ‖(m : ℂ) * (Z * tr)‖ := by
    have e : (1 : ℂ) = (m : ℂ) * (Z * tr) - ((m : ℂ) * (Z * tr) - 1) := by ring
    have := norm_sub_le ((m : ℂ) * (Z * tr)) ((m : ℂ) * (Z * tr) - 1)
    rw [← e, norm_one] at this
    linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hm.le] at h1
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  rw [div_le_iff₀ (by positivity)]
  nlinarith

section Loc

variable {d : ℕ} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ) (V W : Fam d L N)

/-- `ε(Loc_{B_+,B}S(B_+))`, last scale: `|ε S(B')| ≤ w` on all blocks gives `≤ L^d w`. -/
theorem eps_LS_le (hj : j + 1 = N) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ‖ε (Sb j C V W b : Alg d L N)‖ ≤ w)
    (b : Fin d → ℕ) : ‖ε (LS j C V W b : Alg d L N)‖ ≤ (L : ℝ) ^ d * w := by
  set X := Bp (L := L) (N := N) j b
  set Y := blockSet (L := L) (N := N) j b
  have e : ε (LS j C V W b : Alg d L N) = ε (SX j C V W X : Alg d L N) * Y.card / X.card := by
    show ε (Loc2sXY X Y (SX j C V W X : Alg d L N)) = _
    rw [Loc2sXY, map_add, eps_LocXY, eps_Loc4sXY, add_zero]
  have hYX : (Y.card : ℝ) / X.card ≤ 1 := by
    rcases Nat.eq_zero_or_pos X.card with h0 | hpos
    · rw [h0, Nat.cast_zero, div_zero]; exact zero_le_one
    · rw [div_le_one (by exact_mod_cast hpos)]
      exact_mod_cast card_le_card (subset_clo j _)
  have hsub : blocks j X ⊆ blockIdx (d := d) (L := L) (N := N) j :=
    image_subset_image (subset_univ X)
  have hS : ‖ε (SX j C V W X : Alg d L N)‖ ≤ (L : ℝ) ^ d * w := by
    rw [SX, AddSubmonoidClass.coe_finsetSum, map_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ b' ∈ blocks j X, ‖ε (Sb j C V W b' : Alg d L N)‖
        ≤ ∑ _b' ∈ blocks j X, w := sum_le_sum fun b' hb' => hw b' (hsub hb')
      _ = (blocks j X).card * w := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (L : ℝ) ^ d * w := by
          refine mul_le_mul_of_nonneg_right ?_ hw0
          have h1 := (card_le_card hsub).trans (card_blockIdx_last (d := d) (L := L) hj)
          exact_mod_cast h1
  rw [e, mul_div_assoc, norm_mul]
  have hYX' : ‖((Y.card : ℂ) / X.card)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]; exact hYX
  calc ‖ε (SX j C V W X : Alg d L N)‖ * ‖((Y.card : ℂ) / X.card)‖
      ≤ (L : ℝ) ^ d * w * 1 := mul_le_mul hS hYX' (norm_nonneg _) (by positivity)
    _ = (L : ℝ) ^ d * w := mul_one _

/-- `|ε𝒲_{j+1}(B)| ≤ (1 + L^d)w` at the last scale (`𝒲_{j+1} = S - Loc S`). -/
theorem eps_Wp_last_le (hj : j + 1 = N) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : ∀ b ∈ blockIdx (d := d) (L := L) (N := N) j, ‖ε (Sb j C V W b : Alg d L N)‖ ≤ w)
    (b : Fin d → ℕ) (hb : b ∈ blockIdx (d := d) (L := L) (N := N) j) :
    ‖ε (Wp j C V W b : Alg d L N)‖ ≤ (1 + (L : ℝ) ^ d) * w := by
  have e : ε (Wp j C V W b : Alg d L N) =
      ε (Sb j C V W b : Alg d L N) - ε (LS j C V W b : Alg d L N) := by
    rw [Wp, Subalgebra.coe_sub, map_sub]
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := eps_LS_le j C V W hj hw0 hw b
  linarith [hw b hb]

end Loc

end

end PtCorr2
