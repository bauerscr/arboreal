import PtCorr2.Obs.KObsHist
import PtCorr2.Obs.ObsSym
import Obs2.Flow.MuK

-- Merged from `PtCorr2/MuKHist.lean` (phase 3).
section

/-!
# The field `hK` of `MuErr` along the history

**`histKO_hK`**: along the history (steps with `ValidCore` and `RawInv`, initial state with
`ObsLocInv P 0 o₀`), if the `σ_a` components of the full activity `K_j(X)` have
`w_a ‖K_j(X)_a‖_{T_j(ℓ)} ≤ k` on small sets, then

  `|∑_{X ∈ 𝒮_j} m₁(K_j(X)_a)| ≤ c (k / w_a) ℓ^{-1}`

(`Obs2.sum_mass1_le`; the support property `a ∈ X^□` comes from `obsLocInv_hist` and
`olocS_full`). This is the field `hK` of `muErr_hist` with `E_K = c (k / w_a) ℓ^{-1}`; the input
`k` is the size of `K^{obs}_j`, bounded by the `K^{obs}` recursion (`Obs2.kobsK_step`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

theorem histKO_hK : ∃ cs : ℕ, ∀ (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (P : ObsPts 2 L N) (o₀ : ObsSt .one L N) (t : Hist.Seq (Xs R)) (j : ℕ),
    ObsLocInv P 0 o₀ → (∀ i ≤ j, ValidCore R i ∧ RawInv R i (rawHist R i t)) →
    ∀ ℓ k wa : ℝ, 0 < ℓ → 0 < wa → 0 ≤ k →
    (∀ X, IsSmall j X → ENNReal.ofReal wa *
      Tj 2 (L : ℝ) j ℓ (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a ≤ ENNReal.ofReal k) →
    ‖∑ X ∈ smallSets (L := L) (N := N) j,
      mass1 (-1) (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a‖ ≤ cs * (k / wa) * ℓ⁻¹ := by
  obtain ⟨cs, hcs⟩ := sum_mass1_le 2
  refine ⟨cs, fun R _ _ P o₀ t j h0 h ℓ k wa hℓ hwa hk hK => ?_⟩
  have ho := obsLocInv_hist R P o₀ h0 t j fun i hi => h i hi.le
  have HL := olocS_full R P (t j).1 (t j).2.1 (st := rawHist R j t)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2)
    (h j le_rfl).1 (h j le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _) ho
  refine hcs L N j .one P.a (histKO R P o₀ t j) ℓ k wa hℓ hwa hk (fun X hX ha => ?_) hK
  exact ((HL.hK X ⟨hX.1, hX.2.1⟩).2.2.2.2.1 ha).1

end

end PtCorr2

end

/-!
# `MuErr.hK` from the `K^{obs}` bound along the flow

**`kobs_EK`**: along a regular history, if the observable activity at scale `j` satisfies
`A^{(|𝓑_j(X)|-4)_+}‖K^{obs}_j(X)‖_{T_j(s_j)} ≤ k` on connected polymers (`kobs_hist`, with
`k = kseq …`), then for weights with `w_a = wa` the field `hK` of `MuErr` holds with

  `E_K = c (8k / wa) s_j^{-1}`.

The factor `8` is `e^{4δ}` of `K♭ = ∏ e^{Δ(B)}K` (`oTo_fullK_le`); `s_j` is the causal field
scale. Via `histKO_hK`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- `w_a ‖F_a‖ ≤ ‖F^{obs}‖`. -/
theorem wa_Tj_a_le_oTo {c : Obs.Case} (w : Wt) {wa : ℝ} (hwa : w.a = ENNReal.ofReal wa) (j : ℕ)
    (ℓ : ℝ) (F : OE c (Lam 2 L N)) :
    ENNReal.ofReal wa * Tj 2 (L : ℝ) j ℓ (F : SA c (Lam 2 L N)).a ≤ oTo w j ℓ F := by
  simp only [oTo, oTj, oNorm, coe_πobs, piobs_apply]
  rw [hwa]
  exact le_add_right (le_add_right le_add_self)

set_option maxHeartbeats 2000000 in
/-- **`MuErr.hK` along the flow.** -/
theorem kobs_EK : ∃ cs : ℕ, ∀ (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ},
    StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS →
    (∀ j < Nh, ValidAt R j) → (∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) →
    0 ≤ β → δ ≤ 1 → ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS →
    ∀ (P : ObsPts 2 L N) (o₀ : ObsSt .one L N), ObsLocInv P 0 o₀ →
    ∀ (t : Flow2.Hist.Seq (Xs R)) (j : ℕ), j < Nh →
      Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t →
    ∀ (w : Wt), w.ab = 0 → ∀ wa : ℝ, 0 < wa → w.a = ENNReal.ofReal wa → ∀ k : ℝ, 0 ≤ k →
      (∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
        oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k) →
      ‖∑ X ∈ smallSets (L := L) (N := N) j,
        mass1 (-1) (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a‖ ≤
          cs * (8 * k / wa) * (histS R j t)⁻¹ := by
  obtain ⟨cs, hcs⟩ := histKO_hK (L := L) (N := N)
  refine ⟨cs, fun R _ _ C₀' η' εs CK C₂ CD Cq Cl cS Nh Λ β δ κ cg cm cT ε hSB hV hm hβ hδ1 H P o₀
    hl0 t j hj ht w hw0 wa hwa0 hwa k hk0 hKo => ?_⟩
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  have hZ : (rawHist R j t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, -⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, -, -⟩ := ht.1 j le_rfl
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hη : 2 * (cZ R * (t j).1) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * (t j).1) ≤ 1 / 2 := by
    have := H.h2
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hΔ := (rg_inputs R j hVj.toValidCore _ HI (t j).1 (t j).2.1 (hm j hj) hg.le _ hz hy hη).2
  have hs : 0 < histS R j t := mul_pos (fscale_pos hZ) hℓ
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hA : 0 < R.A := Fact.out
  refine hcs R P o₀ t j hl0 (fun i hi => hval i (by omega)) (histS R j t) (8 * k) wa hs hwa0
    (by positivity) (fun X hX => ?_)
  have hXc : IsConn j X := ⟨hX.1, hX.2.1⟩
  have hnb : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
  have h1 := oTo_fullK_le R j (rawHist R j t) (rawK R (rawHist R j t).u (t j).2.2)
    (obsHist R P o₀ j t) w hw0 hs hA (by positivity) hηs hΔ X
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h1
  have h2 := hKo X hXc
  simp only [hnb, pow_zero, ENNReal.ofReal_one, one_mul] at h2
  calc ENNReal.ofReal wa * Tj 2 (L : ℝ) j (histS R j t)
        (histKO R P o₀ t j X : SA .one (Lam 2 L N)).a
      ≤ oTo w j (histS R j t) (histKO R P o₀ t j X) := wa_Tj_a_le_oTo w hwa j _ _
    _ ≤ ENNReal.ofReal 8 * oTo w j (histS R j t) ((obsHist R P o₀ j t).K X) := h1
    _ ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := mul_le_mul_left' h2 _
    _ = ENNReal.ofReal (8 * k) := (ENNReal.ofReal_mul (by norm_num)).symm

end

end PtCorr2
