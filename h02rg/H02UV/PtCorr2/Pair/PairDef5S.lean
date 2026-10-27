import PtCorr2.Pair.SXOStepAB
import PtCorr2.Obs.ObsHistLast

/-!
# The `S`-bound at the top bulk step `N_h`

`sxo_hist_stepAB`/`sxo_hist_ab_le` need `j < N_h` (`hist_raw`). At `j = N_h` the raw facts are
those of `hist_rawL` (`ValidAtL R N_h`), with the same fields, so the step bound holds there too:

* **`sxo_hist_stepABL`**, **`sxo_hist_ab_leL`**: the copies at `j = N_h`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The `S_{N_h}(B_+)` block bound along the history from `j₀`** (copy of `sxo_hist_stepAB`
at `j = N_h`). -/
theorem sxo_hist_stepABL (hSX : SXOBoundsAB L)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS) (hVL : ValidAtL R Nh)
    (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (hjj : j₀ ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHistFrom R P j₀ o₀ Nh t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHistFrom R P j₀ o₀ Nh t).W b) ≤ ENNReal.ofReal mW) :
    ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w (Nh + 1) (histS R (Nh + 1) t)
          (SXO Nh (histCovO R t Nh) (hVR R P j₀ o₀ t Nh) (hWR R P j₀ o₀ t Nh)
            (Step2.Bp (L := L) (N := N) Nh b)) ≤
        ENNReal.ofReal ((L : ℝ) ^ 2 * sO 2 L (cR R Λ cm C₂ * (t Nh).1) mV mW) ∧
      SXO Nh (histCovO R t Nh) (hVR R P j₀ o₀ t Nh) (hWR R P j₀ o₀ t Nh)
          (Step2.Bp (L := L) (N := N) Nh b) ∈
        (anc P (Step2.Bp (L := L) (N := N) Nh b) : Subalgebra ℂ (OE .two (Lam 2 L N))) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, -, -, hvr, -, hr0, -, -, -, -⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  have hval := hist_valid R hV t (n := Nh) le_rfl
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t Nh
  exact hSX N R Nh hVc (rawHist R Nh t) HI (t Nh).1 (t Nh).2.1 (rawD R (rawHist R Nh t).u (t Nh).2.2)
    (rawK R (rawHist R Nh t).u (t Nh).2.2) (rawD_mem R _ _) (rawK_mem R _ _)
    hmN hg _ hz hy hη hηs .two P w hws (obsHistFrom R P j₀ o₀ Nh t) hobs hloc hsym hanc
    _ mV mW hr0.le hmV hmW hvr hVo hWo

/-- **`κ^S_{N_h}(B)` from the `wM` sizes** (copy of `sxo_hist_ab_le` at `j = N_h`). -/
theorem sxo_hist_ab_leL (hSX : SXOBoundsAB L)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS) (hVL : ValidAtL R Nh)
    (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (P : ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (hjj : j₀ ≤ Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo (wM Ma Mb) Nh (histS R Nh t) ((obsHistFrom R P j₀ o₀ Nh t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo (wM Ma Mb) Nh (histS R Nh t) ((obsHistFrom R P j₀ o₀ Nh t).W b) ≤ ENNReal.ofReal mW) :
    ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          (SXO Nh (histCovO R t Nh) (hVR R P j₀ o₀ t Nh) (hWR R P j₀ o₀ t Nh)
            (Step2.Bp (L := L) (N := N) Nh b) : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 * sO 2 L (cR R Λ cm C₂ * (t Nh).1) mV mW)) ∧
      (¬ (Step2.Bp (L := L) (N := N) Nh b ∩ P.pts).Nonempty →
        (SXO Nh (histCovO R t Nh) (hVR R P j₀ o₀ t Nh) (hWR R P j₀ o₀ t Nh)
          (Step2.Bp (L := L) (N := N) Nh b) : SA .two (Lam 2 L N)).ab = 0) := by
  intro b hb
  obtain ⟨h1, h2⟩ := sxo_hist_stepABL R hSX hSB hV hm hβ hδ1 H hVL hmN P (wM Ma Mb) (wM_sub _ _)
    o₀ h0 hl0 hs0 ha0 t hjj ht mV mW hmV hmW hVo hWo b hb
  exact ⟨Tj_ab_le_of_oTo_wM hMa hMb (Nh + 1) _ (anchSub_ab h2) h1, h2.2.2⟩

end Hist

end

end PtCorr2
