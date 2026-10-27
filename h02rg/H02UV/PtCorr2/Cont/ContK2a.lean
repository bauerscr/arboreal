import PtCorr2.Restart.RestartPairTopF1

set_option autoImplicit false

/-!
# B3, T6: the `𝒲^{obs}` step along the restarted history below `N_h` (full norm)

**`k2_wfull_step`**: along `obsHistFrom R P ms o'` (restart at `ms`), the step `j → j + 1` for
`ms ≤ j < N_h` of the `𝒲^{obs}` bound `WObsBoundsU` in the full norm (any `w.Sub`, e.g. `wM`):
from `‖V_j‖_w ≤ m`, `‖𝒲_j‖_w ≤ r_jm` (`r_j = cǧ_j`):
`‖𝒲_{j+1}(B)‖_w ≤ e^{L²C_w(r_j + m²)} − 1`. Copy of `wobs_hist_fullWU` (history from `0`) with the
restarted invariants `rpb_inv_top`; the top step is `rptf_wfull_stepF`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 2000000 in
/-- **The `𝒲^{obs}` step `j → j + 1` (`ms ≤ j < N_h`) along the restarted history, full norm.** -/
theorem k2_wfull_step {Cw : ℝ} (hWB : WObsBoundsU L Cw)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub)
    {ms : ℕ} (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o')
    (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hmj : ms ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (mm : ℝ) (hrm : cR R Λ cm C₂ * (t j).1 ≤ mm) (hr1 : cR R Λ cm C₂ * (t j).1 ≤ 1)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).V b) ≤ ENNReal.ofReal mm)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P ms o' j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * mm))
    (c' : Fin 2 → ℕ) :
    oTo w (j + 1) (histS R (j + 1) t) ((obsHistFrom R P ms o' (j + 1) t).W c') ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (Cw * (cR R Λ cm C₂ * (t j).1 + mm ^ 2))) - 1) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hV j hj
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 j (fun i hi => hV i (by omega)) t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j hj.le t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hv : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ cV R Λ cm * g := by
    unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  set r := cR R Λ cm C₂ * g with hr
  have hvr : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g ≤ r := by
    refine hv.trans ?_; rw [hr]; unfold cR; nlinarith
  have hwr : cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ ≤ r ^ 2 := by
    rw [hr]; unfold cR
    have h1 : cW R Λ cm C₂ + 1 ≤ (cV R Λ cm + cW R Λ cm C₂ + 2) ^ 2 := by nlinarith
    have := H.h3
    nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hg3 H.hcx]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hr0 : 0 < r := by rw [hr]; unfold cR; positivity
  obtain ⟨hobs, hloc, -⟩ := rpb_inv_top R P hV hVL h0 hl0 hs0 t hmj (by omega)
  have key := hWB N R j hVj.toValidCore st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) (hm j hj)
    hg.le (cZ R * g) hz hy hη c P w hw (obsHistFrom R P ms o' j t) hobs hloc
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ r mm (by positivity) (norm_nonneg _) hr0 hr1 hrm hWl
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) hvr hwr hVo hWo c'
  rw [obsHistFrom_succ hmj]
  exact key

end

end PtCorr2
