import PtCorr2.Obs.ObsHistLast
import PtCorr2.Restart.RestartPairAB
import PtCorr2.Restart.RestartPairGamB

/-!
# T5 (item 2): one more step of the restarted flow at `N_h` (`ValidAtL`), general envelope

Along `obsHistFrom R P ms o'` (restart at `ms ≤ N_h`), the step `N_h → N_h + 1` (only
`ValidAtL R N_h` at the top), for an arbitrary weight / envelope:

* `rptf_kobs_state`, **`rptf_kobs_stepF`**: the `K^{obs}` step at `N_h` (`KObsBounds`, `w.ab = 0`)
  with the per-step smallness `8c_br³ + (r/m)8k ≤ ε₀` (no uniform `ε`; for the variant restart);
* `rptf_wfull_state`, **`rptf_wfull_stepF`**: the `𝒲^{obs}` step at `N_h` in the full norm
  (`WObsBoundsU`, any `w.Sub`, e.g. `wM`), copy of `wobs_hist_fullWUL`;
* **`rptf_beta_shA2`**: `‖β^F_{j+1}‖ ≤ |1 − 𝔫F_j|‖β^F_j‖ + E_j` and
  `shA2F (j+1) ≤ |1 − 𝔫F_j|(‖β^F_j‖ + D_j) + 3E_j` (the `LastL1` analogue, `j + 1 < N`, from the
  restarted chain at horizon `j + 1`);
* **`rptf_vobs_block`**: `T_j(V^F_j(B)_a) ≤ s_j²·shA2F j` (datum without constants).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Top

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The `K^{obs}` step at `j = N_h` for an arbitrary state** (per-step smallness). -/
theorem rptf_kobs_state {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (o : ObsSt c L N) (hobs : o.IsObs) (hloc : ObsLocInv P Nh o) (hsym : ObsSymInv Nh o)
    (ck mm k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < mm) (hk0 : 0 ≤ k)
    (hr1 : cR R Λ cm C₂ * (t Nh).1 ≤ 1) (hrε : cR R Λ cm C₂ * (t Nh).1 ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t Nh).1) ^ 2 * mm)
    (hkt : 8 * cx κ cT * (cR R Λ cm C₂ * (t Nh).1) ^ 3 +
      cR R Λ cm C₂ * (t Nh).1 / mm * (8 * k) ≤ ε₀)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh, oTo w Nh (histS R Nh t) (o.V b) ≤ ENNReal.ofReal mm)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh, oTo w Nh (histS R Nh t) (o.W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t Nh).1 * mm))
    (hKo : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      oTo w Nh (histS R Nh t) (o.K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (Nh + 1) U →
      ENNReal.ofReal (R.A ^ (nb (Nh + 1) U - 2 ^ 2)) *
        oTo w (Nh + 1) (histS R (Nh + 1) t) ((obsStep R P Nh (rawHist R Nh t) (t Nh).1 (t Nh).2.1
          (rawD R (rawHist R Nh t).u (t Nh).2.2) (rawK R (rawHist R Nh t).u (t Nh).2.2) o).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t Nh).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t Nh).1) ^ 2 * mm) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, -, hcw, -, -⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  have hρ1 : R.ρ < 1 := by linarith [hVc.2.2.2.2.1]
  have hZ : (rawHist R Nh t).Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨-, -, -, hx⟩ := ht.1 Nh le_rfl
  set g := (t Nh).1 with hgdef
  set x := (t Nh).2.2
  set r := cR R Λ cm C₂ * g with hr
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; unfold cZ; positivity
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hcx := H.hcx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  have hεk' : 8 * ‖x.2‖ + r / mm * (8 * k) ≤ ε₀ := by linarith
  exact hKB N R Nh hVc (rawHist R Nh t) HI g (t Nh).2.1 _ _ (rawD_mem R _ _) (rawK_mem R _ _) hmN
    hg (cZ R * g) hz hy hη hηs c P w hw0 hwa hwb o hobs hloc hsym
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r mm k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl hDd
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 hrε hbr hk8 hεk' hVo hWo hKo

set_option maxHeartbeats 2000000 in
/-- **The `𝒲^{obs}` step at `j = N_h` in the full norm for an arbitrary state.** -/
theorem rptf_wfull_state {Cw : ℝ} (hWB : WObsBoundsU L Cw)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub)
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (o : ObsSt c L N) (hobs : o.IsObs) (hloc : ObsLocInv P Nh o)
    (mm : ℝ) (hrm : cR R Λ cm C₂ * (t Nh).1 ≤ mm) (hr1 : cR R Λ cm C₂ * (t Nh).1 ≤ 1)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh, oTo w Nh (histS R Nh t) (o.V b) ≤ ENNReal.ofReal mm)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh, oTo w Nh (histS R Nh t) (o.W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t Nh).1 * mm))
    (c' : Fin 2 → ℕ) :
    oTo w (Nh + 1) (histS R (Nh + 1) t) ((obsStep R P Nh (rawHist R Nh t) (t Nh).1 (t Nh).2.1
        (rawD R (rawHist R Nh t).u (t Nh).2.2) (rawK R (rawHist R Nh t).u (t Nh).2.2) o).W c') ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (Cw * (cR R Λ cm C₂ * (t Nh).1 + mm ^ 2))) - 1) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, -, hWl, hDd, hvr, hwr, hr0, -, hcw, -, -⟩ :=
    hist_rawL R hSB hV hm hβ hδ1 H hVL t ht
  exact hWB N R Nh hVc (rawHist R Nh t) HI (t Nh).1 (t Nh).2.1 _ _ (rawD_mem R _ _)
    (rawK_mem R _ _) hmN hg (cZ R * (t Nh).1) hz hy hη c P w hw o hobs hloc
    (cW R Λ cm C₂ * (t Nh).1 ^ 2) ‖(t Nh).2.2.1‖ _ mm (by positivity) (norm_nonneg _) hr0 hr1 hrm
    hWl hDd hvr hwr hVo hWo c'

/-- **The `K^{obs}` step `N_h → N_h + 1` along the restarted history.** -/
theorem rptf_kobs_stepF {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    {ms : ℕ} (hms : ms ≤ Nh) (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o')
    (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (ck mm k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < mm) (hk0 : 0 ≤ k)
    (hr1 : cR R Λ cm C₂ * (t Nh).1 ≤ 1) (hrε : cR R Λ cm C₂ * (t Nh).1 ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t Nh).1) ^ 2 * mm)
    (hkt : 8 * cx κ cT * (cR R Λ cm C₂ * (t Nh).1) ^ 3 +
      cR R Λ cm C₂ * (t Nh).1 / mm * (8 * k) ≤ ε₀)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHistFrom R P ms o' Nh t).V b) ≤ ENNReal.ofReal mm)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHistFrom R P ms o' Nh t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t Nh).1 * mm))
    (hKo : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      oTo w Nh (histS R Nh t) ((obsHistFrom R P ms o' Nh t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (Nh + 1) U →
      ENNReal.ofReal (R.A ^ (nb (Nh + 1) U - 2 ^ 2)) *
        oTo w (Nh + 1) (histS R (Nh + 1) t) ((obsHistFrom R P ms o' (Nh + 1) t).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t Nh).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t Nh).1) ^ 2 * mm) := by
  obtain ⟨hobs, hloc, hsym⟩ := rpb_inv_top R P hV hVL h0 hl0 hs0 t hms (Nat.le_succ Nh)
  rw [obsHistFrom_succ hms]
  exact rptf_kobs_state R hKB hSB hV hm hVL hmN hβ hδ1 H P w hw0 hwa hwb t ht _ hobs hloc hsym
    ck mm k hck hm0 hk0 hr1 hrε hk8 hkt hVo hWo hKo

/-- **The `𝒲^{obs}` step `N_h → N_h + 1` along the restarted history, full norm.** -/
theorem rptf_wfull_stepF {Cw : ℝ} (hWB : WObsBoundsU L Cw)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub)
    {ms : ℕ} (hms : ms ≤ Nh) (o' : ObsSt c L N) (h0 : o'.IsObs) (hl0 : ObsLocInv P ms o')
    (hs0 : ObsSymInv ms o')
    (t : Flow2.Hist.Seq (Xs R)) (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (mm : ℝ) (hrm : cR R Λ cm C₂ * (t Nh).1 ≤ mm) (hr1 : cR R Λ cm C₂ * (t Nh).1 ≤ 1)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHistFrom R P ms o' Nh t).V b) ≤ ENNReal.ofReal mm)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHistFrom R P ms o' Nh t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t Nh).1 * mm))
    (c' : Fin 2 → ℕ) :
    oTo w (Nh + 1) (histS R (Nh + 1) t) ((obsHistFrom R P ms o' (Nh + 1) t).W c') ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (Cw * (cR R Λ cm C₂ * (t Nh).1 + mm ^ 2))) - 1) := by
  obtain ⟨hobs, hloc, -⟩ := rpb_inv_top R P hV hVL h0 hl0 hs0 t hms (Nat.le_succ Nh)
  rw [obsHistFrom_succ hms]
  exact rptf_wfull_state R hWB hSB hV hm hVL hmN hβ hδ1 H P w hw t ht _ hobs hloc mm hrm hr1
    hVo hWo c'

end Top

/-! ### The coupling and the share sum one step further (`LastL1` analogue) -/

section Share

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (ms : ℕ)
  (o' : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))

/-- **The restarted coupling and share sum one step further** (general envelope; the inputs are
the restart sizes at `j`: `‖β^F_j‖`, `D_j = shareDev2`, `E_j = shareErrL1_2F`). -/
theorem rptf_beta_shA2 (h0f : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a) {j : ℕ}
    (hmj : ms ≤ j) (hjN : j + 1 < N) :
    ‖betaTot2 (L := L) (N := N) (j + 1) (histVF2 R P ms o' t (j + 1))‖ ≤
      ‖1 - frakN2F P (histCovO R t) (histVF2 R P ms o' t) ms j‖ *
          ‖betaTot2 (L := L) (N := N) j (histVF2 R P ms o' t j)‖ +
        shareErrL1_2F P (histCovO R t) (histVF2 R P ms o' t) (histWF2 R P ms o' t)
          (histKF2 R P ms o' t) ms j ∧
    shA2 (histVF2 R P ms o' t) (j + 1) ≤
      ‖1 - frakN2F P (histCovO R t) (histVF2 R P ms o' t) ms j‖ *
          (‖betaTot2 (L := L) (N := N) j (histVF2 R P ms o' t j)‖ +
            shareDev2 P.a j (histVF2 R P ms o' t j)) +
        3 * shareErrL1_2F P (histCovO R t) (histVF2 R P ms o' t) (histWF2 R P ms o' t)
          (histKF2 R P ms o' t) ms j := by
  have H := muChain2F_histFrom R P ms o' t (n := j + 1) (by omega) hjN h0f
  have hb := H.norm_betaTot2_succ_le hmj (Nat.lt_succ_self j)
  have hD := H.shareDev2_succ_leF hmj (Nat.lt_succ_self j)
  have hA := sum_norm_share2_le P.a (j + 1) (histVF2 R P ms o' t (j + 1))
  refine ⟨hb, ?_⟩
  show ∑ b ∈ blockIdx (L := L) (N := N) (j + 1), _ ≤ _
  refine hA.trans ?_
  nlinarith [hb, hD]

/-- **`T_j(V^F_j(B)_a) ≤ s_j²·shA2F j`** along the restarted history (datum without constants). -/
theorem rptf_vobs_block (h0f : ∀ b, Loc2Form P.a (o'.V b : SA .two (Lam 2 L N)).a)
    (hp : ∀ b, (o'.V b : SA .two (Lam 2 L N)).a =
      mass2 (o'.V b : SA .two (Lam 2 L N)).a • pbp P.a)
    {j : ℕ} (hmj : ms ≤ j) (hs : 0 < histS R j t) (b : Fin 2 → ℕ)
    (hb : b ∈ blockIdx (L := L) (N := N) j) :
    Tj 2 (L : ℝ) j (histS R j t) ((obsHistFrom R P ms o' j t).V b : SA .two (Lam 2 L N)).a ≤
      ENNReal.ofReal (histS R j t ^ 2 * shA2 (histVF2 R P ms o' t) j) := by
  rw [obsHistF2_pure R P ms o' t h0f hp j hmj b]
  refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : ‖mass2 ((obsHistFrom R P ms o' j t).V b : SA .two (Lam 2 L N)).a‖ ≤
      shA2 (histVF2 R P ms o' t) j := by
    rw [← histVF2_a R P ms o' t j b]
    exact single_le_sum (f := fun b => ‖mass2
      (histVF2 R P ms o' t j b : SA .two (Lam 2 L N)).a‖) (fun _ _ => norm_nonneg _) hb
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

end Share

end

end PtCorr2
