import PtCorr2.Obs.WObsStepU
import PtCorr2.Obs.ObsHistTop

/-!
# Top coalescence: the unreduced `ab` steps `N_h → N_h + 1` (`ValidAtL`)

`kobs_hist_stepU` and `wobs_hist_fullWU` at the step `j = N_h` (the last step before the last
covariance): the observable step bounds `KObsBoundsU`, `WObsBoundsU` need only `ValidCore`, the
a priori bounds hold for `j ≤ N_h`, and the history is valid up to `N_h` (`hist_validL`).

* **`kobs_hist_stepUL`**, **`wobs_hist_fullWUL`** (copies, `hj : j = N_h`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

set_option maxHeartbeats 4000000 in
/-- **The step `N_h → N_h + 1` of the unreduced `ab` recursion** (`kobs_hist_stepU` at `j = N_h`
under `ValidAtL`). -/
theorem kobs_hist_stepUL {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j = Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hKs : ∀ X, IsSmall j X → ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ k₂ : ℝ) (hm0 : 0 < m) (hk₁ : 0 ≤ k₁) (hk₂ : 0 ≤ k₂)
    (hrm : cR R Λ cm C₂ * (t j).1 ≤ m)
    (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt : 8 * cx κ cT * (cR R Λ cm C₂ * (t j).1) ^ 3 +
      cR R Λ cm C₂ * (t j).1 / m * (8 * k₁) + (cR R Λ cm C₂ * (t j).1 / m) ^ 2 * (8 * k₂) ≤ ε₀)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (hK1 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal k₁)
    (hK2 : ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) j (histS R j t) ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k₂) :
    let r := cR R Λ cm C₂ * (t j).1
    let kt := 8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)
    ∀ U : Finset (Lam 2 L N), IsConn (j + 1) U →
      ENNReal.ofReal ((r / m) ^ 2) * (ENNReal.ofReal (R.A ^ (nb (j + 1) U - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          ((obsHist R P o₀ (j + 1) t).K U : SA c (Lam 2 L N)).ab)) ≤
      ENNReal.ofReal (kθ0 L R.A C₀ η * kt + C₁ * ((2 * r) ^ 3 + 2 * r * kt + kt ^ 2)) := by
  intro r0 kt0 U hU
  have hℓ : 0 < R.ℓ := Fact.out
  subst hj
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have HI := rawInv_hist R hVL.2.2.2.2.1 j hV t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 j le_rfl
  set g := (t j).1 with hgdef
  set μ := (t j).2.1
  set x := (t j).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
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
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  set ktr := 8 * ‖x.2‖ + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) with hktr
  have hkt' : ktr ≤ kt0 := by
    show 8 * ‖x.2‖ + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂) ≤
      8 * cx κ cT * r ^ 3 + r / m * (8 * k₁) + (r / m) ^ 2 * (8 * k₂)
    linarith
  have hktr0 : 0 ≤ ktr := by positivity
  -- the observable invariants
  have hval := hist_validL R hV hVL t
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hsym := obsSymInv_hist R P o₀ hs0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  have key := hKB N R j hVL.2 st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) hmNh
    hg.le (cZ R * g) hz hy hη hηs c P w hw hwa hwb hwab (obsHist R P o₀ j t) hobs hloc hsym hKs
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k₁ k₂ (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hrm hk₁ hk₂ hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr (by linarith) (hkt'.trans hkt) hVo hWo hK1 hK2 U hU
  rw [obsHist_succ]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ : 0 ≤ C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (R.A / 2) ^ (-η)) := by
    have := Real.rpow_nonneg hA0 (-η); positivity
  have h1 : C₀ * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (R.A / 2) ^ (-η)) * ktr ≤ kθ0 L R.A C₀ η * kt0 :=
    mul_le_mul_of_nonneg_left hkt' hθ
  have h2 : (2 * r) ^ 3 + 2 * r * ktr + ktr ^ 2 ≤ (2 * r) ^ 3 + 2 * r * kt0 + kt0 ^ 2 := by
    have : 2 * r * ktr ≤ 2 * r * kt0 := mul_le_mul_of_nonneg_left hkt' (by linarith)
    have : ktr ^ 2 ≤ kt0 ^ 2 := pow_le_pow_left₀ hktr0 hkt' 2
    linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hC₁
  linarith

set_option maxHeartbeats 2000000 in
/-- **The `𝒲^{obs}` step `N_h → N_h + 1`, unreduced states, full norm** (`wobs_hist_fullWU` at
`j = N_h` under `ValidAtL`). -/
theorem wobs_hist_fullWUL {Cw : ℝ} (hWB : WObsBoundsU L Cw)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j = Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (m : ℝ) (hrm : cR R Λ cm C₂ * (t j).1 ≤ m) (hr1 : cR R Λ cm C₂ * (t j).1 ≤ 1)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j, oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m))
    (c' : Fin 2 → ℕ) :
    oTo w (j + 1) (histS R (j + 1) t) ((obsHist R P o₀ (j + 1) t).W c') ≤
      ENNReal.ofReal (Real.exp ((L : ℝ) ^ 2 * (Cw * (cR R Λ cm C₂ * (t j).1 + m ^ 2))) - 1) := by
  have hℓ : 0 < R.ℓ := Fact.out
  subst hj
  have hρ1 : R.ρ < 1 := by linarith [hVL.2.2.2.2.2.1]
  have HI := rawInv_hist R hVL.2.2.2.2.1 j hV t
  set st := rawHist R j t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H j le_rfl t ht
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
  have hval := hist_validL R hV hVL t
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  have key := hWB N R j hVL.2 st HI g μ (rawD R st.u x) (rawK R st.u x)
    (rawD_mem R _ _) (rawK_mem R _ _) hmNh
    hg.le (cZ R * g) hz hy hη c P w hw (obsHist R P o₀ j t) hobs hloc
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ r m (by positivity) (norm_nonneg _) hr0 hr1 hrm hWl
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) hvr hwr hVo hWo c'
  rw [obsHist_succ]
  exact key


set_option maxHeartbeats 4000000 in
/-- **The `ab` part of the unreduced activity at `N_h + 1`**: `kab_hist` up to `N_h` and the step
`N_h → N_h + 1` (`kobs_hist_stepUL`): `A^{(|𝓑(X)|-4)_+}w_{ab}‖K_{N_h+1}(X)_{ab}‖ ≤ 2B₂r_{N_h}m_{N_h}²`
(`c₂/5 = 2B₂`, `r_{N_h} = c_Rǧ_{N_h}`). -/
theorem kab_hist_top {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBoundsU L R.A C₀ η ε₀ C₁) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hmNh : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw : w.Sub) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (hwab : w.ab ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (hK0 : ∀ X, (o₀.K X : SA c (Lam 2 L N)).ab = 0)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (hKs : ∀ j ≤ Nh, ∀ X, IsSmall j X → ((obsHist R P o₀ j t).K X : SA c (Lam 2 L N)).ab = 0)
    (m k₁ : ℕ → ℝ) (c₁ : ℝ) (hc₁ : 0 ≤ c₁) (hm0 : ∀ j, 0 < m j)
    (hmm : ∀ j < Nh, m j ≤ 2 * m (j + 1)) (hk₁0 : ∀ j, 0 ≤ k₁ j)
    (hk₁ : ∀ j ≤ Nh, k₁ j ≤ c₁ * (cR R Λ cm C₂ * (t j).1) ^ 2 * m j)
    (hrm : ∀ j ≤ Nh, cR R Λ cm C₂ * (t j).1 ≤ m j)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : 2 * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hkt1 : 8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ 1)
    (hktε : 8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
      (cR R Λ cm C₂ * ε) ^ 3 ≤ ε₀)
    (hθ' : 8 * kθ0 L R.A C₀ η + 16 * C₁ * (cR R Λ cm C₂ * ε) +
      8 * C₁ * (8 * (cx κ cT + c₁ + 10 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁) *
        (cR R Λ cm C₂ * ε) ^ 3) ≤ 1 / 10)
    (hVo : ∀ j ≤ Nh, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal (m j))
    (hWo : ∀ j ≤ Nh, ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤
        ENNReal.ofReal (cR R Λ cm C₂ * (t j).1 * m j))
    (hK1 : ∀ j ≤ Nh, ∀ X, IsConn j X → ENNReal.ofReal (R.A ^ (nb j X - 2 ^ 2)) *
      oTo (wOne w) j (histS R j t) ((obsHist R P o₀ j t).K X) ≤ ENNReal.ofReal (k₁ j)) :
    ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
        ((obsHist R P o₀ (Nh + 1) t).K X : SA c (Lam 2 L N)).ab) ≤
        ENNReal.ofReal (2 * kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ *
          (cR R Λ cm C₂ * (t Nh).1) * m Nh ^ 2) := by
  set B₂ := kB2 (kθ0 L R.A C₀ η) C₁ (cx κ cT) c₁ with hB₂
  set c₂ := 10 * B₂ with hc₂
  have hcx := H.hcx
  have hA0 : (0 : ℝ) ≤ R.A / 2 := by have : 0 < R.A := Fact.out; positivity
  have hθ0 : 0 ≤ kθ0 L R.A C₀ η := by
    unfold kθ0; have := Real.rpow_nonneg hA0 (-η); positivity
  have hB0 : 0 ≤ B₂ := by rw [hB₂]; unfold kB2; positivity
  have hcR : 0 ≤ cR R Λ cm C₂ := by
    unfold cR cV cW cZ; have := H.hcmu; have := H.hC₂; positivity
  have hab := kab_hist R hKB hC₀ hC₁ hSB hV hm hβ hδ1 H P w hw hwa hwb hwab o₀ h0 hl0 hs0 t hK0 Nh
    le_rfl ht (fun j hj X hX => hKs j hj.le X hX) m k₁ c₁ hc₁ hm0 hmm hk₁0
    (fun j hj => hk₁ j hj.le) (fun j hj => hrm j hj.le) hε1 hεε hkt1 hktε hθ'
    (fun j hj => hVo j hj.le) (fun j hj => hWo j hj.le) (fun j hj => hK1 j hj.le)
  intro X hX
  set r := cR R Λ cm C₂ * (t Nh).1 with hr
  have hg := (ht.1 Nh le_rfl)
  have hcv : 0 ≤ cV R Λ cm := by unfold cV cZ; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hr0 : 0 < r := by rw [hr]; have := hg.1; nlinarith
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hg.2.1 hcR
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hmj := hm0 Nh
  have hk₂0 : 0 ≤ c₂ * r * m Nh ^ 2 := by positivity
  have hρk : r / m Nh * k₁ Nh ≤ c₁ * r ^ 3 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hmj]
    calc r * k₁ Nh ≤ r * (c₁ * r ^ 2 * m Nh) := mul_le_mul_of_nonneg_left (hk₁ Nh le_rfl) hr0.le
      _ = c₁ * r ^ 3 * m Nh := by ring
  have hρ2 : (r / m Nh) ^ 2 * (c₂ * r * m Nh ^ 2) = c₂ * r ^ 3 := by field_simp
  have hr3 : r ^ 3 ≤ (cR R Λ cm C₂ * ε) ^ 3 := pow_le_pow_left₀ hr0.le hrε 3
  set kt := 8 * cx κ cT * r ^ 3 + r / m Nh * (8 * k₁ Nh) +
    (r / m Nh) ^ 2 * (8 * (c₂ * r * m Nh ^ 2)) with hkt
  have hktb : kt ≤ 8 * (cx κ cT + c₁ + c₂) * (cR R Λ cm C₂ * ε) ^ 3 := by
    have e : kt = 8 * cx κ cT * r ^ 3 + 8 * (r / m Nh * k₁ Nh) +
        8 * ((r / m Nh) ^ 2 * (c₂ * r * m Nh ^ 2)) := by
      rw [hkt]; ring
    rw [e, hρ2]
    have : 8 * (cx κ cT + c₁ + c₂) * r ^ 3 ≤ 8 * (cx κ cT + c₁ + c₂) * (cR R Λ cm C₂ * ε) ^ 3 :=
      mul_le_mul_of_nonneg_left hr3 (by positivity)
    nlinarith
  have hstep := kobs_hist_stepUL R hKB hC₀ hC₁ hSB hV hVL hm hmNh hβ hδ1 H P w hw hwa hwb hwab o₀
    h0 hl0 hs0 t Nh rfl ht (hKs Nh le_rfl) (m Nh) (k₁ Nh) (c₂ * r * m Nh ^ 2) hmj (hk₁0 Nh) hk₂0
    (hrm Nh le_rfl) hεε (hktb.trans hktε) (hVo Nh le_rfl) (hWo Nh le_rfl) (hK1 Nh le_rfl)
    (hab Nh le_rfl) X hX
  have hreal := kab_real (θ₀ := kθ0 L R.A C₀ η) (C₁ := C₁) (cx := cx κ cT) (c₁ := c₁) hr0 hr1 hmj
    (hk₁0 Nh) hk₂0 hθ0 hC₁ hcx hc₁ (hk₁ Nh le_rfl) (hktb.trans hkt1)
  have hρ0 : 0 < (r / m Nh) ^ 2 := by positivity
  set Z := (8 * kθ0 L R.A C₀ η + 16 * C₁ * r + 8 * C₁ * kt) * (c₂ * r * m Nh ^ 2) +
    B₂ * r * m Nh ^ 2 with hZ
  have hY : ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      (w.ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
        ((obsHist R P o₀ (Nh + 1) t).K X : SA c (Lam 2 L N)).ab) ≤ ENNReal.ofReal Z := by
    have h1 : ENNReal.ofReal ((r / m Nh) ^ 2) * (ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        (w.ab * Tj 2 (L : ℝ) (Nh + 1) (histS R (Nh + 1) t)
          ((obsHist R P o₀ (Nh + 1) t).K X : SA c (Lam 2 L N)).ab)) ≤
        ENNReal.ofReal ((r / m Nh) ^ 2) * ENNReal.ofReal Z := by
      refine hstep.trans ?_
      rw [← ENNReal.ofReal_mul hρ0.le]
      exact ENNReal.ofReal_le_ofReal hreal
    exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.2 hρ0))
      ENNReal.ofReal_ne_top).1 h1
  refine hY.trans (ENNReal.ofReal_le_ofReal ?_)
  have hθt : 8 * kθ0 L R.A C₀ η + 16 * C₁ * r + 8 * C₁ * kt ≤ 1 / 10 := by
    have a1 : 16 * C₁ * r ≤ 16 * C₁ * (cR R Λ cm C₂ * ε) :=
      mul_le_mul_of_nonneg_left hrε (by positivity)
    have a2 : 8 * C₁ * kt ≤ 8 * C₁ * (8 * (cx κ cT + c₁ + c₂) * (cR R Λ cm C₂ * ε) ^ 3) :=
      mul_le_mul_of_nonneg_left hktb (by positivity)
    linarith
  have := mul_le_mul_of_nonneg_right hθt hk₂0
  rw [hZ]
  have e : B₂ * r * m Nh ^ 2 = c₂ / 10 * (r * m Nh ^ 2) := by rw [hc₂]; ring
  rw [e]
  have e2 : 2 * B₂ * r * m Nh ^ 2 = c₂ / 5 * (r * m Nh ^ 2) := by rw [hc₂]; ring
  rw [e2]
  nlinarith

end Hist

end

end PtCorr2
