import PtCorr2.Obs.ObsHistLast

/-!
# The `K^{obs}` step at `j = N_h` (`ValidAtL`)

**`kobs_hist_stepL`**: copy of `kobs_hist_step` at the top scale `j = N_h`, where only
`ValidAtL R N_h` holds (`KObsBounds` needs only `ValidCore`): the bound of
`A^{(|𝓑(U)|-4)_+}‖K^{obs}_{N_h+1}(U)‖` by `(θ₀ + C₁(2 + 2c_b + c_k)r)8k + B r²m`.
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
/-- **One step of the `K^{obs}` recursion at `j = N_h`.** -/
theorem kobs_hist_stepL {C₀ η ε₀ C₁ : ℝ} (hKB : KObsBounds L R.A C₀ η ε₀ C₁)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hVL : ValidAtL R Nh) (hmN : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0) (hwa : w.a ≠ ⊤) (hwb : w.b ≠ ⊤)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R))
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε Nh t)
    (ck m k : ℝ) (hck : 0 ≤ ck) (hm0 : 0 < m) (hk0 : 0 ≤ k)
    (hε1 : cR R Λ cm C₂ * ε ≤ 1) (hεε : cR R Λ cm C₂ * ε ≤ ε₀)
    (hεk : (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) ≤ ε₀)
    (hk8 : 8 * k ≤ ck * (cR R Λ cm C₂ * (t Nh).1) ^ 2 * m)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) Nh,
      oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).V b) ≤ ENNReal.ofReal m)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) Nh, oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).W b) ≤
      ENNReal.ofReal (cR R Λ cm C₂ * (t Nh).1 * m))
    (hKo : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      oTo w Nh (histS R Nh t) ((obsHist R P o₀ Nh t).K X) ≤ ENNReal.ofReal k) :
    ∀ U : Finset (Lam 2 L N), IsConn (Nh + 1) U →
      ENNReal.ofReal (R.A ^ (nb (Nh + 1) U - 2 ^ 2)) *
        oTo w (Nh + 1) (histS R (Nh + 1) t) ((obsHist R P o₀ (Nh + 1) t).K U) ≤
      ENNReal.ofReal ((kθ0 L R.A C₀ η + C₁ * (2 + 2 * (8 * cx κ cT) + ck) *
          (cR R Λ cm C₂ * (t Nh).1)) * (8 * k) +
        kB (kθ0 L R.A C₀ η) C₁ (8 * cx κ cT) * (cR R Λ cm C₂ * (t Nh).1) ^ 2 * m) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hVj := hVL.2
  have hρ1 : R.ρ < 1 := by linarith [hVj.2.2.2.2.1]
  have HI := rawInv_hist R hVj.2.2.2.1 Nh hV t
  set st := rawHist R Nh t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero hρ1
  obtain ⟨hz, hy, hWl⟩ := apriori R hSB hV hm hβ hδ1 H Nh le_rfl t ht
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 Nh le_rfl
  set g := (t Nh).1 with hgdef
  set μ := (t Nh).2.1
  set x := (t Nh).2.2
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hg3 : g ^ 3 ≤ ε * g ^ 2 := by
    rw [pow_succ]; nlinarith [sq_nonneg g, mul_le_mul_of_nonneg_left hgε (sq_nonneg g)]
  have hdd : ‖x.1‖ ≤ g ^ 2 := by
    have := H.h3; nlinarith [mul_le_mul_of_nonneg_left hg3 H.hcx, sq_nonneg g]
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
    nlinarith [sq_nonneg g]
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  -- the radius
  have hcR1 : 1 ≤ cR R Λ cm C₂ := by unfold cR; linarith
  have hgr : g ≤ r := by rw [hr]; nlinarith
  have hr0 : 0 < r := by rw [hr]; positivity
  have hrε : r ≤ cR R Λ cm C₂ * ε := mul_le_mul_of_nonneg_left hgε (by linarith)
  have hr1 : r ≤ 1 := hrε.trans hε1
  have hcx := H.hcx
  have hbr : 8 * ‖x.2‖ ≤ 8 * cx κ cT * r ^ 3 := by
    have : g ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hg.le hgr 3
    nlinarith [mul_le_mul_of_nonneg_left this hcx]
  have hr3 : r ^ 3 ≤ r := by
    have : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1
    nlinarith
  have hεk' : 8 * ‖x.2‖ + r / m * (8 * k) ≤ ε₀ := by
    have h1 : r / m * (8 * k) ≤ ck * r ^ 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm0]
      have := mul_le_mul_of_nonneg_left hk8 hr0.le
      calc r * (8 * k) ≤ r * (ck * r ^ 2 * m) := this
        _ = ck * r ^ 3 * m := by ring
    have h2 : (8 * cx κ cT + ck) * r ^ 3 ≤ (8 * cx κ cT + ck) * (cR R Λ cm C₂ * ε) :=
      mul_le_mul_of_nonneg_left (hr3.trans hrε) (by positivity)
    nlinarith
  -- the observable invariants
  have hval := hist_validL R hV hVL t
  have hloc := obsLocInv_hist R P o₀ hl0 t Nh fun i hi => hval i hi.le
  have hsym := obsSymInv_hist R P o₀ hs0 t Nh fun i hi => hval i hi.le
  have hobs := obsHist_isObs R P o₀ h0 Nh t
  exact hKB N R Nh hVj st HI g μ _ _ (rawD_mem R _ _) (rawK_mem R _ _) hmN hg.le
    (cZ R * g) hz hy hη hηs c P w hw0 hwa hwb (obsHist R P o₀ Nh t) hobs hloc hsym
    (cW R Λ cm C₂ * g ^ 2) ‖x.1‖ ‖x.2‖ r m k (8 * cx κ cT) ck (by positivity) (norm_nonneg _)
    (norm_nonneg _) hr0 hm0 hk0 (by positivity) hck hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
    (le_of_eq (Knorm_rawK R HI.hu hZ x)) hvr hwr hr1 (hrε.trans hεε) hbr hk8 hεk' hVo hWo hKo

end Top

end

end PtCorr2
