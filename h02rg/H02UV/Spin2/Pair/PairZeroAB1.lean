import Spin2.Gam.LastKRem1
import Spin2.Pair.PairRed3
import PtCorr2.Last.LastAB3
import PtCorr2.Pair.PairVStep2
import PtCorr2.Pair.KObsStepAB
import Spin2.Pair.PairVStep1

/-!
# The `σ_aσ_b` part of the last step of the reduced history (one trajectory, one `x`)

Pair observable at `x`, reduced history `oR x` (no one-point parts), last step `j = N_h + 1`
(`C = C_N`, inputs `V, 𝒲, K` of scale `N - 1`). From the jet bound `LastJetBd L (A/2) r₀` of the
master construction (applied to the swapped inputs, `PtCorr2.finG_jets_ab`) and the crude bound of
the last-step defect (`PtCorr2.lastDef_ab_le`), for observable sizes at `N_h + 1` in the weights
`wM(M_a, M_b)`:

  `‖V'^{obs}_{N_h+1}(B)‖ ≤ c_V`, `‖𝒲'^{obs}_{N_h+1}(B)‖ ≤ c_Wǧ_{N_h}`,
  `A^{(|𝓑(X)|-4)_+}‖K'^{obs}_{N_h+1}(X)‖ ≤ c_K`,

**`pairLastAB_x`** gives, with `c_S = c_V + c_W + 8c_K + 1` and `s'` the field scale of `C_N`,

  `s'²|c2(F'_N)_{ab}| ≤ (c_J(c_ρ + 4/r₀²) + L²(2Q₁ + 2L²Q₁²))c_S·M_aM_b`,
  `|ε(F'_N)_{ab}| ≤ c_J(c_ρ + 4/r₀²)c_S·M_aM_b`,
  `|lastDefR| ≤ L²(2Q₁ + 5 + 2L²Q₁²)c_S·M_aM_b`,

together with the scale facts `s_{N_h}² ≤ (9/8)s²`, `s² ≤ (9/8)s'²`, `s² ≤ (9/8)ℓ²/|Z_N|`
(`s = s_{N_h+1}`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

/-- The jet constant of the `ab` last step. -/
def cJab (L : ℕ) (r₀ : ℝ) : ℝ :=
  cJet L * (cRho L + 4 / r₀ ^ 2) + (L : ℝ) ^ 2 * (2 * Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2)

/-- The defect constant of the `ab` last step. -/
def cLab (L : ℕ) : ℝ := (L : ℝ) ^ 2 * (2 * Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2)

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

set_option maxHeartbeats 8000000 in
/-- **The `σ_aσ_b` part of the last step along one trajectory** (reduced history at `x`). -/
theorem pairLastAB_x {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK r₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) (hA2 : 2 ≤ R.A)
    (hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (R.A / 2) r₀)
    (hcW : 0 ≤ cW) (hcK : 0 ≤ cK) (hCf : 0 ≤ Cf)
    (hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hs1 : 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ R.ρ)
    (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2)
    (hs3 : cRho L * (cTauL R.ℓ Cf cW cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL R.ℓ Cf cW cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL R.ℓ Cf cW cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) (x : Lam 2 L N)
    (hjN : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (h0 : (oR x).IsObs) (hl0 : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    (hab0 : PtCorr2.ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oR x))
    {Ma Mb cVo cWo cKo : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (hcVo : 0 ≤ cVo) (hcWo : 0 ≤ cWo)
    (hcKo : 0 ≤ cKo)
    (hVo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM Ma Mb) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V b') ≤ ENNReal.ofReal cVo)
    (hWo : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM Ma Mb) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W b') ≤
        ENNReal.ofReal (cWo * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1))
    (hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM Ma Mb) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) (oR x) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X) ≤ ENNReal.ofReal cKo) :
    ∃ s' : ℝ, 0 < s' ∧
      histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤
        (9 / 8) ^ 2 * s' ^ 2 ∧
      histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 ≤
        (9 / 8) ^ 2 * R.ℓ ^ 2 /
          ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ ∧
      s' ^ 2 * ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        cJab L r₀ * (cVo + cWo + 8 * cKo + 1) * (Ma * Mb) ∧
      ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
        cJet L * (cRho L + 4 / r₀ ^ 2) * (cVo + cWo + 8 * cKo + 1) * (Ma * Mb) ∧
      ‖lastDefR R Nh m b μ₀ oR x‖ ≤ cLab L * (cVo + cWo + 8 * cKo + 1) * (Ma * Mb) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : 0 < R.A := Fact.out
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set P := ptsX (L := L) (N := N) x with hPd
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set o := PtCorr2.obsHistFrom R' P j (oR x) (Nh + 1) t with hod
  set st := (histOut R' Nh t).st with hst
  set gg := (t Nh).1 with hgg
  have ho : o.IsObs := PtCorr2.obsHistFrom_isObs (R := R') (P := P) (j := j) h0 t (Nh + 1)
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have H : RawInv R' (Nh + 1) st := rawInv_histU R' hV hVL t (Nh + 1) le_rfl
  obtain ⟨hC0, hCt, hCs, hCsym⟩ := LastN.covN hVN H
  have hjN' : Nh + 1 < N := by omega
  have hD : (histOut R' Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.1
  have hKm : (histOut R' Nh t).K ∈ ASub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.2
  obtain ⟨⟨hz, hy, hnu, hgn, hgre, hWl, hDd, hKk⟩, -⟩ := hG
  have hg0' : 0 ≤ gg := hg0.le
  have hCg : 0 ≤ Cf * gg := mul_nonneg hCf hg0'
  -- the bulk inputs
  obtain ⟨hVv, hWw, hKf, hVin, hV0, hWin, hKin, hΔ⟩ := bulk_last_in R' hVN hL8 H
    (histOut R' Nh t).g.re (histOut R' Nh t).nu.re hD hKm hmN hgre (Cf * gg) hz hy hs1 hs2 hA
    (by positivity) (by positivity) hWl hDd hKk
  -- scales
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hζ8 : ‖stZeta R' st‖ ≤ 1 / 8 := (absorb_le R' hρ0 _ _).trans hρ8
  have hZ' : stZ' R' st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  set s := fscale st.Z * R.ℓ with hsd
  set s' := fscale (stZ' R' st) * R.ℓ with hs'd
  have hs : 0 < s := mul_pos (fscale_pos hZ) hℓ
  have hs' : 0 < s' := mul_pos (fscale_pos hZ') hℓ
  have hsum : s' + s' / 4 ≤ 2 * s := by
    have hsc := scale_ok hZ hζ8 hℓ
    have e : stZ' R' st = st.Z * (1 + stZeta R' st) := rfl
    rw [hs'd, e]; rw [hsd]; linarith
  have hC : GoodCov2 (Nh + 1) (s' / 4) (LastN.stCovN R' (Nh + 1) st) := hC0
  have hss : s ^ 2 ≤ 9 / 8 * s' ^ 2 := by
    rw [hsd, hs'd, mul_pow, mul_pow, Step2.fscale_sq, Step2.fscale_sq]
    have e : stZ' R' st = st.Z * (1 + stZeta R' st) := rfl
    rw [e, norm_mul]
    have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
    have h1 : ‖1 + stZeta R' st‖ ≤ 9 / 8 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have h2 : 7 / 8 ≤ ‖1 + stZeta R' st‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-stZeta R' st)
      rw [sub_neg_eq_add, norm_one, norm_neg] at this; linarith
    rw [mul_inv]
    have hR2 : 0 < R.ℓ ^ 2 := by positivity
    have : (‖st.Z‖)⁻¹ ≤ 9 / 8 * ((‖st.Z‖)⁻¹ * (‖1 + stZeta R' st‖)⁻¹) := by
      rw [← mul_assoc, mul_comm (9 / 8 : ℝ), mul_assoc]
      refine le_mul_of_one_le_right (by positivity) ?_
      rw [le_mul_inv_iff₀ (by linarith)]; linarith
    nlinarith only [this, hR2]
  have hsZ : s ^ 2 ≤ 9 / 8 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖ := by
    have e : (lastOut R' Nh t).Z = st.Z * (1 + stZeta R' st) := rfl
    rw [hsd, mul_pow, Step2.fscale_sq, e, norm_mul]
    have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
    have h1 : ‖1 + stZeta R' st‖ ≤ 9 / 8 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have h2 : 7 / 8 ≤ ‖1 + stZeta R' st‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-stZeta R' st)
      rw [sub_neg_eq_add, norm_one, norm_neg] at this; linarith
    rw [le_div_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hsNh : histS R' Nh t ^ 2 ≤ 9 / 8 * s ^ 2 := by
    have h := histS_sq_le_z R' t Nh hρ0 hρ8
    have e2 : R'.ℓ = R.ℓ := rfl
    rw [e2] at h
    have e : s ^ 2 = R.ℓ ^ 2 * (zH R' t (Nh + 1))⁻¹ := by
      rw [hsd, mul_pow, Step2.fscale_sq, mul_comm]; rfl
    rw [e]; linarith
  have hsS : histS R' (Nh + 1) t = s := rfl
  refine ⟨s', hs', ?_, ?_, ?_⟩
  · show histS R' Nh t ^ 2 ≤ (9 / 8) ^ 2 * s' ^ 2
    linarith only [hsNh, hss]
  · show histS R' Nh t ^ 2 ≤ (9 / 8) ^ 2 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖
    have e : (9 / 8 : ℝ) ^ 2 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖ =
        9 / 8 * (9 / 8 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖) := by ring
    rw [e]; linarith
  -- the observable invariants of the reduced history at `N_h + 1`
  have hloc : PtCorr2.ObsLocInv P (Nh + 1) o :=
    PtCorr2.obsLocInv_histFrom' R' P hl0 t (by omega)
      fun i _ hi => hist_validL R' hV hVL t i (by omega)
  have hOL := olocS_last R' P (histOut R' Nh t).g.re (histOut R' Nh t).nu.re hVN H hD hKm hloc
  have habN : PtCorr2.ObsAbInv (Nh + 1) o := by
    have := PtCorr2.obsAbInv_histFrom R' P hab0 t (Nh + 1 - j)
    rwa [Nat.add_sub_cancel' (by omega)] at this
  have HAb := PtCorr2.oabS_full R' (st := st) (D := (histOut R' Nh t).D) (K := (histOut R' Nh t).K)
    (histOut R' Nh t).g.re (histOut R' Nh t).nu.re habN
  have eV : Obs2.bulkF (lVR R Nh m b μ₀ oR x) =
      stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re :=
    Obs2.bulkF_fullV R' (Nh + 1) st _ _ ho
  have eW : Obs2.bulkF (lWR R Nh m b μ₀ oR x) = st.Wl + (histOut R' Nh t).D :=
    Obs2.bulkF_fullW st _ ho
  have eK : Obs2.bulkF (lKR R Nh m b μ₀ oR x) =
      Kflat (Nh + 1) (stDelta R' (Nh + 1) st) (histOut R' Nh t).K :=
    Obs2.bulkF_fullK R' (Nh + 1) st _ ho
  -- the sizes
  have hcM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hcT : 1 ≤ cTauL R.ℓ Cf cW cK := by
    unfold cTauL
    have : 0 ≤ (4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf := by positivity
    linarith
  set τ := cTauL R.ℓ Cf cW cK * gg with hτd
  have hτ : 0 < τ := mul_pos (by linarith) hg0
  have hτ1 : τ ≤ 1 := hs5.trans hr₀1
  have hgg1 : gg ≤ 1 := (le_mul_of_one_le_left hg0' hcT).trans hτ1
  have hgg2 : gg ^ 2 ≤ gg := by nlinarith only [hgg1, hg0']
  have hgg3 : gg ^ 3 ≤ gg := by nlinarith only [hgg1, hg0', hgg2]
  have hνr : |(histOut R' Nh t).nu.re| ≤ Cf * gg := (Complex.abs_re_le_norm _).trans hnu
  have hgr : (histOut R' Nh t).g.re ≤ Cf * gg := (Complex.re_le_norm _).trans hgn
  have hv : cM * R.ℓ ^ 2 * (2 * |(histOut R' Nh t).nu.re| + 2 * (Cf * gg)) +
      8 * R.ℓ ^ 4 * (histOut R' Nh t).g.re ≤ τ := by
    have h1 : cM * R.ℓ ^ 2 * (2 * |(histOut R' Nh t).nu.re| + 2 * (Cf * gg)) ≤
        cM * R.ℓ ^ 2 * (4 * (Cf * gg)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 8 * R.ℓ ^ 4 * (histOut R' Nh t).g.re ≤ 8 * R.ℓ ^ 4 * (Cf * gg) :=
      mul_le_mul_of_nonneg_left hgr (by positivity)
    have h3 : cM * R.ℓ ^ 2 * (4 * (Cf * gg)) + 8 * R.ℓ ^ 4 * (Cf * gg) ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ (10 * Cf + 9 / 4 * cW + 18 * cK + 1) * gg := by positivity
      linarith only [this]
    linarith
  have hτ8 : 8 * (Cf * gg) ≤ τ := by
    rw [hτd]; unfold cTauL
    have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 9 / 4 * cW + 18 * cK + 1) * gg := by
      positivity
    linarith only [this, hCg]
  have hWτ : Cf * gg ^ 2 + Cf * gg ^ 2 ≤ τ := by
    have := mul_le_mul_of_nonneg_left hgg2 hCf; linarith
  have hKτ : 8 * (Cf * gg ^ 3) ≤ τ := by
    have := mul_le_mul_of_nonneg_left hgg3 hCf; linarith
  have hδ0 : 0 ≤ 8 * cM * R.ℓ ^ 2 * (Cf * gg) := by positivity
  -- the observable sizes of the full inputs (`ab` parts)
  set M0 := Ma * Mb with hM0d
  have hM0 : 0 < M0 := mul_pos hMa hMb
  have hTab : ∀ F : OE .two (Lam 2 L N), ∀ c : ℝ,
      Obs2.oTo (wM Ma Mb) (Nh + 1) s F ≤ ENNReal.ofReal c →
      Tj 2 (L : ℝ) (Nh + 1) s (F : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (M0 * c) :=
    fun F c h => Tj_ab_le_of_oTo_wM' hMa hMb (Nh + 1) s F h
  have hVo' : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Tj 2 (L : ℝ) (Nh + 1) s (lVR R Nh m b μ₀ oR x b' : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (M0 * cVo) := fun b' hb' =>
    hTab _ _ ((PtCorr2.oTo_emb_add_le (wM Ma Mb) (Nh + 1) s _ _).trans (hVo b' hb'))
  have hWo' : ∀ b' ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Tj 2 (L : ℝ) (Nh + 1) s (lWR R Nh m b μ₀ oR x b' : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (M0 * (cWo * gg)) := fun b' hb' =>
    hTab _ _ ((PtCorr2.oTo_emb_add_le (wM Ma Mb) (Nh + 1) s _ _).trans (hWo b' hb'))
  have hKo' : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Tj 2 (L : ℝ) (Nh + 1) s (lKR R Nh m b μ₀ oR x X : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (M0 * (8 * cKo)) := by
    intro X hX
    have h1 := PtCorr2.oTo_fullK_leAB R' (Nh + 1) st (histOut R' Nh t).K o (wM Ma Mb) (wM_sub _ _)
      hs hA hδ0 (by linarith) hΔ X
    have h2 : ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
        Obs2.oTo (wM Ma Mb) (Nh + 1) s (lKR R Nh m b μ₀ oR x X) ≤ ENNReal.ofReal (8 * cKo) := by
      refine h1.trans ?_
      rw [ENNReal.ofReal_mul (by norm_num)]
      exact mul_le_mul_right (hKo X hX) _
    have hw : (wM Ma Mb).ab = ENNReal.ofReal (M0)⁻¹ := by
      show ENNReal.ofReal Ma⁻¹ * ENNReal.ofReal Mb⁻¹ = _
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le), mul_inv]
    have h3 := Obs2.ab_le_oTo (wM Ma Mb) (Nh + 1) s (lKR R Nh m b μ₀ oR x X)
    rw [hw] at h3
    have h4 : Tj 2 (L : ℝ) (Nh + 1) s (lKR R Nh m b μ₀ oR x X : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal M0 * Obs2.oTo (wM Ma Mb) (Nh + 1) s (lKR R Nh m b μ₀ oR x X) := by
      calc Tj 2 (L : ℝ) (Nh + 1) s (lKR R Nh m b μ₀ oR x X : SA .two (Lam 2 L N)).ab
          = ENNReal.ofReal M0 * (ENNReal.ofReal M0⁻¹ *
              Tj 2 (L : ℝ) (Nh + 1) s (lKR R Nh m b μ₀ oR x X : SA .two (Lam 2 L N)).ab) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hM0.le, mul_inv_cancel₀ hM0.ne', ENNReal.ofReal_one,
              one_mul]
        _ ≤ _ := mul_le_mul_right h3 _
    calc ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
          Tj 2 (L : ℝ) (Nh + 1) s (lKR R Nh m b μ₀ oR x X : SA .two (Lam 2 L N)).ab
        ≤ ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
          (ENNReal.ofReal M0 * Obs2.oTo (wM Ma Mb) (Nh + 1) s (lKR R Nh m b μ₀ oR x X)) :=
          mul_le_mul_right h4 _
      _ = ENNReal.ofReal M0 * (ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
          Obs2.oTo (wM Ma Mb) (Nh + 1) s (lKR R Nh m b μ₀ oR x X)) := by ring
      _ ≤ ENNReal.ofReal M0 * ENNReal.ofReal (8 * cKo) := mul_le_mul_right h2 _
      _ = _ := (ENNReal.ofReal_mul hM0.le).symm
  -- the sizes for the jet bound
  set MV := M0 * cVo with hMVd
  set mW := M0 * (cWo * gg) with hmWd
  set Mbig := M0 * (cVo + cWo * gg / τ + 8 * cKo * r₀ / τ + 1) with hMbd
  have hMV0 : 0 ≤ MV := mul_nonneg hM0.le hcVo
  have hmW0 : 0 ≤ mW := mul_nonneg hM0.le (mul_nonneg hcWo hg0')
  have hMb0 : 0 < Mbig := by
    rw [hMbd]
    have : 0 ≤ cWo * gg / τ := div_nonneg (mul_nonneg hcWo hg0') hτ.le
    have : 0 ≤ 8 * cKo * r₀ / τ := div_nonneg (by positivity) hτ.le
    exact mul_pos hM0 (by linarith)
  have hτMb : τ * Mbig = M0 * (τ * cVo + cWo * gg + 8 * cKo * r₀ + τ) := by
    rw [hMbd]; field_simp
  have hMVM : MV ≤ Mbig := by
    rw [hMVd, hMbd]
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    have : 0 ≤ cWo * gg / τ := div_nonneg (mul_nonneg hcWo hg0') hτ.le
    have : 0 ≤ 8 * cKo * r₀ / τ := div_nonneg (by positivity) hτ.le
    linarith
  have hmWτ : mW ≤ τ * Mbig := by
    rw [hτMb, hmWd]
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    have := mul_nonneg hτ.le hcVo
    have : 0 ≤ 8 * cKo * r₀ := by positivity
    linarith
  have hKτ' : M0 * (8 * cKo) ≤ τ * Mbig / r₀ := by
    rw [hτMb, le_div_iff₀ hr₀]
    have : M0 * (8 * cKo) * r₀ = M0 * (8 * cKo * r₀) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    have := mul_nonneg hτ.le hcVo
    have := mul_nonneg hcWo hg0'
    linarith
  have hτMb1 : τ * Mbig ≤ M0 * (cVo + cWo + 8 * cKo + 1) := by
    rw [hτMb]
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    have k1 : τ * cVo ≤ cVo := mul_le_of_le_one_left hcVo hτ1
    have k2 : cWo * gg ≤ cWo := mul_le_of_le_one_right hcWo hg1
    have k3 : 8 * cKo * r₀ ≤ 8 * cKo := mul_le_of_le_one_right (by positivity) hr₀1
    linarith
  -- the jets
  have hJab := finG_jets_ab hJ (by linarith) hr₀ hr₀1 N (Nh + 1) (by omega) hLp s s' (s' / 4) hs hs'
    (by positivity) hsum (LastN.stCovN R' (Nh + 1) st) hC P (lVR R Nh m b μ₀ oR x)
    (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x)
    (by rw [eV]; exact hVin) (by rw [eW]; exact hWin) (by rw [eV]; exact hV0)
    (by rw [eK]; exact hKin)
    (fun b' => Obs2.cmpInA_of_osub (hOL.hV b')) (fun b' => Obs2.cmpInA_of_osub (hOL.hW b'))
    (fun X hX => Obs2.cmpInA_of_osub (hOL.hK X hX)) HAb.hV HAb.hW HAb.hK
    τ Mbig MV mW hτ hs5 hMb0 hMV0 hMVM hmW0 hmWτ
    (by rw [eV]; exact hVv.trans (ENNReal.ofReal_le_ofReal hv))
    (by rw [eW]; exact hWw.trans (ENNReal.ofReal_le_ofReal hWτ))
    (by rw [eK]; exact hKf.trans (ENNReal.ofReal_le_ofReal hKτ)) hVo' hWo'
    (fun X hX => (hKo' X hX).trans (ENNReal.ofReal_le_ofReal hKτ')) hs3 hs4
  obtain ⟨hc2, hε⟩ := hJab
  -- the defect
  have hLD := lastDef_ab_le P (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x)
    (lWR R Nh m b μ₀ oR x) (lKR R Nh m b μ₀ oR x) (by omega) hLp (A := R.A / 2) (by linarith)
    hs hs' (by positivity) hsum hC
    (by rw [eV]; exact hVin) (by rw [eW]; exact hWin) (by rw [eV]; exact hV0)
    (by rw [eK]; exact hKin)
    (fun b' => Obs2.cmpInA_of_osub (hOL.hV b')) (fun b' => Obs2.cmpInA_of_osub (hOL.hW b'))
    HAb.hV HAb.hW hτ hτ1 hMV0 hmW0
    (by rw [eV]; exact hVv.trans (ENNReal.ofReal_le_ofReal hv))
    (by rw [eW]; exact hWw.trans (ENNReal.ofReal_le_ofReal hWτ))
    (by rw [eK]; exact hKf.trans (ENNReal.ofReal_le_ofReal hKτ)) hVo' hWo'
  have eL : lastDefR R Nh m b μ₀ oR x = -Obs2.pdefAB2 P (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x) +
      (Obs2.xAB2 P (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x) (lWR R Nh m b μ₀ oR x)
          (lKR R Nh m b μ₀ oR x) +
        Obs2.rhoA2 P (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x) (lWR R Nh m b μ₀ oR x)
            (lKR R Nh m b μ₀ oR x) *
          Obs2.rhoB2 P (Nh + 1) (lC R Nh m b μ₀) (lVR R Nh m b μ₀ oR x) (lWR R Nh m b μ₀ oR x)
            (lKR R Nh m b μ₀ oR x)) := rfl
  rw [← eL] at hLD
  -- the constants
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hcS : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
  have hcJ0 : 0 ≤ cJet L * (cRho L + 4 / r₀ ^ 2) := by
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcS, hQ1]
    exact mul_nonneg h1 (add_nonneg h2 (by positivity))
  set cSo := cVo + cWo + 8 * cKo + 1 with hcSo
  have hcSo1 : 1 ≤ cSo := by rw [hcSo]; linarith
  have hMVc : MV ≤ M0 * cSo := by
    rw [hMVd]; exact mul_le_mul_of_nonneg_left (by linarith) hM0.le
  have hmWc : mW ≤ M0 * cSo := by
    rw [hmWd]
    refine mul_le_mul_of_nonneg_left ?_ hM0.le
    have := mul_le_of_le_one_right hcWo hg1
    linarith
  have hQ0 : 0 ≤ Q1 2 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · refine hc2.trans ?_
    have k1 : cJet L * (cRho L + 4 / r₀ ^ 2) * τ * Mbig ≤
        cJet L * (cRho L + 4 / r₀ ^ 2) * (M0 * cSo) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hτMb1 hcJ0
    have k2 : (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * MV + Q1 2 * mW) ≤
        (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (M0 * cSo) + Q1 2 * (M0 * cSo)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hL2
      · exact mul_le_mul_of_nonneg_left hMVc (by positivity)
      · exact mul_le_mul_of_nonneg_left hmWc hQ0
    have e : cJab L r₀ * cSo * M0 = cJet L * (cRho L + 4 / r₀ ^ 2) * (M0 * cSo) +
        (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (M0 * cSo) + Q1 2 * (M0 * cSo)) := by
      unfold cJab; ring
    rw [e]; linarith
  · refine hε.trans ?_
    have := mul_le_mul_of_nonneg_left hτMb1 hcJ0
    calc cJet L * (cRho L + 4 / r₀ ^ 2) * τ * Mbig = cJet L * (cRho L + 4 / r₀ ^ 2) * (τ * Mbig) := by
          ring
      _ ≤ cJet L * (cRho L + 4 / r₀ ^ 2) * (M0 * cSo) := this
      _ = _ := by ring
  · refine hLD.trans ?_
    have k : (L : ℝ) ^ 2 * ((Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * MV + Q1 2 * mW) ≤
        (L : ℝ) ^ 2 * ((Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (M0 * cSo) + Q1 2 * (M0 * cSo)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hL2
      · exact mul_le_mul_of_nonneg_left hMVc (by positivity)
      · exact mul_le_mul_of_nonneg_left hmWc hQ0
    have e : cLab L * cSo * M0 =
        (L : ℝ) ^ 2 * ((Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (M0 * cSo) + Q1 2 * (M0 * cSo)) := by
      unfold cLab; ring
    rw [e]; exact k

end Traj

end

end Spin2
