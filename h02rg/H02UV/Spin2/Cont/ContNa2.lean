import Spin2.Cont.ContNa1
import Spin2.H0.H0Factors

set_option autoImplicit false

/-!
# `n_a` of the last factor of a general state, bounded (`na_lastA_le`)

See `Spin2/Cont/ContNa1` for the statement in words. The proof combines the scale facts and bulk
inputs of the last step (as in `pairLastAB_xT`), the one-point sizes of the inputs in `wA`
(`na_wA_le`, `oTo_fullK_leAB`), `na_eps_uXO_a_le`, `na_finG_jets_a`, and the zero mode with the
reference normaliser (`rp_zero_abs`, as in `rp_topE_le`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

theorem rpRef_isObs (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : (rpRef R Nh m b μ₀ x).IsObs :=
  Obs2.obsHist_isObs _ _ _ (Obs2.obsInit_isObs .two (zV b) (ptsX x)) _ _

/-- The reference zero mode as a zero mode along the history restarted at `N_h + 1`. -/
theorem na_zmOF_ref (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) :
    PtCorr2.zmOF (R.withMsq m) (ptsX x) (Nh + 1) (rpRef R Nh m b μ₀ x) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) = zZm R Nh m b μ₀ x := by
  unfold PtCorr2.zmOF PtCorr2.finOF
  rw [PtCorr2.obsHistFrom_self]
  rfl

set_option maxHeartbeats 16000000 in
/-- **The one-point analogue of `rp_topE_le`**: `n_a` of the last factor of a general observable
state `o` at `N_h + 1`, linear in its `a`-size `σ` (any `x`; the reference one-point items of the
last step are inputs). -/
theorem na_lastA_le {Nh : ℕ} (hNh : Nh + 2 = N) {m b μ₀ Cf cW cK0 r₀ : ℝ} (hm0 : 0 < m)
    (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ)
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (hVL : ValidAtL (R.withMsq m) Nh)
    (hVN : LastN.ValidLast (R.withMsq m) (Nh + 1)) (hLp : pauliL0 2 ≤ L)
    (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) (hA2 : 2 ≤ R.A)
    (hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1)
    (hG : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
    (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (R.A / 2) r₀)
    (hcW : 0 ≤ cW) (hcK0 : 0 ≤ cK0) (hCf : 0 ≤ Cf)
    (hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1)
    (hs1 : 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ R.ρ)
    (hs2 : 8 * cM * R.ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2)
    (hs3 : cRho L * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL R.ℓ Cf cW cK0 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀)
    (lam : ℕ → ℂ) (x : Lam 2 L N)
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs) (hlo : PtCorr2.ObsLocInv (ptsX x) (Nh + 1) o)
    {σ Mb cVo cWo cKo cu K4 KA : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb) (hcVo : 0 ≤ cVo)
    (hcWo : 0 ≤ cWo) (hcKo : 0 ≤ cKo) (hcu : 0 ≤ cu)
    (hVo : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.V q) ≤
        ENNReal.ofReal cVo)
    (hWo : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.W q) ≤
        ENNReal.ofReal cWo)
    (hKo : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM1 (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 * σ) Mb)
        (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.K X) ≤
        ENNReal.ofReal cKo)
    (hMa0 : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖hBeta R m b μ₀ x Nh‖ ≤
      cu * ‖Mmag R m b μ₀ lam Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀)
    (hβ0 : hBeta R m b μ₀ x Nh ≠ 0)
    (hone1 : ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖)
    (hone2 : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      KA * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ /
        ‖(lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖)
    (hgam : ‖gamNa R Nh m b μ₀ x‖ ≤ K4 * ‖Mmag R m b μ₀ lam Nh‖)
    (hΩ0 : PtCorr2.sE (zZm R Nh m b μ₀ x) ≠ 0)
    (hnA : PtCorr2.nA (zZm R Nh m b μ₀ x) = -gamNa R Nh m b μ₀ x)
    {Kt : ℝ}
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2) (hmA : 8 * KA * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hmAa : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (cVo + cWo + 8 * cKo + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1) o Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))‖ ≤
      (cLab L * (cVo + cWo + 8 * cKo + 1) * cu +
          8 * (1 / 2 + 81 / 32 * cJab L r₀ * (cVo + cWo + 8 * cKo + 1)) * K4) *
        (σ / ‖hBeta R m b μ₀ x Nh‖) * ‖Mmag R m b μ₀ lam Nh‖ := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hA : 0 < R.A := Fact.out
  set R' := R.withMsq m with hR'
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  set P := ptsX (L := L) (N := N) x with hPd
  set st := (histOut R' Nh t).st with hst
  set gg := (t Nh).1 with hgg
  have hρ0 : 0 ≤ R'.ρ := hVL.2.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have H : RawInv R' (Nh + 1) st := rawInv_histU R' hV hVL t (Nh + 1) le_rfl
  obtain ⟨hC0, -, -, -⟩ := LastN.covN hVN H
  have hD : (histOut R' Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.1
  have hKm : (histOut R' Nh t).K ∈ ASub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R' hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R' _ _)
      (rawK_mem R' _ _)).2.2
  obtain ⟨⟨hz, hy, hnu, hgn, hgre, hWl, hDd, hKk⟩, -⟩ := hG
  have hg0' : 0 ≤ gg := hg0.le
  have hCg : 0 ≤ Cf * gg := mul_nonneg hCf hg0'
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
  have hsc1 : histS R' Nh t ^ 2 ≤ (9 / 8) ^ 2 * s' ^ 2 := by linarith only [hsNh, hss]
  have hsc2 : histS R' Nh t ^ 2 ≤ (9 / 8) ^ 2 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖ := by
    have e : (9 / 8 : ℝ) ^ 2 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖ =
        9 / 8 * (9 / 8 * R.ℓ ^ 2 / ‖(lastOut R' Nh t).Z‖) := by ring
    rw [e]; linarith
  -- the inputs of the last step of `o`
  set V' := Obs2.fullV R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re o with hV'd
  set W' := Obs2.fullW st (histOut R' Nh t).D o with hW'd
  set K' := Obs2.fullK R' (Nh + 1) st (histOut R' Nh t).K o with hK'd
  set C := LastN.stCovN R' (Nh + 1) st with hCd
  have hOL := olocS_last R' P (histOut R' Nh t).g.re (histOut R' Nh t).nu.re hVN H hD hKm hlo
  have eV : Obs2.bulkF V' = stVf R' (Nh + 1) st (histOut R' Nh t).g.re (histOut R' Nh t).nu.re :=
    Obs2.bulkF_fullV R' (Nh + 1) st _ _ ho
  have eW : Obs2.bulkF W' = st.Wl + (histOut R' Nh t).D := Obs2.bulkF_fullW st _ ho
  have eK : Obs2.bulkF K' = Kflat (Nh + 1) (stDelta R' (Nh + 1) st) (histOut R' Nh t).K :=
    Obs2.bulkF_fullK R' (Nh + 1) st _ ho
  -- the bulk sizes
  have hcM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hcT : 1 ≤ cTauL R.ℓ Cf cW cK0 := by
    unfold cTauL
    have : 0 ≤ (4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf := by positivity
    linarith
  set τ := cTauL R.ℓ Cf cW cK0 * gg with hτd
  have hτ : 0 < τ := mul_pos (by linarith) hg0
  have hτ1 : τ ≤ 1 := hs5.trans hr₀1
  have hgg1 : gg ≤ 1 := hg1
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
      have : 0 ≤ (10 * Cf + 9 / 4 * cW + 18 * cK0 + 1) * gg := by positivity
      linarith only [this]
    linarith
  have hWτ : Cf * gg ^ 2 + Cf * gg ^ 2 ≤ τ := by
    have h8 : 8 * (Cf * gg) ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 9 / 4 * cW + 18 * cK0 + 1) * gg := by
        positivity
      linarith only [this, hCg]
    have := mul_le_mul_of_nonneg_left hgg2 hCf; linarith
  have hKτ : 8 * (Cf * gg ^ 3) ≤ τ := by
    have h8 : 8 * (Cf * gg) ≤ τ := by
      rw [hτd]; unfold cTauL
      have : 0 ≤ ((4 * cM * R.ℓ ^ 2 + 8 * R.ℓ ^ 4) * Cf + 9 / 4 * cW + 18 * cK0 + 1) * gg := by
        positivity
      linarith only [this, hCg]
    have := mul_le_mul_of_nonneg_left hgg3 hCf; linarith
  have hδ0 : 0 ≤ 8 * cM * R.ℓ ^ 2 * (Cf * gg) := by positivity
  have hVb : Step2.Fnorm (Nh + 1) s (Obs2.bulkF V') ≤ ENNReal.ofReal τ := by
    rw [eV]; exact hVv.trans (ENNReal.ofReal_le_ofReal hv)
  have hWb : Step2.Fnorm (Nh + 1) s (Obs2.bulkF W') ≤ ENNReal.ofReal τ := by
    rw [eW]; exact hWw.trans (ENNReal.ofReal_le_ofReal hWτ)
  have hKb : Knorm (Nh + 1) s (R.A / 2) (Obs2.bulkF K') ≤ ENNReal.ofReal τ := by
    rw [eK]; exact hKf.trans (ENNReal.ofReal_le_ofReal hKτ)
  -- the `σ_a` sizes of the inputs (weight `wA`)
  set Ma := 2 * histS R' Nh t ^ 2 * σ with hMad
  have hsN : 0 < histS R' Nh t := histS_pos' R' hρ0 hρ8 t Nh
  have hMa : 0 < Ma := mul_pos (mul_pos two_pos (pow_pos hsN 2)) hσ
  have hwa : (wM Ma Mb).a = ENNReal.ofReal Ma⁻¹ := rfl
  have hwa1 : (wM1 Ma Mb).a = ENNReal.ofReal Ma⁻¹ := rfl
  set MV := Ma * cVo with hMVd
  set mW := Ma * cWo with hmWd
  have hMV0 : 0 ≤ MV := mul_nonneg hMa.le hcVo
  have hmW0 : 0 ≤ mW := mul_nonneg hMa.le hcWo
  have hVa : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo Obs2.wA (Nh + 1) s (V' q) ≤ ENNReal.ofReal MV := by
    intro q hq
    refine (PtCorr2.oTo_emb_add_le Obs2.wA (Nh + 1) s _ _).trans ?_
    refine (na_wA_le hMa hwa (Nh + 1) s (o.V q)).trans ?_
    rw [hMVd, ENNReal.ofReal_mul hMa.le]
    exact mul_le_mul_right (hVo q hq) _
  have hWa : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo Obs2.wA (Nh + 1) s (W' q) ≤ ENNReal.ofReal mW := by
    intro q hq
    refine (PtCorr2.oTo_emb_add_le Obs2.wA (Nh + 1) s _ _).trans ?_
    refine (na_wA_le hMa hwa (Nh + 1) s (o.W q)).trans ?_
    rw [hmWd, ENNReal.ofReal_mul hMa.le]
    exact mul_le_mul_right (hWo q hq) _
  have hKa : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal ((R.A / 2) ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo Obs2.wA (Nh + 1) s (K' X) ≤ ENNReal.ofReal (8 * (Ma * cKo)) := by
    intro X hX
    have h1 := PtCorr2.oTo_fullK_leAB R' (Nh + 1) st (histOut R' Nh t).K o Obs2.wA Obs2.wA_sub
      hs hA hδ0 (by linarith) hΔ X
    refine h1.trans ?_
    have h2 : ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) * Obs2.oTo Obs2.wA (Nh + 1) s (o.K X) ≤
        ENNReal.ofReal Ma * ENNReal.ofReal cKo := by
      calc ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) * Obs2.oTo Obs2.wA (Nh + 1) s (o.K X)
          ≤ ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
              (ENNReal.ofReal Ma * Obs2.oTo (wM1 Ma Mb) (Nh + 1) s (o.K X)) :=
            mul_le_mul_right (na_wA_le hMa hwa1 (Nh + 1) s (o.K X)) _
        _ = ENNReal.ofReal Ma * (ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
              Obs2.oTo (wM1 Ma Mb) (Nh + 1) s (o.K X)) := by ring
        _ ≤ _ := mul_le_mul_right (hKo X hX) _
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul hMa.le]
    exact mul_le_mul_right h2 _
  -- the sizes for the jet bound
  set cS := cVo + cWo + 8 * cKo + 1 with hcSd
  have hcS : 1 ≤ cS := by rw [hcSd]; linarith
  set Mbig := Ma * (cVo + cWo / τ + 8 * cKo * r₀ / τ + 1) with hMbd
  have hMb0 : 0 < Mbig := by
    rw [hMbd]
    have : 0 ≤ cWo / τ := div_nonneg hcWo hτ.le
    have : 0 ≤ 8 * cKo * r₀ / τ := div_nonneg (by positivity) hτ.le
    exact mul_pos hMa (by linarith)
  have hτMb : τ * Mbig = Ma * (τ * cVo + cWo + 8 * cKo * r₀ + τ) := by
    rw [hMbd]; field_simp
  have hMVM : MV ≤ Mbig := by
    rw [hMVd, hMbd]
    refine mul_le_mul_of_nonneg_left ?_ hMa.le
    have : 0 ≤ cWo / τ := div_nonneg hcWo hτ.le
    have : 0 ≤ 8 * cKo * r₀ / τ := div_nonneg (by positivity) hτ.le
    linarith
  have hmWτ : mW ≤ τ * Mbig := by
    rw [hτMb, hmWd]
    refine mul_le_mul_of_nonneg_left ?_ hMa.le
    have := mul_nonneg hτ.le hcVo
    have : 0 ≤ 8 * cKo * r₀ := by positivity
    linarith
  have hKτ' : 8 * (Ma * cKo) ≤ τ * Mbig / r₀ := by
    rw [hτMb, le_div_iff₀ hr₀]
    have e : 8 * (Ma * cKo) * r₀ = Ma * (8 * cKo * r₀) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ hMa.le
    have := mul_nonneg hτ.le hcVo
    linarith
  have hτMb1 : τ * Mbig ≤ Ma * cS := by
    rw [hτMb]
    refine mul_le_mul_of_nonneg_left ?_ hMa.le
    have k1 : τ * cVo ≤ cVo := mul_le_of_le_one_left hcVo hτ1
    have k3 : 8 * cKo * r₀ ≤ 8 * cKo := mul_le_of_le_one_right (by positivity) hr₀1
    linarith
  have hlocV : ∀ q, Obs2.CmpIn (nbhd (Nh + 1) (blockSet (L := L) (N := N) (Nh + 1) q) : Set (Lam 2 L N))
      (V' q : SA .two (Lam 2 L N)) := fun q => (Obs2.cmpInA_of_osub (hOL.hV q)).toCmpIn
  have hlocW : ∀ q, Obs2.CmpIn (nbhd (Nh + 1) (blockSet (L := L) (N := N) (Nh + 1) q) : Set (Lam 2 L N))
      (W' q : SA .two (Lam 2 L N)) := fun q => (Obs2.cmpInA_of_osub (hOL.hW q)).toCmpIn
  have hlocK : ∀ X, IsConn (Nh + 1) X → Obs2.CmpIn (nbhd (Nh + 1) X : Set (Lam 2 L N))
      (K' X : SA .two (Lam 2 L N)) := fun X hX => (Obs2.cmpInA_of_osub (hOL.hK X hX)).toCmpIn
  -- the jets of `F'_N`
  obtain ⟨hc2, hε⟩ := PtCorr2.na_finG_jets_a hJ (by linarith) hr₀ hr₀1 N (Nh + 1) (by omega) hLp
    s s' (s' / 4) hs hs' (by positivity) hsum C hC P V' W' K'
    (by rw [eV]; exact hVin) (by rw [eW]; exact hWin) (by rw [eV]; exact hV0)
    (by rw [eK]; exact hKin) hlocV hlocW hlocK τ Mbig MV mW hτ hs5 hMb0 hMV0 hMVM hmW0 hmWτ
    hVb hWb hKb hVa hWa (fun X hX => (hKa X hX).trans (ENNReal.ofReal_le_ofReal hKτ')) hs3 hs4
  -- the constant of the last step
  have hU := PtCorr2.na_eps_uXO_a_le P (Nh + 1) C V' W' K' (by omega) hLp (A := R.A / 2)
    (by linarith) hs hs' (by positivity) hsum hC
    (by rw [eV]; exact hVin) (by rw [eW]; exact hWin) (by rw [eV]; exact hV0)
    (by rw [eK]; exact hKin) hlocV hlocW hτ hτ1 hMV0 hmW0 hVb hWb hKb hVa hWa
  -- constants
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hQ0 : 0 ≤ Q1 2 := by linarith
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hcSN : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
  have hcJ'0 : 0 ≤ cJet L * (cRho L + 4 / r₀ ^ 2) := by
    have h1 : 0 ≤ cJet L := by
      unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
    have h2 : 0 ≤ cRho L := by
      unfold cRho
      have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
      have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
      refine mul_nonneg hL2 ?_
      linarith only [h4, h3, hcSN, hQ1]
    exact mul_nonneg h1 (add_nonneg h2 (by positivity))
  set cJ' := cJet L * (cRho L + 4 / r₀ ^ 2) with hcJ'd
  have hcJ0 : 0 ≤ cJab L r₀ := by unfold cJab; rw [← hcJ'd]; positivity
  have hcL : 0 ≤ cLab L := by unfold cLab; positivity
  have hMVc : MV ≤ Ma * cS := by
    rw [hMVd]; exact mul_le_mul_of_nonneg_left (by linarith) hMa.le
  have hmWc : mW ≤ Ma * cS := by
    rw [hmWd]; exact mul_le_mul_of_nonneg_left (by linarith) hMa.le
  -- `|ε(u^{obs}_N)_a| ≤ c_{Lab}c_SM_a`
  have hUc : ‖ε (Obs2.uXO P (Nh + 1) C V' W' K' univ : SA .two (Lam 2 L N)).a‖ ≤
      cLab L * cS * Ma := by
    refine hU.trans ?_
    have k : (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * MV + Q1 2 * mW) ≤
        (L : ℝ) ^ 2 * ((Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (Ma * cS) + Q1 2 * (Ma * cS)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hL2
      · exact mul_le_mul (by linarith) hMVc hMV0 (by positivity)
      · exact mul_le_mul_of_nonneg_left hmWc hQ0
    have e : cLab L * cS * Ma =
        (L : ℝ) ^ 2 * ((Q1 2 + 5 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (Ma * cS) + Q1 2 * (Ma * cS)) := by
      unfold cLab; ring
    rw [e]; exact k
  -- the jets in the form needed (`F'` the final object of `o`)
  set F' := PtCorr2.finOF R' P (Nh + 1) o Nh t with hF'd
  have eF : F' = PtCorr2.finG P (Nh + 1) C V' W' K' := by
    rw [hF'd]; unfold PtCorr2.finOF; rw [PtCorr2.obsHistFrom_self]; rfl
  have hc2' : s' ^ 2 * ‖Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).a‖ ≤ cJab L r₀ * cS * Ma := by
    rw [eF]
    refine hc2.trans ?_
    have k1 : cJ' * τ * Mbig ≤ cJ' * (Ma * cS) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hτMb1 hcJ'0
    have k2 : (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * MV + Q1 2 * mW) ≤
        (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (Ma * cS) + Q1 2 * (Ma * cS)) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hL2
      · exact mul_le_mul_of_nonneg_left hMVc (by positivity)
      · exact mul_le_mul_of_nonneg_left hmWc hQ0
    have e : cJab L r₀ * cS * Ma = cJ' * (Ma * cS) +
        (L : ℝ) ^ 2 * ((Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) * (Ma * cS) + Q1 2 * (Ma * cS)) := by
      unfold cJab; rw [← hcJ'd]; ring
    rw [e]; linarith
  have hε' : ‖ε (F' : Obs.SA .two (Lam 2 L N)).a‖ ≤ cJ' * cS * Ma := by
    rw [eF]
    refine hε.trans ?_
    have := mul_le_mul_of_nonneg_left hτMb1 hcJ'0
    calc cJ' * τ * Mbig = cJ' * (τ * Mbig) := by ring
      _ ≤ cJ' * (Ma * cS) := this
      _ = _ := by ring
  -- the reference one-point data (as in `rp_topE_le`)
  set Mn := ‖Mmag R m b μ₀ lam Nh‖ with hMn
  set hb0 := ‖hBeta R m b μ₀ x Nh‖ with hb0d
  have hhb0 : 0 < hb0 := norm_pos_iff.2 hβ0
  have hMn0 : 0 ≤ Mn := norm_nonneg _
  set β1 := ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ with hβ1d
  have hβx : hb0 ≤ 2 * β1 := by
    have hflow := bt2_flow R P (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)
    have hBB : ‖bt2 R P (zV b) m b μ₀ Nh‖ ≤ 2 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      rw [hflow]; exact beta_step_ge htop.1 htop.2
    have hβeq : ‖Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x)‖ =
        ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖ := by
      have h : Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (lV R Nh m b μ₀ x) =
          Obs2.betaTot2 (L := L) (N := N) (Nh + 1) (Obs2.histVO2 (R.withMsq m) P
            (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1)) := by
        unfold Obs2.betaTot2
        refine sum_congr rfl fun b' _ => ?_
        rw [Obs2.histVO2_a]
        congr 1
        exact Obs2.emb_add_cmp true _ _
      rw [h]; rfl
    rw [hβ1d, hβeq]; exact hBB
  have hβ10 : 0 < β1 := by linarith
  have hβ1ne : Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0 := norm_pos_iff.1 hβ10
  set Z := (lastOut R' Nh t).Z with hZd
  have hZ0 : Z ≠ 0 := lastOut_Z_ne R' hρ0 hρ1 Nh _
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ0
  have hc := zCc_ge R hNh hm0 b μ₀ hK hmT hZ0
  set Λ := (L : ℝ) ^ (2 * N) with hΛd
  have hΛ : 0 < Λ := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hmid : 1 / (2 * m * Λ) / ‖Z‖ ≤ ‖zCc R Nh m b μ₀‖ := by
    refine le_trans (le_of_eq ?_) hc
    field_simp
    exact (div_self hZn.ne').symm
  -- `|εF'_a| ≤ |c|·½σ`, `|c2F'_a| ≤ (81/32)c_{Jab}c_Sσ`
  set eX := 1 / 2 * σ with heXd
  have heX : 0 ≤ eX := by positivity
  set eY := 81 / 32 * cJab L r₀ * cS * σ with heYd
  have heY : 0 ≤ eY := by positivity
  have hX : ‖ε (F' : Obs.SA .two (Lam 2 L N)).a‖ ≤ ‖zCc R Nh m b μ₀‖ * eX := by
    have k1 : Ma ≤ 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ :=
      calc Ma = 2 * σ * histS R' Nh t ^ 2 := by rw [hMad]; ring
        _ ≤ 2 * σ * ((9 / 8) ^ 2 * R.ℓ ^ 2 / ‖Z‖) := mul_le_mul_of_nonneg_left hsc2 (by linarith)
        _ = 81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ := by ring
    calc ‖ε (F' : Obs.SA .two (Lam 2 L N)).a‖ ≤ cJ' * cS * Ma := hε'
      _ ≤ cJ' * cS * (81 / 32 * R.ℓ ^ 2 / ‖Z‖ * σ) :=
          mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ'0 (by linarith))
      _ = (81 / 16 * cJ' * cS * R.ℓ ^ 2) / ‖Z‖ * eX := by rw [heXd]; ring
      _ ≤ (1 / (2 * m * Λ)) / ‖Z‖ * eX := by
          have h2mΛ : 0 < 2 * m * Λ := mul_pos (mul_pos two_pos hm0) hΛ
          have hq : 81 / 16 * cJ' * cS * R.ℓ ^ 2 ≤ 1 / (2 * m * Λ) := by
            rw [le_div_iff₀ h2mΛ]
            have e : 81 / 16 * cJ' * cS * R.ℓ ^ 2 * (2 * m * Λ) =
                2 * (81 / 16 * cJ' * cS * R.ℓ ^ 2) * m * Λ := by ring
            rw [e]; exact hmAa
          exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hq hZn.le) heX
      _ ≤ ‖zCc R Nh m b μ₀‖ * eX := mul_le_mul_of_nonneg_right hmid heX
  have hs'2 : 0 < s' ^ 2 := pow_pos hs' 2
  have hY : ‖Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).a‖ ≤ eY := by
    have k1 : Ma ≤ s' ^ 2 * (81 / 32 * σ) :=
      calc Ma = 2 * σ * histS R' Nh t ^ 2 := by rw [hMad]; ring
        _ ≤ 2 * σ * ((9 / 8) ^ 2 * s' ^ 2) := mul_le_mul_of_nonneg_left hsc1 (by linarith)
        _ = s' ^ 2 * (81 / 32 * σ) := by ring
    have k2 : s' ^ 2 * ‖Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).a‖ ≤ s' ^ 2 * eY := by
      refine hc2'.trans ?_
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hcJ0 (by linarith : (0 : ℝ) ≤ cS))
      calc cJab L r₀ * cS * Ma ≤ cJab L r₀ * cS * (s' ^ 2 * (81 / 32 * σ)) := this
        _ = s' ^ 2 * eY := by rw [heYd]; ring
    exact le_of_mul_le_mul_left k2 hs'2
  -- `|εF_a| ≤ ¼|c||β|` (reference)
  have he' : ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by
    have hKA : KA * (β1 / ‖Z‖) ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := by
      have hKA0 : KA ≤ 1 / (8 * m * Λ) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have hq : 0 ≤ β1 / ‖Z‖ := div_nonneg hβ10.le hZn.le
      have e : 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 = 1 / (8 * m * Λ) * (β1 / ‖Z‖) := by
        field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hKA0 hq
    have hc' : 1 / (2 * m * ‖Z‖ * Λ) ≤ ‖zCc R Nh m b μ₀‖ := by
      refine le_trans (le_of_eq ?_) hmid
      field_simp
    calc ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤ KA * β1 / ‖Z‖ := hone2
      _ = KA * (β1 / ‖Z‖) := by ring
      _ ≤ 1 / 4 * (1 / (2 * m * ‖Z‖ * Λ)) * β1 := hKA
      _ ≤ 1 / 4 * ‖zCc R Nh m b μ₀‖ * β1 := by gcongr
      _ = 1 / 4 * (‖zCc R Nh m b μ₀‖ * β1) := by ring
  -- the zero mode of `o`, with the reference normaliser
  set F := zFin R Nh m b μ₀ x with hFd
  set cc := zCc R Nh m b μ₀ with hccd
  obtain ⟨s1, s2, -, -⟩ := PtCorr2.sX_omegaCO_cstC cc F
  obtain ⟨s1', s2', -, -⟩ := PtCorr2.sX_omegaCO_cstC cc F'
  have hΩd : zZm R Nh m b μ₀ x = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F := rfl
  have hΩd' : PtCorr2.zmOF R' P (Nh + 1) o Nh t = PtCorr2.omegaCO (PtCorr2.cstC (Lam 2 L N) cc) F' :=
    rfl
  set s0 := ε (F : Obs.SA .two (Lam 2 L N)).e - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).e
    with hs0d
  have hs0 : s0 ≠ 0 := by
    have : PtCorr2.sE (zZm R Nh m b μ₀ x) = s0 := by rw [hΩd, s1]
    rw [← this]; exact hΩ0
  have hsEo : PtCorr2.sE (PtCorr2.zmOF R' P (Nh + 1) o Nh t) = s0 := by
    rw [PtCorr2.rp_sE_zmOF R' P (j' := Nh + 1) ho (rpRef_isObs R Nh m b μ₀ x) Nh t,
      show PtCorr2.zmOF R' P (Nh + 1) (rpRef R Nh m b μ₀ x) Nh t = zZm R Nh m b μ₀ x from
        na_zmOF_ref R Nh m b μ₀ x, hΩd, s1]
  have hnAΩ : PtCorr2.nA (PtCorr2.zmOF R' P (Nh + 1) o Nh t) =
      (ε (F' : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F' : Obs.SA .two (Lam 2 L N)).a) /
        s0 := by
    unfold PtCorr2.nA
    rw [hsEo, hΩd', s2']
  have hγ : ε (F : Obs.SA .two (Lam 2 L N)).a - cc * Suscept.c2 (F : Obs.SA .two (Lam 2 L N)).a =
      -(gamNa R Nh m b μ₀ x * s0) := by
    have h := hnA
    unfold PtCorr2.nA at h
    rw [hΩd, s1, s2] at h
    rw [div_eq_iff hs0] at h
    rw [h]; ring
  have hZm := rp_zero_abs hβ1ne hs0 heX heY hone1 he' hγ hX hY
  rw [← hnAΩ] at hZm
  -- the split of `n_a(lastOF)`
  have hdet := (chainFactors_ne R' hNh hspl hm0 hm hV hVL t).2
  have hXc : PtCorr2.sE (PtCorr2.lastCstOF R' P (Nh + 1) o Nh t) ≠ 0 := by
    rw [PtCorr2.sE_lastCstOF]; exact mul_ne_zero hdet (Complex.exp_ne_zero _)
  have hΩc : PtCorr2.sE (PtCorr2.zmOF R' P (Nh + 1) o Nh t) ≠ 0 := by rw [hsEo]; exact hs0
  have hsplit := na_nA_lastOF_split R' P (Nh + 1) o Nh t hXc hΩc
  rw [PtCorr2.obsHistFrom_self] at hsplit
  -- assembly
  have hMa' : Ma ≤ cu * Mn * (σ / hb0) := by
    have e : Ma = 2 * histS R' Nh t ^ 2 * hb0 * (σ / hb0) := by
      rw [hMad]; field_simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_right hMa0 (div_nonneg hσ.le hhb0.le)
    have h2 : cu * Mn * gg * (σ / hb0) ≤ cu * Mn * (σ / hb0) := by
      have h0 : 0 ≤ cu * Mn * (σ / hb0) := by positivity
      calc cu * Mn * gg * (σ / hb0) = gg * (cu * Mn * (σ / hb0)) := by ring
        _ ≤ 1 * (cu * Mn * (σ / hb0)) := mul_le_mul_of_nonneg_right hgg1 h0
        _ = _ := one_mul _
    exact h1.trans h2
  have hD1 : ‖-ε (Obs2.uXO P (Nh + 1) C V' W' K' univ : SA .two (Lam 2 L N)).a‖ ≤
      cLab L * cS * cu * (σ / hb0) * Mn := by
    rw [norm_neg]
    refine hUc.trans ?_
    have := mul_le_mul_of_nonneg_left hMa' (mul_nonneg hcL (by linarith : (0 : ℝ) ≤ cS))
    calc cLab L * cS * Ma ≤ cLab L * cS * (cu * Mn * (σ / hb0)) := this
      _ = _ := by ring
  have hD2 : ‖PtCorr2.nA (PtCorr2.zmOF R' P (Nh + 1) o Nh t)‖ ≤
      8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * K4 * (σ / hb0) * Mn := by
    refine hZm.trans ?_
    set c1 := 1 / 2 + 81 / 32 * cJab L r₀ * cS with hc1d
    have hc10 : 0 ≤ c1 := by rw [hc1d]; positivity
    have hsum2 : eX + eY = c1 * σ := by rw [heXd, heYd, hc1d]; ring
    have hinv : 1 / β1 ≤ 2 / hb0 := by
      rw [div_le_div_iff₀ hβ10 hhb0]; linarith
    have hK4M : 0 ≤ K4 * Mn := (norm_nonneg _).trans hgam
    rw [hsum2]
    calc 4 * ‖gamNa R Nh m b μ₀ x‖ * (c1 * σ) / β1
        = 4 * ‖gamNa R Nh m b μ₀ x‖ * (c1 * σ) * (1 / β1) := by ring
      _ ≤ 4 * (K4 * Mn) * (c1 * σ) * (2 / hb0) := by
          have a1 : 4 * ‖gamNa R Nh m b μ₀ x‖ * (c1 * σ) ≤ 4 * (K4 * Mn) * (c1 * σ) := by
            have := mul_le_mul_of_nonneg_right hgam (mul_nonneg hc10 hσ.le)
            linarith
          exact mul_le_mul a1 hinv (div_nonneg zero_le_one hβ10.le)
            (mul_nonneg (mul_nonneg (by norm_num) hK4M) (mul_nonneg hc10 hσ.le))
      _ = 8 * c1 * K4 * (σ / hb0) * Mn := by ring
  have key : ‖PtCorr2.nA (PtCorr2.lastOF R' P (Nh + 1) o Nh t)‖ ≤
      (cLab L * cS * cu + 8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * K4) * (σ / hb0) * Mn := by
    rw [hsplit]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ cLab L * cS * cu * (σ / hb0) * Mn +
          8 * (1 / 2 + 81 / 32 * cJab L r₀ * cS) * K4 * (σ / hb0) * Mn := add_le_add hD1 hD2
      _ = _ := by ring
  exact key

end Traj

end

end Spin2
