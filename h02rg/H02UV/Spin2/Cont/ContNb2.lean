import Spin2.Cont.ContK2e
import Spin2.Cont.ContNa7
import Spin2.Cont.ContNb1

set_option autoImplicit false

/-!
# Top coalescence `N_h + 1 ≤ j_y`: decayed sizes, `k₂` discharged, `γ_δ` from `n_a(W(δ)) = 0`

**`MasterFacts.nb_conn_diff_top`**: `k2_conn_diff_top` (decayed size conditions of `art_T5topD`;
`Q`/`Z_{ab}`/waiting data for `k₂`) combined with `na_conn_diff_top'` (the `h = 0` identity
`rpTopU(δ_{N_h+1}) = −n_a(lastOF_{N_h+1})`, `na_rpTopU_eq`): the final call is `nb_T5topD`, so the
term `ctGamB` (initial `ε(δ.u_a)` plus the chain from `ms`) is gone. One extra arrow: the window
`hmAa` of `na_lastA_le`. Conclusion:
`|P(x) − P(y)| ≤ (9/4)((1 + K_O)max(K_A^{na}, 0) + max(K_E, 0)ǧ_{N_h})·cw4Cmp(0)·cddRel·ϑ_{N_h}²`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The top-coalescence bound with decayed transients, `k₂` discharged and `γ_δ` from the
`h = 0` identity** (no `ε(δ.u_a)`; both terms relative to `cw4Cmp(0)·cddRel`). -/
theorem nb_conn_diff_top {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {cK0 Kt : ℝ} (hseed : TopSeedAt R Nh m b (b - m) cK0)
    (hK : ‖(m : ℂ) * ((lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).Z *
        zmRaw (R.withMsq m) (Nh + 1)
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).ζ) - 1‖ ≤
      Kt * m * (L : ℝ) ^ (2 * N))
    (hmT : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2)
    (hmA : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hsmA : (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) +
        9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2)
    (hs1 : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ)
    (hs2 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
      ≤ 1 / 2)
    (hs3 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hs4 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2)
    (hs5 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀)
    (hvb : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) +
      8 * M.core.ℓ ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1)
    (hwb : 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 2) ≤ 1)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (y : Lam 2 L N) (hy : y ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the pair-difference datum
    (hspl : SplitSmall R.P L R.ρ) (x : Lam 2 L N) {ms r : ℕ} (hk0 : 0 < ms) (hkN : ms < Nh)
    (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hsc0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hsc : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hgms : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2) ≤ 1 / 1344) :
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r) ∧
    ∀ {mm k₁ c₁ k2 Q Zab : ℝ}, 0 ≤ c₁ → 0 ≤ k2 →
      1 + cw2Thb M Nh Nh ≤ mm →
      M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + (7 / 30) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
          cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm →
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm →
      (56 / 75) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
          8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 +
          cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) ≤ k₁ →
      k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm →
      8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀ →
      -- route (c): sizes `m_j = k2Mj … Q j`, the datum's own `ab` activity, waiting
      0 ≤ Q →
      (7 / 5) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q →
      (7 / 5) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
        8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q →
      (∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
        ((wM (k2Ma R m b (b - m) y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) Nh)
            (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
          Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
            ((pl2Delta R m b (b - m) x y ms).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal Zab) →
      Zab ≤ M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * Q ^ 2 →
      (8 / 15) ^ (Nh - ms) * Q ≤ 1 →
      M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2) ≤ k2 →
      M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
        M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1 →
      2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm +
          8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) *
        M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ)‖ ≤
        9 / 4 * ((1 + M.fwKO) * max (M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm)
              (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀) 0 +
            max (M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
              (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀) 0 *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) *
          (cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
            (rpIota 0 0) (R.withMsq m).A r) * varthJ R m b (b - m) Nh ^ 2 := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨hid, h0, hl0, hs0', hVab, hVabN, hWabN, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR,
    hKR, hMR, hrel'⟩ := M.ct_T6_inputs_top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD hspl x y hk0
      hkN hmx hj hrk hblk hdist hsc0 hsc hreg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro mm k₁ c₁ k2 Q Zab hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hQ0 hQw hQk hZ hQz hwait hk2e hsmT hmAB
    hmAa
  have hKab := M.k2_top N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x y hk0 hblk hmx hj
    hkN h0 hl0 hs0' hf0 hp0 hδb hM0 hkk hww hbR hWR hKR hgms hMR hQ0 hQw hQk hZ hQz
  have hw1 := (k2_wait M Nh Nh ms hQ0 hkN le_rfl hwait).1
  have hcN : 0 ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    have := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
    have := (hD Nh le_rfl).1.le
    positivity
  have hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r)))
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X :
            Obs.SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2 := by
    intro X hX
    refine (hKab X hX).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hk2e))
    have hm0' := k2Mj_pos M Nh Nh ms hQ0 Nh
    have h5 : 0 ≤ M.k2cab / 5 := div_nonneg M.k2cab_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hm0'.le hw1 2) hcN) h5
  -- the `h = 0` identity for the restarted difference datum
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := hF
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL7 : 7 ≤ L := by have := M.core.hL49; omega
  have hU := na_rpTopU_eq R hNh m hρ1 hspl hm.1 hm.2 hval hvalL hL7 (μ₀ := b - m) hb
    (sub_add_cancel b m).symm x y ms hblk hkN.le
  have hidA : ε (((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).u : Obs.SA .two (Lam 2 L N)).a) =
      PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX y) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) := by
    unfold rpTopU at hU; exact neg_inj.1 hU
  have hT := M.nb_T5topD R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1
    hs2 hs3 hs4 hs5 hvb hwb hsmall y hy hj hk0 hkN.le _ h0 hl0 hs0' hVab hVabN hWabN hf0 hp0 hδb
    hM0 hkk hww hbR hWR hKR hgms hMR hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hK2 hsmT hmAB hidA hmAa
  rw [hid]
  refine hT.trans ?_
  have hβs := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl (zV_mua_ne hb) (by omega) ms (by omega)).1
  have hσ := M.ct_sig_cmp N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD y _ h0 hkN.le (by omega)
    hM0.le
  set X := (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r)) / ‖hBeta R m b (b - m) y Nh‖ with hXd
  set Qr := cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
    (rpIota 0 0) (R.withMsq m).A r with hQd
  have hXY : X ≤ Qr := by
    refine hσ.trans (mul_le_mul_of_nonneg_left ?_ (cw4Cmp_pos M _).le)
    rw [div_le_iff₀ hβs]
    exact hrel'
  have hX0 : 0 ≤ X := by
    refine div_nonneg ?_ (norm_nonneg _)
    unfold ctSig Obs2.rkEnv
    exact mul_nonneg hM0.le (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  set v := varthJ R m b (b - m) Nh with hvd
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 with hgd
  have hg : 0 ≤ g := (hD Nh le_rfl).1.le
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg _
  have hKO0 : 0 ≤ M.fwKO := by
    unfold fwKO
    have := M.topF'_nonneg; have := M.topCL_nonneg
    have : 0 ≤ max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 := le_max_right _ _
    positivity
  set KA := M.naKA (M.ctVT (M.core.c * g)) (M.rptfWT (M.core.c * g) mm)
    (M.rptfKx c₁ (M.core.c * g) mm k₁) r₀ with hKAd
  set KE := M.rpKE ((2 * rpIota (M.ctVT (M.core.c * g))
    (M.rptfWT (M.core.c * g) mm) * M.core.A) ^ (L ^ 2)) r₀ with hKEd
  have hA1 : KA * X ≤ max KA 0 * Qr := mul_le_mul (le_max_left _ _) hXY hX0 (le_max_right _ _)
  have hA2 : KE * X ≤ max KE 0 * Qr := mul_le_mul (le_max_left _ _) hXY hX0 (le_max_right _ _)
  have hQ0' : 0 ≤ Qr := hX0.trans hXY
  calc 3 / 2 * (1 + M.fwKO) * (KA * X * (3 / 2 * v)) * v + 9 / 4 * KE * X * v ^ 2 * g
      = 9 / 4 * ((1 + M.fwKO) * (KA * X) + (KE * X) * g) * v ^ 2 := by ring
    _ ≤ 9 / 4 * ((1 + M.fwKO) * (max KA 0 * Qr) + (max KE 0 * Qr) * g) * v ^ 2 := by
        gcongr
    _ = _ := by ring

end MasterFacts

end

end Spin2
