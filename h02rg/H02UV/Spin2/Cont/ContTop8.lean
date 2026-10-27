import Spin2.Cont.ContTop6
import Spin2.Cont.ContWire9

set_option autoImplicit false

/-!
# Top coalescence: the relative restart size and the final bound

* **`MasterFacts.ct_sig_cmp`** (copy of `cw4_sig_cmp` at `j_y := N_h`): for an observable datum at
  `m_r ≤ N_h`, `σ/|β_{a,N_h}| ≤ cw4Cmp M 0·M₀/|β^{(0,y)}_{m_r}|` with `σ = ctSig` (the envelope at
  `N_h`).
* **`MasterFacts.ct_conn_diff_top'`**: `ct_conn_diff_top` with `σ/|β_{a,N_h}|` replaced by
  `cw4Cmp M 0·cddRel(K_p, ǧ_{ms}, a_{ms}, rpIota 0 0, A, r)` (`cdd_restart_rel`), i.e.
  `|P(x) − P(y)| ≤ (3/2)(1 + K_O)Γ_δϑ_{N_h} + (9/4)max(K_E, 0)·cw4Cmp(0)·cddRel·ϑ_{N_h}²ǧ_{N_h}`,
  `cddRel ≍ ǧ_{ms} + a_{ms} + 48e^{3/2}A·L^{−r}`.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **The relative restart size at the top**: `σ/|β_{a,N_h}| ≤ cw4Cmp M 0·M₀/|β^{(0,y)}_{m_r}|`. -/
theorem ct_sig_cmp (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ)
    (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (y : Lam 2 L N) {mr : ℕ} (δ : ObsSt .two L N) (h0 : δ.IsObs)
    (hmy : mr ≤ Nh) (hNh1 : 1 ≤ Nh) {M₀ : ℝ} (hM0 : 0 ≤ M₀) :
    ctSig R m b Nh y mr δ M₀ / ‖hBeta R m b (b - m) y Nh‖ ≤
      cw4Cmp M 0 * (M₀ / ‖bt2 R (ptsX y) (zV0 b) m b (b - m) mr‖) := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) with htd
  set jy := Nh with hjyd
  have hj : jy ≤ Nh := le_rfl
  set n := Nh - jy with hnd
  set d := jy - mr with hdd
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hNh0 : 0 < Nh := by omega
  have hβs := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl hmu hNh0 mr (by omega)).1
  have hβN := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl hmu hNh0 Nh le_rfl).1
  have hhB : ‖hBeta R m b (b - m) y Nh‖ = ‖bt2 R (ptsX y) (zV0 b) m b (b - m) Nh‖ := by
    rw [hBeta_eq_zV0 R m b (b - m) y hNh1]; rfl
  rw [hhB]
  -- the three comparisons
  have hpc := M.cw4_prod_cmpD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) δ h0 (k := mr) (j := d) (by omega)
  have hra := M.cw2_ratioD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y) (zV0 b)
    hmu (k := mr) (j := d) (by omega)
  rw [show mr + d = jy by omega] at hra
  have hup := M.cw4_beta_up N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b (b - m) hD (ptsX y) (zV0 b)
    hmu (j := jy) hj
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  -- assemble
  set Pf := ∏ i ∈ range d, ‖1 - frakN2F (ptsX y) (histCovO (R.withMsq m) t)
    (histVF2 (R.withMsq m) (ptsX y) mr δ t) mr (mr + i)‖ with hPf
  set Pn := ∏ i ∈ range d, ‖1 - nn2 R (ptsX y) (zV0 b) m b (b - m) (mr + i)‖ with hPn
  set Cm := Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ))))
  set c := 2 * (M.core.cRel * (4 / betaL L) * M.core.ε)
  set βs := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) mr‖
  set βj := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) jy‖
  set βN := ‖bt2 R (ptsX y) (zV0 b) m b (b - m) Nh‖
  have hσ : ctSig R m b Nh y mr δ M₀ = M₀ * Pf := rfl
  rw [hσ]
  have hPf0 : 0 ≤ Pf := prod_nonneg fun _ _ => norm_nonneg _
  have hPn0 : 0 ≤ Pn := prod_nonneg fun _ _ => norm_nonneg _
  have hec : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  -- `βs·Pn ≤ e^c βj`
  have hPi : βs * Pn ≤ Real.exp c * βj := by
    have := mul_le_mul_of_nonneg_left hra (Real.exp_pos c).le
    calc βs * Pn = Real.exp c * (Real.exp (-c) * βs * Pn) := by
          rw [← mul_assoc, ← mul_assoc, hec, one_mul]
      _ ≤ _ := this
  have hkey : M₀ * Pf * βs ≤ M₀ * (Cm * (Real.exp c * (Real.exp c * (8 / 7) ^ n * βN))) := by
    have h1 : Pf * βs ≤ Cm * (βs * Pn) :=
      calc Pf * βs ≤ Cm * Pn * βs := mul_le_mul_of_nonneg_right hpc hβs.le
        _ = Cm * (βs * Pn) := by ring
    have h2 : Cm * (βs * Pn) ≤ Cm * (Real.exp c * (Real.exp c * (8 / 7) ^ n * βN)) :=
      mul_le_mul_of_nonneg_left (hPi.trans (mul_le_mul_of_nonneg_left hup (Real.exp_pos c).le))
        (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hM0
    linarith [show M₀ * (Pf * βs) = M₀ * Pf * βs by ring]
  have hq : M₀ * Pf / βN ≤ Cm * Real.exp c ^ 2 * (8 / 7) ^ n * (M₀ / βs) := by
    rw [div_le_iff₀ hβN, show Cm * Real.exp c ^ 2 * (8 / 7) ^ n * (M₀ / βs) * βN =
      Cm * Real.exp c ^ 2 * (8 / 7) ^ n * M₀ * βN / βs by ring, le_div_iff₀ hβs]
    exact hkey.trans (le_of_eq (by ring))
  have hq0 : 0 ≤ M₀ * Pf / βN := div_nonneg (mul_nonneg hM0 hPf0) hβN.le
  have hn0 : n = 0 := by omega
  calc M₀ * Pf / βN ≤ Cm * Real.exp c ^ 2 * (8 / 7) ^ n * (M₀ / βs) := hq
    _ = cw4Cmp M 0 * (M₀ / βs) := by rw [hn0]; unfold cw4Cmp; ring

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`P(x) − P(y)` at `h = 0`, top coalescence, with the relative restart size**:
`ct_conn_diff_top` with `σ/|β_{a,N_h}| ≤ cw4Cmp M 0·cddRel` (`ct_sig_cmp`, `cdd_restart_rel`). -/
theorem ct_conn_diff_top' {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
        histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ∧
      (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) ≤
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖ ∧
    ∀ {mm k₁ c₁ k2 : ℝ}, 0 ≤ c₁ → 0 ≤ k2 →
      1 + cw2Thb M Nh Nh ≤ mm →
      M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) +
          ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r)) +
          cw2Thb M Nh Nh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) ≤
        M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm →
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm →
      (kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
            (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r)) +
          8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 +
          cw2Thb M Nh Nh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2) ≤ k₁ →
      k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm →
      8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀ →
      (∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r))) (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
          Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
            ((obsHistFrom (R.withMsq m) (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X : Obs.SA .two (Lam 2 L N)).ab) ≤
          ENNReal.ofReal k2) →
      M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
        M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1 →
      2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ)‖ ≤
        3 / 2 * (1 + M.fwKO) *
            M.ctGamB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) kk ww *
            varthJ R m b (b - m) Nh +
          9 / 4 * max (M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
            (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
              M.core.A) ^ (L ^ 2)) r₀) 0 *
            (cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
              (R.withMsq m).A r) * varthJ R m b (b - m) Nh ^ 2 *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨kk, ww, hkk, hww, hMR, hrel, H⟩ := M.ct_conn_diff_top R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hvb hwb hsmall y hy hj hspl x hk0 hkN hmx hrk hblk hdist hsc0 hsc hreg hgms
  refine ⟨kk, ww, hkk, hww, hMR, hrel, ?_⟩
  intro mm k₁ c₁ k2 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  refine (H h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11).trans (add_le_add le_rfl ?_)
  obtain ⟨-, h0, -, -, -, -, -, -, -, -, kk', ww', -, -, hM0, -, -, -, -, hrel'⟩ :=
    M.ct_T6_inputs_top N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD hspl x y hk0 hkN hmx hj hrk
      hblk hdist hsc0 hsc hreg
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hβs := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsX y)
    (zV0 b) rfl (zV_mua_ne hb0) (by omega) ms (by omega)).1
  have hσ := M.ct_sig_cmp N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD y _ h0 hkN.le (by omega)
    hM0.le
  have hXY : ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) /
        ‖hBeta R m b (b - m) y Nh‖ ≤
      cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0) (R.withMsq m).A r := by
    refine hσ.trans (mul_le_mul_of_nonneg_left ?_ (cw4Cmp_pos M _).le)
    rw [div_le_iff₀ hβs]
    exact hrel'
  have hX0 : 0 ≤ ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) /
        ‖hBeta R m b (b - m) y Nh‖ := by
    refine div_nonneg ?_ (norm_nonneg _)
    unfold ctSig Obs2.rkEnv
    exact mul_nonneg hM0.le (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hv : 0 ≤ varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 :=
    mul_nonneg (sq_nonneg _) (hD Nh le_rfl).1.le
  set K := M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
    (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀
  have hKX := mul_le_mul (le_max_left K 0) hXY hX0 (le_max_right K 0)
  have := mul_le_mul_of_nonneg_right hKX hv
  have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 9 / 4)
  calc _ = 9 / 4 * (K * (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms)
        (M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
          ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0) (R.withMsq m).A r) /
        ‖hBeta R m b (b - m) y Nh‖) * (varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) := by ring
    _ ≤ _ := this
    _ = _ := by ring

end MasterFacts

end

end Spin2
