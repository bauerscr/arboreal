import Spin2.Cont.ContEqC3
import Spin2.Cont.ContFin1

set_option autoImplicit false

/-!
# B3, `r`-dependent form, item (d): the intermediate case in the form `C·cddRel·ϑ_{N_h}²`

**`MasterFacts.eqc_mid (hcab)`**: `fin_T6_mid` (same hypotheses, `ms < j_y ≤ N_h`) with the
conclusion `|P(x) − P(y)| ≤ eqcCmid(K_A, K_R, N_h − j_y)·cddRel·ϑ_{N_h}²`, where
`eqcCmid K_A K_R n = (max(K_A,0)·E_c·(3/2) + (n+1)·eqcK)·(3/2)(1 + K_{11})·K_g^n
  + max(K_R,0)·cw4Cmp(n)`, `E_c = e^{c'}e^{c}`. Inputs: `eqc_ctSig_rel` (`σ/|β_{a,N_h}|`),
`eqc_nbGB_le` (item (c)), `eqc_varth_ratio` (`ϑ_{j_y} ≤ K_g^nϑ_{N_h}`), `bθ_{N_h}² = ǧϑ ≤ ϑ`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

/-- `E_c = e^{c'}e^{c}`. -/
def eqcEc : ℝ :=
  Real.exp (8 / 7 * (8 / 3 * (2 / (L : ℝ)))) * Real.exp (2 * (M.core.cRel * (4 / betaL L) * M.core.ε))

/-- **The constant of the intermediate case.** -/
def eqcCmid (KA KR : ℝ) (n : ℕ) : ℝ :=
  (max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK) * (3 / 2 * (1 + M.rpc11KM M.Kp)) *
      M.eqcKg ^ n + max KR 0 * cw4Cmp M n

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The intermediate case `ms < j_y ≤ N_h` as `C·cddRel·ϑ_{N_h}²`.** -/
theorem eqc_mid (hcab : 0 < M.k2cab) : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
    ∀ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    {r₀ : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1) (hJ : LastJetBd L (M.core.A / 2) r₀)
    {Kt : ℝ}
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
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2)
    (hspl : SplitSmall R.P L R.ρ) (hm0' : 0 < m) (hmL : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (x y : Lam 2 L N) (hx : y ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    {ms r : ℕ} (hk0 : 0 < ms) (hmx : ms < Obs.coal L (0 : Lam 2 L N) x)
    (hmy : ms < Obs.coal L (0 : Lam 2 L N) y)
    (hrk : r ≤ ms) (hblk : blk ms (y - x) = blk ms (0 : Lam 2 L N))
    (hdist : supNorm (y - x) ≤ L ^ (ms - r))
    (hs0 : 0 ≤ M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms))
    (hs : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 + zA L m ms) ≤ 1 / 2)
    (hreg : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 ^ 3) ≤ 1)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) *
      2) ≤ 1 / 1344),
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤
        histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r) ∧
    ∀ {vT wT kxT w2 k2 m0 Q₀ mm k₁ c₁ : ℝ} (hvT : 1 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) ≤ vT)
    (hwT : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) +  (7 / 30) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + w2 ≤ wT)
    (hkxT : (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2) ≤ kxT)
    (hw2 : 0 ≤ w2) (hk2 : 0 ≤ k2)
    -- route (c): the per-scale sizes `m_j = k2Mj … Q j`, the datum's own `ab` activity, waiting
    (hQ0 : 0 ≤ Q₀)
    (hQw : (7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q₀)
    (hQk : (7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q₀)
    (hwait : (8 / 15) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) *
      zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) (Obs.coal L (0 : Lam 2 L N) y) Nh Q₀ ≤ 1)
    (hw2e : Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 +
        (2 * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y)) ^ 2))) - 1 ≤ w2)
    (hk2e : M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) *
      k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y) ^ 2 ≤ k2)
    (hsmT : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1 ^ 3 + kxT + k2) ≤ 1)
    (hm0 : 0 < m0) (h8w : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * m0))
    (h8t : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * m0))
    (h8v : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁v * ((4 * C₁v + 1) * m0))
    (h8m : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁m * ((4 * C₁m + 1) * m0))
    (Cδ : ℕ) (hδ : N ≤ Obs.coal L (0 : Lam 2 L N) y + Cδ)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ m0 Cδ) + (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ m0 Cδ) + 8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ m0 Cδ)) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    -- the `a`-sizes at `N_h` (decayed transients) and the window of `na_lastA_le`
    (hc₁ : 0 ≤ c₁) (hmm1 : 1 ≤ mm)
    (hmmW : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) +
        (7 / 30) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * mm)
    (hrm : (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ mm)
    (hk1 : (56 / 75) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
          (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
        8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 ≤ k₁)
    (hk₁ : k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm)
    (hkt : 8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀)
    (hmAa : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm + 8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1),
    |Pconn L N (1 / b) x - Pconn L N (1 / b) y| ≤
      M.eqcCmid (M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀)
          (M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ) (Nh - Obs.coal L (0 : Lam 2 L N) y) *
        M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
          (R.withMsq m).A r * varthJ R m b (b - m) Nh ^ 2 := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.fin_T6_mid hcab
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj ms r hk0 hmx hmy hrk hblk hdist hs0 hs hreg hg
  obtain ⟨-, h0, -, -, -, -, -, -, -, -, -, -, hM0, -, -, -, -, hrel⟩ := M.pl4_T6_inputs N R hP hi0
    hRℓ hRA hRρ (by omega) Nh hNh m hm b hD hspl hm0' hmL x y hk0 hmx hmy hj hrk hblk hdist hs0 hs
    hreg
  obtain ⟨kk, ww, hkk, hww, hMR, hrest⟩ := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK
    hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj hk0 hmx hmy hrk hblk hdist
    hs0 hs hreg hg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro vT wT kxT w2 k2 m0 Q₀ mm k₁ c₁ hvT hwT hkxT hw2 hk2 hQ0 hQw hQk hwait hw2e hk2e hsmT hm0
    h8w h8t h8v h8m Cδ hδ hmAB hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  have hmain := hrest hvT hwT hkxT hw2 hk2 hQ0 hQw hQk hwait hw2e hk2e hsmT hm0 h8w h8t h8v h8m Cδ
    hδ hmAB hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  have hN2 : 2 ≤ N := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set jy := Obs.coal L (0 : Lam 2 L N) y with hjyd
  set n := Nh - jy with hnd
  set Q := M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
    (R.withMsq m).A r with hQd
  set V := varthJ R m b (b - m) Nh with hVd
  set M₀ := M.pl5M0 R m b x y ms r with hM₀d
  have hrel' : M₀ ≤ Q * ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖ := hrel
  have hM0' : 0 ≤ M₀ := hM0.le
  have hc0 : 0 ≤ M.core.c := by linarith [M.eqc_c_ge R hP hi0 hRℓ hRA hRρ hN2 hNh hm]
  have hε : 0 ≤ M.core.ε := (hD 0 (Nat.zero_le _)).1.le.trans (hD 0 (Nat.zero_le _)).2.1
  have hA0 : 0 ≤ (R.withMsq m).A := (Fact.out : 0 < R.A).le
  have hQ0 : 0 ≤ Q := M.eqc_cddRel_nonneg r hc0 hε (hD ms (by omega)).1.le (zA_nonneg L hm.1.le ms)
    (by unfold rpIota; positivity) hA0
  have hV0 : 0 ≤ V := Real.rpow_nonneg (div_pos hb (hD Nh le_rfl).1).le _
  -- `σ/|β_{a,N_h}| ≤ E_c·Q`
  have hσ := M.eqc_ctSig_rel R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD y (pl2Delta R m b (b - m) x y ms) h0
    (ms := ms) (by omega) (by omega) hQ0 hrel'
  have hq : ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) M₀ / ‖hBeta R m b (b - m) y Nh‖ ≤
      M.eqcEc * Q := by
    rcases (norm_nonneg (hBeta R m b (b - m) y Nh)).eq_or_lt with h | h
    · rw [← h, div_zero]; unfold eqcEc; positivity
    · rw [div_le_iff₀ h]; exact hσ.trans (le_of_eq (by unfold eqcEc; ring))
  have hq0 : 0 ≤ ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) M₀ /
      ‖hBeta R m b (b - m) y Nh‖ :=
    div_nonneg (mul_nonneg hM0' (prod_nonneg fun _ _ => norm_nonneg _)) (norm_nonneg _)
  -- the backward chain
  have hG := M.eqc_nbGB_le R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX y)
    (pl2Delta R m b (b - m) x y ms) h0 hk0 (by omega) hM0' hQ0 hrel' hkk hww hMR
    (jy := jy) hmy.le hj
  have hbT : b * thJ R m b (b - m) Nh ^ 2 ≤ V := by
    have e := b_thJ_sq (hD Nh le_rfl).1 hb
    have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 :=
      (hD Nh le_rfl).2.1.trans M.eps_le
    show b * (((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 / b) ^ (1 / 3 : ℝ)) ^ 2 ≤ V
    rw [e]
    exact mul_le_of_le_one_right hV0 hg1
  have hK0 := M.eqcK_nonneg hc0
  have hG' : M.nbGB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) M₀ kk ww jy ≤
      ((n : ℝ) + 1) * M.eqcK * (Q * V) :=
    hG.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbT hQ0) (by positivity))
  -- `ϑ_{j_y} ≤ K_g^nϑ_{N_h}`
  have hθ := M.eqc_varth_ratio R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (j := jy) hj
  have hK11 := M.rpc11KM_nonneg M.Kp
  have hKg := M.eqcKg_one_le
  set KA := M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
    (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm)
    (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ with hKAd
  set KR := M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ with hKRd
  set q := ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) M₀ / ‖hBeta R m b (b - m) y Nh‖
  set Gb := M.nbGB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) M₀ kk ww jy
  have hEc : 0 ≤ M.eqcEc := by unfold eqcEc; positivity
  -- the first factor
  have hF : KA * q * (3 / 2 * V) + Gb ≤
      (max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK) * (Q * V) := by
    have a1 : KA * q * (3 / 2 * V) ≤ max KA 0 * (M.eqcEc * Q) * (3 / 2 * V) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (le_max_left _ _) hq hq0 (le_max_right _ _))
        (by positivity)
    have e : (max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK) * (Q * V) =
        max KA 0 * (M.eqcEc * Q) * (3 / 2 * V) + ((n : ℝ) + 1) * M.eqcK * (Q * V) := by ring
    rw [e]; linarith
  have hFb0 : 0 ≤ (max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK) * (Q * V) := by
    have := le_max_right KA 0
    positivity
  have hS0 : 0 ≤ 3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) jy :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (div_pos hb (hD jy hj).1).le _)
  have hS : 3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) jy ≤
      3 / 2 * (1 + M.rpc11KM M.Kp) * (M.eqcKg ^ n * V) :=
    mul_le_mul_of_nonneg_left hθ (by positivity)
  have hT1 := (mul_le_mul_of_nonneg_right hF hS0).trans (mul_le_mul_of_nonneg_left hS hFb0)
  have hT2 : max KR 0 * (cw4Cmp M n * Q) * V ^ 2 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ max KR 0 * cw4Cmp M n * Q * V ^ 2 := by
    have hg1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 :=
      (hD Nh le_rfl).2.1.trans M.eps_le
    have : 0 ≤ max KR 0 * (cw4Cmp M n * Q) * V ^ 2 := by
      have := le_max_right KR 0; have := cw4Cmp_pos M n; positivity
    have := mul_le_of_le_one_right this hg1
    linarith
  refine hmain.trans ?_
  have e : M.eqcCmid KA KR n * Q * V ^ 2 =
      (max KA 0 * M.eqcEc * (3 / 2) + ((n : ℝ) + 1) * M.eqcK) * (Q * V) *
        (3 / 2 * (1 + M.rpc11KM M.Kp) * (M.eqcKg ^ n * V)) + max KR 0 * cw4Cmp M n * Q * V ^ 2 := by
    unfold eqcCmid; ring
  rw [e]
  linarith

end MasterFacts

end

end Spin2
