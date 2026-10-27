import Spin2.Cont.ContFx2e
import Spin2.Cont.ContFin1

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), Phase 2, layer 3d: the intermediate case with `Θ*` and the window at `m̄₀`

**`MasterFacts.fx_T6_mid`** (`ms < j_y ≤ N_h`): `fin_T6_mid` (`Spin2/Cont/ContFin1`) on top of
`fx_nb_T6_mid`: `Z_{ab}` discharged by `zabQ`/`zab_Zfix`, `hu0` by the backward chain. Compared with
`fin_T6_mid`:
* `hvT`, `hwT`, `hkxT` carry the constant `Θ* = fxTh` (not `e^c(81/56)^{N_h−j_y}`);
* `hw2e`, `hk2e` carry the constant `m̄ = fxmbar = (c_W + 1)(1 + Θ*) + 1`;
* the window `hmAB` is at `m̄₀` (not at `max(1,2Λ₁)^{C_δ}m̄₀`);
* new `r`-free input `hsmN : K_p(ǧ_{N_h−1} + a_{N_h−1}) ≤ 1/2`;
* the conclusion constant is `fxKT r₀ C₁t Λ₁ Λ₂ m̄₀ C_δ = rpc11K(m̄₀, C_δ)·max(1,2Λ₁)^{C_δ}`.
`C_δ` occurs only in `hδ : N ≤ j_y + C_δ` and in the conclusion. The waiting hypothesis `hwait`
(through `zabQ`, which contains `cw2Thb M N_h ms`) is unchanged.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`fin_T6_mid` with `Θ*`, `m̄` constant and the window at `m̄₀`.** -/
theorem fx_T6_mid (hcab : 0 < M.k2cab) : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    (hsmN : M.Kp * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Nh - 1)).1 + zA L m (Nh - 1)) ≤ 1 / 2)
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
    ∀ {vT wT kxT w2 k2 m0 Q₀ mm k₁ c₁ : ℝ} (hvT : 1 + M.fxTh ≤ vT)
    (hwT : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) +  (7 / 30) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      M.fxTh * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + w2 ≤ wT)
    (hkxT : (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 + M.fxTh * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2) ≤ kxT)
    (hw2 : 0 ≤ w2) (hk2 : 0 ≤ k2)
    -- route (c): the per-scale sizes `m_j = fxMj … Q j`, the datum's own `ab` activity, waiting
    (hQ0 : 0 ≤ Q₀)
    (hQw : (7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q₀)
    (hQk : (7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q₀)
    (hwait : (8 / 15) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) *
      zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) (Obs.coal L (0 : Lam 2 L N) y) Nh Q₀ ≤ 1)
    (hw2e : Real.exp ((L : ℝ) ^ 2 * (M.core.Cw * (M.core.c *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ((Obs.coal L (0 : Lam 2 L N) y) - 1)).1 +
        (2 * M.fxmbar) ^ 2))) - 1 ≤ w2)
    (hk2e : M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) *
      M.fxmbar ^ 2 ≤ k2)
    (hsmT : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1 ^ 3 + kxT + k2) ≤ 1)
    (hm0 : 0 < m0) (h8w : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * m0))
    (h8t : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * m0))
    (h8v : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁v * ((4 * C₁v + 1) * m0))
    (h8m : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁m * ((4 * C₁m + 1) * m0))
    (Cδ : ℕ) (hδ : N ≤ Obs.coal L (0 : Lam 2 L N) y + Cδ)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (m0 + (4 * C₁t + 1) * M.core.c * m0 + 8 * ((4 * C₁t + 1) * m0) + 1) *
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
      (M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ *
          (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) / ‖hBeta R m b (b - m) y Nh‖) *
          (3 / 2 * varthJ R m b (b - m) Nh) +
        M.nbGB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) kk ww (Obs.coal L (0 : Lam 2 L N) y)) *
        (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) y)) +
      max (M.fxKT r₀ C₁t Λ₁ Λ₂ m0 Cδ) 0 *
        (cw4Cmp M (Nh - Obs.coal L (0 : Lam 2 L N) y) *
          M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
            (R.withMsq m).A r) *
        varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.fx_nb_T6_mid
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hsmN hspl hm0' hmL x y hx h1 hj ms r hk0 hmx hmy hrk hblk hdist hs0 hs hreg hg
  obtain ⟨-, h0, -, -, -, -, -, -, -, -, -, -, hM0, -, -, -, -, -⟩ := M.pl4_T6_inputs N R hP hi0
    hRℓ hRA hRρ (by omega) Nh hNh m hm b hD hspl hm0' hmL x y hk0 hmx hmy hj hrk hblk hdist hs0 hs
    hreg
  obtain ⟨kk, ww, hkk, hww, hMR, hrest⟩ := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK
    hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hsmall hsmN hspl hm0' hmL x y hx h1 hj hk0 hmx hmy hrk hblk hdist
    hs0 hs hreg hg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro vT wT kxT w2 k2 m0 Q₀ mm k₁ c₁ hvT hwT hkxT hw2 hk2 hQ0 hQw hQk hwait hw2e hk2e hsmT hm0
    h8w h8t h8v h8m Cδ hδ hmAB hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  have hc2 : 2 ≤ M.core.c := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm
    have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    exact hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hcg : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 :=
    mul_pos (by linarith) (hD ms (by omega)).1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  obtain ⟨hQQ, hQ0', hQz⟩ := zabQ_spec M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r)
    (Obs.coal L (0 : Lam 2 L N) y) Nh hQ0 (mul_pos hcab hcg)
  exact hrest hvT hwT hkxT hw2 hk2 hQ0' (hQw.trans (mul_le_mul_of_nonneg_left hQQ hcg.le))
    (hQk.trans (mul_le_mul_of_nonneg_left hQQ
      (mul_nonneg (mul_nonneg (by norm_num) hBk) (sq_nonneg _))))
    (M.zab_Zfix N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x y hk0 (by omega) hmy.le hj
      hmx hmy h0 hM0) hQz hwait hw2e hk2e hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hc₁ hmm1 hmmW hrm hk1
    hk₁ hkt hmAa

end MasterFacts

end

end Spin2
