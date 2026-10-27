import Spin2.Cont.ContK2d
import Spin2.Cont.ContNb8

set_option autoImplicit false

/-!
# B3, T6: the intermediate-coalescence bound `ms < j_y ≤ N_h` without `hu0`

**`MasterFacts.nb_T6_mid`**: `k2_T6_mid` with the open input `hu0` (the initial `ε(δ.u_a)`, which
is `≍ |β| log N` by the grid artefacts) removed. The accumulated `a`-constant at `j_y` is bounded
through the `h = 0` identity at `N_h + 1` and a backward chain:

  `|ε(u^δ_{j_y,a})| ≤ |n_a(lastOF_{N_h+1}(δ_{N_h+1}))| + nbGB`
    `≤ K_A^{na}(ctVT r, w_T, k_{xT})·(σ/|β_{a,N_h}|)·(3/2)ϑ_{N_h} + nbGB`

(`nb_eps_jy`: `na_rpTopU_eq` for any `y`, `nb_naMid` with `a`-only sizes and `nb_ref_zm`,
`nb_gam_back_top`).
In the conclusion `γ₀ + pl5Gam` is replaced by this bound; the forward chain from `ms` (`pl5Gam`)
and `ε(δ.u_a)` no longer occur. New inputs: the `a`-size constants `mm`, `k₁`, `c₁` at `N_h` with
the decayed transient conditions (`hmm1`, `hmmW`, `hrm`, `hk1`, `hk₁`, `hkt`) and the window
`hmAa`. `Q`, `Z_{ab}` (`hZ`, `hQz`) stay hypotheses.
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
/-- **`k2_T6_mid` without `hu0`**: the accumulated `a`-constant at `j_y` from the `h = 0` identity at
`N_h + 1` (`na_rpTopU_eq`, `nb_naMid`) and the backward chain (`nb_gam_back_top`). -/
theorem nb_T6_mid : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    ∀ {vT wT kxT w2 k2 m0 Q Zab mm k₁ c₁ : ℝ} (hvT : 1 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) ≤ vT)
    (hwT : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) +  (7 / 30) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + w2 ≤ wT)
    (hkxT : (56 / 75) ^ (Obs.coal L (0 : Lam 2 L N) y - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) +
      8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2) ≤ kxT)
    (hw2 : 0 ≤ w2) (hk2 : 0 ≤ k2)
    -- route (c): the per-scale sizes `m_j = k2Mj … Q j`, the datum's own `ab` activity, waiting
    (hQ0 : 0 ≤ Q)
    (hQw : (7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q)
    (hQk : (7 / 5) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
      8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q)
    (hZ : ∀ X, IsConn ms X → ENNReal.ofReal ((R.withMsq m).A ^ (nb ms X - 2 ^ 2)) *
      ((wM (k2Ma R m b (b - m) y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) (Obs.coal L (0 : Lam 2 L N) y))
          (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) ms (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((pl2Delta R m b (b - m) x y ms).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal Zab)
    (hQz : Zab ≤ M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * Q ^ 2)
    (hwait : (8 / 15) ^ ((Obs.coal L (0 : Lam 2 L N) y) - ms) * Q ≤ 1)
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
      (M.naKA (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ *
          (ctSig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) / ‖hBeta R m b (b - m) y Nh‖) *
          (3 / 2 * varthJ R m b (b - m) Nh) +
        M.nbGB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) kk ww (Obs.coal L (0 : Lam 2 L N) y)) *
        (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) y)) +
      max (M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ) 0 *
        (cw4Cmp M (Nh - Obs.coal L (0 : Lam 2 L N) y) *
          M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
            (R.withMsq m).A r) *
        varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.art_T5RD
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj ms r hk0 hmx hmy hrk hblk hdist hs0 hs hreg hg
  obtain ⟨hid, h0, hl0, hs0', hVab, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR, hKR, hMR,
    hrel⟩ := M.pl4_T6_inputs N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b hD hspl hm0' hmL x y
      hk0 hmx hmy hj hrk hblk hdist hs0 hs hreg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro vT wT kxT w2 k2 m0 Q Zab mm k₁ c₁ hvT hwT hkxT hw2 hk2 hQ0 hQw hQk hZ hQz hwait hw2e hk2e hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB
    hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  obtain ⟨hKab, hWab⟩ := M.k2_mid N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x y hk0
    hblk hmx hmy hj h0 hl0 hs0' hf0 hp0 hδb hM0 hkk hww hbR hWR hKR hg hMR hQ0 hQw hQk hZ hQz
  have hsN : histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ≠ 0 := by
    obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
    refine (histS_pos' (R.withMsq m) ?_ ?_ _ Nh).ne'
    · rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
    · rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hMaE : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
      cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) =
      k2Ma R m b (b - m) y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r)
        (Obs.coal L (0 : Lam 2 L N) y) := by
    unfold cw2Sig cw2Env k2Ma k2Env; field_simp
  obtain ⟨hw1, hw2'⟩ := k2_wait M Nh (Obs.coal L (0 : Lam 2 L N) y) ms hQ0 hmy hj hwait
  have hW2 : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) y),
      (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r))) (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) y) (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).W q : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal w2 := by
    intro q hq
    rw [hMaE]
    refine (hWab q hq).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hw2e))
    have hm0' := k2Mj_pos M Nh (Obs.coal L (0 : Lam 2 L N) y) ms hQ0 (Obs.coal L (0 : Lam 2 L N) y - 1)
    have h2 : k2Mj M Nh (Obs.coal L (0 : Lam 2 L N) y) ms Q (Obs.coal L (0 : Lam 2 L N) y - 1) ^ 2 ≤
        (2 * k2mbar M Nh (Obs.coal L (0 : Lam 2 L N) y)) ^ 2 := pow_le_pow_left₀ hm0'.le hw2' 2
    have hCw := M.core.hCw
    have := mul_le_mul_of_nonneg_left h2 hCw
    gcongr
  have hK2 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) y) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) y) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r))) (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab * Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) y)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) y)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2 := by
    intro X hX
    rw [hMaE]
    refine (hKab X hX).trans (ENNReal.ofReal_le_ofReal (le_trans ?_ hk2e))
    have hm0' := k2Mj_pos M Nh (Obs.coal L (0 : Lam 2 L N) y) ms hQ0 (Obs.coal L (0 : Lam 2 L N) y)
    have hc0 : 0 ≤ M.k2cab * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) := by
      have := (hD (Obs.coal L (0 : Lam 2 L N) y) hj).1.le
      have := M.k2cab_nonneg
      have : (0 : ℝ) ≤ M.core.c := by
        obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm
        have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
          rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
        have := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
        linarith
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hm0'.le hw1 2) hc0
  have hu := M.nb_eps_jy R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl x y h1 hk0 (by omega) hblk hmy hj h0 hl0 hs0' hf0 hp0 hM0 hkk hww hbR
    hWR hKR hg hMR hc₁ hmm1 hmmW hrm hk1 hk₁ hkt hmAa
  have hT' := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4
    hs5 hsmall y hx h1 hj hk0 hmy.le _ h0 hl0 hs0' hVab hf0 hp0 hδb hM0 hkk hww hbR hWR hKR hg hMR
    hvT hwT hkxT hw2 hk2 hW2 hK2 hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hu
  have hσ := M.cw4_sig_rel N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b hD hspl hm0' hmL x y
    hk0 hmx hmy hj hrk hblk hdist hs0 hs hreg
  have hlhs : |Pconn L N (1 / b) x - Pconn L N (1 / b) y| =
      ‖rpcOut R m b (b - m) y (cw2O R m b y ms (pl2Delta R m b (b - m) x y ms))‖ := by
    rw [← hid, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hlhs]
  refine hT'.trans (add_le_add le_rfl ?_)
  have hσ0 : 0 ≤ cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) := by
    unfold cw2Sig cw2Env rkEnv
    exact div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hM0.le
      (prod_nonneg fun _ _ => norm_nonneg _))) (sq_nonneg _)
  have hq0 : 0 ≤ cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) /
      ‖hBeta R m b (b - m) y Nh‖ := div_nonneg hσ0 (norm_nonneg _)
  have hgN : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := (hD Nh le_rfl).1.le
  have ha : 0 ≤ varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 :=
    mul_nonneg (sq_nonneg _) hgN
  set K := M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ
  set q := cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) /
      ‖hBeta R m b (b - m) y Nh‖
  set Q := cw4Cmp M (Nh - Obs.coal L (0 : Lam 2 L N) y) *
    M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
      (R.withMsq m).A r
  set a := varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1
  have h1 : K * q ≤ max K 0 * Q :=
    (mul_le_mul_of_nonneg_right (le_max_left K 0) hq0).trans
      (mul_le_mul_of_nonneg_left hσ (le_max_right K 0))
  calc K * q * varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1
      = K * q * a := by ring
    _ ≤ max K 0 * Q * a := mul_le_mul_of_nonneg_right h1 ha
    _ = _ := by ring

end MasterFacts

end

end Spin2
