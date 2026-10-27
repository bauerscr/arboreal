import Spin2.Cont.ContZab4
import Spin2.Cont.ContK2e

set_option autoImplicit false

/-!
# B3, T6, route (c): `k2_T6_mid` and `k2_conn_diff_top` with `Z_{ab}` discharged

The inputs `hZ`, `hQz` (and the free `Q`, `Z_{ab}`) of `MasterFacts.k2_T6_mid` and
`MasterFacts.k2_conn_diff_top` are removed: `Q` is chosen explicitly,
`Q = zabQ … Q₀ = Q₀ + √(zabZr/(c_{ab}r_{ms}))` (`Spin2/Cont/ContZab4`), where `Q₀` only has to satisfy the
transient conditions `hQw`, `hQk` (unchanged), and `zabZr` is the explicit bound of the datum's own
`ab` activity at `ms` in the fixed weight (`zab_Zfix`):
`zabZr = (7/5)^{J−ms}Θ_b(ms)/M₀·(|β^{(y−x,y)}_{ms}|(c_{ab}r_{ms}(2c_W)² + 4|y−x|_∞L^{−ms}ι_ZA) +
|β^{(0,y)}_{ms}|c_{ab}r_{ms}(2c_W)²)` (`J = j_y`, resp. `J = N_h`).
The waiting hypothesis is stated for this `Q`. New input: `0 < c_{ab}` (`hcab`, the constant of
`kabCond`; needed to divide by `c_{ab}r_{ms}`). `hu0` (resp. the `ε(δ.u_a)` term inside `ctGamB`)
is unchanged.

* **`MasterFacts.k2_T6_midZ`** (`ms < j_y ≤ N_h`);
* **`MasterFacts.k2_conn_diff_topZ`** (`N_h + 1 ≤ j_y`).
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
/-- **`k2_T6_mid` with `hZ`, `hQz` discharged** (`Q = zabQ … Q₀`). -/
theorem k2_T6_midZ (hcab : 0 < M.k2cab) : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    ∀ {vT wT kxT w2 k2 m0 γ₀ Q₀ : ℝ} (hvT : 1 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) ≤ vT)
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
    (hu0 : ‖ε (((pl2Delta R m b (b - m) x y ms).u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γ₀),
    |Pconn L N (1 / b) x - Pconn L N (1 / b) y| ≤
      (γ₀ + pl5Gam M R m b y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) kk ww) *
        (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) y)) +
      max (M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ) 0 *
        (cw4Cmp M (Nh - Obs.coal L (0 : Lam 2 L N) y) *
          M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
            (R.withMsq m).A r) *
        varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1  := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.k2_T6_mid
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj ms r hk0 hmx hmy hrk hblk hdist hs0 hs hreg hg
  obtain ⟨-, h0, -, -, -, -, -, -, -, -, -, -, hM0, -, -, -, -, -⟩ := M.pl4_T6_inputs N R hP hi0
    hRℓ hRA hRρ (by omega) Nh hNh m hm b hD hspl hm0' hmL x y hk0 hmx hmy hj hrk hblk hdist hs0 hs
    hreg
  obtain ⟨kk, ww, hkk, hww, hMR, hrest⟩ := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK
    hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj hk0 hmx hmy hrk hblk hdist
    hs0 hs hreg hg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro vT wT kxT w2 k2 m0 γ₀ Q₀ hvT hwT hkxT hw2 hk2 hQ0 hQw hQk hwait hw2e hk2e hsmT hm0 h8w h8t
    h8v h8m Cδ hδ hmAB hu0
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
      hmx hmy h0 hM0) hQz hwait hw2e hk2e hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hu0

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`k2_conn_diff_top` with `hZ`, `hQz` discharged** (`Q = zabQ … Q₀`, `J = N_h`). -/
theorem k2_conn_diff_topZ {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (hgms : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) * 2) ≤ 1 / 1344) (hcab : 0 < M.k2cab) :
    ∃ kk ww : ℝ, 0 ≤ kk ∧ 0 ≤ ww ∧
      1344 * (8 * (PtCorr2.csN 2 : ℝ) * kk + M.core.rdtΓ * ww) ≤ histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r) ∧
    ∀ {mm k₁ c₁ k2 Q₀ : ℝ}, 0 ≤ c₁ → 0 ≤ k2 →
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
      0 ≤ Q₀ →
      (7 / 5) ^ (Nh - ms) * (ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤ M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 * Q₀ →
      (7 / 5) ^ (Nh - ms) * ((kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r))) ≤
        8 * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1) ^ 2 * Q₀ →
      (8 / 15) ^ (Nh - ms) * zabQ M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) Nh Nh Q₀ ≤ 1 →
      M.k2cab / 5 * ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * k2mbar M Nh Nh ^ 2) ≤ k2 →
      M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
        M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1 →
      2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        (8 * (2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      ‖((Pconn L N (1 / b) x : ℝ) : ℂ) - ((Pconn L N (1 / b) y : ℝ) : ℂ)‖ ≤
        3 / 2 * (1 + M.fwKO) * M.ctGamB R m b (b - m) Nh (ptsX y) ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) kk ww *
            varthJ R m b (b - m) Nh +
          9 / 4 * max (M.rpKE ((2 * rpIota (M.ctVT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1))
            (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) * M.core.A) ^ (L ^ 2)) r₀) 0 *
            (cw4Cmp M 0 * M.cddRel M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms) (rpIota 0 0)
              (R.withMsq m).A r) * varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1  := by
  have hN2 : 2 ≤ N := by omega
  obtain ⟨-, h0, -, -, -, -, -, -, -, -, -, -, -, -, hM0, -, -, -, -, -⟩ := M.ct_T6_inputs_top N R
    hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD hspl x y hk0 hkN hmx hj hrk hblk hdist hsc0 hsc hreg
  obtain ⟨kk, ww, hkk, hww, hMR, hrest⟩ := M.k2_conn_diff_top R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD
    hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5 hvb hwb hsmall y hy hj hspl x hk0 hkN hmx
    hrk hblk hdist hsc0 hsc hreg hgms
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro mm k₁ c₁ k2 Q₀ hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hQ0 hQw hQk hwait hk2e hsmT hmAB
  have hc2 : 2 ≤ M.core.c := by
    obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
      rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
    exact hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hcg : 0 < M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 :=
    mul_pos (by linarith) (hD ms (by omega)).1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  obtain ⟨hQQ, hQ0', hQz⟩ := zabQ_spec M R m b (b - m) x y ms (M.pl5M0 R m b x y ms r) Nh Nh hQ0
    (mul_pos hcab hcg)
  exact hrest hc₁ hk2 hmmV hmmW hrm hk1 hk₁ hkt hQ0' (hQw.trans (mul_le_mul_of_nonneg_left hQQ hcg.le))
    (hQk.trans (mul_le_mul_of_nonneg_left hQQ
      (mul_nonneg (mul_nonneg (by norm_num) hBk) (sq_nonneg _))))
    (M.zab_Zfix N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x y hk0 hkN hkN.le le_rfl
      hmx (by omega) h0 hM0) hQz hwait hk2e hsmT hmAB

end MasterFacts

end

end Spin2
