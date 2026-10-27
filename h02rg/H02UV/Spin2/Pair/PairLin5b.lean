import Spin2.Pair.PairLin5

set_option autoImplicit false

/-!
# B3, T6 (Task 4, reduction): `|P(x) − P(y)|` for intermediate coalescence `ms < j_y ≤ N_h`

**`MasterFacts.pl5_T6_mid`** (exact; `h = 0`, trajectory `(b, b − m)` in `D_ε`): the constants
`C₁w C₁t C₁v C₁m Λ₁ Λ₂` of `cw3_T5R`; for every `x, y` with `0 < ms < j_x`, `ms < j_y ≤ N_h`,
`1 ≤ j_y`, `y − x` and `0` in one `ms`-block, `|y − x|_∞ ≤ L^{ms−r}`, `r ≤ ms`, and the scale
conditions at `ms`, there are transients `kk, ww ≥ 0` with `1344(8c_Nkk + Γ_w ww) ≤ s_{ms}²M₀`
(`M₀ = pl5M0 = cddM`, `δ = pl2Delta`) such that, for all size constants satisfying the scalar
conditions of `cw3_T5R` (with `x := y`, `m_r := ms`, `k := kk`, `w := ww`), the `σ_aσ_b`
inputs `w₂`, `k₂` at `j_y` and `‖ε(δ.u_a)‖ ≤ γ₀`:

`|P(x) − P(y)| ≤ (γ₀ + pl5Gam(kk, ww))·(3/2)(1 + K_M)ϑ_{j_y}
   + max(K, 0)·cw4Cmp(N_h − j_y)·cddRel(K_p, ǧ_{ms}, a_{ms}, rpIota 0 0, A, r)·ϑ_{N_h}²ǧ_{N_h}`.

Discharged: the exact identity, all datum hypotheses, the restart data (`pl4_T6_inputs`), the
comparison `σ/|β_{a,N_h}|` (`cw4_sig_rel`), the chain part of `γ_δ` (`pl5_gam_jy`).
Open inputs (hypotheses): `hW2`, `hK2` (the `σ_aσ_b` sizes at `j_y`), `hu0` (the initial
`ε(δ.u_a)`), and the scalar conditions.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs FRD Flow2 Flow2.Hist Obs2 Step2.D2

variable {L : ℕ} [NeZero L]

/-- The restart envelope of the pair-difference datum (`cddM`, `pl4_T6_inputs`). -/
def MasterFacts.pl5M0 (M : MasterFacts L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (m b : ℝ) (x y : Lam 2 L N) (ms r : ℕ) : ℝ :=
  M.cddM M.Kp (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) ms).1 (zA L m ms)
    ‖bt2 R (pl2Pts x y) (zV0 b) m b (b - m) ms‖ ‖bt2 R (ptsX y) (zV0 b) m b (b - m) ms‖
    (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (rpIota 0 0)
    (R.withMsq m).A r

namespace MasterFacts

variable (M : MasterFacts L)

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`|P(x) − P(y)|` for intermediate coalescence, reduced to the open inputs.** -/
theorem pl5_T6_mid : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    ∀ {vT wT kxT w2 k2 m0 γ₀ : ℝ} (hvT : 1 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) ≤ vT)
    (hwT : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) +  ww / (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r)) +
      (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1)) + w2 ≤ wT)
    (hkxT : (kk + 120 * M.core.Bk * (M.core.c * M.core.ε) * ww) /
        (histS (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (M.pl5M0 R m b x y ms r)) +
      8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) y)) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) y)).1) ^ 2) ≤ kxT)
    (hw2 : 0 ≤ w2) (hk2 : 0 ≤ k2)
    -- the `σ_aσ_b` parts at `j_x` (open inputs)
    (hW2 : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) y),
      (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r))) (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) y) (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).W q : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal w2)
    (hK2 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) y) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) y) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r))) (pM (R.withMsq m) (ptsS y) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab * Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) y)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) y)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2)
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
        varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.cw3_T5R
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall hspl hm0' hmL x y hx h1 hj ms r hk0 hmx hmy hrk hblk hdist hs0 hs hreg hg
  obtain ⟨hid, h0, hl0, hs0', hVab, hf0, hp0, hδb, kk, ww, hkk, hww, hM0, hbR, hWR, hKR, hMR,
    hrel⟩ := M.pl4_T6_inputs N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b hD hspl hm0' hmL x y
      hk0 hmx hmy hj hrk hblk hdist hs0 hs hreg
  refine ⟨kk, ww, hkk, hww, hMR, ?_⟩
  intro vT wT kxT w2 k2 m0 γ₀ hvT hwT hkxT hw2 hk2 hW2 hK2 hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hu0
  have hgam := M.pl5_gam_jy N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b hD y hj hk0 hmy.le _
    h0 hl0 hs0' hf0 hp0 hM0 hkk hww hbR hWR hKR hg hMR
  have hu : ‖ε (((cw2O R m b y ms (pl2Delta R m b (b - m) x y ms)).u :
      Obs.SA .two (Lam 2 L N)).a)‖ ≤
      γ₀ + pl5Gam M R m b y ms (pl2Delta R m b (b - m) x y ms) (M.pl5M0 R m b x y ms r) kk ww :=
    hgam.trans (add_le_add hu0 (le_of_eq rfl))
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
