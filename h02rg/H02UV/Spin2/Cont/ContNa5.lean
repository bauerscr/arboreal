import Spin2.Cont.ContTop3
import Spin2.Cont.ContNa4

set_option autoImplicit false

/-!
# Top coalescence: the relaxed `rptf_top_traj` with `γ_δ` from the `h = 0` identity

**`MasterFacts.na_top_trajR`**: `MasterFacts.ct_top_trajR` (the restarted state
`o = obsHistFrom … ms δ (N_h+1)` with the sizes at `N_h + 1` built from the restart sizes at `N_h`)
with the final call `rp_top_traj` replaced by `na_top_traj`: the accumulated `a`-constant is not
bounded by the chain `rptfGam` (which contains the initial `ε(δ.u_a)`), but through the identity
`ε(u^o_a) = n_a(lastOF_{N_h+1}(o))` (hypothesis `hid`) and `na_lastA_le`. Extra input: the window
`hmAa` with `c_S = v_T + w_T + 8k_{xT} + 1` (the sizes `rptfVT`, `rptfWT`, `rptfKx` at `N_h + 1`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 16000000 in
/-- **`rptf_top_traj` with `V_{ab} = 0` at `N_h + 1` in place of `ObsCoalInv`** (its only use;
for the relaxed coalescence invariant of the pair-difference datum). -/
theorem na_top_trajR {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (x : Lam 2 L N) (hx : x ≠ 0) (hj : Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    -- the restart datum at `ms ≤ N_h` (reference `b`-part)
    {ms : ℕ} (hms : ms ≤ Nh) (δ : Obs2.ObsSt .two L N) (hδ : δ.IsObs)
    (hδl : ObsLocInv (ptsX x) ms δ) (hδs : ObsSymInv ms δ)
    (hδc : ∀ q, ((obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q : SA .two (Lam 2 L N)).ab = 0)
    (hδf : ∀ q, Obs2.Loc2Form (ptsX x).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      mass2 (δ.V q : SA .two (Lam 2 L N)).a • pbp (ptsX x).a)
    (hδb : Obs2.prjSt false δ = Obs2.prjSt false (Obs2.obsHist (R.withMsq m) (ptsX x)
      (Obs2.obsInit .two (zV b) (ptsX x)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))))
    -- the envelope and the restart sizes at `N_h` in `w = wM(2s_{N_h}²σ, M_b)`
    {σ mm k₁ c₁ aN bD e k2 : ℝ} (hσ : 0 < σ) (hmm0 : 0 < mm) (hc₁ : 0 ≤ c₁) (hk2 : 0 ≤ k2)
    (hrm : M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ mm)
    (hk₁ : k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm)
    (hk₁0 : 0 ≤ k₁)
    (hkt : 8 * (cx M.core.κ M.core.cT + c₁) *
      (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀)
    (hVo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))
        Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q) ≤ ENNReal.ofReal mm)
    (hWo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))
        Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q) ≤
        ENNReal.ofReal (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 * mm))
    (hK1 : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      Obs2.oTo (wM1 (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))
        Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX x) ms δ Nh
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X) ≤ ENNReal.ofReal k₁)
    (haN : ‖1 - Obs2.frakN2F (ptsX x) (Obs2.histCovO (R.withMsq m)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh‖ ≤
        aN)
    (hbD : ‖Obs2.betaTot2 (L := L) (N := N) Nh
        (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)‖ +
      Obs2.shareDev2 (ptsX x).a Nh
        (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) ≤ bD)
    (he : Obs2.shareErrL1_2F (ptsX x) (Obs2.histCovO (R.withMsq m)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histWF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histKF2 (R.withMsq m) (ptsX x) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh ≤ e)
    -- the `ab` part at `N_h + 1` (`rpab_top`)
    (hK2 : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)
          (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Nh + 1) (histS (R.withMsq m) (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X : Obs.SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k2)
    -- the smallness conditions of `rp_top_traj` with these sizes
    (hsmT : M.core.A ^ 4 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ^ 3 +
      M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + k2) ≤ 1)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (8 * (2 * rpIota (rptfVT aN bD e σ)
        (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
          M.core.A) ^ (L ^ 2) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    -- the `h = 0` identity for the restarted state and the window of `na_lastA_le`
    (hid : ε (((obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).u : Obs.SA .two (Lam 2 L N)).a) =
      PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX x) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) Nh
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))))
    (hmAa : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (rptfVT aN bD e σ + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm +
        8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖rpTopOut R Nh m b (b - m) x
        (obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))‖ ≤
      3 / 2 * (1 + M.fwKO) *
          (M.naKA (rptfVT aN bD e σ)
              (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm)
              (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁)
              r₀ * (σ / ‖hBeta R m b (b - m) x Nh‖) * (3 / 2 * varthJ R m b (b - m) Nh)) *
            varthJ R m b (b - m) Nh +
        9 / 4 * M.rpKE ((2 * rpIota (rptfVT aN bD e σ)
          (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) *
            M.core.A) ^ (L ^ 2)) r₀ *
          (σ / ‖hBeta R m b (b - m) x Nh‖) * varthJ R m b (b - m) Nh ^ 2 *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hε1 := M.eps_le
  have hF := M.flow
  have hN2 : 2 ≤ N := by omega
  have hNh1 : 1 ≤ Nh := by omega
  set μ₀ := b - m with hμ₀
  set R' := R.withMsq m with hR'
  set t : Hist.Seq (Xs R') := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hval : ∀ j < Nh, ValidAt R' j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL R' Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8, -, -⟩ := hF
  have hρ0' : 0 ≤ R'.ρ := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8' : R'.ρ ≤ 1 / 8 := by rw [show R'.ρ = M.core.ρ from hRρ]; exact hρ8
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have ht := inDh_rg_of_D R' F1 hD Nh le_rfl
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x M.core.CDx
      M.core.Cqx M.core.Clx M.core.cSx := by
    rw [show R'.A = M.core.A from hRA]; exact M.core.hSBx
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hc2 : 2 ≤ M.core.c := hcR ▸ two_le_cR R' H.hcmu H.hC₂
  have hβ2 := betaL_ge (by omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have hmN : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    show |m| * _ ≤ 1
    rw [abs_of_pos hm.1]
    have h1 := PtCorr2.msq_mul_pow_le_one (L := L) (N := N) (by omega) (by omega) hm.2
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have h2 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * (N - 1)) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    exact (mul_le_mul_of_nonneg_left h2 hm.1.le).trans h1
  have hg0 : 0 < (t Nh).1 := (hD Nh le_rfl).1
  have hgε : (t Nh).1 ≤ M.core.ε := (hD Nh le_rfl).2.1
  set r := M.core.c * (t Nh).1 with hrd
  have hr0 : 0 ≤ r := mul_nonneg (by linarith) hg0.le
  have hr1 : r ≤ 1 :=
    (mul_le_mul_of_nonneg_left hgε (by linarith)).trans M.core.hcε
  have hrε : r ≤ M.core.ε₀ :=
    (mul_le_mul_of_nonneg_left hgε (by linarith)).trans M.core.hεε
  have hs : 0 < histS R' Nh t := histS_pos' R' hρ0' hρ8' t Nh
  have hsp1 : 0 < histS R' (Nh + 1) t := histS_pos' R' hρ0' hρ8' t (Nh + 1)
  have hss : histS R' (Nh + 1) t ^ 2 ≤ 81 / 64 * histS R' Nh t ^ 2 := by
    have h := histS_succ_le_q R' hρ0' hρ8' t Nh
    have := pow_le_pow_left₀ hsp1.le h 2
    exact this.trans (le_of_eq (by ring))
  have ht0 : (t 0).2.2 = 0 := traj_zero_X R m b μ₀
  set o₀ := Obs2.obsInit .two (zV b) (ptsX x) with ho₀d
  have ho₀ : o₀.IsObs := Obs2.obsInit_isObs .two (zV b) (ptsX x)
  set o := obsHistFrom R' (ptsX x) ms δ (Nh + 1) t with hod
  set Ma := 2 * histS R' Nh t ^ 2 * σ with hMad
  set Mb := pM R' (ptsS x) (zV0 b) t Nh with hMbd
  have hMa : 0 < Ma := by positivity
  obtain ⟨-, hMb, -⟩ := hseed x hx hj
  -- the invariants
  obtain ⟨ho, hlo, -⟩ := rpb_inv_top R' (ptsX x) hval hvalL hδ hδl hδs t (j := Nh + 1) (by omega)
    le_rfl
  -- `V` at `N_h + 1`
  have hcN : Nh + 1 < N := by omega
  obtain ⟨-, hA1⟩ := rptf_beta_shA2 R' (ptsX x) ms δ t hδf (j := Nh) hms hcN
  have hD0 : 0 ≤ Obs2.shareDev2 (ptsX x).a Nh (histVF2 R' (ptsX x) ms δ t Nh) :=
    sum_nonneg fun _ _ => norm_nonneg _
  have hbD0 : 0 ≤ bD := (add_nonneg (norm_nonneg _) hD0).trans hbD
  have hE0 : 0 ≤ Obs2.shareErrL1_2F (ptsX x) (Obs2.histCovO R' t) (histVF2 R' (ptsX x) ms δ t)
      (histWF2 R' (ptsX x) ms δ t) (histKF2 R' (ptsX x) ms δ t) ms Nh :=
    sum_nonneg fun _ _ => norm_nonneg _
  have he0 : 0 ≤ e := hE0.trans he
  have haN0 : 0 ≤ aN := (norm_nonneg _).trans haN
  have hA2 : Obs2.shA2 (histVF2 R' (ptsX x) ms δ t) (Nh + 1) ≤ aN * bD + 3 * e := by
    refine hA1.trans ?_
    have h1 := mul_le_mul haN hbD (add_nonneg (norm_nonneg _) hD0) haN0
    linarith
  have htS := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x)).1
  have hl1S := M.lastL1D N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x)
    (htS.1.trans (by norm_num))
  have hβS : ‖bt2 R (ptsS x) (zV b) m b μ₀ (Nh + 1)‖ ≤ 81 / 64 * ‖bt2 R (ptsS x) (zV b) m b μ₀ Nh‖ := by
    rw [bt2_flow R (ptsS x) (zV b) (Nh := Nh + 1) (by omega) m b μ₀ (k := Nh) (by omega)]
    exact beta_step_le htS.1 htS.2
  have hMbE := pM_eq_bt2G R' t ht0 b (ptsS x) hNh1
  have hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM Ma Mb) (Nh + 1) (histS R' (Nh + 1) t) (o.V q) ≤
        ENNReal.ofReal (rptfVT aN bD e σ) := by
    intro q hq
    have hVab := hδc q
    have ha : Tj 2 (L : ℝ) (Nh + 1) (histS R' (Nh + 1) t) (o.V q : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (81 / 64 * histS R' Nh t ^ 2 * (aN * bD + 3 * e)) := by
      refine (rptf_vobs_block R' (ptsX x) ms δ t hδf hδp (j := Nh + 1) (by omega) hsp1 q hq).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have h0 : 0 ≤ Obs2.shA2 (histVF2 R' (ptsX x) ms δ t) (Nh + 1) :=
        sum_nonneg fun _ _ => norm_nonneg _
      calc histS R' (Nh + 1) t ^ 2 * Obs2.shA2 (histVF2 R' (ptsX x) ms δ t) (Nh + 1)
          ≤ (81 / 64 * histS R' Nh t ^ 2) * (aN * bD + 3 * e) :=
            mul_le_mul hss hA2 h0 (by positivity)
        _ = 81 / 64 * histS R' Nh t ^ 2 * (aN * bD + 3 * e) := by ring
    have hb : Tj 2 (L : ℝ) (Nh + 1) (histS R' (Nh + 1) t) (o.V q : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (3 / 2 * (81 / 64) ^ 2 * Mb) := by
      rw [(rpb_b_eq R' (ptsX x) o₀ δ t hδb (k := Nh + 1) (by omega)).1 q,
        (mirror_zV_cmpG R' t ht0 b x (j := Nh + 1) (by omega)).1 q, ← Obs2.oTo_wA]
      refine (vobs2_block_le' R' (ptsS x) (zV b) t ht0 (by omega) hsp1 q hq).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have h0 : 0 ≤ ‖Obs2.betaTot2 (L := L) (N := N) Nh
          (Obs2.histVO2 R' (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) t Nh)‖ := norm_nonneg _
      rw [hMbd, hMbE]
      have hl : Obs2.shA2 (Obs2.histVO2 R' (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) t) (Nh + 1) ≤
          3 * (81 / 64 * ‖Obs2.betaTot2 (L := L) (N := N) Nh
            (Obs2.histVO2 R' (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) t Nh)‖) := by
        refine hl1S.trans ?_
        have := hβS
        unfold bt2 at this ⊢
        linarith
      calc histS R' (Nh + 1) t ^ 2 *
            Obs2.shA2 (Obs2.histVO2 R' (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) t) (Nh + 1)
          ≤ (81 / 64 * histS R' Nh t ^ 2) * (3 * (81 / 64 * ‖Obs2.betaTot2 (L := L) (N := N) Nh
            (Obs2.histVO2 R' (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x)) t Nh)‖)) :=
            mul_le_mul hss hl (sum_nonneg fun _ _ => norm_nonneg _) (by positivity)
        _ = _ := by ring
    refine (oTo_wM_le_of_ab hMa hMb (Nh + 1) _ _ hVab (by positivity) (by positivity) ha hb).trans
      (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hMad]; unfold rptfVT
    field_simp
    ring
  -- `𝒲` at `N_h + 1`
  have hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (wM Ma Mb) (Nh + 1) (histS R' (Nh + 1) t) (o.W q) ≤
        ENNReal.ofReal (M.rptfWT r mm) := by
    intro q _
    have h := rptf_wfull_stepF R' M.core.hWw hSB' hval hm1 hvalL hmN hβ0 (by norm_num) H
      (ptsX x) (wM Ma Mb) (wM_sub Ma Mb) hms δ hδ hδl hδs t ht mm (by rw [hcR]; exact hrm)
      (by rw [hcR]; exact hr1) hVo (fun q hq => by rw [hcR]; exact hWo q hq) q
    rw [hcR] at h
    exact h
  -- `K` at `N_h + 1` (one-point weights)
  have hKt : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (wM1 Ma Mb) (Nh + 1) (histS R' (Nh + 1) t) (o.K X) ≤
        ENNReal.ofReal (M.rptfKx c₁ r mm k₁) := by
    have hKB' : KObsBounds L R'.A M.core.C₀o M.core.ηo M.core.ε₀ M.core.C₁k := by
      rw [show R'.A = M.core.A from hRA]; exact M.core.hKB
    have hcx : 0 ≤ cx M.core.κ M.core.cT := H.hcx
    have hk₁' : k₁ ≤ c₁ * r ^ 2 * mm := hk₁
    have hkt₀ : 8 * (cx M.core.κ M.core.cT + c₁) * r ^ 3 ≤ M.core.ε₀ := hkt
    have hk8 : 8 * k₁ ≤ 8 * c₁ * (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t Nh).1) ^ 2 * mm := by
      rw [hcR, ← hrd]; linarith
    have hkt' : 8 * cx M.core.κ M.core.cT * (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t Nh).1) ^ 3 +
        cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t Nh).1 / mm * (8 * k₁) ≤ M.core.ε₀ := by
      rw [hcR, ← hrd]
      have h1 : r / mm * (8 * k₁) ≤ 8 * c₁ * r ^ 3 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hmm0]
        have := mul_le_mul_of_nonneg_left hk₁' (by linarith : (0 : ℝ) ≤ 8 * r)
        calc r * (8 * k₁) = 8 * r * k₁ := by ring
          _ ≤ 8 * r * (c₁ * r ^ 2 * mm) := this
          _ = 8 * c₁ * r ^ 3 * mm := by ring
      linarith
    have hWo' : ∀ q ∈ blockIdx (L := L) (N := N) Nh, Obs2.oTo (wM Ma Mb) Nh (histS R' Nh t)
        ((obsHistFrom R' (ptsX x) ms δ Nh t).W q) ≤
          ENNReal.ofReal (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t Nh).1 * mm) := by
      rw [hcR]; exact hWo
    have h := rptf_kobs_stepF R' hKB' hSB' hval hm1 hvalL hmN hβ0 (by norm_num) H (ptsX x)
      (wM1 Ma Mb) rfl ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hms δ hδ hδl hδs t ht (8 * c₁) mm
      k₁ (by positivity) hmm0 hk₁0 (by rw [hcR]; exact hr1) (by rw [hcR]; exact hrε) hk8 hkt'
      (fun q hq => (Obs2.oTo_one_le _ _ _ _).trans (hVo q hq))
      (fun q hq => (Obs2.oTo_one_le _ _ _ _).trans (hWo' q hq)) hK1
    intro X hX
    have h' := h X hX
    rw [hcR, show R'.A = M.core.A from hRA] at h'
    rw [hRA]
    exact h'
  -- nonnegativity
  have hvT : 0 ≤ rptfVT aN bD e σ := by unfold rptfVT; positivity
  have hwT : 0 ≤ M.rptfWT r mm := by
    unfold rptfWT
    have := M.core.hCw
    have : 0 ≤ (L : ℝ) ^ 2 * (M.core.Cw * (r + mm ^ 2)) := by positivity
    linarith [Real.add_one_le_exp ((L : ℝ) ^ 2 * (M.core.Cw * (r + mm ^ 2)))]
  have hkxT : 0 ≤ M.rptfKx c₁ r mm k₁ := by
    unfold rptfKx kB
    have hcx : 0 ≤ cx M.core.κ M.core.cT := H.hcx
    have hA0 : (0 : ℝ) ≤ M.core.A / 2 := by
      have : 0 < R.A := Fact.out; rw [hRA] at this; positivity
    have hθ0 : 0 ≤ kθ0 L M.core.A M.core.C₀o M.core.ηo := by
      unfold kθ0; have := Real.rpow_nonneg hA0 (-M.core.ηo); have := M.core.hC₀o; positivity
    have := M.core.hC₁k
    positivity
  exact M.na_top_traj R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hseed hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hvb hwb hsmall x hx hj o ho hlo hσ hvT hwT hkxT hk2 hVt hWt hKt hK2 hsmT hmAB hid hmAa

end MasterFacts

end

end Spin2
