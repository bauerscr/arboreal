import Spin2.Cont.ContNa5
import Spin2.Cont.ContNb3
import Spin2.Cont.ContNb4
import Spin2.Cont.ContTop4

set_option autoImplicit false

/-!
# `n_a` of the last factor of the restarted datum for **any** `y` (`a`-only sizes)

**`MasterFacts.nb_naStep`**: for a restart datum `δ` at `ms ≤ N_h` (observable, local,
`U(1)`-invariant, pure `V(B)_a = β_Bψ̄_aψ_a`), the `a`-sizes of `δ_{N_h}` in the `a`-only weight
`nbWa(2s_{N_h}²σ)` and the share data at `N_h` (`aN`, `bD`, `e`), the restarted state
`o = δ_{N_h+1}` satisfies

  `|n_a(lastOF_{N_h+1}(o))| ≤ K_A^{na}(rptfVT, w_T, k_{xT})·(σ/|β_{a,N_h}|)·(3/2)ϑ_{N_h}`

with **no coalescence condition** on `y` (only `1 ≤ j_y`). Steps (ContNa remaining items 1–3):
the `a`-sizes of `δ_{N_h+1}` from `rptf_vobs_block`/`rptf_beta_shA2`, `rptf_wfull_stepF`,
`rptf_kobs_stepF` in the weight `nbWa` (weight-generic step lemmas); `nb_lastA_le` with
`w_V = w_K = nbWa`; the reference zero mode from `nb_ref_zm` (in place of `pairTop_E`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs.LocObs

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 16000000 in
/-- **`n_a(lastOF_{N_h+1})` of the restarted datum, any `y`** (`a`-only sizes at `N_h`). -/
theorem nb_naStep {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
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
    (y : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) y)
    -- the restart datum at `ms ≤ N_h`
    {ms : ℕ} (hms : ms ≤ Nh) (δ : Obs2.ObsSt .two L N) (hδ : δ.IsObs)
    (hδl : ObsLocInv (ptsX y) ms δ) (hδs : ObsSymInv ms δ)
    (hδf : ∀ q, Obs2.Loc2Form (ptsX y).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      mass2 (δ.V q : SA .two (Lam 2 L N)).a • pbp (ptsX y).a)
    -- the envelope and the `a`-sizes at `N_h` in `nbWa (2s_{N_h}²σ)`
    {σ mm k₁ c₁ aN bD e : ℝ} (hσ : 0 < σ) (hmm0 : 0 < mm) (hc₁ : 0 ≤ c₁)
    (hrm : (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ mm)
    (hk₁ : k₁ ≤ c₁ * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 2 * mm)
    (hk₁0 : 0 ≤ k₁)
    (hkt : 8 * (cx M.core.κ M.core.cT + c₁) * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ^ 3 ≤ M.core.ε₀)
    (hVo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (nbWa (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V q) ≤ ENNReal.ofReal mm)
    (hWo : ∀ q ∈ blockIdx (L := L) (N := N) Nh,
      Obs2.oTo (nbWa (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).W q) ≤ ENNReal.ofReal ((M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) * mm))
    (hK1 : ∀ X, IsConn Nh X → ENNReal.ofReal (R.A ^ (nb Nh X - 2 ^ 2)) *
      Obs2.oTo (nbWa (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ)) Nh (histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((obsHistFrom (R.withMsq m) (ptsX y) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).K X) ≤ ENNReal.ofReal k₁)
    (haN : ‖1 - Obs2.frakN2F (ptsX y) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh‖ ≤ aN)
    (hbD : ‖Obs2.betaTot2 (L := L) (N := N) Nh (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)‖ +
      Obs2.shareDev2 (ptsX y).a Nh (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) ≤ bD)
    (he : Obs2.shareErrL1_2F (ptsX y) (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histVF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (histWF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
      (histKF2 (R.withMsq m) (ptsX y) ms δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ms Nh ≤ e)
    -- the window of `na_lastA_le`
    (hmAa : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (rptfVT aN bD e σ + M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm + 8 * M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁ + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1) :
    ‖PtCorr2.nA (PtCorr2.lastOF (R.withMsq m) (ptsX y) (Nh + 1)
        (obsHistFrom (R.withMsq m) (ptsX y) ms δ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))‖ ≤
      M.naKA (rptfVT aN bD e σ) (M.rptfWT (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm) (M.rptfKx c₁ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) mm k₁) r₀ *
        (σ / ‖hBeta R m b (b - m) y Nh‖) * (3 / 2 * varthJ R m b (b - m) Nh) := by
  have hL49 : 49 ≤ L := M.core.hL49
  have hLp : pauliL0 2 ≤ L := M.core.hLpl
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL7 : 7 ≤ L := by omega
  have hε1 := M.eps_le
  have hF := M.flow
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hcWL := M.cWL_nonneg
  have hcKL := M.cKL_nonneg
  have hN2 : 2 ≤ N := by omega
  have hNh1 : 1 ≤ Nh := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set μ₀ := b - m with hμ₀
  set R' := R.withMsq m with hR'
  set t : Hist.Seq (Xs R') := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  have hval : ∀ j < Nh, ValidAt R' j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL R' Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, hCf0, -, -, hρ8, hspl, -⟩ := hF
  have hh0 : b = μ₀ + m := by rw [hμ₀]; ring
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hspl' : SplitSmall R.P L R.ρ := by rw [hP, hRρ]; exact hspl
  have hVN := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hG : GlueOut R' Nh M.core.Cf t :=
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD).1
  have hg0 : 0 < (t Nh).1 := (hD Nh le_rfl).1
  have hg1 : (t Nh).1 ≤ 1 := ((hD Nh le_rfl).2.1).trans hε1
  have hmN : |R'.msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    show |m| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]; exact h1
  have hJ' : PtCorr2.LastJetBd L (R.A / 2) r₀ := by rw [hRA]; exact hJ
  have e2 : 8 * cM * R.ℓ ^ 2 = 8 * cM * M.core.ℓ ^ 2 := by rw [hRℓ]
  have eT : cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL =
      cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL := by rw [hRℓ]
  have hs1' : 2 * (M.core.Cf * (t Nh).1) ≤ R.ρ := by rw [hRρ]; exact hs1
  have hs2' : 8 * cM * R.ℓ ^ 2 * (M.core.Cf * (t Nh).1) ≤ 1 / 2 := by rw [e2]; exact hs2
  have hs3' : PtCorr2.cRho L * (cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL * (t Nh).1) ≤ 1 := by
    rw [eT]; exact hs3
  have hs4' : 4 * (cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL * (t Nh).1) ≤ r₀ ^ 2 := by
    rw [eT]; exact hs4
  have hs5' : cTauL R.ℓ M.core.Cf M.core.cWL M.core.cKL * (t Nh).1 ≤ r₀ := by rw [eT]; exact hs5
  -- the one-point parts at `N − 1` and `γ_{a,N}` (reference)
  set lam := lamHat2 R (ptsX y) (zV b) m b μ₀ with hlamd
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX y)
  obtain ⟨-, -, hgam⟩ := M.oneTopD R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD lam hKp hl hsmall y
  -- the one-point items of the last step at `y` (reference)
  have hNh0 : 0 < Nh := by omega
  have hWx := M.lastWD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX y) hNh0
  have hKx := M.lastKD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX y) hNh0
  have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX y)).1
  have hl1 := M.lastL1D N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX y)
    (htop.1.trans (by norm_num))
  have hKR := lastKRem_x R hNh hval hvalL hVN hLp hL8 hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1
    hs1' hs2' hs3' hs4' hs5' y h1 hWx hKx htop hl1
  have hsmA' : (M.core.Cf * (R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128) + 9 / 4 * (cBn * Q1 2 * M.core.cWL) +
      cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (t Nh).1 ≤ 1 / 2 := by
    rw [hRℓ]; exact hsmA
  obtain ⟨hP0, hone1, hone2⟩ := lastOneRem_x R hNh hval hvalL hVN hLp hL8 hG hcWL hg0.le y hWx
    htop hsmA' hKR
  rw [hP0, mul_one, norm_one, mul_one] at hone1
  rw [hP0, norm_one, mul_one] at hone2
  -- the reference weight `|β_{a,N_h}| > 0` and `2s²|β| ≤ c_u|M|ǧ`
  have hMaM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam M.Kp hKp hl
    hsmall (ptsX y) hNh1 le_rfl le_rfl
  have hMa2 : pM R' (ptsX y) (zV0 b) t Nh = 2 * histS R' Nh t ^ 2 * ‖hBeta R m b μ₀ y Nh‖ := by
    rw [hBeta_eq_zV0 R m b μ₀ y hNh1]; rfl
  have hβN := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX y)
    (zV0 b) rfl (zV_mua_ne hb) hNh0 Nh le_rfl).1
  have hβ0 : hBeta R m b μ₀ y Nh ≠ 0 := by
    have hhB : ‖hBeta R m b μ₀ y Nh‖ = ‖bt2 R (ptsX y) (zV0 b) m b μ₀ Nh‖ := by
      rw [hBeta_eq_zV0 R m b μ₀ y hNh1]; rfl
    intro h0; rw [h0, norm_zero] at hhB; rw [← hhB] at hβN; exact lt_irrefl _ hβN
  have hMa0 : 2 * histS R' Nh t ^ 2 * ‖hBeta R m b μ₀ y Nh‖ ≤
      pairUnitC M * ‖Mmag R m b μ₀ lam Nh‖ * (t Nh).1 := by rw [← hMa2]; exact hMaM
  have hmA' : 8 * cKAL L R.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m *
      (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmA
  -- the reference zero mode (`h = 0`, any `y`)
  obtain ⟨hΩ0, hnA⟩ := nb_ref_zm R hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hL7 hb hh0 y
  -- the sizes of the restarted state at `N_h + 1` (`a`-only weight)
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
  have hβL : 0 ≤ betaL L := by linarith
  have hmNh : |R'.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ 1 := by
    show |m| * _ ≤ 1
    rw [abs_of_pos hm.1]
    have h1 := PtCorr2.msq_mul_pow_le_one (L := L) (N := N) (by omega) (by omega) hm.2
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
    have h2 : ((L : ℝ) ^ Nh) ^ 2 ≤ (L : ℝ) ^ (2 * (N - 1)) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
    exact (mul_le_mul_of_nonneg_left h2 hm.1.le).trans h1
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
  set o := obsHistFrom R' (ptsX y) ms δ (Nh + 1) t with hod
  set Ma := 2 * histS R' Nh t ^ 2 * σ with hMad
  have hMa : 0 < Ma := by positivity
  obtain ⟨ho, hlo, -⟩ := rpb_inv_top R' (ptsX y) hval hvalL hδ hδl hδs t (j := Nh + 1) (by omega)
    le_rfl
  have hcN : Nh + 1 < N := by omega
  obtain ⟨-, hA1⟩ := rptf_beta_shA2 R' (ptsX y) ms δ t hδf (j := Nh) hms hcN
  have hD0 : 0 ≤ Obs2.shareDev2 (ptsX y).a Nh (histVF2 R' (ptsX y) ms δ t Nh) :=
    sum_nonneg fun _ _ => norm_nonneg _
  have hbD0 : 0 ≤ bD := (add_nonneg (norm_nonneg _) hD0).trans hbD
  have hE0 : 0 ≤ Obs2.shareErrL1_2F (ptsX y) (Obs2.histCovO R' t) (histVF2 R' (ptsX y) ms δ t)
      (histWF2 R' (ptsX y) ms δ t) (histKF2 R' (ptsX y) ms δ t) ms Nh :=
    sum_nonneg fun _ _ => norm_nonneg _
  have he0 : 0 ≤ e := hE0.trans he
  have haN0 : 0 ≤ aN := (norm_nonneg _).trans haN
  have hA2 : Obs2.shA2 (histVF2 R' (ptsX y) ms δ t) (Nh + 1) ≤ aN * bD + 3 * e := by
    refine hA1.trans ?_
    have h1 := mul_le_mul haN hbD (add_nonneg (norm_nonneg _) hD0) haN0
    linarith
  have hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (nbWa Ma) (Nh + 1) (histS R' (Nh + 1) t) (o.V q) ≤
        ENNReal.ofReal (rptfVT aN bD e σ) := by
    intro q hq
    have ha : Tj 2 (L : ℝ) (Nh + 1) (histS R' (Nh + 1) t) (o.V q : SA .two (Lam 2 L N)).a ≤
        ENNReal.ofReal (81 / 64 * histS R' Nh t ^ 2 * (aN * bD + 3 * e)) := by
      refine (rptf_vobs_block R' (ptsX y) ms δ t hδf hδp (j := Nh + 1) (by omega) hsp1 q hq).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have h0 : 0 ≤ Obs2.shA2 (histVF2 R' (ptsX y) ms δ t) (Nh + 1) :=
        sum_nonneg fun _ _ => norm_nonneg _
      calc histS R' (Nh + 1) t ^ 2 * Obs2.shA2 (histVF2 R' (ptsX y) ms δ t) (Nh + 1)
          ≤ (81 / 64 * histS R' Nh t ^ 2) * (aN * bD + 3 * e) :=
            mul_le_mul hss hA2 h0 (by positivity)
        _ = 81 / 64 * histS R' Nh t ^ 2 * (aN * bD + 3 * e) := by ring
    rw [nb_oTo_wa]
    refine (mul_le_mul_right ha _).trans ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hMa.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : Ma⁻¹ * (81 / 64 * histS R' Nh t ^ 2 * (aN * bD + 3 * e)) =
        81 / 128 * ((aN * bD + 3 * e) / σ) := by
      rw [hMad]; field_simp; ring
    rw [e1]; unfold rptfVT
    have : (0 : ℝ) ≤ 3 / 2 * (81 / 64) ^ 2 := by norm_num
    linarith
  have hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Nh + 1),
      Obs2.oTo (nbWa Ma) (Nh + 1) (histS R' (Nh + 1) t) (o.W q) ≤
        ENNReal.ofReal (M.rptfWT r mm) := by
    intro q _
    have h := rptf_wfull_stepF R' M.core.hWw hSB' hval hm1 hvalL hmNh hβL (by norm_num) H
      (ptsX y) (nbWa Ma) (nbWa_sub Ma) hms δ hδ hδl hδs t ht mm (by rw [hcR]; exact hrm)
      (by rw [hcR]; exact hr1) hVo (fun q hq => by rw [hcR]; exact hWo q hq) q
    rw [hcR] at h
    exact h
  have hKt : ∀ X, IsConn (Nh + 1) X → ENNReal.ofReal (R.A ^ (nb (Nh + 1) X - 2 ^ 2)) *
      Obs2.oTo (nbWa Ma) (Nh + 1) (histS R' (Nh + 1) t) (o.K X) ≤
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
    have hWo' : ∀ q ∈ blockIdx (L := L) (N := N) Nh, Obs2.oTo (nbWa Ma) Nh (histS R' Nh t)
        ((obsHistFrom R' (ptsX y) ms δ Nh t).W q) ≤
          ENNReal.ofReal (cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * (t Nh).1 * mm) := by
      rw [hcR]; exact hWo
    have h := rptf_kobs_stepF R' hKB' hSB' hval hm1 hvalL hmNh hβL (by norm_num) H (ptsX y)
      (nbWa Ma) rfl ENNReal.ofReal_ne_top ENNReal.zero_ne_top hms δ hδ hδl hδs t ht (8 * c₁) mm
      k₁ (by positivity) hmm0 hk₁0 (by rw [hcR]; exact hr1) (by rw [hcR]; exact hrε) hk8 hkt'
      hVo hWo' hK1
    intro X hX
    have h' := h X hX
    rw [hcR, show R'.A = M.core.A from hRA] at h'
    rw [hRA]
    exact h'
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
  -- `n_a` of the last factor of `o`
  have hmAa' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (rptfVT aN bD e σ + M.rptfWT r mm + 8 * M.rptfKx c₁ r mm k₁ + 1) *
      R.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by rw [hRℓ]; exact hmAa
  have hA := nb_lastA_le R hNh hm.1 hm.2 hρ1 hspl' hval hvalL hVN hLp hL8
    (by rw [hRA]; exact M.core.hA2) hmN hG hr₀ hr₀1 hJ' hcWL hcKL hCf0 hg0 hg1 hs1' hs2' hs3'
    hs4' hs5' lam y o ho hlo hσ (nbWa Ma) (nbWa Ma) rfl rfl hvT hwT hkxT (pairUnitC_nonneg M)
    hVt hWt hKt hMa0 htop hβ0 hone1 hone2 hgam hΩ0 hnA hK hmT hmA' hmAa'
  -- `|M_{N_h}| ≤ (3/2)ϑ_{N_h}`
  set Mc := Mmag R m b μ₀ lam Nh with hMcd
  set g := (t Nh).1 with hgd
  set Fm := max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 with hFd
  set v := varthJ R m b μ₀ Nh with hvd
  have hv : 0 ≤ v := Real.rpow_nonneg (div_pos hb hg0).le _
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hMl := hMag lam M.Kp hKp hl Nh le_rfl
  have hMl' : ‖Mc - ((v : ℝ) : ℂ)‖ ≤ Fm * v * g :=
    hMl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
      hg0.le)
  have hFg : Fm * g ≤ 1 / 2 := hsmall Nh le_rfl
  have hMc : ‖Mc‖ ≤ 3 / 2 * v := by
    have h1 : ‖Mc‖ ≤ ‖Mc - ((v : ℝ) : ℂ)‖ + ‖((v : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hv] at h1
    have h2 : Fm * v * g ≤ 1 / 2 * v := by
      have e : Fm * v * g = Fm * g * v := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hFg hv
    linarith
  have hKA0 : 0 ≤ M.naKA (rptfVT aN bD e σ) (M.rptfWT r mm) (M.rptfKx c₁ r mm k₁) r₀ *
      (σ / ‖hBeta R m b μ₀ y Nh‖) := by
    have hcu := pairUnitC_nonneg M
    have hcL : 0 ≤ cLab L := by
      unfold cLab
      have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
      positivity
    have hcJ : 0 ≤ cJab L r₀ := by
      unfold cJab
      have hL2' : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
      have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
      have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
      have h1 : 0 ≤ cJet L := by
        unfold cJet; have := mul_nonneg hL2' (by linarith : (0 : ℝ) ≤ Q1 2); linarith
      have h2 : 0 ≤ cRho L := by
        unfold cRho
        have h4 : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
        have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
        refine mul_nonneg hL2' ?_
        linarith only [h4, h3, hcS', hQ1]
      have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
      positivity
    have := M.topF'_nonneg; have := M.topCL_nonneg
    unfold naKA
    positivity
  exact hA.trans (mul_le_mul_of_nonneg_left hMc hKA0)

end MasterFacts

end

end Spin2
