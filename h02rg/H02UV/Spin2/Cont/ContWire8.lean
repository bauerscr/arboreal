import Spin2.Cont.ContWire7

set_option autoImplicit false

/-!
# B3, T6 (a) wiring for the pair-difference datum: `cw2_T5R` with the `zV` reference `b`-part and
`V_{ab} = 0` at `j_x` as the only coalescence input

`pl2Delta` carries the `σ_b` part of the `zV b` history (not `zV0 b`: the `u_b` differ), and satisfies
only the relaxed coalescence invariant (`Spin2/Pair/PairLin3`). Copies:

* **`MasterFacts.cw3_bSizes`**: `cw2_bSizes` with `prjSt false δ = prjSt false (zV-reference at m_r)`,
  `1 ≤ m_r` (`obsHist_zV0`: the `V, 𝒲, K` of the two references agree from scale `1` on);
* **`MasterFacts.cw3_T5R`**: `cw2_T5R` with `hδb` for the `zV` reference and `hδc` replaced by
  `V_{ab} = 0` of the restarted state at `j_x` (the only use of `ObsCoalInv` in `cw2_T5R`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs2

variable {L : ℕ} [NeZero L]

namespace MasterFacts

variable (M : MasterFacts L)

set_option maxHeartbeats 1000000 in
/-- **The `b`-sector sizes of the restarted history** (reference `b`-part). -/
theorem cw3_bSizes (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A) (hRρ : R.ρ = M.core.ρ)
    (hN3 : 3 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N) (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) {mr : ℕ} (δ : ObsSt .two L N)
    (hb : prjSt false δ = prjSt false (obsHist (R.withMsq m) (ptsX x)
      (obsInit .two (zV b) (ptsX x)) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hmr1 : 1 ≤ mr) {j : ℕ} (hmj : mr ≤ j) (hjN : j ≤ Nh) :
    (∀ q ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (((obsHistFrom (R.withMsq m) (ptsX x) mr δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖)) ∧
    (∀ q ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (((obsHistFrom (R.withMsq m) (ptsX x) mr δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).W q :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) *
          (2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖))) ∧
    (∀ X, IsConn j X → ENNReal.ofReal ((R.withMsq m).A ^ (nb j X - 2 ^ 2)) *
      Tj 2 (L : ℝ) j (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (((obsHistFrom (R.withMsq m) (ptsX x) mr δ j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).K X :
          OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (16 * M.core.cWo * M.core.Bk *
          (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ 2 *
          (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
            ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖))) := by
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  obtain ⟨hV1, hW1, hK1, -⟩ := rpb_b_eq (R.withMsq m) (ptsX x) (obsInit .two (zV b) (ptsX x)) δ
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hb hmj
  obtain ⟨z1, z2, z3⟩ := obsHist_zV0 (R.withMsq m) (ptsX x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b
    (traj_zero_X R m b μ₀) j (by omega)
  obtain ⟨hV2, hW2, hK2⟩ := prjSt_eq_cmp (mirror_b_eq (R.withMsq m)
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) b x j)
  have hNh0 : 0 < Nh := by omega
  have hN : 2 ≤ N := by omega
  obtain ⟨-, hA, hW, hK⟩ := M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD (ptsS x)
    (zV0 b) rfl hmu hNh0 j hjN
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hs := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun X hX => ?_⟩
  · rw [hV1 q]; erw [z1]; rw [hV2 q, obsHist2_pure (R.withMsq m) (ptsS x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (zV0 b) rfl j q]
    refine (Tj_smul_pbp_le j hs _ _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : ‖LocObs.mass2 (((obsHist (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x)) j
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).V q : OE .two (Lam 2 L N)) :
          SA .two (Lam 2 L N)).a‖ ≤
        Obs2.shA2 (Obs2.histVO2 (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) j := by
      rw [← histVO2_a (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x))
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j q]
      exact Finset.single_le_sum (f := fun c => ‖LocObs.mass2
        (Obs2.histVO2 (R.withMsq m) (ptsS x) (obsInit .two (zV0 b) (ptsS x))
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j c : SA .two (Lam 2 L N)).a‖)
        (fun _ _ => norm_nonneg _) hq
    have := mul_le_mul_of_nonneg_right (h1.trans hA)
      (sq_nonneg (histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    have e : 2 * ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ *
        histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 =
        2 * histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R (ptsS x) (zV0 b) m b μ₀ j‖ := by ring
    linarith
  · rw [hW1 q]; erw [z2]; rw [hW2 q]
    have h := hW q hq
    rw [Obs2.oTo_wA] at h
    exact h
  · rw [hK1 X]; erw [z3]; rw [hK2 X]
    have h := hK X hX
    rw [Obs2.oTo_wA] at h
    exact h

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The T5 bound for a restarted datum at `j_x ≤ N_h`, one-point sizes discharged.** -/
theorem cw3_T5R : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    (x : Lam 2 L N) (hx : x ≠ 0) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    -- the restart datum `δ` at scale `m_r ≤ j_x` (reference `b`-part)
    {mr : ℕ} (hmr0 : 0 < mr) (hmrj : mr ≤ (Obs.coal L (0 : Lam 2 L N) x))
    (δ : Obs2.ObsSt .two L N) (hδ0 : δ.IsObs) (hδl : PtCorr2.ObsLocInv (ptsX x) mr δ)
    (hδs : PtCorr2.ObsSymInv mr δ)
    (hδc : ∀ q, ((cw2O R m b x mr δ).V q : SA .two (Lam 2 L N)).ab = 0)
    (hδf : ∀ q, Obs2.Loc2Form (ptsX x).a (δ.V q : SA .two (Lam 2 L N)).a)
    (hδp : ∀ q, (δ.V q : SA .two (Lam 2 L N)).a =
      LocObs.mass2 (δ.V q : SA .two (Lam 2 L N)).a • LocObs.pbp (ptsX x).a)
    (hδb : prjSt false δ = prjSt false (obsHist (R.withMsq m) (ptsX x)
      (obsInit .two (zV b) (ptsX x)) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))))
    -- the restart envelope at `m_r` (the data of `MasterCore.restartDT_lin`)
    {M₀ k w : ℝ} (hM0 : 0 < M₀) (hk : 0 ≤ k) (hw : 0 ≤ w)
    (hbR : ‖Obs2.betaTot2 (L := L) (N := N) mr (histVF2 (R.withMsq m) (ptsX x) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr)‖ +
        Obs2.shareDev2 (ptsX x).a mr (histVF2 (R.withMsq m) (ptsX x) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr) ≤ M₀)
    (hWR : WbHF (R.withMsq m) (ptsX x) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr w)
    (hKR : KbHF (R.withMsq m) (ptsX x) mr δ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) mr k)
    (hg : M.core.rdtC * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) mr).1) *
      2) ≤ 1 / 1344)
    (hMR : 1344 * (8 * (PtCorr2.csN 2 : ℝ) * k + M.core.rdtΓ * w) ≤
      histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)
    -- the size constants at `j_x`
    {vT wT kxT w2 k2 m0 γδ : ℝ} (hvT : 1 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) ≤ vT)
    (hwT : M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) + w / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀) +
      (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1)) + w2 ≤ wT)
    (hkxT : (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀) +
      8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2 + (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2) ≤ kxT)
    (hw2 : 0 ≤ w2) (hk2 : 0 ≤ k2)
    -- the `σ_aσ_b` parts at `j_x` (open inputs)
    (hW2 : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh x mr δ M₀)) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x) (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((cw2O R m b x mr δ).W q : SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal w2)
    (hK2 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh x mr δ M₀)) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab * Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) ((cw2O R m b x mr δ).K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2)
    (hsmT : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1 ^ 3 + kxT + k2) ≤ 1)
    (hm0 : 0 < m0) (h8w : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * m0))
    (h8t : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * m0))
    (h8v : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁v * ((4 * C₁v + 1) * m0))
    (h8m : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁m * ((4 * C₁m + 1) * m0))
    (Cδ : ℕ) (hδ : N ≤ Obs.coal L (0 : Lam 2 L N) x + Cδ)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ m0 Cδ) + (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ m0 Cδ) + 8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ m0 Cδ)) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε (((cw2O R m b x mr δ).u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x (cw2O R m b x mr δ)‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)) +
        M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ * ((cw2Sig R m b Nh x mr δ M₀) / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1   := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.cw2_T5M
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj mr hmr0 hmrj δ hδ0 hδl hδs hδc hδf hδp hδb M₀ k w hM0 hk hw hbR
    hWR hKR hg hMR vT wT kxT w2 k2 m0 γδ hvT hwT hkxT hw2 hk2 hW2 hK2 hsmT hm0 h8w h8t h8v h8m Cδ hδ
    hmAB hu
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by have := M.core.hL49; norm_num; omega
  have hN2 : 2 ≤ N := by omega
  have hF := M.flow
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hvalL : ValidAtL (R.withMsq m) Nh := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by
    rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hsN := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh
  have hsj := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) (Obs.coal L (0 : Lam 2 L N) x)
  obtain ⟨H, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hcR : cR (R.withMsq m) ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hc2 : 2 ≤ M.core.c := hcR ▸ two_le_cR (R.withMsq m) H.hcmu H.hC₂
  have hε0 : 0 ≤ M.core.ε := by have := H.hε; linarith
  have hcW : 1 ≤ M.core.cWo := M.core.consts_nonneg.2.2.2.2.2.1
  have hBk : 0 ≤ M.core.Bk := M.core.consts_nonneg.2.2.2.2.2.2.1
  have hg0 : 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1 := (hD _ hj).1.le
  have hG0 : 0 ≤ (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) := by positivity
  have hΘ : 0 ≤ (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) := by unfold cw2Thb; positivity
  -- the invariants of the restarted state at `j_x`
  obtain ⟨ho, hlo, hso⟩ := rpb_inv_top (R.withMsq m) (ptsX x) hval hvalL hδ0 hδl hδs (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))
    (j := (Obs.coal L (0 : Lam 2 L N) x)) hmrj (by omega)
  -- the `a`-sector (restart envelope) and the `b`-sector (reference)
  obtain ⟨hAV, hAW, hAK, henv⟩ := M.core.cw2_aSizes N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b
    (b - m) hD (ptsX x) (zV0 b) mr δ hmr0 (by omega) hδ0 hδl hδs hδf hδp hM0 hk hw hbR hWR hKR hg
    hMR ((Obs.coal L (0 : Lam 2 L N) x) - mr) (by omega)
  have e : mr + ((Obs.coal L (0 : Lam 2 L N) x) - mr) = (Obs.coal L (0 : Lam 2 L N) x) := by omega
  rw [e] at hAV hAW hAK
  obtain ⟨hBV, hBW, hBK⟩ := M.cw3_bSizes N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD x δ
    hδb hmr0 hmrj hj
  have hrat := M.cw2_pMS_ratio N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD x hj
  replace hrat : 2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * ‖bt2 R (ptsS x) (zV0 b) m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)‖ ≤
      (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) := by
    refine hrat.trans (le_of_eq ?_); unfold cw2Thb; ring
  have hb0 : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb0
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsS x)
    (zV0 b) rfl hmu (by omega) Nh le_rfl).1
  have hMb : 0 < (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh) := by
    unfold pM; exact mul_pos (mul_pos two_pos (pow_pos hsN 2)) hβS
  have henv' : 0 < cw2Env R m b x mr δ M₀ := henv
  have hMa' : 0 < 2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * cw2Env R m b x mr δ M₀ := by positivity
  have hMa : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (cw2Sig R m b Nh x mr δ M₀) =
      2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * cw2Env R m b x mr δ M₀ := by
    unfold cw2Sig; field_simp
  have hσ : 0 < (cw2Sig R m b Nh x mr δ M₀) := by unfold cw2Sig; positivity
  have hvT0 : 0 ≤ vT := by linarith
  have hwT0 : 0 ≤ wT := by
    have : 0 ≤ w / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀) := by positivity
    have : 0 ≤ M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) := by positivity
    have : 0 ≤ (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1)) := by positivity
    linarith
  have hkxT0 : 0 ≤ kxT := by
    have : 0 ≤ (k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
      (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀) := by positivity
    have : 0 ≤ 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2 := by positivity
    have : 0 ≤ (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2) := by positivity
    linarith
  refine hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall x hx h1 hj (cw2O R m b x mr δ) ho hlo hso hσ hvT0 hwT0 hkxT0 hk2 ?_ ?_ ?_ hK2 hsmT hm0 h8w h8t h8v h8m
    Cδ hδ hmAB hu
  · -- `V`
    intro q hq
    rw [hMa]
    have hVab := hδc q
    have hbv : Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x) (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((cw2O R m b x mr δ).V q : SA .two (Lam 2 L N)).b ≤ ENNReal.ofReal ((cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) :=
      (hBV q hq).trans (ENNReal.ofReal_le_ofReal hrat)
    refine (oTo_wM_le_of_ab hMa' hMb (Obs.coal L (0 : Lam 2 L N) x) _ _ hVab hMa'.le (by positivity) (hAV q hq) hbv).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [div_self hMa'.ne', mul_div_assoc, div_self hMb.ne', mul_one]
    exact hvT
  · -- `𝒲`
    intro q hq
    have h2 := hW2 q hq
    rw [hMa] at h2 ⊢
    rw [oTo_split_ab, wOne_wM]
    have hbw : Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x) (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
        ((cw2O R m b x mr δ).W q : SA .two (Lam 2 L N)).b ≤ ENNReal.ofReal (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) * ((cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))) :=
      (hBW q hq).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hrat (by positivity)))
    have hu0 : 0 ≤ (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) + w / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) *
        (2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * cw2Env R m b x mr δ M₀) := by positivity
    have h1 := oTo_wM1_le hMa' hMb (Obs.coal L (0 : Lam 2 L N) x) _ ((cw2O R m b x mr δ).W q) hu0 (by positivity) (hAW q hq) hbw
    calc _ ≤ ENNReal.ofReal ((M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) + w / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) *
            (2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * cw2Env R m b x mr δ M₀) /
            (2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * cw2Env R m b x mr δ M₀) +
          M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) * ((cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) / (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) + ENNReal.ofReal w2 := add_le_add h1 h2
      _ = ENNReal.ofReal ((M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) + w / (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀)) +
          (cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (M.core.cWo * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1)) + w2) := by
        rw [← ENNReal.ofReal_add (by positivity) hw2, mul_div_assoc, div_self hMa'.ne', mul_one]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal wT := ENNReal.ofReal_le_ofReal (by linarith)
  · -- `K`
    intro X hX
    rw [hMa]
    have hbk : ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x) (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((cw2O R m b x mr δ).K X : SA .two (Lam 2 L N)).b ≤
        ENNReal.ofReal (8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2 * ((cw2Thb M Nh (Obs.coal L (0 : Lam 2 L N) x)) * (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh))) := by
      refine (hBK X hX).trans (ENNReal.ofReal_le_ofReal ?_)
      have := mul_le_mul_of_nonneg_left hrat
        (by positivity : (0 : ℝ) ≤ 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2)
      nlinarith
    have hu0 : 0 ≤ ((k + 120 * M.core.Bk * (M.core.c * M.core.ε) * w) /
        (histS (R.withMsq m) mr (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * M₀) + 8 * M.core.cWo * M.core.Bk * (M.core.c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1) ^ 2) *
        (2 * histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * cw2Env R m b x mr δ M₀) := by positivity
    refine (reg_oTo_wM1_le hMa' hMb (Obs.coal L (0 : Lam 2 L N) x) _ ((cw2O R m b x mr δ).K X) _ hu0 (by positivity) (hAK X hX) hbk).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [mul_div_assoc, div_self hMa'.ne', mul_one, mul_div_assoc, mul_div_assoc,
      div_self hMb.ne', mul_one]
    linarith

end MasterFacts


end

end Spin2
