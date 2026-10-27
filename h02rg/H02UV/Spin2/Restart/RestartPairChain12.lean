import Spin2.Restart.RestartPairChain11

set_option autoImplicit false

/-!
# T5, item (5)(iii): the combined bound with `δ`-dependent constants

**`MasterFacts.rpc11_T5δ`**: `rpc11_T5` under `N ≤ j_x + C_δ`, with the constant
`rpc11K … (max(1,2Λ₁)^{C_δ}m̄₀) C_δ` (monotonicity `rpc11K_mono`; the window `hmAB` at the
`C_δ` size) — a constant depending on `L` (master constants), `m̄₀` and `C_δ` only.

**`MasterFacts.rpc12_T5S`**: the same with the one-point sizes `v_T, w_T, k_{xT}, k₂` of `o`
at `j_x` in `wM(2s_{N_h}²σ, M_b)` (the restart sizes at `j_x`) as the only state input.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

theorem rpc11K_mono {r₀ C₁t Λ₁ Λ₂ : ℝ} (hr₀ : 0 < r₀) (hC₁t : 0 ≤ C₁t) (hc : 0 ≤ M.core.c)
    {mb mb' : ℝ} (h0 : 0 ≤ mb) (h : mb ≤ mb') {n n' : ℕ} (hn : n ≤ n') :
    M.rpc11K r₀ C₁t Λ₁ Λ₂ mb n ≤ M.rpc11K r₀ C₁t Λ₁ Λ₂ mb' n' := by
  have hcJ := cJab_nonneg L hr₀
  have hcu := pairUnitC_nonneg M
  have hF := M.topF'_nonneg
  have hCL := M.topCL_nonneg
  have hcL : 0 ≤ cLab L := by
    unfold cLab; have := Step2.one_le_Q1 (d := 2) one_le_two; positivity
  have hm' : 0 ≤ mb' := h0.trans h
  have hS : mb + (4 * C₁t + 1) * M.core.c * mb + 8 * ((4 * C₁t + 1) * mb) + 1 ≤
      mb' + (4 * C₁t + 1) * M.core.c * mb' + 8 * ((4 * C₁t + 1) * mb') + 1 := by
    have h1 : (4 * C₁t + 1) * M.core.c * mb ≤ (4 * C₁t + 1) * M.core.c * mb' :=
      mul_le_mul_of_nonneg_left h (by positivity)
    have h2 : (4 * C₁t + 1) * mb ≤ (4 * C₁t + 1) * mb' :=
      mul_le_mul_of_nonneg_left h (by positivity)
    linarith
  have hS0 : 0 ≤ mb + (4 * C₁t + 1) * M.core.c * mb + 8 * ((4 * C₁t + 1) * mb) + 1 := by
    positivity
  have hnn : (n : ℝ) ≤ n' := by exact_mod_cast hn
  unfold rpc11K rpcKZ
  have hA : 0 ≤ 2 * max Λ₁ 0 + max Λ₂ 0 := by
    have := le_max_right Λ₁ 0; have := le_max_right Λ₂ 0; linarith
  have k1 : (n : ℝ) * ((2 * max Λ₁ 0 + max Λ₂ 0) * mb) ≤
      (n' : ℝ) * ((2 * max Λ₁ 0 + max Λ₂ 0) * mb') :=
    mul_le_mul hnn (mul_le_mul_of_nonneg_left h hA) (mul_nonneg hA h0) (Nat.cast_nonneg _)
  have k2 : (L : ℝ) ^ 2 * (max Λ₁ 0 * mb) ≤ (L : ℝ) ^ 2 * (max Λ₁ 0 * mb') :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (le_max_right _ _)) (by positivity)
  have k3 := mul_le_mul_of_nonneg_left hS hcL
  have k4 : 81 / 32 * cJab L r₀ *
      (mb + (4 * C₁t + 1) * M.core.c * mb + 8 * ((4 * C₁t + 1) * mb) + 1) ≤
      81 / 32 * cJab L r₀ *
      (mb' + (4 * C₁t + 1) * M.core.c * mb' + 8 * ((4 * C₁t + 1) * mb') + 1) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have hP : 0 ≤ pairUnitC M * (2 * (1 + M.topF' + M.topCL)) := by positivity
  have k5 : 9 / 4 * (8 * (1 / 2 + 81 / 32 * cJab L r₀ *
      (mb + (4 * C₁t + 1) * M.core.c * mb + 8 * ((4 * C₁t + 1) * mb) + 1)) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL))) ≤ 9 / 4 * (8 * (1 / 2 + 81 / 32 * cJab L r₀ *
      (mb' + (4 * C₁t + 1) * M.core.c * mb' + 8 * ((4 * C₁t + 1) * mb') + 1)) * pairUnitC M *
      (2 * (1 + M.topF' + M.topCL))) := by
    have := mul_le_mul_of_nonneg_right k4 hP
    nlinarith
  have k6 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add k1 k2) k3)
    (by positivity : (0 : ℝ) ≤ 9 / 4 * pairUnitC M ^ 2)
  linarith

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The combined T5 bound for `N − C_δ ≤ j_x ≤ N_h`**: the constant depends on `L` (master
constants) and `C_δ` only (`m̄_top ≤ max(1,2Λ₁)^{C_δ}m̄₀`, at most `C_δ` steps). -/
theorem rpc11_T5δ : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    -- the general state at `j_x`
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hlo : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o)
    (hso : PtCorr2.ObsSymInv (Obs.coal L (0 : Lam 2 L N) x) o)
    {σ Mb k₀ m0 γδ : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb)
    (hMbM : Mb ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
    (hMaM : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * ‖hBeta R m b (b - m) x Nh‖ ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
    (hk₀ : 0 ≤ k₀)
    (hK0 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((rpcRed R m b (b - m) x o).K X) ≤ ENNReal.ofReal k₀)
    (hm0 : 0 < m0) (h8w : 8 * k₀ ≤ vck C₁w * ((4 * C₁w + 1) * m0))
    (h8t : 8 * k₀ ≤ vck C₁t * ((4 * C₁t + 1) * m0))
    (h8v : 8 * k₀ ≤ vck C₁v * ((4 * C₁v + 1) * m0))
    (h8m : 8 * k₀ ≤ vck C₁m * ((4 * C₁m + 1) * m0))
    (Cδ : ℕ) (hδ : N ≤ Obs.coal L (0 : Lam 2 L N) x + Cδ)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ m0 Cδ) + (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ m0 Cδ) + 8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ m0 Cδ)) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)) +
        M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1  := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.rpc11_T5
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ Mb k₀ m0 γδ hσ hMb hMbM hMaM hk₀ hK0 hm0 h8w h8t
    h8v h8m Cδ hδ hmAB hu
  have hN2 : 2 ≤ N := by omega
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD
    rw [← hcR]; unfold cR cV cW cZ
    obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    have := Hap.hcmu; have := Hap.hC₂; positivity
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  have hle : rpc9Mb Λ₁ m0 (Nh + 1 - j) ≤ rpc9Mb Λ₁ m0 Cδ := rpc9Mb_mono hm0 (by omega)
  have hmb0 := (rpc9Mb_pos (Λ₁ := Λ₁) hm0 (Nh + 1 - j)).le
  set mT := rpc9Mb Λ₁ m0 (Nh + 1 - j) with hmTd
  set mD := rpc9Mb Λ₁ m0 Cδ with hmDd
  have hmAB' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (mT + (4 * C₁t + 1) * M.core.c * mT + 8 * ((4 * C₁t + 1) * mT) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    refine le_trans ?_ hmAB
    have hQ1 := Step2.one_le_Q1 (d := 2) one_le_two
    have hcJ : 0 ≤ cJet L := by unfold cJet; positivity
    have hcR : 0 ≤ cRho L := by
      unfold cRho; have : 0 ≤ Step2.LastN.cSN 2 L := by unfold Step2.LastN.cSN; positivity
      positivity
    have hS : mT + (4 * C₁t + 1) * M.core.c * mT + 8 * ((4 * C₁t + 1) * mT) + 1 ≤
        mD + (4 * C₁t + 1) * M.core.c * mD + 8 * ((4 * C₁t + 1) * mD) + 1 := by
      have h1 : (4 * C₁t + 1) * M.core.c * mT ≤ (4 * C₁t + 1) * M.core.c * mD :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have h2 : (4 * C₁t + 1) * mT ≤ (4 * C₁t + 1) * mD :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      linarith
    have hm0' : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.1.le (by positivity)
    have hk : 0 ≤ 81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) := by positivity
    have a1 := mul_le_mul_of_nonneg_left hS hk
    have a2 := mul_le_mul_of_nonneg_right a1 (sq_nonneg M.core.ℓ)
    have a3 := mul_le_mul_of_nonneg_left a2 (by norm_num : (0 : ℝ) ≤ 2)
    have a4 := mul_le_mul_of_nonneg_right a3 hm.1.le
    exact mul_le_mul_of_nonneg_right a4 (by positivity)
  have h := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall x hx h1 hj o ho hlo hso hσ hMb hMbM hMaM hk₀ hK0 hm0 h8w h8t h8v h8m hmAB' hu
  refine h.trans (add_le_add le_rfl ?_)
  have hK := M.rpc11K_mono hr₀ hC₁t hc0 (Λ₁ := Λ₁) (Λ₂ := Λ₂) hmb0 hle
    (show Nh + 1 - j ≤ Cδ by omega)
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg0 : 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := (hD Nh le_rfl).1
  have hv : 0 ≤ varthJ R m b (b - m) Nh := Real.rpow_nonneg (div_pos hb hg0).le _
  have hX : 0 ≤ (σ / ‖hBeta R m b (b - m) x Nh‖) * varthJ R m b (b - m) Nh ^ 2 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by positivity
  have := mul_le_mul_of_nonneg_right hK hX
  calc M.rpc11K r₀ C₁t Λ₁ Λ₂ mT (Nh + 1 - j) * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1
      = M.rpc11K r₀ C₁t Λ₁ Λ₂ mT (Nh + 1 - j) * ((σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) := by
        ring
    _ ≤ M.rpc11K r₀ C₁t Λ₁ Λ₂ mD Cδ * ((σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) := this
    _ = _ := by ring

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The T5 bound with the one-point (restart) sizes of `o` at `j_x` as the only state input**:
`rpc11_T5δ` with the seed `k₀ = (2ι(v_T, w_T)A)^{(L+18)²}` of `rpc_seed_MFD`. -/
theorem rpc12_T5S : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    -- the general state at `j_x`
    (o : Obs2.ObsSt .two L N) (ho : o.IsObs)
    (hlo : PtCorr2.ObsLocInv (ptsX x) (Obs.coal L (0 : Lam 2 L N) x) o)
    (hso : PtCorr2.ObsSymInv (Obs.coal L (0 : Lam 2 L N) x) o)
    {σ Mb vT wT kxT k2 m0 γδ : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb)
    (hMbM : Mb ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
    (hMaM : 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * ‖hBeta R m b (b - m) x Nh‖ ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
    (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) (hkxT : 0 ≤ kxT) (hk2 : 0 ≤ k2)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.V q) ≤ ENNReal.ofReal vT)
    (hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.W q) ≤ ENNReal.ofReal wT)
    (hKt : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        oTo (wM1 (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.K X) ≤ ENNReal.ofReal kxT)
    (hK2 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) Mb).ab * Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2)
    (hsmT : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1 ^ 3 + kxT + k2) ≤ 1)
    (hm0 : 0 < m0) (h8w : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * m0))
    (h8t : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * m0))
    (h8v : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁v * ((4 * C₁v + 1) * m0))
    (h8m : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁m * ((4 * C₁m + 1) * m0))
    (Cδ : ℕ) (hδ : N ≤ Obs.coal L (0 : Lam 2 L N) x + Cδ)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ m0 Cδ) + (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ m0 Cδ) + 8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ m0 Cδ)) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)) +
        M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 Cδ) Cδ * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1   := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.rpc11_T5δ
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ Mb vT wT kxT k2 m0 γδ hσ hMb hMbM hMaM hvT hwT
    hkxT hk2 hVt hWt hKt hK2 hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hu
  have hk₀ : 0 ≤ (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) := by
    have := one_le_rpIota hvT hwT; have := M.core.hA2; positivity
  exact hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall x hx h1 hj o ho hlo hso hσ hMb hMbM hMaM hk₀
    (M.rpc_seed_MFD R hP hi0 hRℓ hRA hRρ (by omega) hNh hm hD x hj o ho hvT hwT hkxT hk2 hVt hWt
      hKt hK2 hsmT) hm0 h8w h8t h8v h8m Cδ hδ hmAB hu

end MasterFacts

end

end Spin2
