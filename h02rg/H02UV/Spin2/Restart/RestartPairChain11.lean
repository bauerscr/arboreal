import Spin2.Restart.RestartPairChain10
import Spin2.H0.MasterH0Multi
import Spin2.Pair.PairFinal6

set_option autoImplicit false

/-!
# T5, item (5)(iii), task 3 and the combined bound: `N − C(δ) ≤ j_x ≤ N_h`

* **`MasterFacts.rpc11_zBelowD`**: `ZBelowU1 … λ K_M` along every trajectory in `D_ε`, for every
  `λ` with (H_λ) at `K_λ` and the smallness `max(K_M(K_λ), 0)ǧ_j ≤ 1/2`, with
  `K_M = zbKM L c_g K_e K_Z K_G K_p c_γ (K_p + c_γ) K_λ`, `c_γ = (c_{GB} + c_w)(1 + 3K_p)` (the
  construction inside `twoPtSq_of_gam_flowBD`/`twoPtSqD`, exported).
* **`MasterFacts.rpc11_T5`**: the combined T5 bound for `1 ≤ j_x ≤ N_h` (no other input than the
  seed of the reduced state, i.e. the restart sizes at `j_x` through `rpc_seed_MFD`):
  `|rpcOut o| ≤ (3/2)(1 + K_M)·γ_δ·ϑ_{j_x} + K_T·(σ/|β_{a,N_h}|)·ϑ_{N_h}²·ǧ_{N_h}`,
  `K_T = rpc11K … (N_h + 1 − j_x) m̄_top`, `m̄_top = max(1, 2Λ₁)^{N_h+1−j_x}m̄₀`.
  Chain: `rpc9_chainD` (masses, defects; targets `m̄_i`) → `rpc_out_trajC` at `m̄ = m̄_top` →
  `rpc10_cst_bd` (`|n_{ab}X'| ≤ M_aM_b·(…)`) → `M_aM_b = 2s_{N_h}²σM_b ≤ c_u²(σ/|β|)‖M_{N_h}‖²ǧ²`
  (`hMaM`, `hMbM`) → `‖M_k‖ ≤ (3/2)ϑ_k` → `rpc_uB_le` with `rpc11_zBelowD`.
* **`MasterFacts.rpc11_T5δ`** (`Spin2/Restart/RestartPairChain12`): with `N ≤ j_x + C_δ`, the constant is `K_T(C_δ, max(1,2Λ₁)^{C_δ}m̄₀)`
  — a constant depending on `L` (master constants) and `C_δ` only.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The `ZBelowU1` constant of the master construction at `K_λ`. -/
def rpc11KM (Kl : ℝ) : ℝ :=
  zbKM L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp
    ((M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) Kl

theorem rpc11KM_nonneg (Kl : ℝ) : 0 ≤ M.rpc11KM Kl := by
  unfold rpc11KM zbKM
  have := le_max_right (spinMK L M.core.cg M.core.Ke M.core.KZ
    (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0
  have := le_max_right (spinMK L M.core.cg M.core.Ke M.core.KZ
    (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0
  have := le_max_right (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0
  linarith

set_option maxHeartbeats 4000000 in
/-- **`ZBelowU1` along windowed trajectories** (exported from the construction inside
`twoPtSq_of_gam_flowBD`). -/
theorem rpc11_zBelowD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (lam : ℕ → ℂ) {Kl : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    ZBelowU1 R Nh m b μ₀ lam (M.rpc11KM Kl) := by
  have hL49 := M.core.hL49
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hB := M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := M.flow
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk.le).1.le, ((hD k hk.le).2.1).trans M.eps_le⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  have hpairP := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD
  obtain ⟨hW, hWS, -, -⟩ := wk_inputsD M.wkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) M.Kp :=
    fun x _ => hpairP (ptsX x)
  have hpairS : ∀ x : Lam 2 L N, x ≠ 0 →
      HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) M.Kp :=
    fun x _ => hpairP (ptsS x)
  have hrem := gamRemRel_ofA R hb hKp M.cGB_nonneg M.cw_nonneg hval hg ha hpair hB hW
  have hremS := gamRemRelS_ofA R hb hKp M.cGB_nonneg M.cw_nonneg hval hg ha hpairS hB hWS
  have hcγ : 0 ≤ (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp) :=
    mul_nonneg (add_nonneg M.cGB_nonneg M.cw_nonneg) (by linarith)
  have hg' : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := fun k hk => (hD k hk).1
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hA := gamFormA_of R hP hb hm.1.le hcγ hg' hpair hrem
  have hB' := gamFormB_of R hP hb hm.1.le hcγ hg' hpairS hremS
  exact zBelowU1_of_forms R hMag hm.1.le hb hg' hKl hl hsmall (add_nonneg hKp hcγ)
    (add_nonneg hKp hcγ) hA hB'

/-- The combined T5 constant: `K_Z(c_S) + (9/4)c_u²·(n(2Λ₁⁺ + Λ₂⁺)m̄ + L²Λ₁⁺m̄ + c_{Lab}c_S)`,
`c_S = m̄ + (4C₁t+1)cm̄ + 8(4C₁t+1)m̄ + 1`. -/
def rpc11K (r₀ C₁t Λ₁ Λ₂ mb : ℝ) (n : ℕ) : ℝ :=
  M.rpcKZ r₀ (mb + (4 * C₁t + 1) * M.core.c * mb + 8 * ((4 * C₁t + 1) * mb) + 1) +
    9 / 4 * pairUnitC M ^ 2 * ((n : ℝ) * ((2 * max Λ₁ 0 + max Λ₂ 0) * mb) +
      (L : ℝ) ^ 2 * (max Λ₁ 0 * mb) +
      cLab L * (mb + (4 * C₁t + 1) * M.core.c * mb + 8 * ((4 * C₁t + 1) * mb) + 1))

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The combined T5 bound for `1 ≤ j_x ≤ N_h`** (see the module docstring). -/
theorem rpc11_T5 : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ m0 (Nh + 1 - (Obs.coal L (0 : Lam 2 L N) x))) + (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ m0 (Nh + 1 - (Obs.coal L (0 : Lam 2 L N) x))) + 8 * ((4 * C₁t + 1) * (rpc9Mb Λ₁ m0 (Nh + 1 - (Obs.coal L (0 : Lam 2 L N) x)))) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)) +
        M.rpc11K r₀ C₁t Λ₁ Λ₂ (rpc9Mb Λ₁ m0 (Nh + 1 - (Obs.coal L (0 : Lam 2 L N) x))) (Nh + 1 - (Obs.coal L (0 : Lam 2 L N) x)) * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 := by
  obtain ⟨C₁w, C₁t, hC₁w, hC₁t, hTC⟩ := M.rpc_out_trajC
  obtain ⟨C₁v, C₁m, Λ₁, Λ₂, hC₁v, hC₁m, hCH⟩ := rpc9_chainD M
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ Mb k₀ m0 γδ hσ hMb hMbM hMaM hk₀ hK0 hm0 h8w h8t
    h8v h8m hmAB hu
  have hL49 : 49 ≤ L := M.core.hL49
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hN2 : 2 ≤ N := by omega
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set μ₀ := b - m with hμ₀
  set t : Hist.Seq (Xs (R.withMsq m)) := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨hval, hvalL, hGC, hRI⟩ :=
    M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hρ0 : 0 ≤ (R.withMsq m).ρ := (hRI 0 (Nat.zero_le _)).1.2.2.2.1
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := ((hRI 0 (Nat.zero_le _)).1).2.2.2.2.1
  have hs : ∀ n, 0 < histS (R.withMsq m) n t := fun n => histS_pos' (R.withMsq m) hρ0 hρ8 t n
  have hsN := hs Nh
  set Ma := 2 * histS (R.withMsq m) Nh t ^ 2 * σ with hMad
  have hMa : 0 < Ma := by positivity
  set mb := rpc9Mb Λ₁ m0 with hmbd
  set mT := mb (Nh + 1 - j) with hmTd
  have hmT0 : 0 < mT := rpc9Mb_pos hm0 _
  -- the joint induction
  obtain ⟨-, hmassC, hdefC⟩ := hCH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD x hx h1 hj o ho
    hlo hso Ma Mb hMa hMb k₀ hk₀ hK0 m0 hm0 h8v h8m
  set ρ : ℕ → ℝ := fun n => Ma * Mb * (Λ₁ * mb (n - 1 - j)) /
    (histS (R.withMsq m) n t * histS (R.withMsq m) n t) with hρd
  have hρ : ∀ n, j < n → n ≤ Nh + 1 → ∀ c ∈ blockIdx (L := L) (N := N) n,
      ‖LocObs.mass2 ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) n t).V c :
        SA .two (Lam 2 L N)).ab‖ ≤ ρ n := fun n h1' h2' c _ => by
    rw [hρd]; dsimp only
    rw [le_div_iff₀ (mul_pos (hs n) (hs n))]; exact hmassC n h1' h2' c
  have hρm : ∀ n, j < n → n ≤ Nh + 1 →
      (2 * histS (R.withMsq m) Nh t ^ 2 * σ * Mb)⁻¹ *
        (ρ n * (histS (R.withMsq m) n t * histS (R.withMsq m) n t)) ≤ mT / 2 := by
    intro n h1' h2'
    have e : (2 * histS (R.withMsq m) Nh t ^ 2 * σ * Mb)⁻¹ *
        (ρ n * (histS (R.withMsq m) n t * histS (R.withMsq m) n t)) = Λ₁ * mb (n - 1 - j) := by
      rw [hρd]; dsimp only
      have := hs n
      field_simp
      rw [hMad]
    rw [e]
    refine (rpc9Mb_succ hm0 _).trans ?_
    have := rpc9Mb_mono (Λ₁ := Λ₁) hm0 (show n - 1 - j + 1 ≤ Nh + 1 - j by omega)
    linarith
  -- the output bound at `m̄ = m̄_top`
  obtain ⟨hout, hlastD⟩ := hTC R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1
    hs2 hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso hσ hMb hMbM hk₀ hK0 hmT0
    (rpc9_seed hC₁w h8w (rpc9Mb_ge hm0 _)) (rpc9_seed hC₁t h8t (rpc9Mb_ge hm0 _)) ρ hρ hρm hmAB hu
  -- `n_{ab}X'`
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, hCf0, -, -, hρ8', hspl, -⟩ := M.flow
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hspl' : SplitSmall R.P L R.ρ := by rw [hP, hRρ]; exact hspl
  have hVN := M.lastValid N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hh0 : b = μ₀ + m := by rw [hμ₀]; ring
  have hGCN : GoodCov2 (Nh + 1) (histS (R.withMsq m) (Nh + 1) t) (lC R Nh m b μ₀) := by
    have hℓ : 0 < R.ℓ := Fact.out
    have H : RawInv (R.withMsq m) (Nh + 1) (histOut (R.withMsq m) Nh t).st :=
      rawInv_histU (R.withMsq m) hval hvalL t (Nh + 1) le_rfl
    obtain ⟨hC0, -, -, -⟩ := LastN.covN hVN H
    have hρ0' : 0 ≤ (R.withMsq m).ρ := hvalL.2.2.2.2.1
    have hρ8'' : (R.withMsq m).ρ ≤ 1 / 8 := hvalL.2.2.2.2.2.1
    set st := (histOut (R.withMsq m) Nh t).st with hst
    have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ8 : ‖stZeta (R.withMsq m) st‖ ≤ 1 / 8 :=
      (absorb_le (R.withMsq m) hρ0' _ _).trans hρ8''
    have hmono : fscale (stZ' (R.withMsq m) st) * (R.withMsq m).ℓ / 4 ≤
        histS (R.withMsq m) (Nh + 1) t := by
      have hsc := scale_ok hZ hζ8 hℓ
      have e : stZ' (R.withMsq m) st = st.Z * (1 + stZeta (R.withMsq m) st) := rfl
      have eℓ : (R.withMsq m).ℓ = R.ℓ := rfl
      rw [e]
      show _ ≤ fscale st.Z * (R.withMsq m).ℓ
      rw [eℓ]
      have hp1 := mul_pos (fscale_pos hZ) hℓ
      have hp2 := mul_pos (fscale_pos (mul_ne_zero hZ
        (one_add_ne_zero (show ‖stZeta (R.withMsq m) st‖ < 1 by linarith)))) hℓ
      linarith
    exact hC0.mono hmono
  set A := Ma * Mb * (max Λ₁ 0 * mT) with hAd
  set Dd := Ma * Mb * (max Λ₂ 0 * mT) with hDd
  have hMaMb : 0 < Ma * Mb := mul_pos hMa hMb
  have hA0 : 0 ≤ A := mul_nonneg hMaMb.le (mul_nonneg (le_max_right _ _) hmT0.le)
  have hmass' : ∀ n, j < n → n ≤ Nh + 1 → ∀ c : Fin 2 → ℕ,
      ‖LocObs.mass2 ((obsHistFrom (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) n t).V c :
        SA .two (Lam 2 L N)).ab‖ * (histS (R.withMsq m) n t * histS (R.withMsq m) n t) ≤ A := by
    intro n h1' h2' c
    refine (hmassC n h1' h2' c).trans (mul_le_mul_of_nonneg_left ?_ hMaMb.le)
    have hm1 : mb (n - 1 - j) ≤ mT := rpc9Mb_mono hm0 (by omega)
    have hm2 := (rpc9Mb_pos (Λ₁ := Λ₁) hm0 (n - 1 - j)).le
    calc Λ₁ * mb (n - 1 - j) ≤ max Λ₁ 0 * mb (n - 1 - j) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm2
      _ ≤ max Λ₁ 0 * mT := mul_le_mul_of_nonneg_left hm1 (le_max_right _ _)
  have hdef' : ∀ k, j ≤ k → k ≤ Nh →
      ‖-pdefAB2 (ptsX x) k (histCovO (R.withMsq m) t k)
          (hVR (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) t k) +
        xAB2 (ptsX x) k (histCovO (R.withMsq m) t k)
          (hVR (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) t k)
          (hWR (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) t k)
          (hKR (R.withMsq m) (ptsX x) j (rpcRed R m b μ₀ x o) t k)‖ ≤ Dd := by
    intro k h1' h2'
    refine (hdefC k h1' h2').trans (mul_le_mul_of_nonneg_left ?_ hMaMb.le)
    have hm1 : mb (k - j) ≤ mT := rpc9Mb_mono hm0 (by omega)
    have hm2 := (rpc9Mb_pos (Λ₁ := Λ₁) hm0 (k - j)).le
    calc Λ₂ * mb (k - j) ≤ max Λ₂ 0 * mb (k - j) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hm2
      _ ≤ max Λ₂ 0 * mT := mul_le_mul_of_nonneg_left hm1 (le_max_right _ _)
  set cS := mT + (4 * C₁t + 1) * M.core.c * mT + 8 * ((4 * C₁t + 1) * mT) + 1 with hcSd
  have hcst := rpc10_cst_bd R hP hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hVN hL8 hb (le_of_eq hh0) x
    hx h1 hj o ho hlo hs hGC hGCN hA0 hmass' hdef' hlastD
  -- `M_aM_b ≤ c_u²(σ/|β|)‖M‖²ǧ²`
  set lam := lamHat2 R (ptsX x) (zV b) m b μ₀ with hlamd
  set Mc := Mmag R m b μ₀ lam Nh with hMcd
  set g := (t Nh).1 with hgd
  set cu := pairUnitC M with hcud
  have hcu : 0 ≤ cu := pairUnitC_nonneg M
  have hg0 : 0 < g := (hD Nh le_rfl).1
  have hg1 : g ≤ 1 := ((hD Nh le_rfl).2.1).trans M.eps_le
  have hβ0 : hBeta R m b μ₀ x Nh ≠ 0 := by
    have htop := (M.topD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1
    obtain ⟨q, -, -, hlq⟩ :=
      (M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b)).2.2
    exact (hBeta_rel_of R hNh hb x
      (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (zV b) (zV_mua_ne hb))
      (fun k hk => (hlq k hk).1) htop Nh le_rfl).1
  set hb0 := ‖hBeta R m b μ₀ x Nh‖ with hb0d
  have hhb0 : 0 < hb0 := norm_pos_iff.2 hβ0
  have hMaMbB : Ma * Mb ≤ cu ^ 2 * (σ / hb0) * ‖Mc‖ ^ 2 * g ^ 2 := by
    have h2s : 2 * histS (R.withMsq m) Nh t ^ 2 ≤ cu * ‖Mc‖ * g / hb0 := by
      rw [le_div_iff₀ hhb0]; exact hMaM
    have hMcg : 0 ≤ cu * ‖Mc‖ * g := by positivity
    calc Ma * Mb = 2 * histS (R.withMsq m) Nh t ^ 2 * σ * Mb := rfl
      _ ≤ cu * ‖Mc‖ * g / hb0 * σ * (cu * ‖Mc‖ * g) := by
          gcongr
          exact hMbM
      _ = cu ^ 2 * (σ / hb0) * ‖Mc‖ ^ 2 * g ^ 2 := by ring
  -- `‖M_k‖ ≤ (3/2)ϑ_k`
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX x)
  have hMag := magAt_ofD R M.magD hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hMk : ∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ 3 / 2 * varthJ R m b μ₀ k := by
    intro k hk
    set F := max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 with hFd
    set v := varthJ R m b μ₀ k with hvd
    have hgk : 0 < (t k).1 := (hD k hk).1
    have hv : 0 ≤ v := Real.rpow_nonneg (div_pos hb hgk).le _
    have hMl := hMag lam M.Kp hKp hl k hk
    have hMl' : ‖Mmag R m b μ₀ lam k - ((v : ℝ) : ℂ)‖ ≤ F * v * (t k).1 :=
      hMl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hv)
        hgk.le)
    have hFg : F * (t k).1 ≤ 1 / 2 := hsmall k hk
    have h1' : ‖Mmag R m b μ₀ lam k‖ ≤ ‖Mmag R m b μ₀ lam k - ((v : ℝ) : ℂ)‖ + ‖((v : ℝ) : ℂ)‖ :=
      norm_le_norm_sub_add _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hv] at h1'
    have h2' : F * v * (t k).1 ≤ 1 / 2 * v := by
      have e : F * v * (t k).1 = F * (t k).1 * v := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hFg hv
    linarith
  set v := varthJ R m b μ₀ Nh with hvd
  have hv : 0 ≤ v := Real.rpow_nonneg (div_pos hb hg0).le _
  have hMc2 : ‖Mc‖ ^ 2 ≤ 9 / 4 * v ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) (hMk Nh le_rfl) 2
    calc ‖Mc‖ ^ 2 ≤ (3 / 2 * v) ^ 2 := this
      _ = 9 / 4 * v ^ 2 := by ring
  have hMaMbV : Ma * Mb ≤ 9 / 4 * cu ^ 2 * (σ / hb0) * v ^ 2 * g := by
    refine hMaMbB.trans ?_
    have hsb : 0 ≤ σ / hb0 := div_nonneg hσ.le hhb0.le
    have hg2 : g ^ 2 ≤ g := by nlinarith
    calc cu ^ 2 * (σ / hb0) * ‖Mc‖ ^ 2 * g ^ 2 ≤ cu ^ 2 * (σ / hb0) * (9 / 4 * v ^ 2) * g := by
          gcongr
      _ = 9 / 4 * cu ^ 2 * (σ / hb0) * v ^ 2 * g := by ring
  -- `uB`
  have hZ := M.rpc11_zBelowD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD lam hKp hl hsmall
  have huB := rpc_uB_le R hZ x hx h1 hj
  have hKM := M.rpc11KM_nonneg M.Kp
  have hgj1 : (t j).1 ≤ 1 := ((hD j hj).2.1).trans M.eps_le
  have hgj0 : 0 ≤ (t j).1 := (hD j hj).1.le
  have huB' : ‖uB R m b μ₀ x j‖ ≤ 3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b μ₀ j := by
    refine huB.trans ?_
    have h1' : 1 + M.rpc11KM M.Kp * (t j).1 ≤ 1 + M.rpc11KM M.Kp := by
      have := mul_le_mul_of_nonneg_left hgj1 hKM; linarith
    have h2' := hMk j hj
    have hvj : 0 ≤ varthJ R m b μ₀ j := Real.rpow_nonneg (div_pos hb (hD j hj).1).le _
    calc (1 + M.rpc11KM M.Kp * (t j).1) * ‖Mmag R m b μ₀ lam j‖
        ≤ (1 + M.rpc11KM M.Kp) * (3 / 2 * varthJ R m b μ₀ j) :=
          mul_le_mul h1' h2' (norm_nonneg _) (by linarith)
      _ = 3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b μ₀ j := by ring
  -- assembly
  have hγ : 0 ≤ γδ := (norm_nonneg _).trans hu
  have hn : ‖PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ ≤
      Ma * Mb * (((Nh + 1 - j : ℕ) : ℝ) * ((2 * max Λ₁ 0 + max Λ₂ 0) * mT) +
        (L : ℝ) ^ 2 * (max Λ₁ 0 * mT) + cLab L * cS) := by
    refine hcst.trans (le_of_eq ?_)
    rw [hAd, hDd, hMad]; ring
  set Q := ((Nh + 1 - j : ℕ) : ℝ) * ((2 * max Λ₁ 0 + max Λ₂ 0) * mT) +
      (L : ℝ) ^ 2 * (max Λ₁ 0 * mT) + cLab L * cS with hQd
  have hQ0 : 0 ≤ Q := by
    have := (norm_nonneg _).trans hn
    nlinarith [hMaMb]
  have hn' : ‖PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ ≤
      9 / 4 * cu ^ 2 * (σ / hb0) * v ^ 2 * g * Q :=
    hn.trans (mul_le_mul_of_nonneg_right hMaMbV hQ0)
  have hu' : γδ * ‖uB R m b μ₀ x j‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b μ₀ j) :=
    mul_le_mul_of_nonneg_left huB' hγ
  have hout' : ‖rpcOut R m b μ₀ x o‖ ≤ γδ * ‖uB R m b μ₀ x j‖ +
      ‖PtCorr2.nAB (zCstR R Nh m b μ₀ (fun _ => rpcRed R m b μ₀ x o) x)‖ +
      M.rpcKZ r₀ cS * (σ / hb0) * v ^ 2 * g := hout
  have e : M.rpc11K r₀ C₁t Λ₁ Λ₂ mT (Nh + 1 - j) * (σ / hb0) * v ^ 2 * g =
      9 / 4 * cu ^ 2 * (σ / hb0) * v ^ 2 * g * Q + M.rpcKZ r₀ cS * (σ / hb0) * v ^ 2 * g := by
    rw [hQd, hcSd]; unfold rpc11K; ring
  have hfin : ‖rpcOut R m b μ₀ x o‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b μ₀ j) +
        M.rpc11K r₀ C₁t Λ₁ Λ₂ mT (Nh + 1 - j) * (σ / hb0) * v ^ 2 * g := by
    rw [e]; linarith
  exact hfin


end MasterFacts

end

end Spin2
