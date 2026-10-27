import Spin2.Cont.ContWire5
import Spin2.Cont.ContFx1

set_option autoImplicit false

/-!
# Option 2 (fixed `β_R`), Phase 2, layer 1: the T5 bound with the window `hmAB` at `m̄₀`

**`MasterFacts.fx_T5S`**: `rpc12_T5S` with the window `hmAB` at the seed constant `m̄₀` itself
(not at `rpc9Mb Λ₁ m̄₀ C_δ = max(1,2Λ₁)^{C_δ}m̄₀`). Proof: `rpc11_T5δ` at `σ' = Kσ`, seed `k₀/K`,
`m̄₀' = m̄₀/K`, `K = max(1,2Λ₁)^{C_δ}`; the reduced chain is pure `ab` (`obsAbInv_redSt`), so its
seed in `wM(2s²Kσ, M_b)` is `K^{-1}` times that in `wM(2s²σ, M_b)` (`fx_oTo_wM_ab_le`), and
`rpc9Mb Λ₁ (m̄₀/K) C_δ = m̄₀`. The conclusion constant is `fxKT = rpc11K(m̄₀, C_δ)·K`.

**`MasterFacts.fx_T5M`**: `cw2_T5M` (`M_b = pM(ptsS x)_{N_h}`, weight conditions discharged) on top
of `fx_T5S`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The rescaled T5 constant `rpc11K(m̄₀, C_δ)·max(1,2Λ₁)^{C_δ}`. -/
def fxKT (r₀ C₁t Λ₁ Λ₂ m0 : ℝ) (Cδ : ℕ) : ℝ :=
  M.rpc11K r₀ C₁t Λ₁ Λ₂ m0 Cδ * (max 1 (2 * Λ₁)) ^ Cδ

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **The T5 bound with the window at `m̄₀`** (rescaled `a`-weight; see the module docstring). -/
theorem fx_T5S : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (m0 + (4 * C₁t + 1) * M.core.c * m0 + 8 * ((4 * C₁t + 1) * m0) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)) +
        M.fxKT r₀ C₁t Λ₁ Λ₂ m0 Cδ * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1   := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.rpc11_T5δ
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ Mb vT wT kxT k2 m0 γδ hσ hMb hMbM hMaM hvT hwT
    hkxT hk2 hVt hWt hKt hK2 hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hu
  set K : ℝ := (max 1 (2 * Λ₁)) ^ Cδ with hKd
  have hK1 : 1 ≤ K := one_le_pow₀ (le_max_left _ _)
  have hK0 : 0 < K := by linarith
  set k := (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) with hkd
  have hk₀ : 0 ≤ k := by
    have := one_le_rpIota hvT hwT; have := M.core.hA2; positivity
  have hseed := M.rpc_seed_MFD R hP hi0 hRℓ hRA hRρ (by omega) hNh hm hD x hj o ho hvT hwT hkxT hk2
    hVt hWt hKt hK2 hsmT
  have hseed' : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        Obs2.oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
          (K * σ)) Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))
          ((rpcRed R m b (b - m) x o).K X) ≤ ENNReal.ofReal (k / K) := by
    intro X hX
    have hF : ((rpcRed R m b (b - m) x o).K X : SA .two (Lam 2 L N)).a = 0 ∧
        ((rpcRed R m b (b - m) x o).K X : SA .two (Lam 2 L N)).b = 0 :=
      Obs2.mem_abSub.1 ((PtCorr2.obsAbInv_redSt _ _ _ _ _ _ _ _ _ _).K X hX)
    rw [show 2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * (K * σ) =
      K * (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) by ring]
    exact PtCorr2.fx_oTo_wM_ab_le hK0 _ _ _ hF (hseed X hX)
  have hdiv : ∀ C : ℝ, 8 * k ≤ vck C * ((4 * C + 1) * m0) →
      8 * (k / K) ≤ vck C * ((4 * C + 1) * (m0 / K)) := fun C h => by
    have := div_le_div_of_nonneg_right h hK0.le
    calc 8 * (k / K) = 8 * k / K := (mul_div_assoc _ _ _).symm
      _ ≤ vck C * ((4 * C + 1) * m0) / K := this
      _ = _ := by ring
  have hmB : rpc9Mb Λ₁ (m0 / K) Cδ = m0 := by
    unfold rpc9Mb; rw [← hKd]; field_simp
  have hmAB' : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * ((rpc9Mb Λ₁ (m0 / K) Cδ) +
      (4 * C₁t + 1) * M.core.c * (rpc9Mb Λ₁ (m0 / K) Cδ) + 8 * ((4 * C₁t + 1) *
      (rpc9Mb Λ₁ (m0 / K) Cδ)) + 1) * M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    rw [hmB]; exact hmAB
  have h := hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall x hx h1 hj o ho hlo hso (σ := K * σ) (k₀ := k / K) (m0 := m0 / K) (mul_pos hK0 hσ) hMb
    hMbM hMaM (div_nonneg hk₀ hK0.le) hseed' (div_pos hm0 hK0) (hdiv _ h8w) (hdiv _ h8t)
    (hdiv _ h8v) (hdiv _ h8m) Cδ hδ hmAB' hu
  rw [hmB] at h
  refine h.trans (le_of_eq ?_)
  unfold fxKT
  rw [← hKd]
  ring

set_option linter.unusedVariables false in
set_option maxHeartbeats 16000000 in
/-- **`fx_T5S` with `M_b = pM(ptsS x)_{N_h}` and the weight conditions discharged.** -/
theorem fx_T5M : ∃ C₁w C₁t C₁v C₁m Λ₁ Λ₂ : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧ 0 ≤ C₁v ∧ 0 ≤ C₁m ∧
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
    {σ vT wT kxT k2 m0 γδ : ℝ} (hσ : 0 < σ) (hvT : 0 ≤ vT) (hwT : 0 ≤ wT) (hkxT : 0 ≤ kxT) (hk2 : 0 ≤ k2)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.V q) ≤ ENNReal.ofReal vT)
    (hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      oTo (wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.W q) ≤ ENNReal.ofReal wT)
    (hKt : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        oTo (wM1 (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.K X) ≤ ENNReal.ofReal kxT)
    (hK2 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        ((wM (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ) (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh)).ab * Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))) (o.K X : SA .two (Lam 2 L N)).ab) ≤ ENNReal.ofReal k2)
    (hsmT : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1 ^ 3 + kxT + k2) ≤ 1)
    (hm0 : 0 < m0) (h8w : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * m0))
    (h8t : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * m0))
    (h8v : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁v * ((4 * C₁v + 1) * m0))
    (h8m : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁m * ((4 * C₁m + 1) * m0))
    (Cδ : ℕ) (hδ : N ≤ Obs.coal L (0 : Lam 2 L N) x + Cδ)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (m0 + (4 * C₁t + 1) * M.core.c * m0 + 8 * ((4 * C₁t + 1) * m0) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * (3 / 2 * (1 + M.rpc11KM M.Kp) * varthJ R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x)) +
        M.fxKT r₀ C₁t Λ₁ Λ₂ m0 Cδ * (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1   := by
  obtain ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, hT⟩ := M.fx_T5S
  refine ⟨C₁w, C₁t, C₁v, C₁m, Λ₁, Λ₂, hC₁w, hC₁t, hC₁v, hC₁m, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ vT wT kxT k2 m0 γδ hσ hvT hwT
    hkxT hk2 hVt hWt hKt hK2 hsmT hm0 h8w h8t h8v h8m Cδ hδ hmAB hu
  have hN2 : 2 ≤ N := by omega
  have hNh1 : 1 ≤ Nh := by omega
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (ptsX x)
  have hMaM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD _ M.Kp
    M.Kp_nonneg hl hsmall (ptsX x) hNh1 le_rfl le_rfl
  have hMbM := pM_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD _ M.Kp
    M.Kp_nonneg hl hsmall (ptsS x) hNh1 le_rfl le_rfl
  have hMa2 : pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh =
      2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 *
        ‖hBeta R m b (b - m) x Nh‖ := by
    rw [hBeta_eq_zV0 R m b (b - m) x hNh1]; rfl
  rw [hMa2] at hMaM
  have hmu : Obs2.OCoup2.mua (zV0 b) ≠ 0 := zV_mua_ne hb
  have hβS := (M.cw2_relBaseD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (ptsS x)
    (zV0 b) rfl hmu (by omega) Nh le_rfl).1
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, -, -, -, hρ8', -, -⟩ := id M.core.hC2
  have hρ0 : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρpos.le
  have hρ8 : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = M.core.ρ from hRρ]; exact hρ8'
  have hsN := histS_pos' (R.withMsq m) hρ0 hρ8 (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh
  have hMb : 0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) Nh := by
    unfold pM; exact mul_pos (mul_pos two_pos (pow_pos hsN 2)) hβS
  exact hT R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall x hx h1 hj o ho hlo hso hσ hMb hMbM hMaM hvT hwT hkxT hk2 hVt hWt hKt hK2 hsmT hm0
    h8w h8t h8v h8m Cδ hδ hmAB hu

end MasterFacts

end

end Spin2
