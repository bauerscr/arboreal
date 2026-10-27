import Spin2.Restart.RestartPairChain6
import Spin2.Restart.RestartPairChain2

/-!
# T5, item (5): wiring of the seed — the combined bound from the one-point sizes of `o` at `j_x`

* **`MasterFacts.rpc_seed_MFD`**: `rpc_seed_gen` + `rpc_seed_dxStd` along every trajectory in
  `D_ε`: for a general observable state `o` at `j_x ≤ N_h` with sizes in `wM(M_a, M_b)`
  (`‖V(B)‖ ≤ v_T`, `‖𝒲(B)‖ ≤ w_T`, `A^{(…)}‖K(X)‖_{wM1} ≤ k_{xT}`, `A^{(…)}w_{ab}‖K(X)_{ab}‖ ≤ k₂`,
  `A⁴(c_xǧ_{j_x}³ + k_{xT} + k₂) ≤ 1`), the reduced state satisfies
  `A^{(|𝓑(X)|-4)_+}‖K'_{j_x}(X)‖_{wM(M_a,M_b)} ≤ (2ι(v_T,w_T)A)^{(L+18)²}` — the input `k₀` of
  `rpc_chain_sizesD` / `rpc_out_trajC`.
* **`MasterFacts.rpc_out_trajS`**: `rpc_out_trajC` with `k₀ = (2ιA)^{(L+18)²}` from the one-point
  sizes of `o` at `j_x` in `wM(2s_{N_h}²σ, M_b)` (e.g. `o = obsHistFrom … m δ j_x`, sizes from the
  restart envelopes of T4, `obs_hist_restartB`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs Obs.SA Obs2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **The seed of the reduced state of a general state at `j_x ≤ N_h`** (master constants). -/
theorem rpc_seed_MFD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh)
    (o : ObsSt .two L N) (ho : o.IsObs) {Ma Mb vT wT kxT k2 : ℝ} (hvT : 0 ≤ vT) (hwT : 0 ≤ wT)
    (hkxT : 0 ≤ kxT) (hk2 : 0 ≤ k2)
    (hVt : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      oTo (wM Ma Mb) (Obs.coal L (0 : Lam 2 L N) x)
        (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.V q) ≤ ENNReal.ofReal vT)
    (hWt : ∀ q ∈ blockIdx (L := L) (N := N) (Obs.coal L (0 : Lam 2 L N) x),
      oTo (wM Ma Mb) (Obs.coal L (0 : Lam 2 L N) x)
        (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.W q) ≤ ENNReal.ofReal wT)
    (hKt : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        oTo (wM1 Ma Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.K X) ≤ ENNReal.ofReal kxT)
    (hK2 : ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal (R.A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        ((wM Ma Mb).ab * Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (o.K X : SA .two (Lam 2 L N)).ab) ≤
        ENNReal.ofReal k2)
    (hsmT : M.core.A ^ 4 * (cx M.core.κ M.core.cT *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ^ 3 + kxT + k2) ≤ 1) :
    ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
      ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
        oTo (wM Ma Mb) (Obs.coal L (0 : Lam 2 L N) x)
          (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          ((rpcRed R m b μ₀ x o).K X) ≤
        ENNReal.ofReal ((2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2)) := by
  set j := Obs.coal L (0 : Lam 2 L N) x with hjd
  set R' := R.withMsq m with hR'
  set t : Hist.Seq (Xs R') := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with htd
  obtain ⟨H, hm1, F1⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  obtain ⟨hV, hVL, -, hRI⟩ := M.core.pairTrajD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hRA' : R'.A = M.core.A := hRA
  have hSB' : StepBounds L R'.A M.core.C₀x M.core.ηx M.core.εsx M.core.CKx M.core.C₂x
      M.core.CDx M.core.Cqx M.core.Clx M.core.cSx := by rw [hRA']; exact M.core.hSBx
  have hcR : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x = M.core.c := by
    rw [M.core.hc]; exact cR_congr (show R.ℓ = M.core.ℓ from hRℓ) _ _ _
  have hβ2 := betaL_ge (by have := M.core.hL49; omega : 8 ≤ L)
  have hβ0 : 0 ≤ betaL L := by linarith
  have ht := inDh_rg_of_D R' F1 hD j hj
  have hρ0 : 0 ≤ R'.ρ := (hRI j hj).1.2.2.2.1
  have hρ8 : R'.ρ ≤ 1 / 8 := (hRI j hj).1.2.2.2.2.1
  have hA1 : 1 ≤ R'.A := by rw [hRA']; have := M.core.hA2; linarith
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by have := M.core.hL49; omega)
  have hmj : |R'.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact hm1 j h
    · obtain rfl : j = Nh := le_antisymm hj h
      have h1 := msq_horizon (L := (L : ℝ)) (by linarith) hm.2 (Nh := j) (k := 0) (by omega)
      simp only [pow_zero, one_pow, inv_one] at h1
      have h2 : ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ (j + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 (by omega)) 2
      show |m| * ((L : ℝ) ^ j) ^ 2 ≤ 1
      rw [abs_of_pos hm.1]
      exact (mul_le_mul_of_nonneg_left h2 hm.1.le).trans h1
  have hε1 : cR R' ((L : ℝ) ^ 2) M.core.cm M.core.C₂x * M.core.ε ≤ 1 := by
    rw [hcR]; exact M.core.hcε
  have hseed := rpc_seed_gen R' hSB' hV hm1 hβ0 (by norm_num : (1 / 2 : ℝ) ≤ 1) H hρ0 hρ8 hA1 t hj
    ht (hRI j hj).1 hmj hε1 (ptsX x) o ho (dxStd (L := L) (N := N) x) hvT hwT hkxT hk2 hVt hWt hKt
    hK2 (by rw [hRA']; exact hsmT)
  have hL2 : 2 ≤ L := by have := M.core.hL49; omega
  have hjN : j ≤ N := by omega
  have hdx := rpc_seed_dxStd R' hL2 x hjN hvT hwT hA1
  intro X hX
  refine (hseed X hX).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hRA'] at hdx ⊢
  exact hdx

set_option linter.unusedVariables false in
set_option maxHeartbeats 8000000 in
/-- **The two-point output of a general state at `j_x ≤ N_h` from its one-point sizes at `j_x`**
(`rpc_out_trajC` with the seed `rpc_seed_MFD`). -/
theorem rpc_out_trajS : ∃ C₁w C₁t : ℝ, 0 ≤ C₁w ∧ 0 ≤ C₁t ∧
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
    {σ Mb vT wT kxT k2 mbar γδ : ℝ} (hσ : 0 < σ) (hMb : 0 < Mb)
    (hMbM : Mb ≤ pairUnitC M *
      ‖Mmag R m b (b - m) (lamHat2 R (ptsX x) (zV b) m b (b - m)) Nh‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1)
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
    (hmbar : 0 < mbar) (h8 : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁w * ((4 * C₁w + 1) * mbar))
    (h8' : 8 * (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) ≤ vck C₁t * ((4 * C₁t + 1) * mbar)) (ρ : ℕ → ℝ)
    (hρ : ∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 →
      ∀ c ∈ blockIdx (L := L) (N := N) n,
      ‖LocObs.mass2 ((PtCorr2.obsHistFrom (R.withMsq m) (ptsX x) (Obs.coal L (0 : Lam 2 L N) x)
        (rpcRed R m b (b - m) x o) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))).V c :
          SA .two (Lam 2 L N)).ab‖ ≤ ρ n)
    (hρm : ∀ n, Obs.coal L (0 : Lam 2 L N) x < n → n ≤ Nh + 1 →
      (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ * Mb)⁻¹ *
        (ρ n * (histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) *
          histS (R.withMsq m) n (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))) ≤ mbar / 2)
    (hmAB : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
      (mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1) *
      M.core.ℓ ^ 2) * m * (L : ℝ) ^ (2 * N) ≤ 1)
    (hu : ‖ε ((o.u : Obs.SA .two (Lam 2 L N)).a)‖ ≤ γδ),
    ‖rpcOut R m b (b - m) x o‖ ≤
      γδ * ‖uB R m b (b - m) x (Obs.coal L (0 : Lam 2 L N) x)‖ +
        ‖PtCorr2.nAB (zCstR R Nh m b (b - m) (fun _ => rpcRed R m b (b - m) x o) x)‖ +
        M.rpcKZ r₀ (mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1) *
          (σ / ‖hBeta R m b (b - m) x Nh‖) *
          varthJ R m b (b - m) Nh ^ 2 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ∧
    ‖lastDefR R Nh m b (b - m) (fun _ => rpcRed R m b (b - m) x o) x‖ ≤
      cLab L * (mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1) *
        (2 * histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) ^ 2 * σ * Mb)  := by
  obtain ⟨C₁w, C₁t, hC₁w, hC₁t, hC⟩ := rpc_out_trajC M
  refine ⟨C₁w, C₁t, hC₁w, hC₁t, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b hD r₀ hr₀ hr₀1 hJ Kt hK hmT hmA hsmA hs1 hs2
    hs3 hs4 hs5 hsmall x hx h1 hj o ho hlo hso σ Mb vT wT kxT k2 mbar γδ hσ hMb hMbM hvT hwT hkxT
    hk2 hVt hWt hKt hK2 hsmT hmbar h8 h8' ρ hρ hρm hmAB hu
  have hk₀ : 0 ≤ (2 * rpIota vT wT * M.core.A) ^ ((L + 18) ^ 2) := by
    have := one_le_rpIota hvT hwT; have := M.core.hA2; positivity
  exact hC R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hK hmT hmA hsmA hs1 hs2 hs3 hs4 hs5
    hsmall x hx h1 hj o ho hlo hso hσ hMb hMbM hk₀
    (M.rpc_seed_MFD R hP hi0 hRℓ hRA hRρ (by omega) hNh hm hD x hj o ho hvT hwT hkxT hk2 hVt hWt
      hKt hK2 hsmT) hmbar h8 h8' ρ hρ hρm hmAB hu

end MasterFacts

end

end Spin2
