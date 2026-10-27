import PtCorr2.Pair.PairLin1
import Spin2.H0.H0Factors
import Spin2.Restart.RestartPairChain1
import PtCorr2.Restart.RestartPairB

/-!
# Pair linearity, part 3: the pair output of the relocated difference datum

Case (2), the trajectory `t = traj (rgData R) (L²) b μ₀`, `N = N_h + 2`. Two pairs `P`, `P'` with a
**common `b`-point** `P.b = P'.b`; data `o₁` (at `P`) and `o₂` (at `P'`) at scale `m` with equal
`∅`/`σ_b` parts (`prjSt false o₁ = prjSt false o₂`, e.g. two reference histories with the same
`b`-point, `prj_obsHistFrom`). The **difference datum**

  `δ = plDiffSt (rrStH o₁) o₂` (`a`, `ab` parts: relocated `o₁` minus `o₂`; `∅`/`b` parts: `o₂`'s)

has the reference `b`-part (`pl_diff_prj`, the `rpb_b_eq` hypothesis of T5).

* `plU`, `plY`: `u_k`, `ω_{Γ_k}Z_k` along the history from `m`; `plW = e^{−plU}·plY`.
* **`pl_pair_diff`** (`m ≤ j ≤ N_h`, any `γ`; hypotheses of `hist_omegaOF_from`, `IsObs`,
  `ObsLocInv` of the three data):
  `out(P,o₁) − out(P',o₂) − out(P',δ) = −D_a(γ + n_bW₂ + ε(u_{2,b})·s/s) − D_{ab}·s/s`,
  `out(Q,o) = −ε((u_j)_a)γ − n_{ab}(ω_{Γ_j}Z_j)` (`plOut`), `W₂ = plW(P', o₂)`, `s = sE W₂`,
  `D_• = ε(u_{1,•}) − ε(u_{2,•}) − ε(u_{3,•})` at scale `j`.
* **`pl_pair_diff_top`**: the same at `N_h + 1` with `Y = lastOF` (the `rpTopOut` form).
* `pl_rpcOut_eq`, `pl_rpTopOut_eq`: `rpcOut`/`rpTopOut` of a restarted state are `plOut` with the
  reference `γ = uB`.
* **`pl_rpc_diff`**, **`pl_rpTop_diff`** (`P' = ptsX y`, `o₂` = the reference history at `ms`,
  `s ≠ 0`): `plOut_{uB}(P, o₁) − rpcOut_y(ref) − rpcOut_y(δ at j_y) = −D_a·n_bW₂ − D_{ab}`
  (resp. `rpTopOut`, `rpRef` at `N_h + 1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Spin2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist PtCorr2

variable {L N : ℕ} [NeZero L]

section Gen

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `u_k` along the history from `m`. -/
def plU (P : ObsPts 2 L N) (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    OE .two (Lam 2 L N) := (obsHistFrom R P m o k t).u

/-- `ω_{Γ_k}Z_k` along the history from `m`. -/
def plY (P : ObsPts 2 L N) (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    OE .two (Lam 2 L N) := omegaCO (Γh R k t) (ZhOF R P m o k t)

theorem plW_eq (P : ObsPts 2 L N) (m : ℕ) (o : ObsSt .two L N) (k : ℕ) (t : Hist.Seq (Xs R)) :
    plW R P m o k t = oexp (-plU R P m o k t) * plY R P m o k t := rfl

theorem plWTop_eq (P : ObsPts 2 L N) (m : ℕ) (o : ObsSt .two L N) (Nh : ℕ)
    (t : Hist.Seq (Xs R)) :
    plWTop R P m o Nh t = oexp (-plU R P m o (Nh + 1) t) * lastOF R P m o Nh t := rfl

theorem plU_bulk (P : ObsPts 2 L N) (m : ℕ) {o : ObsSt .two L N} (h : o.IsObs) (k : ℕ)
    (t : Hist.Seq (Xs R)) : bulk (plU R P m o k t) = 0 := (obsHistFrom_isObs h t k).u

theorem pl_ch_ne {Nh : ℕ} (hN : Nh + 2 = N) (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) {i : ℕ} (hi : i ≤ Nh) : ch R i t ≠ 0 :=
  prod_ne_zero_iff.1 (chainFactors_ne R hN hspl hm0 hm hV hVL t).1 i (mem_range.2 (by omega))

/-- Equal `σ_b` projections (and a common `b`-point) give equal `σ_b` parts of `u_k`. -/
theorem pl_u_b_eq {P P' : ObsPts 2 L N} (hPb : P.b = P'.b) (m : ℕ) {o o' : ObsSt .two L N}
    (h : prjSt false o = prjSt false o') (t : Hist.Seq (Xs R)) (k : ℕ) :
    (plU R P m o k t : SA .two (Lam 2 L N)).b = (plU R P' m o' k t : SA .two (Lam 2 L N)).b := by
  have h1 := prj_obsHistFrom R false (P := P) (P' := ⟨P'.b, P'.b, P'.Ra⟩)
    (by show P'.b = P.b; exact hPb.symm) m o t k
  have h2 := prj_obsHistFrom R false (P := P') (P' := ⟨P'.b, P'.b, P'.Ra⟩) rfl m o' t k
  have h3 : prjSt false (obsHistFrom R P m o k t) = prjSt false (obsHistFrom R P' m o' k t) := by
    rw [h1, h2, h]
  exact (pl_prjO_false_eq (congrArg ObsSt.u h3)).2

/-- The triple hypothesis for the relocated difference datum. -/
theorem pl_relSt_rr (m : ℕ) (t : Hist.Seq (Xs R)) (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ)
    {o₁ o₂ : ObsSt .two L N} (hb : prjSt false o₁ = prjSt false o₂) :
    PlRelSt (rrStH R m t a a' β o₁) o₂ (plDiffSt (rrStH R m t a a' β o₁) o₂) :=
  pl_relSt_diff ((pl_rrSt_prj R m _ _ _ _ _ a a' β o₁).trans hb)

set_option maxHeartbeats 400000 in
/-- **The pair output of the relocated difference datum** (`m ≤ j ≤ N_h`). -/
theorem pl_pair_diff {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ)
    (hm0 : 0 < R.msq) (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {P P' : ObsPts 2 L N}
    (hPb : P.b = P'.b) (m : ℕ) (β : (Fin 2 → ℕ) → ℂ) {o₁ o₂ : ObsSt .two L N}
    (h₁ : o₁.IsObs) (h₂ : o₂.IsObs) (hl₁ : ObsLocInv P m o₁) (hl₂ : ObsLocInv P' m o₂)
    (hb : prjSt false o₁ = prjSt false o₂)
    (hl₃ : ObsLocInv P' m
      (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁) o₂))
    {j : ℕ} (hmj : m ≤ j) (hj : j ≤ Nh) (γ : ℂ) :
    plOut γ (plU R P m o₁ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (plY R P m o₁ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) -
      plOut γ (plU R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (plY R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) -
      plOut γ (plU R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β
          o₁) o₂) j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (plY R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁) o₂)
          j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
    -(ε (plU R P m o₁ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        ε (plU R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        ε (plU R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁)
          o₂) j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a) *
      (γ + nB (plW R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) +
        ε (plU R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).b *
          (sE (plW R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) /
            sE (plW R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)))) -
    (ε (plU R P m o₁ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab -
        ε (plU R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab -
        ε (plU R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁)
          o₂) j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab) *
      (sE (plW R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) /
        sE (plW R P' m o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))) := by
  have h₃ := pl_diff_isObs (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁) h₂
  have hc : ∏ i ∈ Ico m j, ch R i (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi =>
      pl_ch_ne R hN hspl hm0 hm hV hVL _ (by have := (mem_Ico.1 hi).2; omega)
  have hW := pl_W_rel R P m hN hρ1 hspl hm0 hm hV hVL b μ₀ P' P.a P'.a β h₁ h₂ h₃ hl₁ hl₂ hl₃
    (pl_relSt_rr R m _ P.a P'.a β hb) hmj hj hc
  rw [plW_eq, plW_eq, plW_eq] at hW
  rw [plW_eq]
  exact pl_out_triple (plU_bulk R P m h₁ j _) (plU_bulk R P' m h₂ j _) (plU_bulk R P' m h₃ j _)
    (pl_u_b_eq R hPb m hb _ j) (pl_u_b_eq R rfl m (pl_diff_prj _ _) _ j) hW γ

set_option maxHeartbeats 400000 in
/-- **The pair output of the relocated difference datum at the top** (`N_h + 1`, `Y = lastOF`). -/
theorem pl_pair_diff_top {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {P P' : ObsPts 2 L N} (hPb : P.b = P'.b) (m : ℕ)
    (β : (Fin 2 → ℕ) → ℂ) {o₁ o₂ : ObsSt .two L N} (h₁ : o₁.IsObs) (h₂ : o₂.IsObs)
    (hl₁ : ObsLocInv P m o₁) (hl₂ : ObsLocInv P' m o₂) (hb : prjSt false o₁ = prjSt false o₂)
    (hl₃ : ObsLocInv P' m
      (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁) o₂))
    (hmN : m ≤ Nh) (γ : ℂ) :
    plOut γ (plU R P m o₁ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (lastOF R P m o₁ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) -
      plOut γ (plU R P' m o₂ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (lastOF R P' m o₂ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) -
      plOut γ (plU R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β
          o₁) o₂) (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (lastOF R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁)
          o₂) Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
    -(ε (plU R P m o₁ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        ε (plU R P' m o₂ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        ε (plU R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁)
          o₂) (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a) *
      (γ + nB (plWTop R P' m o₂ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) +
        ε (plU R P' m o₂ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) :
          SA .two (Lam 2 L N)).b *
          (sE (plWTop R P' m o₂ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) /
            sE (plWTop R P' m o₂ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)))) -
    (ε (plU R P m o₁ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab -
        ε (plU R P' m o₂ (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab -
        ε (plU R P' m (plDiffSt (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁)
          o₂) (Nh + 1) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab) *
      (sE (plWTop R P' m o₂ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) /
        sE (plWTop R P' m o₂ Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))) := by
  have h₃ := pl_diff_isObs (rrStH R m (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) P.a P'.a β o₁) h₂
  have hc : ∏ i ∈ Ico m Nh, ch R i (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ≠ 0 :=
    prod_ne_zero_iff.2 fun i hi =>
      pl_ch_ne R hN hspl hm0 hm hV hVL _ (by have := (mem_Ico.1 hi).2; omega)
  have hW := pl_W_rel R P m hN hρ1 hspl hm0 hm hV hVL b μ₀ P' P.a P'.a β h₁ h₂ h₃ hl₁ hl₂ hl₃
    (pl_relSt_rr R m _ P.a P'.a β hb) hmN le_rfl hc
  have hcN := pl_ch_ne R hN hspl hm0 hm hV hVL (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) (le_refl Nh)
  have hT := pl_rel_smul (ch R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))⁻¹ hW
  rw [pl_W_top R P m hN hρ1 hspl hm0 hm hV hVL b μ₀ h₁ hl₁ hmN,
    pl_W_top R P' m hN hρ1 hspl hm0 hm hV hVL b μ₀ h₂ hl₂ hmN,
    pl_W_top R P' m hN hρ1 hspl hm0 hm hV hVL b μ₀ h₃ hl₃ hmN, smul_smul, smul_smul, smul_smul,
    inv_mul_cancel₀ hcN, one_smul, one_smul, one_smul] at hT
  rw [plWTop_eq, plWTop_eq, plWTop_eq] at hT
  rw [plWTop_eq]
  exact pl_out_triple (plU_bulk R P m h₁ (Nh + 1) _) (plU_bulk R P' m h₂ (Nh + 1) _)
    (plU_bulk R P' m h₃ (Nh + 1) _) (pl_u_b_eq R hPb m hb _ (Nh + 1))
    (pl_u_b_eq R rfl m (pl_diff_prj _ _) _ (Nh + 1)) hT γ

end Gen

/-! ### `rpcOut`, `rpTopOut` of a restarted state -/

section Rpc

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `rpcOut` of the restarted state at `j_x` is `plOut` with the reference `γ = uB`. -/
theorem pl_rpcOut_eq (m b μ₀ : ℝ) (x : Lam 2 L N) (ms : ℕ) (δ : ObsSt .two L N) :
    rpcOut R m b μ₀ x (obsHistFrom (R.withMsq m) (ptsX x) ms δ (Obs.coal L (0 : Lam 2 L N) x)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) =
      plOut (uB R m b μ₀ x (Obs.coal L (0 : Lam 2 L N) x))
        (plU (R.withMsq m) (ptsX x) ms δ (Obs.coal L (0 : Lam 2 L N) x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (plY (R.withMsq m) (ptsX x) ms δ (Obs.coal L (0 : Lam 2 L N) x)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  unfold rpcOut rpcE rpcZ rpTopU plOut plU plY ZhOF
  rw [obsHistFrom_self]

/-- `rpTopOut` of the restarted state at `N_h + 1` is `plOut` with `Y = lastOF`, `γ = uB`. -/
theorem pl_rpTopOut_eq (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) (ms : ℕ) (δ : ObsSt .two L N) :
    rpTopOut R Nh m b μ₀ x (obsHistFrom (R.withMsq m) (ptsX x) ms δ (Nh + 1)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) =
      plOut (uB R m b μ₀ x (Nh + 1))
        (plU (R.withMsq m) (ptsX x) ms δ (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (lastOF (R.withMsq m) (ptsX x) ms δ Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) := by
  unfold rpTopOut rpTopE rpTopU plOut plU lastOF zmOF finOF
  rw [obsHistFrom_self]

set_option maxHeartbeats 400000 in
/-- **`rpcOut`-level pair difference** (`h`-independent; `j = j_y ≤ N_h`). `P' = ptsX y`, reference
`o₂` = the history of the pair observable of `(0, y)` at `ms`; `P` any pair with `P.b = y` and a
datum `o₁` at `ms` with the reference `σ_b` projection; `δ` = the relocated difference datum.
With `s = sE W₂ ≠ 0`:
`plOut_{uB}(P, o₁) − rpcOut_y(ref) − rpcOut_y(δ at j_y) = −D_a·n_bW₂ − D_{ab}`. -/
theorem pl_rpc_diff {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (b μ₀ : ℝ)
    (y : Lam 2 L N) {P : ObsPts 2 L N} (hPb : P.b = y) (ms : ℕ) (β : (Fin 2 → ℕ) → ℂ)
    {o₁ : ObsSt .two L N} (h₁ : o₁.IsObs) (hl₁ : ObsLocInv P ms o₁)
    (hl₂ : ObsLocInv (ptsX y) ms (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hb : prjSt false o₁ = prjSt false (obsHist (R.withMsq m) (ptsX y)
      (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hl₃ : ObsLocInv (ptsX y) ms (plDiffSt (rrStH (R.withMsq m) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a (ptsX y).a β o₁)
      (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))))
    (hmj : ms ≤ Obs.coal L (0 : Lam 2 L N) y) (hj : Obs.coal L (0 : Lam 2 L N) y ≤ Nh)
    (hs : sE (plW (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
      (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≠ 0) :
    plOut (uB R m b μ₀ y (Obs.coal L (0 : Lam 2 L N) y))
        (plU (R.withMsq m) P ms o₁ (Obs.coal L (0 : Lam 2 L N) y)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (plY (R.withMsq m) P ms o₁ (Obs.coal L (0 : Lam 2 L N) y)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
      rpcOut R m b μ₀ y (rpcRef R m b μ₀ y) -
      rpcOut R m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms
        (plDiffSt (rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a
          (ptsX y).a β o₁) (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
        (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) =
    -(ε (plU (R.withMsq m) P ms o₁ (Obs.coal L (0 : Lam 2 L N) y)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
          (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).a -
        ε (plU (R.withMsq m) (ptsX y) ms (plDiffSt (rrStH (R.withMsq m) ms
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a (ptsX y).a β o₁)
          (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).a) *
      nB (plW (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
        (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
    (ε (plU (R.withMsq m) P ms o₁ (Obs.coal L (0 : Lam 2 L N) y)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab -
        ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
          (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).ab -
        ε (plU (R.withMsq m) (ptsX y) ms (plDiffSt (rrStH (R.withMsq m) ms
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a (ptsX y).a β o₁)
          (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).ab) := by
  have h₂ := obsHist_isObs (R := R.withMsq m) (P := ptsX y)
    (o₀ := obsInit .two (zV b) (ptsX y)) (obsInit_isObs .two (zV b) (ptsX y)) ms
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have H := pl_pair_diff (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL b μ₀ hPb ms β h₁ h₂ hl₁ hl₂
    hb hl₃ hmj hj
    (-ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
      (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
        SA .two (Lam 2 L N)).b)
  have href : rpcRef R m b μ₀ y = obsHistFrom (R.withMsq m) (ptsX y) ms
      (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    (rpb_histFrom_obsHist (R.withMsq m) (ptsX y) _ ms _ _ hmj).symm
  have huB : uB R m b μ₀ y (Obs.coal L (0 : Lam 2 L N) y) =
      -ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
        (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Obs.coal L (0 : Lam 2 L N) y) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
          SA .two (Lam 2 L N)).b := by
    unfold uB plU
    rw [rpb_histFrom_obsHist (R.withMsq m) (ptsX y) _ ms _ _ hmj]
  rw [href, pl_rpcOut_eq, pl_rpcOut_eq, huB, H, div_self hs]
  ring

set_option maxHeartbeats 400000 in
/-- **`rpTopOut`-level pair difference** (top: `N_h + 1`, `Y = lastOF`, `W₂ = plWTop`).
Setting of `pl_rpc_diff`, no condition on `j_y`:
`plOut_{uB}(P, o₁) − rpTopOut_y(rpRef) − rpTopOut_y(δ at N_h + 1) = −D_a·n_bW₂ − D_{ab}`. -/
theorem pl_rpTop_diff {Nh : ℕ} (hN : Nh + 2 = N) (m : ℝ) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < m) (hm : m ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))))
    (hV : ∀ j < Nh, ValidAt (R.withMsq m) j) (hVL : ValidAtL (R.withMsq m) Nh) (b μ₀ : ℝ)
    (y : Lam 2 L N) {P : ObsPts 2 L N} (hPb : P.b = y) (ms : ℕ) (β : (Fin 2 → ℕ) → ℂ)
    {o₁ : ObsSt .two L N} (h₁ : o₁.IsObs) (hl₁ : ObsLocInv P ms o₁)
    (hl₂ : ObsLocInv (ptsX y) ms (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hb : prjSt false o₁ = prjSt false (obsHist (R.withMsq m) (ptsX y)
      (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
    (hl₃ : ObsLocInv (ptsX y) ms (plDiffSt (rrStH (R.withMsq m) ms
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a (ptsX y).a β o₁)
      (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))))
    (hmN : ms ≤ Nh)
    (hs : sE (plWTop (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
      (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ≠ 0) :
    plOut (uB R m b μ₀ y (Nh + 1))
        (plU (R.withMsq m) P ms o₁ (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (lastOF (R.withMsq m) P ms o₁ Nh
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
      rpTopOut R Nh m b μ₀ y (rpRef R Nh m b μ₀ y) -
      rpTopOut R Nh m b μ₀ y (obsHistFrom (R.withMsq m) (ptsX y) ms
        (plDiffSt (rrStH (R.withMsq m) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a
          (ptsX y).a β o₁) (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
        (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) =
    -(ε (plU (R.withMsq m) P ms o₁ (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).a -
        ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
          (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).a -
        ε (plU (R.withMsq m) (ptsX y) ms (plDiffSt (rrStH (R.withMsq m) ms
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a (ptsX y).a β o₁)
          (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).a) *
      nB (plWTop (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
        (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
    (ε (plU (R.withMsq m) P ms o₁ (Nh + 1)
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) : SA .two (Lam 2 L N)).ab -
        ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
          (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).ab -
        ε (plU (R.withMsq m) (ptsX y) ms (plDiffSt (rrStH (R.withMsq m) ms
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) P.a (ptsX y).a β o₁)
          (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)))
          (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
            SA .two (Lam 2 L N)).ab) := by
  have h₂ := obsHist_isObs (R := R.withMsq m) (P := ptsX y)
    (o₀ := obsInit .two (zV b) (ptsX y)) (obsInit_isObs .two (zV b) (ptsX y)) ms
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have H := pl_pair_diff_top (R.withMsq m) hN hρ1 hspl hm0 hm hV hVL b μ₀ hPb ms β h₁ h₂ hl₁ hl₂
    hb hl₃ hmN
    (-ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
      (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
        SA .two (Lam 2 L N)).b)
  have href : rpRef R Nh m b μ₀ y = obsHistFrom (R.withMsq m) (ptsX y) ms
      (obsHist (R.withMsq m) (ptsX y) (obsInit .two (zV b) (ptsX y)) ms
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
      (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    (rpb_histFrom_obsHist (R.withMsq m) (ptsX y) _ ms _ _ (by omega)).symm
  have huB : uB R m b μ₀ y (Nh + 1) =
      -ε (plU (R.withMsq m) (ptsX y) ms (obsHist (R.withMsq m) (ptsX y)
        (obsInit .two (zV b) (ptsX y)) ms (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
        (Nh + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :
          SA .two (Lam 2 L N)).b := by
    unfold uB plU
    rw [rpb_histFrom_obsHist (R.withMsq m) (ptsX y) _ ms _ _ (by omega)]
  rw [href, pl_rpTopOut_eq, pl_rpTopOut_eq, huB, H, div_self hs]
  ring

end Rpc

end

end Spin2
