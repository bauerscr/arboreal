import PtCorr2.Restart.RestartPairTop

/-!
# T5, item (5): the reduction at the coalescence scale `j ≤ N_h` for a general state (exact)

For an arbitrary observable state `o` at scale `j ≤ N_h` (local at `j`; e.g. the restarted
history of a small `a`-side datum at the coalescence scale), along the bulk trajectory:

* **`rpc_sE_indep`**: `sE(ω_{Γ_j}Z_j(o))` does not see the observable state (any two observable,
  local states at `j`);
* **`rpc_pair_red_gen`** (the generalisation of `pair_red_ratio`/`pairSect_hist` to any local
  state): with `o' = redSt … o D` (the reduced state at `j`, covering polymer `D`),
  `sE(ω_{Γ_j}Z_j(o)) = sE X'·sE Ω'` and, if `≠ 0`, `n_{ab}(ω_{Γ_j}Z_j(o)) = n_{ab}X' + n_{ab}Ω'`
  (`X' = cstOF j`, `Ω' = zmOF`);
* **`rpc_pair_red_tail`**: the same split with the reduced chain cut at `N_h + 1`:
  `n_{ab}(ω_{Γ_j}Z_j(o)) = n_{ab}(∏_{j ≤ i ≤ N_h} chOF_i) + n_{ab}(lastOF (N_h+1) o'')`,
  `o'' = obsHistFrom j o' (N_h + 1)` (the reduced chain at `N_h + 1`; no one-point parts), so the
  last part is the top output `rpTopE` of the state `o''`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The reduced state of a general state `o` at scale `j`** along the bulk history `t`. -/
def rpcRedSt (j : ℕ) (t : Hist.Seq (Xs R)) (o : ObsSt .two L N) (D : Finset (Lam 2 L N)) :
    ObsSt .two L N :=
  redSt R P j (rawHist R j t) (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) o D

theorem rpc_ZhOF_self (j : ℕ) (o : ObsSt .two L N) (t : Hist.Seq (Xs R)) :
    ZhOF R P j o j t = ZinO R j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) o := by
  unfold ZhOF; rw [obsHistFrom_self]

/-- The input of the reference history at `j` is the input of the history started at `j` from the
reference state. -/
theorem rpc_ZhO_eq (o₀ : ObsSt .two L N) (j : ℕ) (t : Hist.Seq (Xs R)) :
    ZhO R P o₀ j t = ZhOF R P j (obsHist R P o₀ j t) j t := by
  unfold ZhO ZhOF; rw [obsHistFrom_self]

theorem rpcRedSt_isObs (j : ℕ) (t : Hist.Seq (Xs R)) (o : ObsSt .two L N)
    (D : Finset (Lam 2 L N)) : (rpcRedSt R P j t o D).IsObs :=
  redSt_isObs _ _ _ _ _ _ _ _ _ _

theorem rpcRedSt_abInv (j : ℕ) (t : Hist.Seq (Xs R)) (o : ObsSt .two L N)
    (D : Finset (Lam 2 L N)) : ObsAbInv j (rpcRedSt R P j t o D) :=
  obsAbInv_redSt _ _ _ _ _ _ _ _ _ _

variable {R P}

/-- The reduced state of a local state is local (`j ≤ N_h`). -/
theorem rpcRedSt_loc {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (t : Hist.Seq (Xs R)) {j : ℕ} (hj : j ≤ Nh) {o : ObsSt .two L N} (hl : ObsLocInv P j o)
    (D : Finset (Lam 2 L N)) : ObsLocInv P j (rpcRedSt R P j t o D) := by
  have hcore : ValidCore R j := by
    rcases Nat.lt_or_ge j Nh with h | h
    · exact (hV j h).toValidCore
    · rw [show j = Nh by omega]; exact hVL.2
  exact obsLocInv_redSt hcore (rawInv_histU R hV hVL t j (by omega)) (rawD_mem R _ _)
    (rawK_mem R _ _) hl

variable (R P)

set_option maxHeartbeats 1000000 in
/-- **`sE(ω_{Γ_j}Z_j(o))` does not see the observable state** (`j ≤ N_h`; observable, local
states). -/
theorem rpc_sE_indep {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {j : ℕ} (hj : j ≤ Nh) {o o₂ : ObsSt .two L N}
    (ho : o.IsObs) (hl : ObsLocInv P j o) (ho₂ : o₂.IsObs) (hl₂ : ObsLocInv P j o₂) :
    sE (omegaCO (Γh R j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (ZhOF R P j o j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))) =
      sE (omegaCO (Γh R j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (ZhOF R P j o₂ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))) := by
  rw [hist_omegaOF_from R P j o hN hρ1 hspl hm0 hm hV hVL b μ₀ ho hl le_rfl hj,
    hist_omegaOF_from R P j o₂ hN hρ1 hspl hm0 hm hV hVL b μ₀ ho₂ hl₂ le_rfl hj,
    prodHiF_eq, prodHiF_eq, sE_mul, sE_mul, sE_cstOF_indep R P ho ho₂, rp_sE_zmOF R P ho ho₂]

set_option maxHeartbeats 1000000 in
/-- **The reduction at the coalescence scale `j ≤ N_h` for a general state** (exact). For an
observable state `o` at scale `j`, local at `j`, a covering polymer `D`, and `o' = rpcRedSt j o D`:
`sE(ω_{Γ_j}Z_j(o)) = sE X'·sE Ω'` and, if `sE(ω_{Γ_j}Z_j(o)) ≠ 0`, both factors are nonzero and
`n_{ab}(ω_{Γ_j}Z_j(o)) = n_{ab}X' + n_{ab}Ω'` (`X' = cstOF j o'`, `Ω' = zmOF j o'`). -/
theorem rpc_pair_red_gen {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {j : ℕ} (hj : j ≤ Nh) (o : ObsSt .two L N)
    (ho : o.IsObs) (hl : ObsLocInv P j o) {D : Finset (Lam 2 L N)} (hD : DCov P j D) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    let o' := rpcRedSt R P j t o D
    sE (omegaCO (Γh R j t) (ZhOF R P j o j t)) =
        sE (cstOF R P j o' Nh j t) * sE (zmOF R P j o' Nh t) ∧
      (sE (omegaCO (Γh R j t) (ZhOF R P j o j t)) ≠ 0 →
        sE (cstOF R P j o' Nh j t) ≠ 0 ∧ sE (zmOF R P j o' Nh t) ≠ 0 ∧
        nAB (omegaCO (Γh R j t) (ZhOF R P j o j t)) =
          nAB (cstOF R P j o' Nh j t) + nAB (zmOF R P j o' Nh t)) := by
  intro t o'
  have ho' : o'.IsObs := rpcRedSt_isObs R P j t o D
  have hab' : ObsAbInv j o' := rpcRedSt_abInv R P j t o D
  have hl' : ObsLocInv P j o' := rpcRedSt_loc hV hVL t hj hl D
  have hS : SectEq (ZhOF R P j o j t) (ZhOF R P j o' j t) := by
    rw [rpc_ZhOF_self, rpc_ZhOF_self]
    exact zinO_sect ho hl hD
  have hw := hist_omegaOF_from R P j o' hN hρ1 hspl hm0 hm hV hVL b μ₀ ho' hl' le_rfl hj
  have hS' := hS.omegaCO (Γh R j t)
  rw [hw, prodHiF_eq] at hS'
  have hE : sE (omegaCO (Γh R j t) (ZhOF R P j o j t)) =
      sE (cstOF R P j o' Nh j t) * sE (zmOF R P j o' Nh t) := by
    rw [hS'.sE_eq, sE_mul]
  refine ⟨hE, fun hY0 => ?_⟩
  rw [hE] at hY0
  have hX0 : sE (cstOF R P j o' Nh j t) ≠ 0 := fun h => hY0 (by rw [h, zero_mul])
  have hΩ0 : sE (zmOF R P j o' Nh t) ≠ 0 := fun h => hY0 (by rw [h, mul_zero])
  refine ⟨hX0, hΩ0, ?_⟩
  rw [hS'.nAB_eq]
  exact nAB_mul_ab (cstOF_mem_ab R P hab' t le_rfl (by omega)) hX0 hΩ0

/-- The last factor of the reduced chain is the last factor of its state at `N_h + 1`. -/
theorem rpc_lastOF_tail (j : ℕ) (o' : ObsSt .two L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    lastOF R P j o' Nh t = lastOF R P (Nh + 1) (obsHistFrom R P j o' (Nh + 1) t) Nh t := by
  unfold lastOF zmOF finOF
  rw [obsHistFrom_self]

set_option maxHeartbeats 1000000 in
/-- **The reduction at `j ≤ N_h`, cut at `N_h + 1`**: with `o'' = obsHistFrom j o' (N_h+1)` (the
reduced chain at `N_h + 1`), `Y = ∏_{j ≤ i ≤ N_h} chOF_i`:
`sE(ω_{Γ_j}Z_j(o)) = sE Y·sE(lastOF (N_h+1) o'')` and, if `≠ 0`,
`n_{ab}(ω_{Γ_j}Z_j(o)) = n_{ab}Y + n_{ab}(lastOF (N_h+1) o'')`. -/
theorem rpc_pair_red_tail {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) {j : ℕ} (hj : j ≤ Nh) (o : ObsSt .two L N)
    (ho : o.IsObs) (hl : ObsLocInv P j o) {D : Finset (Lam 2 L N)} (hD : DCov P j D) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    let o' := rpcRedSt R P j t o D
    let o'' := obsHistFrom R P j o' (Nh + 1) t
    sE (omegaCO (Γh R j t) (ZhOF R P j o j t)) =
        sE (∏ i ∈ Ico j (Nh + 1), chOF R P j o' i t) * sE (lastOF R P (Nh + 1) o'' Nh t) ∧
      (sE (omegaCO (Γh R j t) (ZhOF R P j o j t)) ≠ 0 →
        nAB (omegaCO (Γh R j t) (ZhOF R P j o j t)) =
          nAB (∏ i ∈ Ico j (Nh + 1), chOF R P j o' i t) + nAB (lastOF R P (Nh + 1) o'' Nh t)) := by
  intro t o' o''
  have ho' : o'.IsObs := rpcRedSt_isObs R P j t o D
  have hab' : ObsAbInv j o' := rpcRedSt_abInv R P j t o D
  have hl' : ObsLocInv P j o' := rpcRedSt_loc hV hVL t hj hl D
  have hS : SectEq (ZhOF R P j o j t) (ZhOF R P j o' j t) := by
    rw [rpc_ZhOF_self, rpc_ZhOF_self]
    exact zinO_sect ho hl hD
  have hw := hist_omegaOF_from R P j o' hN hρ1 hspl hm0 hm hV hVL b μ₀ ho' hl' le_rfl hj
  have hS' := hS.omegaCO (Γh R j t)
  have eP : prodHiF R P j o' Nh j t =
      (∏ i ∈ Ico j (Nh + 1), chOF R P j o' i t) * lastOF R P (Nh + 1) o'' Nh t := by
    rw [prodHiF, rpc_lastOF_tail]
  rw [hw, eP] at hS'
  have hE : sE (omegaCO (Γh R j t) (ZhOF R P j o j t)) =
      sE (∏ i ∈ Ico j (Nh + 1), chOF R P j o' i t) * sE (lastOF R P (Nh + 1) o'' Nh t) := by
    rw [hS'.sE_eq, sE_mul]
  refine ⟨hE, fun hY0 => ?_⟩
  rw [hE] at hY0
  have hX0 : sE (∏ i ∈ Ico j (Nh + 1), chOF R P j o' i t) ≠ 0 := fun h =>
    hY0 (by rw [h, zero_mul])
  have hΩ0 : sE (lastOF R P (Nh + 1) o'' Nh t) ≠ 0 := fun h => hY0 (by rw [h, mul_zero])
  rw [hS'.nAB_eq]
  exact nAB_mul_ab (prod_mem fun i hi => chOF_mem_ab R P hab' t (mem_Ico.1 hi).1) hX0 hΩ0

/-- The reduced chain keeps no one-point parts; in particular its accumulated `a`-constant at
`N_h + 1` vanishes. -/
theorem rpc_tail_abInv {j : ℕ} {o' : ObsSt .two L N} (h0 : ObsAbInv j o') (t : Hist.Seq (Xs R))
    {k : ℕ} (hk : j ≤ k) : ObsAbInv k (obsHistFrom R P j o' k t) := by
  have h := obsAbInv_histFrom R P h0 t (k - j)
  rwa [show j + (k - j) = k by omega] at h

theorem rpc_tail_ua {j : ℕ} {o' : ObsSt .two L N} (h0 : ObsAbInv j o') (t : Hist.Seq (Xs R))
    {k : ℕ} (hk : j ≤ k) :
    ((obsHistFrom R P j o' k t).u : SA .two (Lam 2 L N)).a = 0 :=
  (rpc_tail_abInv R P h0 t hk).u.1

end Hist

end

end PtCorr2
