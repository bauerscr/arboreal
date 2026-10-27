import PtCorr2.Last.TopCoal1

/-!
# T5 (pair/top restart): the last factor for a general state at scale `N_h + 1`

For an arbitrary observable state `o` at scale `N_h + 1` (not necessarily on the history of the
pair observable), along the bulk trajectory:

* **`rp_bulk_finO`**: the bulk part of the final object `F_N` does not depend on the observable
  state (`IsObs`); hence **`rp_sE_zmOF`**, **`rp_sE_lastCstOF`**, **`rp_sE_lastOF`**: the bulk
  normalisations `sE` of the zero mode, of the constants and of the last factor are those of any
  other observable state (e.g. the reference history).
* **`rp_pair_red_gen`** (the reduction at `N - 1` for a general state, exact): for
  `ObsLocInv P (N_h+1) o` and a covering polymer `D`, with `o' = redSt … o D`,
  `sE(lastOF o) = sE X'·sE Ω'` and, if `sE(lastOF o) ≠ 0`, `n_{ab}(lastOF o) = n_{ab}X' + n_{ab}Ω'`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Bulk

variable {c : Obs.Case} (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N)
  (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)

/-- **The bulk part of `F_N` does not see the observables.** -/
theorem rp_bulk_finO {o o' : ObsSt c L N} (ho : o.IsObs) (ho' : o'.IsObs) :
    bulk (finO R P j st g μ D K o) = bulk (finO R P j st g μ D K o') := by
  have hV : bulkF (fullV R j st g μ o) = bulkF (fullV R j st g μ o') := by
    rw [bulkF_fullV R j st g μ ho, bulkF_fullV R j st g μ ho']
  have hW : bulkF (fullW st D o) = bulkF (fullW st D o') := by
    rw [bulkF_fullW st D ho, bulkF_fullW st D ho']
  have hK : bulkF (fullK R j st K o) = bulkF (fullK R j st K o') := by
    rw [bulkF_fullK R j st K ho, bulkF_fullK R j st K ho']
  unfold finO
  rw [map_sum, map_sum]
  refine sum_congr rfl fun U _ => ?_
  rw [map_mul, map_mul, bulk_bpowO, bulk_bpowO, bulk_Knext2O, bulk_Knext2O, hV, hW, hK]
  congr 1
  congr 1
  funext b
  rw [bulkF_apply, bulkF_apply, bulk_GpO, bulk_GpO, hV, hW, hK]

end Bulk

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- `sE` of the zero mode `ω_{cQ}(F_N)` does not see the observable state. -/
theorem rp_sE_zmOF {j j' : ℕ} {o o' : ObsSt .two L N} (ho : o.IsObs) (ho' : o'.IsObs)
    (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    sE (zmOF R P j o Nh t) = sE (zmOF R P j' o' Nh t) := by
  unfold zmOF
  rw [(sX_omegaCO_cstC _ _).1, (sX_omegaCO_cstC _ _).1]
  have h := congrArg (fun x : Step.EvR (Lam 2 L N) => (x : Grassmann.N (Lam 2 L N)))
    (rp_bulk_finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
      (histOut R Nh t).D (histOut R Nh t).K (obsHistFrom_isObs (P := P) (j := j) ho t (Nh + 1))
      (obsHistFrom_isObs (P := P) (j := j') ho' t (Nh + 1)))
  simp only [coe_bulk] at h
  unfold finOF
  rw [h]

/-- `sE` of the constants of the last step does not see the observable state. -/
theorem rp_sE_lastCstOF {j j' : ℕ} {o o' : ObsSt .two L N} (ho : o.IsObs) (ho' : o'.IsObs)
    (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    sE (lastCstOF R P j o Nh t) = sE (lastCstOF R P j' o' Nh t) := by
  rw [sE_lastCstOF, sE_lastCstOF, uXB_full_indep R P (Nh + 1) (histOut R Nh t).st
    (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
    (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
    (obsHistFrom_isObs (P := P) (j := j) ho t (Nh + 1))
    (obsHistFrom_isObs (P := P) (j := j') ho' t (Nh + 1)) univ]

/-- `sE` of the last factor does not see the observable state. -/
theorem rp_sE_lastOF {j j' : ℕ} {o o' : ObsSt .two L N} (ho : o.IsObs) (ho' : o'.IsObs)
    (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    sE (lastOF R P j o Nh t) = sE (lastOF R P j' o' Nh t) := by
  rw [lastOF_eq_cst_zm, lastOF_eq_cst_zm, sE_mul, sE_mul, rp_sE_lastCstOF R P ho ho',
    rp_sE_zmOF R P ho ho']

/-- `sE(lastO) = sE(lastOF)` for any observable state. -/
theorem rp_sE_lastO_eq {o₀ o : ObsSt .two L N} (ho₀ : o₀.IsObs) (ho : o.IsObs) {j : ℕ}
    (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    sE (lastO R P o₀ Nh t) = sE (lastOF R P j o Nh t) := by
  have e : lastO R P o₀ Nh t = lastOF R P 0 o₀ Nh t := by
    rw [lastO_eq_cst_zm, lastOF_eq_cst_zm]
  rw [e]; exact rp_sE_lastOF R P ho₀ ho Nh t

set_option maxHeartbeats 1000000 in
/-- **The reduction at scale `N - 1` for a general state** (exact). For an observable state `o` at
scale `N_h + 1` (taken as the start of the history, `j' ≥ N_h + 1`), local at `N_h + 1`, and a
covering polymer `D`, with `o' = redSt … o D`, `X' = lastCstOF j o'`, `Ω' = zmOF j o'`
(`j ≥ N_h + 1`): `sE(lastOF j' o) = sE X'·sE Ω'`, and if `sE(lastOF j' o) ≠ 0`,
`n_{ab}(lastOF j' o) = n_{ab}X' + n_{ab}Ω'`. -/
theorem rp_pair_red_gen {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) (o : ObsSt .two L N) (ho : o.IsObs)
    (hl : ObsLocInv P (Nh + 1) o) {D : Finset (Lam 2 L N)} (hD : DCov P (Nh + 1) D)
    {j j' : ℕ} (hj : Nh + 1 ≤ j) (hj' : Nh + 1 ≤ j') :
    let o' := redSt R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
      (histOut R Nh t).D (histOut R Nh t).K o D
    sE (lastOF R P j' o Nh t) = sE (lastCstOF R P j o' Nh t) * sE (zmOF R P j o' Nh t) ∧
      (sE (lastOF R P j' o Nh t) ≠ 0 →
        sE (lastCstOF R P j o' Nh t) ≠ 0 ∧ sE (zmOF R P j o' Nh t) ≠ 0 ∧
        nAB (lastOF R P j' o Nh t) =
          nAB (lastCstOF R P j o' Nh t) + nAB (zmOF R P j o' Nh t)) := by
  intro o'
  have ho' : o'.IsObs := redSt_isObs _ _ _ _ _ _ _ _ _ _
  have hS := (zinO_sect (R := R) (P := P) (j := Nh + 1) (st := (histOut R Nh t).st)
    (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (Dw := (histOut R Nh t).D)
    (K := (histOut R Nh t).K) ho hl hD).omegaCO (GtopO R Nh t)
  have e1 : omegaCO (GtopO R Nh t) (ZinO R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K o) = lastOF R P j' o Nh t := by
    have h := lastOF_omega R P hN hρ1 hspl hm0 hm hV hVL t j' o ho
    rw [obsHistFrom_le (R := R) (P := P) o t hj'] at h
    exact h
  have e2 : omegaCO (GtopO R Nh t) (ZinO R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K o') = lastOF R P j o' Nh t := by
    have h := lastOF_omega R P hN hρ1 hspl hm0 hm hV hVL t j o' ho'
    rw [obsHistFrom_le (R := R) (P := P) o' t hj] at h
    exact h
  rw [e1, e2, lastOF_eq_cst_zm R P j o' Nh t] at hS
  have hE : sE (lastOF R P j' o Nh t) = sE (lastCstOF R P j o' Nh t) * sE (zmOF R P j o' Nh t) := by
    rw [hS.sE_eq, sE_mul]
  refine ⟨hE, fun hY0 => ?_⟩
  rw [hE] at hY0
  have hX0 : sE (lastCstOF R P j o' Nh t) ≠ 0 := fun h => hY0 (by rw [h, zero_mul])
  have hΩ0 : sE (zmOF R P j o' Nh t) ≠ 0 := fun h => hY0 (by rw [h, mul_zero])
  refine ⟨hX0, hΩ0, ?_⟩
  rw [hS.nAB_eq]
  refine nAB_mul_ab (lastCstOF_mem_ab' R P t ?_) hX0 hΩ0
  rw [obsHistFrom_le (R := R) (P := P) o' t hj]
  exact obsAbInv_redSt _ _ _ _ _ _ _ _ _ _

end Hist

end

end PtCorr2
