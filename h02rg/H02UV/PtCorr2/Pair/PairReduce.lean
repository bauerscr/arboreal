import PtCorr2.Obs.ObsHistFrom

/-!
# The sector reduction of the pair observable (PR1, exact consequences)

`SectEq A B`: the `∅` and `σ_aσ_b` components of `A`, `B` agree. Since `ω_Γ` acts componentwise,
`SectEq` passes to `ω_Γ` (`SectEq.omegaCO`), hence to `sE`, `sAB` and the pair ratio
`n_{ab} = sAB/sE`.

Along the history started at scale `j` from a state `o'` without one-point parts (`ObsAbInv j o'`):
* every step constant `chOF_k` (`k ≥ j`) and the last constant lie in `abSub` (`chOF_mem_ab`,
  `lastCstOF_mem_ab`), so the reduced constants `X' = cstOF` have no one-point parts and
  `n_{ab}(X'Ω') = n_{ab}X' + n_{ab}Ω'` (`nAB_mul_ab`): **no cross terms**;
* the bulk normalisations do not see the observables: `sE (chOF) = sE (chO)`,
  `sE X' = sE X` for any two observable states (`sE_cstOF_indep`).

**`pair_red_ratio`** (exact): if `SectEq (Z_j(o)) (Z_j(o'))` at scale `j` (`o` the original history,
`o'` reduced), then `n_{ab}(ω_{Γ_j}Z_j(o)) = n_{ab}X' + n_{ab}Ω'` with `X' = cstOF j`,
`Ω' = ω_{cQ}(F'_N)`, and `sE X' = sE X`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

/-! ### Sector equality -/

section Sect

variable {c : Obs.Case} {Λ : Type*} [DecidableEq Λ] [Fintype Λ]

/-- The `∅` and `σ_aσ_b` components agree. -/
def SectEq (A B : OE c Λ) : Prop :=
  (A : SA c Λ).e = (B : SA c Λ).e ∧ (A : SA c Λ).ab = (B : SA c Λ).ab

theorem SectEq.omegaCO {A B : OE c Λ} (h : SectEq A B) (Γ : Matrix Λ Λ ℂ) :
    SectEq (omegaCO Γ A) (omegaCO Γ B) :=
  ⟨by rw [omegaCO_e, omegaCO_e, h.1], by rw [omegaCO_ab, omegaCO_ab, h.2]⟩

theorem SectEq.sE_eq {A B : OE .two Λ} (h : SectEq A B) : sE A = sE B := by
  unfold sE; rw [h.1]

theorem SectEq.sAB_eq {A B : OE .two Λ} (h : SectEq A B) : sAB A = sAB B := by
  unfold sAB; rw [h.2]

theorem SectEq.nAB_eq {A B : OE .two Λ} (h : SectEq A B) : nAB A = nAB B := by
  unfold nAB; rw [h.sE_eq, h.sAB_eq]

theorem sA_of_mem_ab {F : OE .two Λ} (h : F ∈ (abSub : Subalgebra ℂ (OE .two Λ))) :
    sA F = 0 := by unfold sA; rw [h.1, map_zero]

theorem sB_of_mem_ab {F : OE .two Λ} (h : F ∈ (abSub : Subalgebra ℂ (OE .two Λ))) :
    sB F = 0 := by unfold sB; rw [h.2, map_zero]

/-- **No cross terms**: if `X` has no one-point parts, `n_{ab}(XY) = n_{ab}X + n_{ab}Y`. -/
theorem nAB_mul_ab {X Y : OE .two Λ} (hX : X ∈ (abSub : Subalgebra ℂ (OE .two Λ)))
    (hX0 : sE X ≠ 0) (hY0 : sE Y ≠ 0) : nAB (X * Y) = nAB X + nAB Y := by
  rw [nAB_mul hX0 hY0]
  unfold nA nB
  rw [sA_of_mem_ab hX, sB_of_mem_ab hX]
  ring

theorem sE_prod {ι : Type*} (s : Finset ι) (f : ι → OE .two Λ) :
    sE (∏ i ∈ s, f i) = ∏ i ∈ s, sE (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sE]
  | insert a s ha ih => rw [prod_insert ha, prod_insert ha, sE_mul, ih]

/-- The scalar bulk part of `r • e^{x}e^{F}` for an observable `F`. -/
theorem sE_smul_expU (r x : ℂ) {F : OE .two Λ} (hF : bulk F = 0) :
    sE (r • expU x F) = r * Complex.exp x := by
  unfold sE expU
  simp only [SetLike.val_smul, SA.smul_e, map_smul, smul_eq_mul]
  rw [oexp_obs_e hF, map_one, mul_one]

end Sect

/-! ### The bulk normalisations do not see the observables -/

section Bulk

variable {L N : ℕ} [NeZero L] {c : Obs.Case}
variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (D : Fam 2 L N) (K : Act 2 L N) {o o' : ObsSt c L N}

theorem uXB_full_indep (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (ho : o.IsObs) (ho' : o'.IsObs)
    (X : Finset (Lam 2 L N)) :
    uXB P j C (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) X =
      uXB P j C (fullV R j st g μ o') (fullW st D o') (fullK R j st K o') X := by
  rw [uXB_eq, uXB_eq, bulkF_fullV R j st g μ ho, bulkF_fullV R j st g μ ho',
    bulkF_fullW st D ho, bulkF_fullW st D ho', bulkF_fullK R j st K ho, bulkF_fullK R j st K ho']

theorem bulk_uObsTot (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam c 2 L N)
    (K' : OAct c 2 L N) : bulk (uObsTot P j C V W K') = 0 := by
  rw [uObsTot, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _

theorem bulk_uXO_gen (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) (V W : OFam c 2 L N)
    (K' : OAct c 2 L N) (X : Finset (Lam 2 L N)) : bulk (uXO P j C V W K' X) = 0 := by
  rw [uXO, map_sum]; exact sum_eq_zero fun _ _ => bulk_πobs _

end Bulk

section Hist

variable {L N : ℕ} [NeZero L]
variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

theorem sE_chOF (j : ℕ) (o' : ObsSt .two L N) (i : ℕ) (t : Hist.Seq (Xs R)) :
    sE (chOF R P j o' i t) = detStep R i (rawHist R i t) *
      Complex.exp (-uOut R i (rawHist R i t) (t i).1 (t i).2.1
        (rawD R (rawHist R i t).u (t i).2.2) (rawK R (rawHist R i t).u (t i).2.2)) := by
  unfold chOF uOutO
  rw [sE_smul_expU]
  rw [map_neg, bulk_uObsTot, neg_zero]

theorem sE_lastCstOF (j : ℕ) (o' : ObsSt .two L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    sE (lastCstOF R P j o' Nh t) = detStep R (Nh + 1) (histOut R Nh t).st *
      Complex.exp (-uXB P (Nh + 1) (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
        (fullV R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
          (obsHistFrom R P j o' (Nh + 1) t))
        (fullW (histOut R Nh t).st (histOut R Nh t).D (obsHistFrom R P j o' (Nh + 1) t))
        (fullK R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).K
          (obsHistFrom R P j o' (Nh + 1) t)) univ) := by
  unfold lastCstOF uOutNO
  rw [sE_smul_expU]
  rw [map_neg, bulk_uXO_gen, neg_zero]

/-- **The bulk normalisation of the constants does not see the observables.** -/
theorem sE_cstOF_indep {j j' : ℕ} {o' o'' : ObsSt .two L N} (ho' : o'.IsObs) (ho'' : o''.IsObs)
    (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    sE (cstOF R P j o' Nh k t) = sE (cstOF R P j' o'' Nh k t) := by
  have e := uXB_full_indep R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re
    (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
    (LastN.stCovN R (Nh + 1) (histOut R Nh t).st) (obsHistFrom_isObs (P := P) (j := j) ho' t (Nh + 1))
      (obsHistFrom_isObs (P := P) (j := j') ho'' t (Nh + 1)) univ
  have e2 : ∀ i, sE (chOF R P j o' i t) = sE (chOF R P j' o'' i t) := fun i => by
    rw [sE_chOF, sE_chOF]
  unfold cstOF
  rw [sE_mul, sE_mul, sE_lastCstOF, sE_lastCstOF, e, sE_prod, sE_prod,
    prod_congr rfl fun i _ => e2 i]

/-! ### No one-point parts in the reduced constants -/

local notation "AB" => (abSub : Subalgebra ℂ (OE Obs.Case.two (Lam 2 L N)))

theorem chOF_mem_ab {j : ℕ} {o' : ObsSt .two L N} (h0 : ObsAbInv j o') (t : Hist.Seq (Xs R))
    {i : ℕ} (hi : j ≤ i) : chOF R P j o' i t ∈ AB := by
  have hab := obsAbInv_histFrom R P h0 t (i - j)
  rw [show j + (i - j) = i by omega] at hab
  have H := oabS_full R (t i).1 (t i).2.1 (st := rawHist R i t)
    (D := rawD R (rawHist R i t).u (t i).2.2) (K := rawK R (rawHist R i t).u (t i).2.2) hab
  unfold chOF uOutO
  exact Subalgebra.smul_mem _ (expU_mem _ (neg_mem (Subalgebra.sum_mem _ fun b _ =>
    H.up_ab (P := P) (C := stCov R i (rawHist R i t)) b))) _

theorem lastCstOF_mem_ab {j : ℕ} {o' : ObsSt .two L N} (h0 : ObsAbInv j o')
    (t : Hist.Seq (Xs R)) {Nh : ℕ} (hj : j ≤ Nh + 1) : lastCstOF R P j o' Nh t ∈ AB := by
  have hab := obsAbInv_histFrom R P h0 t (Nh + 1 - j)
  rw [show j + (Nh + 1 - j) = Nh + 1 by omega] at hab
  have H := oabS_full R (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (st := (histOut R Nh t).st) (D := (histOut R Nh t).D) (K := (histOut R Nh t).K) hab
  unfold lastCstOF uOutNO
  exact Subalgebra.smul_mem _ (expU_mem _ (neg_mem
    (H.uXO_ab (P := P) (C := LastN.stCovN R (Nh + 1) (histOut R Nh t).st) univ))) _

theorem cstOF_mem_ab {j : ℕ} {o' : ObsSt .two L N} (h0 : ObsAbInv j o') (t : Hist.Seq (Xs R))
    {Nh k : ℕ} (hjk : j ≤ k) (hj : j ≤ Nh + 1) : cstOF R P j o' Nh k t ∈ AB :=
  mul_mem (prod_mem fun _ hi => chOF_mem_ab R P h0 t (hjk.trans (mem_Ico.1 hi).1))
    (lastCstOF_mem_ab R P h0 t hj)

/-! ### The reduction -/

set_option maxHeartbeats 1000000 in
/-- **PR1 (exact): the pair part above `j` from the reduced history.** Let `o'` be an observable
state at scale `j ≤ N_h` without one-point parts, local, whose input `Z_j(o')` has the same `∅` and
`σ_aσ_b` components as the input `Z_j(o)` of the original history. Then, with
`X' = cstOF j`, `Ω' = zmOF`: `sE X' = sE X` for the original constants `X = cstOF 0 o₀ j`, and if
`sE(ω_{Γ_j}Z_j(o)) ≠ 0`, `n_{ab}(ω_{Γ_j}Z_j(o)) = n_{ab}X' + n_{ab}Ω'` (no one-point parts, no
cross terms). -/
theorem pair_red_ratio {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) {j : ℕ}
    (hj : j ≤ Nh) (o' : ObsSt .two L N) (ho' : o'.IsObs) (hl' : ObsLocInv P j o')
    (hab' : ObsAbInv j o')
    (hS : SectEq (ZhO R P o₀ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (ZhOF R P j o' j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)))
    (hY0 : sE (omegaCO (Γh R j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
      (ZhO R P o₀ j (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))) ≠ 0) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    sE (cstOF R P j o' Nh j t) = sE (cstOF R P 0 o₀ Nh j t) ∧
      sE (cstOF R P j o' Nh j t) ≠ 0 ∧ sE (zmOF R P j o' Nh t) ≠ 0 ∧
      sE (omegaCO (Γh R j t) (ZhO R P o₀ j t)) =
        sE (cstOF R P j o' Nh j t) * sE (zmOF R P j o' Nh t) ∧
      nAB (omegaCO (Γh R j t) (ZhO R P o₀ j t)) =
        nAB (cstOF R P j o' Nh j t) + nAB (zmOF R P j o' Nh t) := by
  intro t
  have hw := hist_omegaOF_from R P j o' hN hρ1 hspl hm0 hm hV hVL b μ₀ ho' hl' le_rfl hj
  have hS' := hS.omegaCO (Γh R j t)
  rw [hw, prodHiF_eq] at hS'
  have hE : sE (omegaCO (Γh R j t) (ZhO R P o₀ j t)) =
      sE (cstOF R P j o' Nh j t) * sE (zmOF R P j o' Nh t) := by
    rw [hS'.sE_eq, sE_mul]
  rw [hE] at hY0
  have hX0 : sE (cstOF R P j o' Nh j t) ≠ 0 := fun h => hY0 (by rw [h, zero_mul])
  have hΩ0 : sE (zmOF R P j o' Nh t) ≠ 0 := fun h => hY0 (by rw [h, mul_zero])
  refine ⟨sE_cstOF_indep R P ho' ho₀ Nh j t, hX0, hΩ0, hE, ?_⟩
  rw [hS'.nAB_eq]
  exact nAB_mul_ab (cstOF_mem_ab R P hab' t le_rfl (by omega)) hX0 hΩ0

/-- **The reduced zero mode** (pure): if `c2F'_{ab} = ρ̃·c2F_a` and `s = x_e - c·y_e ≠ 0`, then
`(x'_{ab} - c·y'_{ab})/s = (x'_{ab} - ρ̃x_a)/s + ρ̃·(x_a - c·y_a)/s`. -/
theorem zm_red_elim {xab' yab' xa ya cc s ρ : ℂ} (hρ : yab' = ρ * ya) :
    (xab' - cc * yab') / s = (xab' - ρ * xa) / s + ρ * ((xa - cc * ya) / s) := by
  rw [hρ]; ring

end Hist

end

end PtCorr2
