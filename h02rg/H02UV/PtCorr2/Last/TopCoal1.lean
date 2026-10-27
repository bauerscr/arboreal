import PtCorr2.Pair.TwoPtZZ
import PtCorr2.Pair.PairSectHist
import Obs2.Pair.CoalHistL

/-!
# Top coalescence `j_ab ≥ N_h + 1`: the exact square at the split `k = N_h + 1`, the last step and
the reduction at scale `N - 1`

* **`prodLo_rankOneL`**: `Π^{<k}` is rank one for `k ≤ min(j_ab, N_h + 1)` (`ValidAt` below `N_h`,
  `ValidAtL` at `N_h`; `Obs2.obsHist_coal_validL`).
* **`zz_square_split_at`**: the exact `d = 2` square of `zz_square_split` at any split
  `k ≤ min(j_ab, N_h + 1)`; at `k = N_h + 1`, `Π^{≥k} = lastO` (`prodHi_top`).
* **`ZtopO`**, **`GtopO`**: the input of the last step (inputs `histOut N_h`) and its covariance;
  **`lastO_omega`**, **`lastOF_omega`**: `ω_{Γ_{N-1}}(Z_{N-1}) = lastO` (the last-step chain
  identity, original and from-`j` history).
* **`redTop`**: the reduced state at scale `N_h + 1` (`redSt` of the last-step input, covering
  polymer `D`); **`pair_red_top`**: for `j ≥ N_h + 1`, `DCov P (N_h+1) D`:
  `sE(lastO) = sE X'·sE Ω'`, `sE X' = sE(det·e^{-u_N})` and `n_{ab}(lastO) = n_{ab}X' + n_{ab}Ω'`,
  `X' = lastCstOF j o'`, `Ω' = zmOF j o'`, `o' = redTop` (a pair chain of length zero).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **Rank one below `min(j_ab, N_h + 1)`.** -/
theorem prodLo_rankOneL (V : OCoup2) (hV : AbFree .two V) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    {Nh : ℕ} (hN : Nh + 2 = N) (hVv : ∀ k < Nh, ValidAt R k) (hVL : ValidAtL R Nh)
    (t : Hist.Seq (Xs R)) :
    ∀ k ≤ min (coal L P.a P.b) (Nh + 1), RankOne (prodLo R P (obsInit .two V P) k t) := by
  have hc := obsHist_coal_validL R P (obsInit .two V P) hN (obsInit_isObs .two V P)
    (coalInv_init .two hV P) hL hVv hVL t
  intro k
  induction k with
  | zero => intro _; rw [prodLo, prod_range_zero]; exact rankOne_one
  | succ k ih =>
    intro hk
    have h := ih (by omega)
    rw [prodLo, prod_range_succ]
    exact h.mul (chO_rankOne R P _ k t (hc k (by omega)).2 (hc (k + 1) hk).2)

set_option maxHeartbeats 1000000 in
/-- **The exact `d = 2` square at a split `k ≤ min(j_ab, N_h + 1)`** (`zz_square_split` with the
split index as a parameter). -/
theorem zz_square_split_at {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {k : ℕ}
    (hk : k ≤ min (coal L P.a P.b) (Nh + 1))
    {b μ₀ : ℝ} (hb : 0 < b) (hh : b ≤ μ₀ + R.msq) (V : OCoup2) (hVab : AbFree .two V) :
    let t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀
    let X := prodLo R P (obsInit .two V P) k t
    let Y := prodHi R P (obsInit .two V P) Nh k t
    sE X ≠ 0 ∧ sE Y ≠ 0 ∧
      avg0 L N R.msq b μ₀ (zObsA V P) = sA X / sE X + sA Y / sE Y ∧
      avg0 L N R.msq b μ₀ (zObsB V P) = sB X / sE X + sB Y / sE Y ∧
      avg0 L N R.msq b μ₀ (zObsA V P * zObsB V P) =
        -(sA X / sE X * (sB X / sE X)) + avg0 L N R.msq b μ₀ (zObsB V P) * (sA X / sE X) +
          avg0 L N R.msq b μ₀ (zObsA V P) * (sB X / sE X) + sAB Y / sE Y := by
  intro t X Y
  obtain ⟨hZ, ha, hb', hab⟩ := zz_rg_ratio R P hN hρ1 hspl hm0 hm hV hVL (by omega) hb hh V hVab
  have hs := rgProdO_split R P (obsInit .two V P) (k := k) (Nh := Nh)
    ((hk.trans (min_le_right _ _))) t
  rw [hs] at hZ ha hb' hab
  have hX0 : sE X ≠ 0 := fun h0 => hZ (by rw [sE_mul]; simp [X, h0])
  have hY0 : sE Y ≠ 0 := fun h0 => hZ (by rw [sE_mul]; simp [Y, h0])
  have hX := prodLo_rankOneL R P V hVab hL hN hV hVL t k hk
  obtain ⟨e1, e2, e3⟩ := ratio_split hX hX0 hY0
  refine ⟨hX0, hY0, ha.trans e1, hb'.trans e2, ?_⟩
  rw [hab, ha, hb']
  exact e3

/-- At the split `k = N_h + 1`, `Π^{≥k}` is the last factor. -/
theorem prodHi_top {c : Obs.Case} (o₀ : ObsSt c L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    prodHi R P o₀ Nh (Nh + 1) t = lastO R P o₀ Nh t := by
  rw [prodHi, Ico_self, prod_empty, one_mul]

/-! ### The last step -/

/-- The input of the last step along the history (inputs `histOut N_h`, state `obsHist (N_h+1)`). -/
def ZtopO {c : Obs.Case} (o : ObsSt c L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  ZinO R (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (histOut R Nh t).D (histOut R Nh t).K o

/-- The covariance `Γ_{N-1}` of the last step. -/
def GtopO (Nh : ℕ) (t : Hist.Seq (Xs R)) : Matrix (Lam 2 L N) (Lam 2 L N) ℂ :=
  DressedFRD.kmat ((stData R (Nh + 1) (histOut R Nh t).st).Gam (Nh + 1))

set_option maxHeartbeats 1000000 in
/-- **The last-step chain identity**: `ω_{Γ_{N-1}}(Z_{N-1}(o)) = det·(e^{-u_N}·ω_{cQ}(F_N))` for
every observable state `o` at scale `N_h + 1` (no locality needed). -/
theorem omega_ZtopO {c : Obs.Case} {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) (o : ObsSt c L N) (ho : o.IsObs) :
    omegaCO (GtopO R Nh t) (ZtopO R o Nh t) =
      detStep R (Nh + 1) (histOut R Nh t).st • (uOutNO R P (Nh + 1) (histOut R Nh t).st
        (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K o *
        omegaCO (cstC (Lam 2 L N) (zmRaw R (Nh + 1) (Function.update (histOut R Nh t).st.ζ
          (Nh + 1) (stZeta R (histOut R Nh t).st)) / Fintype.card (Lam 2 L N)))
          (finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
            (histOut R Nh t).D (histOut R Nh t).K o)) := by
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hRI : RawInv R (Nh + 1) (histOut R Nh t).st := rawInv_histU R hV hVL t (Nh + 1) le_rfl
  have hS : SplitOK R (Nh + 1) (histOut R Nh t).st :=
    splitOK_hist R hρ0 hspl (by omega) hm0 hm t (j := Nh + 1) (by omega)
  exact lastStepO_omega (R := R) (P := P) (j := Nh + 1) (st := (histOut R Nh t).st)
    (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (D := (histOut R Nh t).D)
    (K := (histOut R Nh t).K) (o := o) (by omega) hRI hS ho

/-- `lastO = ω_{Γ_{N-1}}(Z_{N-1})` along the original history. -/
theorem lastO_omega {c : Obs.Case} {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) (o₀ : ObsSt c L N) (ho₀ : o₀.IsObs) :
    omegaCO (GtopO R Nh t) (ZtopO R (obsHist R P o₀ (Nh + 1) t) Nh t) = lastO R P o₀ Nh t :=
  omega_ZtopO R P hN hρ1 hspl hm0 hm hV hVL t _ (obsHist_isObs R P o₀ ho₀ (Nh + 1) t)

/-- `lastOF = ω_{Γ_{N-1}}(Z_{N-1}(o'))` along the history from `j`. -/
theorem lastOF_omega {c : Obs.Case} {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) (j : ℕ) (o' : ObsSt c L N) (ho' : o'.IsObs) :
    omegaCO (GtopO R Nh t) (ZtopO R (obsHistFrom R P j o' (Nh + 1) t) Nh t) =
      lastOF R P j o' Nh t :=
  omega_ZtopO R P hN hρ1 hspl hm0 hm hV hVL t _ (obsHistFrom_isObs ho' t (Nh + 1))

/-! ### The reduction at scale `N - 1` -/

/-- **The reduced state at scale `N_h + 1`**: `V' = 𝒲' = 0`, `u' = 0`, `K' = kRed` of the input
of the last step. -/
def redTop {c : Obs.Case} (o₀ : ObsSt c L N) (D : Finset (Lam 2 L N)) (Nh : ℕ)
    (t : Hist.Seq (Xs R)) : ObsSt c L N :=
  redSt R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (histOut R Nh t).D (histOut R Nh t).K (obsHist R P o₀ (Nh + 1) t) D

theorem redTop_isObs {c : Obs.Case} (o₀ : ObsSt c L N) (D : Finset (Lam 2 L N)) (Nh : ℕ)
    (t : Hist.Seq (Xs R)) : (redTop R P o₀ D Nh t).IsObs :=
  redSt_isObs _ _ _ _ _ _ _ _ _ _

theorem obsAbInv_redTop {c : Obs.Case} (o₀ : ObsSt c L N) (D : Finset (Lam 2 L N)) (Nh : ℕ)
    (t : Hist.Seq (Xs R)) : ObsAbInv (Nh + 1) (redTop R P o₀ D Nh t) :=
  obsAbInv_redSt _ _ _ _ _ _ _ _ _ _

/-- The history from `j ≥ N_h + 1` is constant up to `N_h + 1`. -/
theorem obsHistFrom_top {c : Obs.Case} {Nh j : ℕ} (hj : Nh + 1 ≤ j) (o' : ObsSt c L N)
    (t : Hist.Seq (Xs R)) : obsHistFrom R P j o' (Nh + 1) t = o' :=
  obsHistFrom_le o' t hj

/-- **The sector identity at scale `N - 1`.** -/
theorem zinO_sect_top {c : Obs.Case} {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (o₀ : ObsSt c L N) (ho₀ : o₀.IsObs) (h0 : ObsLocInv P 0 o₀)
    (t : Hist.Seq (Xs R)) {D : Finset (Lam 2 L N)} (hD : DCov P (Nh + 1) D) :
    SectEq (ZtopO R (obsHist R P o₀ (Nh + 1) t) Nh t) (ZtopO R (redTop R P o₀ D Nh t) Nh t) := by
  have hcore : ∀ i ≤ Nh, ValidCore R i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t
  have hl : ObsLocInv P (Nh + 1) (obsHist R P o₀ (Nh + 1) t) :=
    obsLocInv_hist R P o₀ h0 t (Nh + 1) fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩
  exact zinO_sect (obsHist_isObs R P o₀ ho₀ (Nh + 1) t) hl hD

/-- `lastO = det·e^{-u_N}·Ω` (the original constants and zero mode at scale `N`). -/
theorem lastO_eq_cst_zm {c : Obs.Case} (o₀ : ObsSt c L N) (Nh : ℕ) (t : Hist.Seq (Xs R)) :
    lastO R P o₀ Nh t = lastCstOF R P 0 o₀ Nh t * zmOF R P 0 o₀ Nh t := by
  unfold lastO lastCstOF zmOF finOF zmC
  rw [obsHistFrom_zero, smul_mul_assoc]

theorem lastOF_eq_cst_zm {c : Obs.Case} (j : ℕ) (o' : ObsSt c L N) (Nh : ℕ)
    (t : Hist.Seq (Xs R)) :
    lastOF R P j o' Nh t = lastCstOF R P j o' Nh t * zmOF R P j o' Nh t := by
  unfold lastOF lastCstOF
  rw [smul_mul_assoc]

local notation "AB" => (abSub : Subalgebra ℂ (OE Obs.Case.two (Lam 2 L N)))

theorem lastCstOF_mem_ab' {j : ℕ} {o' : ObsSt .two L N} (t : Hist.Seq (Xs R)) {Nh : ℕ}
    (hab : ObsAbInv (Nh + 1) (obsHistFrom R P j o' (Nh + 1) t)) : lastCstOF R P j o' Nh t ∈ AB := by
  have H := oabS_full R (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (st := (histOut R Nh t).st) (D := (histOut R Nh t).D) (K := (histOut R Nh t).K) hab
  unfold lastCstOF uOutNO
  exact Subalgebra.smul_mem _ (expU_mem _ (neg_mem
    (H.uXO_ab (P := P) (C := LastN.stCovN R (Nh + 1) (histOut R Nh t).st) univ))) _

set_option maxHeartbeats 1000000 in
/-- **PR1 at scale `N - 1` (exact), a pair chain of length zero.** For `j ≥ N_h + 1` and a covering
polymer `D` at scale `N_h + 1`, with `o' = redTop`, `X' = lastCstOF j o'`, `Ω' = zmOF j o'`:
`sE X' = sE(det·e^{-u_N})` of the original history, `sE(lastO) = sE X'·sE Ω'`, and if
`sE(lastO) ≠ 0`, `n_{ab}(lastO) = n_{ab}X' + n_{ab}Ω'`. -/
theorem pair_red_top {Nh : ℕ} (hN : Nh + 2 = N) (hρ1 : R.ρ < 1)
    (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (o₀ : ObsSt .two L N) (ho₀ : o₀.IsObs) (h0 : ObsLocInv P 0 o₀)
    (t : Hist.Seq (Xs R)) {D : Finset (Lam 2 L N)} (hD : DCov P (Nh + 1) D) {j : ℕ}
    (hj : Nh + 1 ≤ j) :
    let o' := redTop R P o₀ D Nh t
    sE (lastCstOF R P j o' Nh t) = sE (lastCstOF R P 0 o₀ Nh t) ∧
      sE (lastO R P o₀ Nh t) = sE (lastCstOF R P j o' Nh t) * sE (zmOF R P j o' Nh t) ∧
      (sE (lastO R P o₀ Nh t) ≠ 0 →
        sE (lastCstOF R P j o' Nh t) ≠ 0 ∧ sE (zmOF R P j o' Nh t) ≠ 0 ∧
        nAB (lastO R P o₀ Nh t) = nAB (lastCstOF R P j o' Nh t) + nAB (zmOF R P j o' Nh t)) := by
  intro o'
  have hS := (zinO_sect_top R P hV hVL o₀ ho₀ h0 t hD).omegaCO (GtopO R Nh t)
  rw [lastO_omega R P hN hρ1 hspl hm0 hm hV hVL t o₀ ho₀,
    ← obsHistFrom_top R P hj (redTop R P o₀ D Nh t) t,
    lastOF_omega R P hN hρ1 hspl hm0 hm hV hVL t j _ (redTop_isObs R P o₀ D Nh t),
    lastOF_eq_cst_zm] at hS
  have hE : sE (lastO R P o₀ Nh t) = sE (lastCstOF R P j o' Nh t) * sE (zmOF R P j o' Nh t) := by
    rw [hS.sE_eq, sE_mul]
  have hI : sE (lastCstOF R P j o' Nh t) = sE (lastCstOF R P 0 o₀ Nh t) := by
    rw [sE_lastCstOF, sE_lastCstOF]
    rw [uXB_full_indep R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re
      (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
      (LastN.stCovN R (Nh + 1) (histOut R Nh t).st)
      (obsHistFrom_isObs (P := P) (j := j) (redTop_isObs R P o₀ D Nh t) t (Nh + 1))
      (obsHistFrom_isObs (P := P) (j := 0) ho₀ t (Nh + 1)) univ]
  refine ⟨hI, hE, fun hY0 => ?_⟩
  rw [hE] at hY0
  have hX0 : sE (lastCstOF R P j o' Nh t) ≠ 0 := fun h => hY0 (by rw [h, zero_mul])
  have hΩ0 : sE (zmOF R P j o' Nh t) ≠ 0 := fun h => hY0 (by rw [h, mul_zero])
  refine ⟨hX0, hΩ0, ?_⟩
  rw [hS.nAB_eq]
  refine nAB_mul_ab (lastCstOF_mem_ab' R P t ?_) hX0 hΩ0
  rw [obsHistFrom_top R P hj o' t]
  exact obsAbInv_redTop R P o₀ D Nh t

end Hist

end

end PtCorr2
