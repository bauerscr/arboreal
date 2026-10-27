import PtCorr2.Pair.PairAbove
import Obs2.Map.SigmaScale

/-!
# The observable history started at scale `j` and its chain identity (PR1/PR2 of the reduced
pair observable, `sec:obs-flow`)

* `obsHistFrom j o' k t`: the observable state at scale `k` of the observable flow started at scale
  `j` from the state `o'` (`= o'` for `k ≤ j`, `obsStep` above); `obsHistFrom_zero`: from `j = 0` it
  is `obsHist`. Invariants: `obsHistFrom_isObs`, `obsLocInv_histFrom` (locality), and
  **`obsAbInv_histFrom`** (PR2): a state without `σ_a`, `σ_b` parts keeps none (`Obs2.OAbS.step`).
* `ZhOF`, `chOF`, `lastOF`, `prodHiF`: the inputs and the step constants along it.
* **`hist_omegaOF_from`**: `ω_{Γ_k}(Z_k(o')) = Π'^{≥k}` for `j ≤ k ≤ N_h` (copy of
  `hist_omegaO_from`).
* **`pair_red_ratio`** (PR1, the sector reduction, exact): if at scale `j` the `∅` and `σ_aσ_b`
  components of `Z_j(o)` and `Z_j(o')` agree (`SectEq`), then the pair part above `j` of the original
  history equals the reduced one, `E = n_{ab}(Π^{≥j}) = n_{ab}(Π'^{≥j})`, and
  `n_{ab}(Π'^{≥j}) = n_{ab}X' + n_{ab}Ω'` with the reduced constants `X'` and zero mode `Ω'`: no
  one-point parts, no cross terms (`nAB_red_split`). The denominators agree: `sE X' = sE X`
  (`sE_chOF_eq`, `sE_cstOF_eq`; the bulk constants do not see the observables).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### The history from scale `j` -/

section From

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The observable history started at scale `j` from `o'`.** -/
def obsHistFrom (j : ℕ) (o' : ObsSt c L N) : ℕ → Hist.Seq (Xs R) → ObsSt c L N
  | 0, _ => o'
  | k + 1, t => if k + 1 ≤ j then o' else
      obsStep R P k (rawHist R k t) (t k).1 (t k).2.1 (rawD R (rawHist R k t).u (t k).2.2)
        (rawK R (rawHist R k t).u (t k).2.2) (obsHistFrom j o' k t)

variable {R P}

theorem obsHistFrom_le {j : ℕ} (o' : ObsSt c L N) (t : Hist.Seq (Xs R)) :
    ∀ {k : ℕ}, k ≤ j → obsHistFrom R P j o' k t = o'
  | 0, _ => rfl
  | k + 1, hk => by rw [obsHistFrom, if_pos hk]

theorem obsHistFrom_self (j : ℕ) (o' : ObsSt c L N) (t : Hist.Seq (Xs R)) :
    obsHistFrom R P j o' j t = o' := obsHistFrom_le o' t le_rfl

theorem obsHistFrom_succ {j k : ℕ} (hk : j ≤ k) (o' : ObsSt c L N) (t : Hist.Seq (Xs R)) :
    obsHistFrom R P j o' (k + 1) t = obsStep R P k (rawHist R k t) (t k).1 (t k).2.1
      (rawD R (rawHist R k t).u (t k).2.2) (rawK R (rawHist R k t).u (t k).2.2)
      (obsHistFrom R P j o' k t) := by
  rw [obsHistFrom, if_neg (by omega)]

/-- From scale `0` the history is `obsHist`. -/
theorem obsHistFrom_zero (o₀ : ObsSt c L N) (t : Hist.Seq (Xs R)) :
    ∀ k, obsHistFrom R P 0 o₀ k t = obsHist R P o₀ k t
  | 0 => rfl
  | k + 1 => by rw [obsHistFrom_succ (Nat.zero_le k), obsHistFrom_zero o₀ t k]; rfl

theorem obsHistFrom_isObs {j : ℕ} {o' : ObsSt c L N} (h : o'.IsObs) (t : Hist.Seq (Xs R)) :
    ∀ k, (obsHistFrom R P j o' k t).IsObs
  | 0 => h
  | k + 1 => by
    by_cases hk : k + 1 ≤ j
    · rw [obsHistFrom_le o' t hk]; exact h
    · rw [obsHistFrom_succ (by omega)]
      exact obsStep_isObs R P k _ _ _ _ _ _ (obsHistFrom_isObs h t k)

/-- **Locality along the history from scale `j`.** -/
theorem obsLocInv_histFrom {j : ℕ} {o' : ObsSt c L N} (h0 : ObsLocInv P j o')
    (t : Hist.Seq (Xs R)) :
    ∀ d, (∀ i, j ≤ i → i < j + d → ValidCore R i ∧ RawInv R i (rawHist R i t)) →
      ObsLocInv P (j + d) (obsHistFrom R P j o' (j + d) t)
  | 0, _ => by rw [Nat.add_zero, obsHistFrom_self]; exact h0
  | d + 1, h => by
    rw [← Nat.add_assoc, obsHistFrom_succ (by omega)]
    exact obsLocInv_step R P _ _ (h (j + d) (by omega) (by omega)).1
      (h (j + d) (by omega) (by omega)).2 (rawD_mem R _ _) (rawK_mem R _ _)
      (obsLocInv_histFrom h0 t d fun i hi1 hi2 => h i hi1 (by omega))

end From

/-! ### No one-point parts along the history (PR2) -/

section Ab

local notation "AB" => (abSub : Subalgebra ℂ (OE c (Lam 2 L N)))

/-- **No `σ_a`, `σ_b` parts in an observable state.** -/
structure ObsAbInv (j : ℕ) (o : ObsSt c L N) : Prop where
  V : ∀ b, o.V b ∈ AB
  W : ∀ b, o.W b ∈ AB
  K : ∀ Y, IsConn j Y → o.K Y ∈ AB
  u : o.u ∈ AB

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N} (g μ : ℝ)
  {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N}

/-- The full inputs of a step have no `σ_a`, `σ_b` parts. -/
theorem oabS_full (ho : ObsAbInv j o) :
    OAbS j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) :=
  ⟨fun b => add_mem (emb_mem_ab _) (ho.V b), fun b => add_mem (emb_mem_ab _) (ho.W b),
    fun Y hY => mul_mem (emb_mem_ab _) (add_mem (emb_mem_ab _) (ho.K Y hY))⟩

/-- **The zero one-point sectors are preserved by one step of the observable flow.** -/
theorem obsAbInv_step (ho : ObsAbInv j o) :
    ObsAbInv (j + 1) (obsStep R P j st g μ D K o) := by
  have H := oabS_full R g μ (st := st) (D := D) (K := K) ho
  have hS := H.step (P := P) (C := stCov R j st)
  exact ⟨fun c' => πobs_mem_ab (hS.hV c'), fun c' => πobs_mem_ab (hS.hW c'),
    fun Y hY => πobs_mem_ab (hS.hK Y hY),
    add_mem ho.u (Subalgebra.sum_mem _ fun b _ => H.up_ab b)⟩

variable [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **PR2: along the history from `j`, a state without one-point parts keeps none.** -/
theorem obsAbInv_histFrom {o' : ObsSt c L N} (h0 : ObsAbInv j o') (t : Hist.Seq (Xs R)) :
    ∀ d, ObsAbInv (j + d) (obsHistFrom R P j o' (j + d) t)
  | 0 => by rw [Nat.add_zero, obsHistFrom_self]; exact h0
  | d + 1 => by
    rw [← Nat.add_assoc, obsHistFrom_succ (by omega)]
    exact obsAbInv_step R P _ _ (obsAbInv_histFrom h0 t d)

end Ab

/-! ### The chain identity from scale `j` -/

section Chain

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (j : ℕ) (o' : ObsSt c L N)

/-- The input with sources of step `k` along the history from `j`. -/
def ZhOF (k : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  ZinO R k (rawHist R k t) (t k).1 (t k).2.1 (rawD R (rawHist R k t).u (t k).2.2)
    (rawK R (rawHist R k t).u (t k).2.2) (obsHistFrom R P j o' k t)

/-- The step constant `det·e^{-u_{k+1}(Λ)}` along the history from `j`. -/
def chOF (k : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  detStep R k (rawHist R k t) • uOutO R P k (rawHist R k t) (t k).1 (t k).2.1
    (rawD R (rawHist R k t).u (t k).2.2) (rawK R (rawHist R k t).u (t k).2.2)
    (obsHistFrom R P j o' k t)

/-- The final object `F_N` along the history from `j`. -/
def finOF (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  finO R P (Nh + 1) (histOut R Nh t).st (histOut R Nh t).g.re (histOut R Nh t).nu.re
    (histOut R Nh t).D (histOut R Nh t).K (obsHistFrom R P j o' (Nh + 1) t)

/-- The constant `det·e^{-u_N}` of the last step along the history from `j`. -/
def lastCstOF (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  detStep R (Nh + 1) (histOut R Nh t).st • uOutNO R P (Nh + 1) (histOut R Nh t).st
    (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
    (obsHistFrom R P j o' (Nh + 1) t)

/-- The zero-mode constant `c = t_raw/|Λ|` (independent of the observables). -/
def zmC (Nh : ℕ) (t : Hist.Seq (Xs R)) : ℂ :=
  zmRaw R (Nh + 1) (Function.update (histOut R Nh t).st.ζ (Nh + 1)
    (stZeta R (histOut R Nh t).st)) / Fintype.card (Lam 2 L N)

/-- The zero-mode integral `Ω' = ω_{cQ}(F_N)` along the history from `j`. -/
def zmOF (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  omegaCO (cstC (Lam 2 L N) (zmC R Nh t)) (finOF R P j o' Nh t)

/-- The last factor (the step `N - 1` and the zero mode) along the history from `j`. -/
def lastOF (Nh : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  detStep R (Nh + 1) (histOut R Nh t).st • (uOutNO R P (Nh + 1) (histOut R Nh t).st
    (histOut R Nh t).g.re (histOut R Nh t).nu.re (histOut R Nh t).D (histOut R Nh t).K
    (obsHistFrom R P j o' (Nh + 1) t) * zmOF R P j o' Nh t)

/-- The constants of `Π'^{≥k}`: `X' = ∏_{k ≤ i ≤ N_h} chOF_i · det·e^{-u_N}`. -/
def cstOF (Nh k : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  (∏ i ∈ Ico k (Nh + 1), chOF R P j o' i t) * lastCstOF R P j o' Nh t

/-- `Π'^{≥k}` along the history from `j`. -/
def prodHiF (Nh k : ℕ) (t : Hist.Seq (Xs R)) : OE c (Lam 2 L N) :=
  (∏ i ∈ Ico k (Nh + 1), chOF R P j o' i t) * lastOF R P j o' Nh t

theorem prodHiF_eq (Nh k : ℕ) (t : Hist.Seq (Xs R)) :
    prodHiF R P j o' Nh k t = cstOF R P j o' Nh k t * zmOF R P j o' Nh t := by
  rw [prodHiF, cstOF, lastOF, lastCstOF, mul_assoc, smul_mul_assoc]

set_option maxHeartbeats 1000000 in
/-- **`ω_{Γ_k}(Z_k(o')) = Π'^{≥k}`**: the observable chain of the history started at scale `j` from
`o'` (`j ≤ k ≤ N_h`; copy of `hist_omegaO_from`). -/
theorem hist_omegaOF_from {Nh : ℕ} (hN : Nh + 2 = N)
    (hρ1 : R.ρ < 1) (hspl : SplitSmall R.P L R.ρ) (hm0 : 0 < R.msq)
    (hm : R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hV : ∀ j < Nh, ValidAt R j)
    (hVL : ValidAtL R Nh) (b μ₀ : ℝ) (ho' : o'.IsObs) (h0 : ObsLocInv P j o') {k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ Nh) :
    omegaCO (Γh R k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀))
        (ZhOF R P j o' k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)) =
      prodHiF R P j o' Nh k (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
  set t := traj (rgData R) ((L : ℝ) ^ 2) b μ₀ with htd
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hLg := hVL.1
  have hcore : ∀ i ≤ Nh, ValidCore R i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI : ∀ i ≤ Nh + 1, RawInv R i (rawHist R i t) := rawInv_histU R hV hVL t
  have hloc : ∀ i, j ≤ i → i ≤ Nh → OLocHyp P i
      (fullV R i (rawHist R i t) (t i).1 (t i).2.1 (obsHistFrom R P j o' i t))
      (fullW (rawHist R i t) (rawD R (rawHist R i t).u (t i).2.2) (obsHistFrom R P j o' i t))
      (fullK R i (rawHist R i t) (rawK R (rawHist R i t).u (t i).2.2)
        (obsHistFrom R P j o' i t)) := fun i hi1 hi2 => by
    have hl := obsLocInv_histFrom (R := R) h0 t (i - j) fun i' _ hi' =>
      ⟨hcore i' (by omega), hRI i' (by omega)⟩
    rw [show j + (i - j) = i by omega] at hl
    exact (olocS_full R P _ _ (hcore i hi2) (hRI i (by omega)) (rawD_mem R _ _)
      (rawK_mem R _ _) hl).toOLocHyp
  have hS : ∀ i ≤ Nh + 1, SplitOK R i (rawHist R i t) := fun i hi =>
    splitOK_hist R hρ0 hspl (by omega) hm0 hm t (by omega)
  have hO : ∀ i, (obsHistFrom R P j o' i t).IsObs := fun i => obsHistFrom_isObs ho' t i
  have hstep : ∀ i, j ≤ i → i ≤ Nh → omegaCO (Γh R i t) (ZhOF R P j o' i t) =
      chOF R P j o' i t * omegaCO (DressedFRD.kmat ((stData R i (rawHist R i t)).Gam (i + 1)))
        (ZoutO R P i (rawHist R i t) (t i).1 (t i).2.1 (rawD R (rawHist R i t).u (t i).2.2)
          (rawK R (rawHist R i t).u (t i).2.2) (obsHistFrom R P j o' i t)) :=
    fun i hi1 hi2 => by
      rw [chOF, smul_mul_assoc]
      exact rawStepO_omega (hcore i hi2) (hRI i (by omega)) (hS i (by omega)) (hO i)
        (hloc i hi1 hi2)
  have hzout : ∀ i, j ≤ i → i ≤ Nh → ZoutO R P i (rawHist R i t) (t i).1 (t i).2.1
      (rawD R (rawHist R i t).u (t i).2.2) (rawK R (rawHist R i t).u (t i).2.2)
      (obsHistFrom R P j o' i t) = ZinO R (i + 1) (histOut R i t).st (histOut R i t).g.re
        (histOut R i t).nu.re (histOut R i t).D (histOut R i t).K
        (obsHistFrom R P j o' (i + 1) t) := fun i hi1 hi2 => by
    have hVL' : ValidAtL R i := by
      rcases Nat.lt_or_ge i Nh with h | h
      · exact (hV i h).toValidAtL hLg
      · rw [show i = Nh by omega]; exact hVL
    obtain ⟨hnu, hg⟩ := traj_out_real R hρ0 hρ1 ((L : ℝ) ^ 2) b μ₀ i
    rw [obsHistFrom_succ hi1]
    exact zoutO_eq R P hVL' (hRI i (by omega)) (rawD_mem R _ _) (rawK_mem R _ _) hρ1 hnu hg
      (hO i)
  have hrec : ∀ i, j ≤ i → i < Nh → omegaCO (Γh R i t) (ZhOF R P j o' i t) =
      chOF R P j o' i t * omegaCO (Γh R (i + 1) t) (ZhOF R P j o' (i + 1) t) :=
    fun i hi1 hi => by
      have hVi : ∀ k ≤ i, ValidAt R k := fun k hk => hV k (by omega)
      obtain ⟨e1, e2, e3, e4⟩ := traj_next R hρ1 b μ₀ hVi
      rw [hstep i hi1 hi.le, hzout i hi1 hi.le, (traj_exact R hρ1 hLg b μ₀ hVi).2]
      unfold ZhOF
      rw [e1, e2, e3, e4]
      rfl
  have hlast : omegaCO (Γh R Nh t) (ZhOF R P j o' Nh t) =
      chOF R P j o' Nh t * lastOF R P j o' Nh t := by
    have h2 := hstep Nh (hjk.trans hk) le_rfl
    rw [hzout Nh (hjk.trans hk) le_rfl, (traj_exactL R hρ1 b μ₀ hV hVL).2] at h2
    have h3 := lastStepO_omega (R := R) (P := P) (j := Nh + 1) (st := (histOut R Nh t).st)
      (g := (histOut R Nh t).g.re) (μ := (histOut R Nh t).nu.re) (D := (histOut R Nh t).D)
      (K := (histOut R Nh t).K) (o := obsHistFrom R P j o' (Nh + 1) t) (by omega)
      (hRI (Nh + 1) le_rfl) (hS (Nh + 1) le_rfl) (hO (Nh + 1))
    rw [h2, h3]
    rfl
  have key : ∀ n k, j ≤ k → k + n = Nh →
      omegaCO (Γh R k t) (ZhOF R P j o' k t) = prodHiF R P j o' Nh k t := by
    intro n
    induction n with
    | zero =>
      intro k hjk' hk'
      obtain rfl : k = Nh := by omega
      rw [hlast, prodHiF, Nat.Ico_succ_singleton, prod_singleton]
    | succ n ih =>
      intro k hjk' hk'
      rw [hrec k hjk' (by omega), ih (k + 1) (by omega) (by omega), prodHiF, prodHiF,
        prod_eq_prod_Ico_succ_bot (by omega : k < Nh + 1), mul_assoc]
  exact key (Nh - k) k hjk (by omega)

end Chain

end

end PtCorr2
