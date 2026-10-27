import PtCorr2.Pair.PairReduceChain
import Obs2.Flow.MuChainAB

/-!
# The reduced `r` flow in the `𝔫^{(2)}` split along the history from coalescence

Along `obsHistFrom` from `j` (state `o'` without one-point parts, `𝒲'_{j,ab} = 0`):

* `hWR_succ_ab`, **`muChainAB_hR`**: the reduced inputs form an `Obs2.MuChainAB` from `j`.
* `tadInc2_hR_eq`: the tadpole increments only see the bulk, so they are those of any other
  observable history (e.g. the original one, `nn2`).
* **`srcAB_hR_eq`**: `σ'_k + (∑_{i<k}tadInc2 i k)r'_k = -(drift'_k + err'_k)` (`k ≥ j`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

theorem VprLO_e_fullV_indep (R : RGPar 2 L N) (k : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
    (C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ) {o1 o2 : ObsSt .two L N} (h1 : o1.IsObs)
    (h2 : o2.IsObs) :
    (VprLO k C (fullV R k st g μ o1) : SA .two (Lam 2 L N)).e =
      (VprLO k C (fullV R k st g μ o2) : SA .two (Lam 2 L N)).e := by
  unfold VprLO
  rw [AddSubmonoidClass.coe_finsetSum, sum_e, AddSubmonoidClass.coe_finsetSum, sum_e]
  refine sum_congr rfl fun b _ => ?_
  unfold VprO EthO
  rw [coe_ECCO, ECCS_e, coe_ECCO, ECCS_e, coe_thetaO, thetaS_e, coe_thetaO, thetaS_e,
    fullV_e_indep R k st g μ h1 h2 b]

section Chain

variable {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {P : ObsPts 2 L N} {j : ℕ}
  {o' : ObsSt .two L N} {t : Hist.Seq (Xs R)}

theorem hWR_succ_ab {k : ℕ} (hk : j ≤ k) (c' : Fin 2 → ℕ) :
    (hWR R P j o' t (k + 1) c' : SA .two (Lam 2 L N)).ab =
      (Wnext2O P k (histCovO R t k) (hVR R P j o' t k) (hWR R P j o' t k) c' :
        SA .two (Lam 2 L N)).ab := by
  show (((emb _ : OE .two (Lam 2 L N)) + (obsHistFrom R P j o' (k + 1) t).W c' :
    OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = _
  rw [obsHistFrom_succ hk]
  exact (zero_add _).trans (piobs_ab _)

theorem hWR_self_ab (hW0 : ∀ b, (o'.W b : SA .two (Lam 2 L N)).ab = 0) (b : Fin 2 → ℕ) :
    (hWR R P j o' t j b : SA .two (Lam 2 L N)).ab = 0 := by
  show (((emb _ : OE .two (Lam 2 L N)) + (obsHistFrom R P j o' j t).W b :
    OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab = _
  rw [obsHistFrom_self]
  exact (zero_add _).trans (hW0 b)

/-- **The reduced inputs form an `ab` chain from `j`.** -/
theorem muChainAB_hR (h0 : ObsAbInv j o') (hW0 : ∀ b, (o'.W b : SA .two (Lam 2 L N)).ab = 0)
    (n : ℕ) : MuChainAB P (histCovO R t) (hVR R P j o' t) (hWR R P j o' t) j n where
  hW0 := hWR_self_ab hW0
  hW _ hk _ c' := hWR_succ_ab hk c'
  hVa _ hk _ b := hVR_a h0 hk b

/-- The tadpole increments of the reduced history are those of any observable history. -/
theorem tadInc2_hR_eq (ho' : o'.IsObs) {o₀ : ObsSt .two L N} (ho₀ : o₀.IsObs) (i k : ℕ) :
    tadInc2 P (histCovO R t) (hVR R P j o' t) i k =
      tadInc2 P (histCovO R t) (histVO2 R P o₀ t) i k := by
  unfold tadInc2 bulkE2 hVR histVO2
  rw [VprLO_e_fullV_indep R i _ _ _ _ (obsHistFrom_isObs ho' t i) (obsHist_isObs R P o₀ ho₀ i t)]

/-- **The reduced `r` source in the `𝔫^{(2)}` split** (exact, `k ≥ j`). -/
theorem srcAB_hR_eq (h0 : ObsAbInv j o') (hW0 : ∀ b, (o'.W b : SA .two (Lam 2 L N)).ab = 0)
    {k : ℕ} (hk : j ≤ k) :
    srcAB P (histCovO R t) (hVR R P j o' t) (hWR R P j o' t) (hKR R P j o' t) k +
        (∑ i ∈ range k, tadInc2 P (histCovO R t) (hVR R P j o' t) i k) * rR R P j o' t k =
      -(driftAB P (histCovO R t) (hVR R P j o' t) j k +
        errAB P (histCovO R t) (hVR R P j o' t) (hWR R P j o' t) (hKR R P j o' t) j k) :=
  (muChainAB_hR h0 hW0 k).srcAB_eq (hKR R P j o' t) hk le_rfl

end Chain

end

end PtCorr2
