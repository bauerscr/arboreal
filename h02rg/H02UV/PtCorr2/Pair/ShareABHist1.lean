import PtCorr2.Pair.PairChainAB
import PtCorr2.Pair.VObsStepAB1
import Obs2.Pair.ShareAB1

/-!
# The per-region `r'` flow along the reduced history

Along `obsHistFrom` from `j` (state `o'` without one-point parts, `𝒲'_{j,ab} = 0`):

* `rRX X k = r'_k(X) = ∑_{B ∈ 𝓑_k(X)} m₂(V_k(B)_{ab})` (`rRX_blockSet`: the mass of a `k`-block);
* `frakN2_hR_eq`: `𝔫^{(2)}` of the reduced history is that of any other observable history (it
  only sees the bulk);
* **`rRX_flow`**: for an `n`-polymer `X` and `j ≤ k < n`,
  `r'_{k+1}(X) = (1 − 𝔫^{(2)}_k)r'_k(X) − drift_k(X) − err_k(X)` (`Obs2.MuChainAB.rABX_flow`);
* `rRX_self`: `r'_j(X) = 0` when `V'_{j,ab} = 0` (the reduced state, `redSt`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LocObs

variable {L N : ℕ} [NeZero L]

section Chain

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N) (j : ℕ)
  (o' : ObsSt .two L N) (t : Hist.Seq (Xs R))

/-- `r'_k(X)` along the reduced history from `j`. -/
def rRX (X : Finset (Lam 2 L N)) (k : ℕ) : ℂ := rABX k (hVR R P j o' t k) X

variable {R P j o' t}

theorem rRX_blockSet (k : ℕ) (c : Fin 2 → ℕ) (hne : (blockSet (L := L) (N := N) k c).Nonempty) :
    rRX R P j o' t (blockSet (L := L) (N := N) k c) k =
      mass2 (hVR R P j o' t k c : SA .two (Lam 2 L N)).ab :=
  rABX_blockSet k _ hne

/-- `𝔫^{(2)}` only sees the bulk. -/
theorem frakN2_hR_eq (ho' : o'.IsObs) {o₀ : ObsSt .two L N} (ho₀ : o₀.IsObs) (k : ℕ) :
    frakN2 P (histCovO R t) (hVR R P j o' t) k = frakN2 P (histCovO R t) (histVO2 R P o₀ t) k := by
  have he : bulkE2 (histCovO R t) (hVR R P j o' t) k = bulkE2 (histCovO R t) (histVO2 R P o₀ t) k :=
    VprLO_e_fullV_indep R k _ _ _ _ (obsHistFrom_isObs ho' t k) (obsHist_isObs R P o₀ ho₀ k t)
  have hs : ∑ i ∈ range k, tadInc2 P (histCovO R t) (hVR R P j o' t) i k =
      ∑ i ∈ range k, tadInc2 P (histCovO R t) (histVO2 R P o₀ t) i k :=
    sum_congr rfl fun i _ => tadInc2_hR_eq ho' ho₀ i k
  unfold frakN2 nuBar2
  rw [he, hs]

/-- **The relative recursion of `r'(X)` along the reduced history** (an `n`-polymer `X`). -/
theorem rRX_flow (h0 : ObsAbInv j o') (hW0 : ∀ b, (o'.W b : SA .two (Lam 2 L N)).ab = 0) {n : ℕ}
    {X : Finset (Lam 2 L N)} (hX : IsPolymer n X) {k : ℕ} (hk : j ≤ k) (hkn : k < n) :
    rRX R P j o' t X (k + 1) =
      (1 - frakN2 P (histCovO R t) (hVR R P j o' t) k) * rRX R P j o' t X k -
        driftABX P (histCovO R t) (hVR R P j o' t) X j k -
        errABX2 P (histCovO R t) (hVR R P j o' t) (hWR R P j o' t) (hKR R P j o' t) X j k :=
  (muChainAB_hR h0 hW0 n).rABX_flow (hKR R P j o' t) (fun _ hk' _ c' => hVR_succ_ab hk' c') hX hk
    hkn

/-- `r'_j(X) = 0` when the reduced state has no `V_{ab}`. -/
theorem rRX_self (hV0 : ∀ b, (o'.V b : SA .two (Lam 2 L N)).ab = 0) (X : Finset (Lam 2 L N)) :
    rRX R P j o' t X j = 0 := by
  unfold rRX rABX
  refine sum_eq_zero fun b _ => ?_
  rw [hVR_ab, obsHistFrom_self, hV0 b, mass2_zero]

end Chain

end

end PtCorr2
