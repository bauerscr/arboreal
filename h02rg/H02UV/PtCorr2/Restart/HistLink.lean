import PtCorr2.Restart.RestartHist

/-!
# The restarted history of a history state is the history (B3, T6 input)

Restarting the observable flow at scale `m` from the state of the history at `m` reproduces the
history above `m`:

* **`obsHistFrom_obsHist`**: `obsHistFrom R P m (obsHist R P o₀ m t) k t = obsHist R P o₀ k t`
  for `k ≥ m`;
* `wbHF_obsHist_iff`, `kbHF_obsHist_iff`: the restarted size predicates `WbHF`, `KbHF` of this
  datum are the history predicates `WbHc`, `KbHc` (`k ≥ m`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L] {c : Obs.Case}
variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The restart of the history at `m` from its own state is the history.** -/
theorem obsHistFrom_obsHist (o₀ : ObsSt c L N) (t : Flow2.Hist.Seq (Xs R)) {m k : ℕ}
    (hk : m ≤ k) : obsHistFrom R P m (obsHist R P o₀ m t) k t = obsHist R P o₀ k t := by
  induction k, hk using Nat.le_induction with
  | base => exact obsHistFrom_self m _ t
  | succ k hmk ih => rw [obsHistFrom_succ hmk, ih]; rfl

theorem wbHF_obsHist_iff (o₀ : ObsSt c L N) (t : Flow2.Hist.Seq (Xs R)) {m k : ℕ} (hk : m ≤ k)
    (x : ℝ) : WbHF R P m (obsHist R P o₀ m t) t k x ↔ WbHc R P o₀ t k x := by
  unfold WbHF WbHc; rw [obsHistFrom_obsHist R P o₀ t hk]

theorem kbHF_obsHist_iff (o₀ : ObsSt c L N) (t : Flow2.Hist.Seq (Xs R)) {m k : ℕ} (hk : m ≤ k)
    (x : ℝ) : KbHF R P m (obsHist R P o₀ m t) t k x ↔ KbHc R P o₀ t k x := by
  unfold KbHF KbHc; rw [obsHistFrom_obsHist R P o₀ t hk]

end

end PtCorr2
