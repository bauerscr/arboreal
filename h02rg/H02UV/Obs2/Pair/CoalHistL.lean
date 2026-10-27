import Obs2.Pair.CoalHist
import Step2.Last.FlowLastF1a

/-!
# Lemma `lem:coal` up to a cap below `j_ab` (top coalescence)

`obsHist_coal` needs the range of the step covariances for every `k < j_ab`. At the top of the
flow (`j_ab ∈ {N - 1, N}`) the covariance of the step `N_h = N - 2` has the range `L^{N-1}/2`
(`ValidAtL` contains `ValidCore`, `RawInv.covL`), but the last covariance has none. The cap:

* **`obsHist_coal_upto`**: for `n ≤ j_ab` and the range of the step covariances for `k < n`,
  `V^{obs}_{j,ab} = 0` and `u^{obs}_{j,ab} = 0` for all `j ≤ n`;
* **`obsHist_coal_validL`**: the same with `n = min(j_ab, N_h + 1)` from `ValidAt` below `N_h` and
  `ValidAtL` at `N_h`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs FRD

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- **`lem:coal` up to a cap `n ≤ j_ab`**: the range of the step covariances for `k < n` gives
`V^{obs}_{j,ab} = 0`, `u^{obs}_{j,ab} = 0` for `j ≤ n`. -/
theorem obsHist_coal_upto (h₀ : o₀.IsObs) (hinv₀ : ObsCoalInv P 0 o₀)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) {n : ℕ} (hn : n ≤ coal L P.a P.b) (hnN : n ≤ N)
    (t : Flow2.Hist.Seq (Xs R))
    (hC : ∀ k < n, ∀ x y, (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (x - y) →
      stCov R k (rawHist R k t) x y = 0) :
    ∀ j ≤ n, (∀ B, ((obsHist R P o₀ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHist R P o₀ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  have inv : ∀ j, j < coal L P.a P.b → j ≤ n → ObsCoalInv P j (obsHist R P o₀ j t) := by
    intro j
    induction j with
    | zero => intro _ _; exact hinv₀
    | succ k ih =>
      intro hk hkn
      rw [obsHist_succ]
      exact obsStep_coalInv R P k _ _ _ _ _ (ih (by omega) (by omega))
        (obsHist_isObs R P o₀ h₀ k t) hL (by omega) (hC k (by omega)) (pow_le_of_lt_coal hk)
  intro j hj
  rcases Nat.lt_or_ge j (coal L P.a P.b) with hlt | hge
  · exact ⟨(inv j hlt hj).Vab, (inv j hlt hj).uab⟩
  · obtain rfl : j = coal L P.a P.b := le_antisymm (hj.trans hn) hge
    rcases Nat.eq_zero_or_pos (coal L P.a P.b) with h0 | hpos
    · rw [h0]; exact ⟨hinv₀.Vab, hinv₀.uab⟩
    · obtain ⟨k, hk⟩ : ∃ k, coal L P.a P.b = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk, obsHist_succ]
      exact obsStep_coal_last R P k _ _ _ _ _ (inv k (by omega) (by omega))
        (obsHist_isObs R P o₀ h₀ k t) hL (by omega) (hC k (by omega)) (pow_le_of_lt_coal (by omega))

/-- **`lem:coal` up to `min(j_ab, N_h + 1)`** from `ValidAt` below `N_h` and `ValidAtL` at `N_h`
(the step `N_h` has the range `L^{N_h+1}/2` through `ValidCore`). -/
theorem obsHist_coal_validL {Nh : ℕ} (hN : Nh + 2 = N) (h₀ : o₀.IsObs)
    (hinv₀ : ObsCoalInv P 0 o₀) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hV : ∀ k < Nh, ValidAt R k) (hVL : ValidAtL R Nh) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ j ≤ min (coal L P.a P.b) (Nh + 1),
      (∀ B, ((obsHist R P o₀ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHist R P o₀ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  refine obsHist_coal_upto R P o₀ h₀ hinv₀ hL (min_le_left _ _)
    ((min_le_right _ _).trans (by omega)) t fun k hk x y hxy => ?_
  have hkN : k ≤ Nh := by have := min_le_right (coal L P.a P.b) (Nh + 1); omega
  have H := rawInv_histU R hV hVL t k (by omega)
  exact (covU R hV hVL hkN H).1.range (by omega) x y hxy

end Hist

end

end Obs2
