import PtCorr2.Obs.LinearHist
import PtCorr2.Obs.ObsHistTop
import PtCorr2.Pair.KObsHistAB
import PtCorr2.Obs.ObsSymFrom
import Obs2.Pair.CoalHistL

/-!
# T5: the restarted history — the `b`-sector, the coalescence invariant, locality at `N_h + 1`

Along the restarted history `obsHistFrom R P m δ` (datum `δ` at scale `m`):

* `rpb_histFrom_obsHist`: restarting the history `obsHist R P o₀` at `m` from its own state gives
  it back (`k ≥ m`).
* **`rpb_b_sector`**: if the datum carries the reference `b`-part
  (`prjSt false δ = prjSt false (obsHist R P o₀ m t)`), so does every later state;
  **`rpb_b_eq`**: the `σ_b` components of `V(B)`, `𝒲(B)`, `K(X)`, `u` agree with the reference.
* **`rpb_coalInv`**: `ObsCoalInv` from the datum along the history below coalescence;
  **`rpb_coal_validL`**: `V_{ab} = 0`, `u_{ab} = 0` up to `min(j_ab, N_h + 1)` (`ValidAtL`).
* **`rpb_inv_top`**: `IsObs`, `ObsLocInv`, `ObsSymInv` at every `m ≤ j ≤ N_h + 1` (`hist_validL`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L]

section Gen

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- Restarting the history at `m` from its own state at `m` gives the history back. -/
theorem rpb_histFrom_obsHist {c : Obs.Case} (o₀ : ObsSt c L N) (m : ℕ) (t : Hist.Seq (Xs R)) :
    ∀ k, m ≤ k → obsHistFrom R P m (obsHist R P o₀ m t) k t = obsHist R P o₀ k t
  | 0, h => by
    obtain rfl : m = 0 := by omega
    rfl
  | k + 1, h => by
    rcases Nat.eq_or_lt_of_le h with e | hlt
    · rw [← e, obsHistFrom_self]
    · rw [obsHistFrom_succ (by omega), obsHist_succ, rpb_histFrom_obsHist o₀ m t k (by omega)]

end Gen

/-! ### The `b`-sector -/

section BSector

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The points `(P.b, P.b)` (the `σ_b` projection sees only `P.b`). -/
def rpbPb (P : ObsPts 2 L N) : ObsPts 2 L N := ⟨P.b, P.b, P.Ra⟩

/-- **The restarted history carries the reference `b`-part.** -/
theorem rpb_b_sector (P : ObsPts 2 L N) (o₀ δ : ObsSt .two L N) {m : ℕ} (t : Hist.Seq (Xs R))
    (hb : prjSt false δ = prjSt false (obsHist R P o₀ m t)) :
    ∀ k, m ≤ k → prjSt false (obsHistFrom R P m δ k t) = prjSt false (obsHist R P o₀ k t) := by
  intro k hk
  have hP : (rpbPb P).a = P.pt false := rfl
  rw [prj_obsHistFrom R false hP m δ t k, hb, ← prj_obsHistFrom R false hP m _ t k,
    rpb_histFrom_obsHist R P o₀ m t k hk]

/-- Equal `σ_b` projections have equal `σ_b` components. -/
theorem rpb_prjSt_false_eq {o o' : ObsSt .two L N} (h : prjSt false o = prjSt false o') :
    (∀ b, (o.V b : SA .two (Lam 2 L N)).b = (o'.V b : SA .two (Lam 2 L N)).b) ∧
    (∀ b, (o.W b : SA .two (Lam 2 L N)).b = (o'.W b : SA .two (Lam 2 L N)).b) ∧
    (∀ X, (o.K X : SA .two (Lam 2 L N)).b = (o'.K X : SA .two (Lam 2 L N)).b) ∧
    (o.u : SA .two (Lam 2 L N)).b = (o'.u : SA .two (Lam 2 L N)).b := by
  refine ⟨fun b => ?_, fun b => ?_, fun X => ?_, ?_⟩
  · have := congrArg (fun s : ObsSt .two L N => ((s.V b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_false] using this
  · have := congrArg (fun s : ObsSt .two L N => ((s.W b : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_false] using this
  · have := congrArg (fun s : ObsSt .two L N => ((s.K X : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_false] using this
  · have := congrArg (fun s : ObsSt .two L N => ((s.u : OE .two (Lam 2 L N)) :
      SA .two (Lam 2 L N)).a) h
    simpa [prjSt, Obs2.coe_prjO, Obs2.prjS_a, Obs2.cmp_false] using this

/-- **The `σ_b` components of the restarted states are the reference ones.** -/
theorem rpb_b_eq (P : ObsPts 2 L N) (o₀ δ : ObsSt .two L N) {m : ℕ} (t : Hist.Seq (Xs R))
    (hb : prjSt false δ = prjSt false (obsHist R P o₀ m t)) {k : ℕ} (hk : m ≤ k) :
    (∀ b, ((obsHistFrom R P m δ k t).V b : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ k t).V b : SA .two (Lam 2 L N)).b) ∧
    (∀ b, ((obsHistFrom R P m δ k t).W b : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ k t).W b : SA .two (Lam 2 L N)).b) ∧
    (∀ X, ((obsHistFrom R P m δ k t).K X : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ k t).K X : SA .two (Lam 2 L N)).b) ∧
    ((obsHistFrom R P m δ k t).u : SA .two (Lam 2 L N)).b =
      ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).b :=
  rpb_prjSt_false_eq (rpb_b_sector R P o₀ δ t hb k hk)

end BSector

/-! ### Invariants along the restarted history -/

section Inv

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The coalescence invariant along the restarted history** (`m ≤ j < j_{ab}`, `j ≤ n`), from
the range of the step covariances below `n`. -/
theorem rpb_coalInv {c : Obs.Case} {m : ℕ} {δ : ObsSt c L N} (h₀ : δ.IsObs)
    (hinv₀ : ObsCoalInv P m δ) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {n : ℕ} (hnN : n ≤ N)
    (t : Hist.Seq (Xs R))
    (hC : ∀ k < n, ∀ x y, (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (x - y) →
      stCov R k (rawHist R k t) x y = 0) :
    ∀ j, m ≤ j → j < coal L P.a P.b → j ≤ n → ObsCoalInv P j (obsHistFrom R P m δ j t) := by
  intro j
  induction j with
  | zero => intro hm _ _; obtain rfl : m = 0 := by omega
            rw [obsHistFrom_self]; exact hinv₀
  | succ k ih =>
    intro hm hk hkn
    rcases Nat.eq_or_lt_of_le hm with e | hlt
    · rw [← e, obsHistFrom_self]; exact hinv₀
    · rw [obsHistFrom_succ (by omega)]
      exact obsStep_coalInv R P k _ _ _ _ _ (ih (by omega) (by omega) (by omega))
        (obsHistFrom_isObs h₀ t k) hL (by omega) (hC k (by omega)) (pow_le_of_lt_coal hk)

/-- **`V_{ab} = 0`, `u_{ab} = 0` along the restarted history up to `min(j_{ab}, n)`.** -/
theorem rpb_coal_upto {c : Obs.Case} {m : ℕ} {δ : ObsSt c L N} (h₀ : δ.IsObs)
    (hinv₀ : ObsCoalInv P m δ) (hL : 2 ^ (2 + 3) + 8 * 2 < L) {n : ℕ}
    (hn : n ≤ coal L P.a P.b) (hnN : n ≤ N) (t : Hist.Seq (Xs R))
    (hC : ∀ k < n, ∀ x y, (L : ℝ) ^ (k + 1) / 2 ≤ supNorm (x - y) →
      stCov R k (rawHist R k t) x y = 0) :
    ∀ j, m ≤ j → j ≤ n → (∀ B, ((obsHistFrom R P m δ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHistFrom R P m δ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  have inv := rpb_coalInv R P h₀ hinv₀ hL hnN t hC
  intro j hmj hj
  rcases Nat.lt_or_ge j (coal L P.a P.b) with hlt | hge
  · exact ⟨(inv j hmj hlt hj).Vab, (inv j hmj hlt hj).uab⟩
  · obtain rfl : j = coal L P.a P.b := le_antisymm (hj.trans hn) hge
    rcases Nat.eq_or_lt_of_le hmj with e | hlt
    · rw [← e, obsHistFrom_self]; exact ⟨hinv₀.Vab, hinv₀.uab⟩
    · obtain ⟨k, hk⟩ : ∃ k, coal L P.a P.b = k + 1 := ⟨coal L P.a P.b - 1, by omega⟩
      rw [hk, obsHistFrom_succ (by omega)]
      exact obsStep_coal_last R P k _ _ _ _ _ (inv k (by omega) (by omega) (by omega))
        (obsHistFrom_isObs h₀ t k) hL (by omega) (hC k (by omega))
        (pow_le_of_lt_coal (by omega))

/-- **`V_{ab} = 0`, `u_{ab} = 0` up to `min(j_{ab}, N_h + 1)`** (`ValidAt` below `N_h`,
`ValidAtL` at `N_h`). -/
theorem rpb_coal_validL {c : Obs.Case} {Nh m : ℕ} (hN : Nh + 2 = N) {δ : ObsSt c L N}
    (h₀ : δ.IsObs) (hinv₀ : ObsCoalInv P m δ) (hL : 2 ^ (2 + 3) + 8 * 2 < L)
    (hV : ∀ k < Nh, ValidAt R k) (hVL : ValidAtL R Nh) (t : Hist.Seq (Xs R)) :
    ∀ j, m ≤ j → j ≤ min (coal L P.a P.b) (Nh + 1) →
      (∀ B, ((obsHistFrom R P m δ j t).V B : SA c (Lam 2 L N)).ab = 0) ∧
      ((obsHistFrom R P m δ j t).u : SA c (Lam 2 L N)).ab = 0 := by
  refine rpb_coal_upto R P h₀ hinv₀ hL (min_le_left _ _)
    ((min_le_right _ _).trans (by omega)) t fun k hk x y hxy => ?_
  have hkN : k ≤ Nh := by have := min_le_right (coal L P.a P.b) (Nh + 1); omega
  have H := rawInv_histU R hV hVL t k (by omega)
  exact (covU R hV hVL hkN H).1.range (by omega) x y hxy

/-- **The invariants of the restarted history up to `N_h + 1`.** -/
theorem rpb_inv_top {c : Obs.Case} {Nh m : ℕ} (hV : ∀ k < Nh, ValidAt R k)
    (hVL : ValidAtL R Nh) {δ : ObsSt c L N} (h0 : δ.IsObs) (hl0 : ObsLocInv P m δ)
    (hs0 : ObsSymInv m δ) (t : Hist.Seq (Xs R)) {j : ℕ} (hmj : m ≤ j) (hj : j ≤ Nh + 1) :
    (obsHistFrom R P m δ j t).IsObs ∧ ObsLocInv P j (obsHistFrom R P m δ j t) ∧
      ObsSymInv j (obsHistFrom R P m δ j t) := by
  have hval := hist_validL R hV hVL t
  exact ⟨obsHistFrom_isObs h0 t j,
    obsLocInv_histFrom' R P hl0 t hmj fun i _ hi => hval i (by omega),
    obsSymInv_histFrom' R P hs0 t hmj fun i _ hi => hval i (by omega)⟩

end Inv

end

end PtCorr2
