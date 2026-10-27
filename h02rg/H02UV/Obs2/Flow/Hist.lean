import Obs2.Map.Map
import Step2.Flow.FlowBounds

/-!
# The observable flow along the bulk history (`h02uv-outline.tex`, Section `sec:obs-flow`)

`d = 2`, raw fields. `Step2.rawStep` is unchanged; the observables form a separate recursion
driven by the bulk history (`Step2.rawHist`). At scale `j` the observable state (`ObsSt`) is
* `V`: the observable part `V^{obs}_j(B)` of the block polynomial (a block family with sources),
* `W`: the observable part `𝒲^{obs}_j(B)` of the second-order remainder,
* `K`: the observable part `K^{obs}_j(X)` of the activity,
* `u`: the accumulated observable constant `∑_{k<j} u^{obs}_{k+1}(Λ)` (the generating function of
  the correlations; the bulk constant is a normalisation and is discarded, as in `rawStep`),
all with vanishing bulk component (`ObsSt.IsObs`).

**One step** (`obsStep`): with the bulk pieces of `rawStep` (`Step2.Flow.FlowBounds`: covariance
`stCov`, `V♭ = stVf`, absorbed polynomial `Δ = stDelta`, `𝒲 = W^{lin} + D`), the full inputs are
(`fullV`, `fullW`, `fullK`)

  `V♭ + V^{obs}`,  `𝒲 + 𝒲^{obs}`,  `K♭_{full} = ∏_{B ⊆ X} e^{Δ(B)} (K + K^{obs})(X)`

(the observables are not affected by the absorption of the field strength in raw fields), and the
outputs are the observable parts of the full second-order map (`Obs2.Map.Map`):
`V^{obs}_{j+1} = π_obs V_{j+1}`, `𝒲^{obs}_{j+1} = π_obs 𝒲_{j+1}`,
`K^{obs}_{j+1} = π_obs K_{j+1}` on connected polymers, `u ↦ u + u^{obs}_{j+1}(Λ)`.

## Results
* `full_bulk_K`, `full_bulk_V`, `full_bulk_D`: **the bulk part of the extended step is `rawStep`'s**
  (for observable states);
* `obsHist`: the recursion along the history; `obsHist_causal`: it only depends on `t_0, …, t_{j-1}`;
  `obsHist_isObs`: the states are observable.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Loc Step Step2 FRD

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

/-- The observable state at scale `j`. -/
structure ObsSt (c : Obs.Case) (L N : ℕ) [NeZero L] where
  /-- `V^{obs}_j(B)`. -/
  V : OFam c 2 L N
  /-- `𝒲^{obs}_j(B)`. -/
  W : OFam c 2 L N
  /-- `K^{obs}_j(X)`. -/
  K : OAct c 2 L N
  /-- The accumulated observable constant. -/
  u : OE c (Lam 2 L N)

/-- The observable state has vanishing bulk components. -/
structure ObsSt.IsObs (o : ObsSt c L N) : Prop where
  V : ∀ b, bulk (o.V b) = 0
  W : ∀ b, bulk (o.W b) = 0
  K : ∀ X, bulk (o.K X) = 0
  u : bulk o.u = 0

section Step

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
  (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt c L N)

/-- The full `V♭ + V^{obs}`. -/
def fullV : OFam c 2 L N := embF (stVf R j st g μ) + o.V

/-- The full `𝒲 + 𝒲^{obs}`, `𝒲 = W^{lin} + D`. -/
def fullW : OFam c 2 L N := embF (st.Wl + D) + o.W

/-- The full `K♭ + K^{obs,♭}`. -/
def fullK : OAct c 2 L N := KflatO j (stDelta R j st) (embF K + o.K)

/-- **One step of the observable flow.** -/
def obsStep : ObsSt c L N :=
  let C := stCov R j st
  let V := fullV R j st g μ o
  let W := fullW st D o
  let Kf := fullK R j st K o
  { V := fun c' => πobs (Vnext2O P j C V W Kf c')
    W := fun c' => πobs (Wnext2O P j C V W c')
    K := fun X => πobs (KconnO (j + 1) (KplusO P j C V W Kf) X)
    u := o.u + uObsTot P j C V W Kf }

theorem obsStep_isObs (ho : o.IsObs) : (obsStep R P j st g μ D K o).IsObs where
  V _ := bulk_πobs _
  W _ := bulk_πobs _
  K _ := bulk_πobs _
  u := by
    show bulk (o.u + uObsTot _ _ _ _ _ _) = 0
    rw [map_add, ho.u, uObsTot, map_sum]
    simp [bulk_upO]

variable {o}

theorem bulkF_fullV (ho : o.IsObs) : bulkF (fullV R j st g μ o) = stVf R j st g μ := by
  funext b; simp [fullV, embF, ho.V b]

theorem bulkF_fullW (ho : o.IsObs) : bulkF (fullW st D o) = st.Wl + D := by
  funext b; simp [fullW, embF, ho.W b]

theorem bulkF_fullK (ho : o.IsObs) : bulkF (fullK R j st K o) = Kflat j (stDelta R j st) K := by
  funext X
  rw [bulkF_apply, fullK, bulk_KflatO]
  congr 1
  funext Y; simp [embF, ho.K Y]

/-- **The bulk part of the extended step is `rawStep`'s: the activity.** -/
theorem full_bulk_K (ho : o.IsObs) (X : Finset (Lam 2 L N)) :
    bulk (KconnO (j + 1) (KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
      (fullK R j st K o)) X) = (rawStep R j st g μ D K).K X := by
  rw [bulk_KconnO, rawStep_K]
  unfold Kconn
  split_ifs
  · rw [bulkF_apply, bulk_KplusO, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho,
      bulkF_fullK R j st K ho]
  · rfl

/-- **The bulk part of the extended step is `rawStep`'s: the coupling polynomial** (whose
coefficients at the block `0` are the next couplings of `rawStep`). -/
theorem full_bulk_V (ho : o.IsObs) (c' : Fin 2 → ℕ) :
    bulk (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) c') =
      Vnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) c' := by
  rw [bulk_Vnext2O, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho, bulkF_fullK R j st K ho]

/-- **The bulk part of the extended step is `rawStep`'s: the remainder** `D_{j+1} =
𝒲_{j+1} - W^{lin}_{j+1}`. -/
theorem full_bulk_D (ho : o.IsObs) (c' : Fin 2 → ℕ) :
    (rawStep R j st g μ D K).D c' =
      bulk (Wnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c') -
        WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl c' := by
  rw [bulk_Wnext2O, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho, rawStep_D]
  rfl

end Step

/-! ### The recursion along the history -/

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- **The observable state along the history** (causal: uses `t_0, …, t_{j-1}`), from the initial
observable state `o₀` (e.g. `V^{obs}_0 = evalO` of the bare couplings, `𝒲 = K = u = 0`). -/
def obsHist : ℕ → Flow2.Hist.Seq (Xs R) → ObsSt c L N
  | 0, _ => o₀
  | j + 1, t => obsStep R P j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2) (obsHist j t)

theorem obsHist_succ (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) :
    obsHist R P o₀ (j + 1) t = obsStep R P j (rawHist R j t) (t j).1 (t j).2.1
      (rawD R (rawHist R j t).u (t j).2.2) (rawK R (rawHist R j t).u (t j).2.2)
      (obsHist R P o₀ j t) := rfl

theorem obsHist_isObs (h₀ : o₀.IsObs) : ∀ (j : ℕ) (t : Flow2.Hist.Seq (Xs R)),
    (obsHist R P o₀ j t).IsObs
  | 0, _ => h₀
  | j + 1, t => obsStep_isObs R P j _ _ _ _ _ _ (obsHist_isObs h₀ j t)

end Hist

end

end Obs2
