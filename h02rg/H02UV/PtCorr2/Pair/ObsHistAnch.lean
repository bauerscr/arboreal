import PtCorr2.Pair.PairSectHist
import Obs2.Pair.AnchAB

/-!
# Anchoring along the reduced pair history

`ObsAnchInv P j o`: the observable parts of `V(B)`, `𝒲(B)`, `K(Y)` have no one-point parts and
their `σ_aσ_b` parts vanish unless `B` (resp. `Y`) meets `{a, b}` (`Obs2.anc`).

* `obsAnchInv_step`: preserved by one step of the observable flow (`Obs2.OAnchS.step`);
* **`obsAnchInv_histFrom`**: along `obsHistFrom` from an anchored state;
* **`obsAnchInv_redSt`**: the reduced state `redSt` at coalescence is anchored (its activity
  `kRed` lives on `Y ⊇ D ∋ a`, `DCov.a_mem`).

Consequence: on the reduced history, every `ab` part that `Loc` sees sits on a small set meeting
`{a, b}`, where the barycentric `loc^{ab}` is based at a point of `X` and contracts
(`exists_locABt_contract`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}


/-- **Anchored observable state.** -/
structure ObsAnchInv (P : ObsPts 2 L N) (j : ℕ) (o : ObsSt c L N) : Prop where
  V : ∀ b, o.V b ∈ (Obs2.anc P (blockSet (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam 2 L N)))
  W : ∀ b, o.W b ∈ (Obs2.anc P (blockSet (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam 2 L N)))
  K : ∀ Y, IsConn j Y → o.K Y ∈ (Obs2.anc P Y : Subalgebra ℂ (OE c (Lam 2 L N)))

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N} (g μ : ℝ)
  {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N}

/-- The full inputs of a step are anchored. -/
theorem oanchS_full (ho : ObsAnchInv P j o) :
    OAnchS P j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) :=
  ⟨fun b => add_mem (emb_mem_anch _) (ho.V b), fun b => add_mem (emb_mem_anch _) (ho.W b),
    fun Y hY => mul_mem (emb_mem_anch _) (add_mem (emb_mem_anch _) (ho.K Y hY))⟩

/-- **Anchoring is preserved by one step of the observable flow.** -/
theorem obsAnchInv_step (ho : ObsAnchInv P j o) :
    ObsAnchInv P (j + 1) (obsStep R P j st g μ D K o) := by
  have H := oanchS_full R P g μ (st := st) (D := D) (K := K) ho
  have hS := H.step (C := stCov R j st)
  exact ⟨fun c' => πobs_mem_anch (hS.hV c'), fun c' => πobs_mem_anch (hS.hW c'),
    fun Y hY => πobs_mem_anch (hS.hK Y hY)⟩

variable [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **Anchoring along the history from scale `j`.** -/
theorem obsAnchInv_histFrom {o' : ObsSt c L N} (h0 : ObsAnchInv P j o') (t : Hist.Seq (Xs R)) :
    ∀ d, ObsAnchInv P (j + d) (obsHistFrom R P j o' (j + d) t)
  | 0 => by rw [Nat.add_zero, obsHistFrom_self]; exact h0
  | d + 1 => by
    rw [← Nat.add_assoc, obsHistFrom_succ (by omega)]
    exact obsAnchInv_step R P _ _ (obsAnchInv_histFrom h0 t d)

omit [Fact (0 < R.ℓ)] [Fact (0 < R.A)] in
/-- **The reduced state at coalescence is anchored.** -/
theorem obsAnchInv_redSt {Dw : Fam 2 L N} {Dx : Finset (Lam 2 L N)} (hD : DCov P j Dx) :
    ObsAnchInv P j (redSt R P j st g μ Dw K o Dx) where
  V _ := zero_mem _
  W _ := zero_mem _
  K Y _ := by
    classical
    by_cases hY : Dx ⊆ Y
    · refine anchSub_of_ab ⟨P.a, mem_inter.2 ⟨hY hD.a_mem, ?_⟩⟩ (kRed_mem_ab _ _ Y)
      simp [ObsPts.pts]
    · show kRed j Dx P.a _ _ Y ∈ _
      rw [kRed_of_not _ _ hY]; exact zero_mem _

end

end PtCorr2
