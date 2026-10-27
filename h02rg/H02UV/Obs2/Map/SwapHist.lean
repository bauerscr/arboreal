import Obs2.Map.SwapO
import Obs2.Flow.GamChain2

/-!
# The one-source projections along the observable flow; the `σ_b` part as a `σ_a` part

* `prjSt i`: `prjO i` applied to every component of an observable state.
* **`prj_obsStep`**: `prjSt i ∘ obsStep_P = obsStep_{P'} ∘ prjSt i` whenever `P'.a = P.pt i`
  (`Obs2/Map/SwapO.lean`: every map commutes; the bulk pieces `V♭`, `𝒲`, `K♭` are embedded and fixed).
* **`prj_obsHist`**: the same along the history.
* `prjSt_obsInit_swap`: for couplings with `γ_a = γ_b`, `μ_a = μ_b`, the `σ_b` projection of
  `obsInit V (a, b)` is the `σ_a` projection of `obsInit V (b, ·)`.
* **`neg_eps_u_b_eq_gamA`**: `-ε(u^{obs}_{k,b})` along the history with points `(a, b)` equals
  `γ_{a,k} = gamA` along the history with points `(b, ·)` (for symmetric couplings): the `σ_b` part
  of the `γ` flow is the `σ_a` part of the mirrored flow.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD

variable {L N : ℕ} [NeZero L]

/-- `prjO i` on an observable state. -/
def prjSt (i : Bool) (o : ObsSt .two L N) : ObsSt .two L N :=
  ⟨prjF i o.V, prjF i o.W, prjF i o.K, prjO i o.u⟩

theorem prjSt_u (i : Bool) (o : ObsSt .two L N) : (prjSt i o).u = prjO i o.u := rfl

section Step

variable (i : Bool) {P P' : ObsPts 2 L N} (hP : P'.a = P.pt i) (R : RGPar 2 L N) (j : ℕ)
  (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N) (o : ObsSt .two L N)

theorem prj_fullV : prjF i (fullV R j st g μ o) = fullV R j st g μ (prjSt i o) := by
  funext b
  simp only [prjF_apply, fullV, Pi.add_apply, map_add, embF, prjO_emb]
  rfl

theorem prj_fullW : prjF i (fullW st D o) = fullW st D (prjSt i o) := by
  funext b
  simp only [prjF_apply, fullW, Pi.add_apply, map_add, embF, prjO_emb]
  rfl

theorem prj_fullK : prjF i (fullK R j st K o) = fullK R j st K (prjSt i o) := by
  funext X
  rw [prjF_apply, fullK, fullK, prj_KflatO]
  congr 1
  funext Y
  simp only [prjF_apply, Pi.add_apply, map_add, embF, prjO_emb]
  rfl

include hP

/-- **`prjSt i ∘ obsStep_P = obsStep_{P'} ∘ prjSt i`.** -/
theorem prj_obsStep :
    prjSt i (obsStep R P j st g μ D K o) = obsStep R P' j st g μ D K (prjSt i o) := by
  have hV := prj_fullV i R j st g μ o
  have hW := prj_fullW i st D o
  have hK := prj_fullK i R j st K o
  unfold obsStep prjSt
  simp only [ObsSt.mk.injEq]
  refine ⟨funext fun c' => ?_, funext fun c' => ?_, funext fun X => ?_, ?_⟩
  · rw [prjF_apply, prjO_πobs, prj_Vnext2O i hP, hV, hW, hK]; rfl
  · rw [prjF_apply, prjO_πobs, prj_Wnext2O i hP, hV, hW]; rfl
  · rw [prjF_apply, prjO_πobs, prj_KconnO,
      show prjF i (KplusO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
          (fullK R j st K o)) = KplusO P' j (stCov R j st) (prjF i (fullV R j st g μ o))
            (prjF i (fullW st D o)) (prjF i (fullK R j st K o)) from
        funext fun U => prj_KplusO i hP j _ _ _ _ U, hV, hW, hK]
    rfl
  · rw [map_add, prj_uObsTot i hP, hV, hW, hK]
    rfl

end Step

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **`prjSt i` along the history.** -/
theorem prj_obsHist (i : Bool) {P P' : ObsPts 2 L N} (hP : P'.a = P.pt i) (o₀ : ObsSt .two L N)
    (t : Flow2.Hist.Seq (Xs R)) :
    ∀ k : ℕ, prjSt i (obsHist R P o₀ k t) = obsHist R P' (prjSt i o₀) k t
  | 0 => rfl
  | k + 1 => by
    rw [obsHist_succ, obsHist_succ, prj_obsStep i hP, prj_obsHist i hP o₀ t k]

/-- `γ_{a,k}` only depends on the `σ_a` projection of the initial state. -/
theorem gamA_prjSt (P : ObsPts 2 L N) (o₀ : ObsSt .two L N) (t : Flow2.Hist.Seq (Xs R))
    (k : ℕ) : gamA R P (prjSt true o₀) t k = gamA R P o₀ t k := by
  unfold gamA
  rw [← prj_obsHist R true (P := P) (P' := P) rfl o₀ t k, prjSt_u, coe_prjO, prjS_a]
  rfl

/-- **The `σ_b` part of the accumulated constant is the `σ_a` part of the mirrored flow.** -/
theorem neg_eps_u_b_eq_gamA {P P' : ObsPts 2 L N} (hP : P'.a = P.b) (o₀ o₀' : ObsSt .two L N)
    (h₀ : prjSt false o₀ = prjSt true o₀') (t : Flow2.Hist.Seq (Xs R)) (k : ℕ) :
    -ε ((obsHist R P o₀ k t).u : SA .two (Lam 2 L N)).b = gamA R P' o₀' t k := by
  rw [← gamA_prjSt R P' o₀' t k, ← h₀]
  unfold gamA
  rw [← prj_obsHist R false (P := P) (P' := P') hP o₀ t k, prjSt_u, coe_prjO, prjS_a]
  rfl

/-- For `γ_a = γ_b`, `μ_a = μ_b`: `prjSt false (obsInit V (a, b)) = prjSt true (obsInit V (b, c))`. -/
theorem prjSt_obsInit_swap (V : OCoup .two) (hg : OCoup2.ga V = OCoup2.gb V)
    (hm : OCoup2.mua V = OCoup2.mub V) {P P' : ObsPts 2 L N} (hP : P'.a = P.b) :
    prjSt false (obsInit .two V P) = prjSt true (obsInit .two V P') := by
  unfold prjSt obsInit
  simp only [ObsSt.mk.injEq]
  refine ⟨funext fun b => ?_, funext fun b => ?_, funext fun X => ?_, ?_⟩
  · refine Subtype.ext (SA.ext ?_ ?_ ?_ ?_)
    · rfl
    · show (evalS .two V P.a P.b _).b = (evalS .two V P'.a P'.b _).a
      rw [hP]
      show (OCoup2.evalS V P.a P.b _).b = (OCoup2.evalS V P.b P'.b _).a
      simp only [OCoup2.evalS, hg, hm]
    · rfl
    · rfl
  · simp
  · simp
  · simp

end Hist

end

end Obs2
