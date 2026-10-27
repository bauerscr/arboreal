import PtCorr2.Obs.ObsLoc
import Obs2.Map.SymO

/-!
# `U(1)` invariance along the observable flow (`sec:obs-flow`)

The invariant `ObsSymInv j o` (`V^{obs}(B)`, `𝒲^{obs}(B)`, `K^{obs}(Y)` for connected `Y` are
`U(1)` invariant, `IsSymS`) holds for the initial state `obsInit c V P` (`obsSymInv_init`) and is
preserved by `obsStep` (`obsSymInv_step`, from `Obs2.OSymS.step` and the `U(1)` invariance of the
bulk inputs). Hence

* **`obsSymInv_hist`**: the invariant along `obsHist` at all steps with `ValidCore` and `RawInv`;
* **`osymS_hist`**: the full inputs (bulk plus observable) of every step along the history are
  `U(1)` invariant (`OSymS`); in particular `IsSymS (K_j(X))` for connected `X`, the hypothesis of
  `Obs2.step2O_ts` / `Obs2.stepKO_ts`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

local notation "SY" => (symSub : Subalgebra ℂ (OE c (Lam 2 L N)))

/-- **The `U(1)` invariant of an observable state at scale `j`.** -/
structure ObsSymInv (j : ℕ) (o : ObsSt c L N) : Prop where
  V : ∀ b, o.V b ∈ SY
  W : ∀ b, o.W b ∈ SY
  K : ∀ Y, IsConn j Y → o.K Y ∈ SY

theorem scal_m4' (a b : Lam 2 L N) : Step.scal _ 2 (Obs2.m4 a b) = Obs2.m4 a b := by
  rw [Obs2.m4, map_mul, Obs.scal_psibar_psi 2 two_ne_zero, Obs.scal_psibar_psi 2 two_ne_zero]

theorem evalO2_mem_sym (c : Obs.Case) (V : OCoup c) (a b : Lam 2 L N) (X : Finset (Lam 2 L N)) :
    Obs2.evalO c V a b X ∈ (symSub : Subalgebra ℂ (OE c (Lam 2 L N))) := by
  refine mem_symSub.2 ?_
  show IsSymS (Obs2.evalS c V a b X)
  cases c
  · rw [isSymS_iff_one]
    refine ⟨by simp [Obs2.evalS, OCoup1.evalS], ?_, ?_, ?_⟩ <;>
      simp only [Obs2.evalS, OCoup1.evalS, map_smul, map_add, map_neg, AlgHom.commutes, scal_nn,
        scal_m4']
    · rw [psibar, Step.scal_ψ, if_neg Loc.units_ne.symm, smul_comm (2⁻¹ : ℂ),
        smul_comm (2⁻¹ : ℂ)]
    · rw [psi, Step.scal_ψ, if_pos rfl, smul_comm (2 : ℂ), smul_comm (2 : ℂ)]
  · rw [isSymS_iff_two]
    refine ⟨by simp [Obs2.evalS, OCoup2.evalS], ?_, ?_, ?_⟩ <;>
      simp only [Obs2.evalS, OCoup2.evalS, map_smul, map_add, map_sub, AlgHom.commutes, scal_nn,
        scal_nx, scal_m4', Obs.scal_psibar_psi 2 two_ne_zero]

/-- **The initial state is `U(1)` invariant** (any couplings). -/
theorem obsSymInv_init (c : Obs.Case) (V : OCoup c) (P : ObsPts 2 L N) :
    ObsSymInv 0 (obsInit c V P) where
  V b := evalO2_mem_sym c V P.a P.b _
  W _ := zero_mem _
  K _ _ := zero_mem _

section Step

variable (R : RGPar 2 L N) (P : ObsPts 2 L N) {j : ℕ} {st : RawSt 2 L N} (g μ : ℝ)
  {D : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N}

/-- The full inputs (bulk plus observable) of a step are `U(1)` invariant. -/
theorem osymS_full (hV : ValidCore R j) (H : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j)
    (hK : K ∈ ASub (L := L) (N := N) j) (ho : ObsSymInv j o) :
    OSymS j (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem H.hWl hD).1
  refine ⟨fun b => add_mem (emb_mem_sym ((isSym_iff_mem_SymS _).1 (hVm.1.sym b))) (ho.V b),
    fun b => add_mem (emb_mem_sym ((isSym_iff_mem_SymS _).1 (hW.sym b))) (ho.W b),
    fun Y hY => ?_⟩
  have hbp : ((bpow j (fun b => gexp (stDelta R j st b)) Y : EvR (Lam 2 L N)) : Alg 2 L N) ∈
      SymS (Lam 2 L N) :=
    coe_prod_mem _ (blocks j Y) _ fun b _ =>
      mem_SE.1 (gexp_mem_SE (S := SymS (Lam 2 L N))
        (mem_SE.2 ((isSym_iff_mem_SymS _).1 (hΔm.1.sym b))))
  exact mul_mem (emb_mem_sym hbp)
    (add_mem (emb_mem_sym ((isSym_iff_mem_SymS _).1 (hK.1.sym Y hY))) (ho.K Y hY))

/-- **The `U(1)` invariant is preserved by one step of the observable flow.** -/
theorem obsSymInv_step (hV : ValidCore R j) (H : RawInv R j st)
    (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (ho : ObsSymInv j o) : ObsSymInv (j + 1) (obsStep R P j st g μ D K o) := by
  have hS := (osymS_full R g μ hV H hD hK ho).step (P := P) (C := stCov R j st)
  exact ⟨fun c' => πobs_mem_sym (hS.hV c'), fun c' => πobs_mem_sym (hS.hW c'),
    fun Y hY => πobs_mem_sym (hS.hK Y hY)⟩

end Step

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
  (o₀ : ObsSt c L N)

/-- **The `U(1)` invariant along the history.** -/
theorem obsSymInv_hist (h0 : ObsSymInv 0 o₀) (t : Hist.Seq (Xs R)) :
    ∀ n, (∀ j < n, ValidCore R j ∧ RawInv R j (rawHist R j t)) →
      ObsSymInv n (obsHist R P o₀ n t)
  | 0, _ => h0
  | n + 1, h => by
    rw [obsHist_succ]
    exact obsSymInv_step R P _ _ (h n (by omega)).1 (h n (by omega)).2 (rawD_mem R _ _)
      (rawK_mem R _ _) (obsSymInv_hist h0 t n fun j hj => h j (by omega))

/-- **The full inputs of every step along the history are `U(1)` invariant.** -/
theorem osymS_hist (h0 : ObsSymInv 0 o₀) (t : Hist.Seq (Xs R)) {n : ℕ}
    (h : ∀ j ≤ n, ValidCore R j ∧ RawInv R j (rawHist R j t)) :
    OSymS n (fullV R n (rawHist R n t) (t n).1 (t n).2.1 (obsHist R P o₀ n t))
      (fullW (rawHist R n t) (rawD R (rawHist R n t).u (t n).2.2) (obsHist R P o₀ n t))
      (fullK R n (rawHist R n t) (rawK R (rawHist R n t).u (t n).2.2) (obsHist R P o₀ n t)) :=
  osymS_full R _ _ (h n le_rfl).1 (h n le_rfl).2 (rawD_mem R _ _) (rawK_mem R _ _)
    (obsSymInv_hist R P o₀ h0 t n fun j hj => h j hj.le)

end Hist

end

end PtCorr2
