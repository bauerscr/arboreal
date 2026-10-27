import PtCorr2.Restart.RerepState
import PtCorr2.Obs.ObsSym

/-!
# `U(1)` invariance of the re-represented state (B3, T6 input)

`ψ̄_aψ_a` is `U(1)` invariant, so the relocation element `rrD = σ_aβ_B(ψ̄_aψ_a − ψ̄_{a'}ψ_{a'})` is,
and so are the corrections `−rrD(B)·I'(B)·(K♭+K)^{Y∖B}` when the bulk inputs are:

* `rrD_mem_sym`;
* **`rrSt_obsSymInv`** (bulk symmetry of `V♭ + Δ`, `𝒲`, `K` as hypotheses): `ObsSymInv j o ⟹
  ObsSymInv j (rrSt … o)`;
* **`rrSt_obsSymInv_core`** (`ValidCore R j`, `RawInv R j st`, `D ∈ BSub j`, `K ∈ ASub j`, as in
  `osymS_full`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

local notation "SY" => (symSub : Subalgebra ℂ (OE Obs.Case.two (Lam 2 L N)))

theorem rrD_mem_sym (a a' : Lam 2 L N) (β : (Fin 2 → ℕ) → ℂ) (b : Fin 2 → ℕ) :
    rrD a a' β b ∈ SY := by
  refine mem_symSub.2 ((isSymS_iff_two _).2 ⟨by simp, ?_, by simp, by simp⟩)
  rw [rrD_a, map_smul, map_sub, pbp, pbp, Obs.scal_psibar_psi 2 two_ne_zero,
    Obs.scal_psibar_psi 2 two_ne_zero]

variable {R : RGPar 2 L N} {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ} {D : Fam 2 L N} {K : Act 2 L N}
  {a a' : Lam 2 L N} {β : (Fin 2 → ℕ) → ℂ}

/-- **`U(1)` invariance of the re-represented state.** -/
theorem rrSt_obsSymInv {o : ObsSt .two L N} (H : ObsSymInv j o)
    (hVb : ∀ b, ((stVf R j st g μ b + stDelta R j st b : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈
      SymS (Lam 2 L N))
    (hWb : ∀ b, (((st.Wl + D) b : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈ SymS (Lam 2 L N))
    (hKb : ∀ Y, IsConn j Y → ((K Y : Step.EvR (Lam 2 L N)) : Alg 2 L N) ∈ SymS (Lam 2 L N)) :
    ObsSymInv j (rrSt R j st g μ D K a a' β o) := by
  have hV' : ∀ b, o.V b - rrD a a' β b ∈ SY := fun b => sub_mem (H.V b) (rrD_mem_sym a a' β b)
  refine ⟨hV', H.W, fun Y hY => ?_⟩
  refine add_mem (H.K Y hY) (Subalgebra.sum_mem _ fun b _ => ?_)
  refine mul_mem (mul_mem (neg_mem (rrD_mem_sym a a' β b)) ?_) ?_
  · exact mul_mem (Obs2.oexp_mem (neg_mem (add_mem (emb_mem_sym (hVb b)) (hV' b))))
      (add_mem (one_mem _) (add_mem (emb_mem_sym (hWb b)) (H.W b)))
  · refine prod_mem fun Z hZ => ?_
    have hYp : IsPolymer j (Y \ blockSet j b) := IsPolymer.sdiff hY.1 (isPolymer_blockSet j b)
    have hZc := isConn_of_mem_comp hYp hZ
    exact add_mem (emb_mem_sym (hKb Z hZc)) (H.K Z hZc)

/-- **`U(1)` invariance of the re-represented state from the raw-step invariants.** -/
theorem rrSt_obsSymInv_core {o : ObsSt .two L N} (H : ObsSymInv j o) (hV : ValidCore R j)
    (HR : RawInv R j st) (hD : D ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j) :
    ObsSymInv j (rrSt R j st g μ D K a a' β o) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem HR.hWl hD).1
  exact rrSt_obsSymInv H
    (fun b => add_mem ((isSym_iff_mem_SymS _).1 (hVm.1.sym b))
      ((isSym_iff_mem_SymS _).1 (hΔm.1.sym b)))
    (fun b => (isSym_iff_mem_SymS _).1 (hW.sym b))
    (fun Y hY => (isSym_iff_mem_SymS _).1 (hK.1.sym Y hY))

end

end PtCorr2
