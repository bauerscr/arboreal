import PtCorr2.Obs.ObsSym
import PtCorr2.Obs.ObsHistFrom
import PtCorr2.Pair.PairSectHist

/-!
# `U(1)` invariance along the history from scale `j` and of the reduced state

* **`obsSymInv_histFrom`**: `ObsSymInv` along `obsHistFrom j o'` (copy of `obsSymInv_hist`);
* `isSymS_πab`, `πab_mem_sym`: the projection to the `σ_aσ_b` sector is `U(1)` equivariant;
* **`obsSymInv_redSt`**: the reduced state `redSt` at coalescence is `U(1)` invariant (its activity
  `kRed = π_{ab} zLoc` is a sum of products of the `U(1)`-invariant block factors and activities).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

local notation "SY" => (symSub : Subalgebra ℂ (OE c (Lam 2 L N)))

section From

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The `U(1)` invariant along the history from scale `j`.** -/
theorem obsSymInv_histFrom {j : ℕ} {o' : ObsSt c L N} (h0 : ObsSymInv j o')
    (t : Hist.Seq (Xs R)) :
    ∀ d, (∀ i, j ≤ i → i < j + d → ValidCore R i ∧ RawInv R i (rawHist R i t)) →
      ObsSymInv (j + d) (obsHistFrom R P j o' (j + d) t)
  | 0, _ => by rw [Nat.add_zero, obsHistFrom_self]; exact h0
  | d + 1, h => by
    rw [← Nat.add_assoc, obsHistFrom_succ (by omega)]
    exact obsSymInv_step R P _ _ (h (j + d) (by omega) (by omega)).1
      (h (j + d) (by omega) (by omega)).2 (rawD_mem R _ _) (rawK_mem R _ _)
      (obsSymInv_histFrom h0 t d fun i hi1 hi2 => h i hi1 (by omega))

/-- `obsSymInv_histFrom` at an absolute scale `k ≥ j`. -/
theorem obsSymInv_histFrom' {j : ℕ} {o' : ObsSt c L N} (h0 : ObsSymInv j o')
    (t : Hist.Seq (Xs R)) {k : ℕ} (hjk : j ≤ k)
    (h : ∀ i, j ≤ i → i < k → ValidCore R i ∧ RawInv R i (rawHist R i t)) :
    ObsSymInv k (obsHistFrom R P j o' k t) := by
  have := obsSymInv_histFrom R P h0 t (k - j) (fun i hi1 hi2 => h i hi1 (by omega))
  rwa [Nat.add_sub_cancel' hjk] at this

end From

section Red

theorem isSymS_πab {Λ : Type*} [DecidableEq Λ] [Fintype Λ] {F : OE c Λ}
    (hF : IsSymS (F : SA c Λ)) : IsSymS (πab F : SA c Λ) := by
  unfold IsSymS at hF ⊢
  have hab := congrArg SA.ab hF
  simp only [scalS_ab] at hab
  rw [coe_πab, piab_apply]
  refine SA.ext ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp only [scalS_ab]; exact hab

theorem πab_mem_sym {F : OE c (Lam 2 L N)} (hF : F ∈ SY) : πab F ∈ SY :=
  mem_symSub.2 (isSymS_πab (mem_symSub.1 hF))

variable {R : RGPar 2 L N} {P : ObsPts 2 L N} {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ}
  {Dw : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N} {D : Finset (Lam 2 L N)}

/-- **The reduced state is `U(1)` invariant.** -/
theorem obsSymInv_redSt (hV : ValidCore R j) (H : RawInv R j st)
    (hDw : Dw ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (ho : ObsSymInv j o) : ObsSymInv j (redSt R P j st g μ Dw K o D) := by
  obtain ⟨hj2, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem H.hWl hDw).1
  have hI : ∀ b, inI R j st g μ Dw o b ∈ SY := fun b =>
    mul_mem (Obs2.oexp_mem (neg_mem (add_mem (emb_mem_sym (add_mem
      ((isSym_iff_mem_SymS _).1 (hVm.1.sym b)) ((isSym_iff_mem_SymS _).1 (hΔm.1.sym b))))
      (ho.V b))))
      (add_mem (one_mem _) (add_mem (emb_mem_sym ((isSym_iff_mem_SymS _).1 (hW.sym b)))
        (ho.W b)))
  have hKs : ∀ Y, IsConn j Y → inK K o Y ∈ SY := fun Y hY =>
    add_mem (emb_mem_sym ((isSym_iff_mem_SymS _).1 (hK.1.sym Y hY))) (ho.K Y hY)
  refine ⟨fun _ => zero_mem _, fun _ => zero_mem _, fun Y _ => ?_⟩
  show kRed j D P.a (inI R j st g μ Dw o) (inK K o) Y ∈ _
  by_cases hDY : D ⊆ Y
  · rw [kRed_of_sub _ _ hDY]
    refine πab_mem_sym (sum_mem fun A hA => mul_mem (prod_mem fun b _ => hI b)
      (prod_mem fun Z hZ => hKs Z (isConn_of_mem_comp (mem_sY.1 hA).1.2 hZ)))
  · rw [kRed_of_not _ _ hDY]; exact zero_mem _

end Red

end

end PtCorr2
