import PtCorr2.Last.TopCoal1
import PtCorr2.Last.LastObsK6

/-!
# Top coalescence: locality of the reduced state at scale `N - 1`

`obsLocInv_redSt` needs `ValidCore` at the scale of the reduction (through `olocS_in`). At the
scale `N_h + 1 = N - 1` of the last step only `ValidLast` is available; the locality of the full
inputs `V♭ + Δ + V^{obs}`, `𝒲 + 𝒲^{obs}`, `K + K^{obs}` follows from it in the same way
(`olocS_in_last`, copy of `olocS_in`), hence **`obsLocInv_redSt_last`** and
**`obsLocInv_redTop`**.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2 Flow2.Hist

variable {L N : ℕ} [NeZero L] {c : Obs.Case}

section Red

variable {R : RGPar 2 L N} {P : ObsPts 2 L N} {j : ℕ} {st : RawSt 2 L N} {g μ : ℝ}
  {Dw : Fam 2 L N} {K : Act 2 L N} {o : ObsSt c L N} {D : Finset (Lam 2 L N)}

/-- The full inputs of `Z_j` are local (`ValidLast` form of `olocS_in`). -/
theorem olocS_in_last (hV : LastN.ValidLast R j) (H : RawInv R j st)
    (hDw : Dw ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (ho : ObsLocInv P j o) :
    OLocS P j (inV R j st g μ o) (fullW st Dw o) (inK K o) := by
  obtain ⟨hj1, hd, hL, -, -, -, -⟩ := hV
  have hjN : j < N := by omega
  have hVm := VfamL_mem (L := L) (N := N) hd hL hjN ![st.z + stYc R st - stA R st,
    st.y - stYc R st, stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]
  have hΔm := VfamL_mem (L := L) (N := N) hd hL hjN
    ![stA R st - stYc R st, stYc R st, stA R st * R.msq, 0]
  have hW := (add_mem H.hWl hDw).1
  refine ⟨fun b => add_mem (emb_mem_osub ?_) (ho.V b),
    fun b => add_mem (emb_mem_osub (hW.loc b)) (ho.W b),
    fun Y hY => add_mem (emb_mem_osub (hK.1.loc Y hY)) (ho.K Y hY)⟩
  exact add_mem (hVm.1.loc b) (hΔm.1.loc b)

/-- **The reduced state is local** (`ValidLast` form of `obsLocInv_redSt`). -/
theorem obsLocInv_redSt_last (hV : LastN.ValidLast R j) (H : RawInv R j st)
    (hDw : Dw ∈ BSub (L := L) (N := N) j) (hK : K ∈ ASub (L := L) (N := N) j)
    (ho : ObsLocInv P j o) : ObsLocInv P j (redSt R P j st g μ Dw K o D) := by
  have HL := olocS_in_last (g := g) (μ := μ) hV H hDw hK ho
  refine ⟨fun _ => zero_mem _, fun _ => zero_mem _, fun Y hY => ?_⟩
  show kRed j D P.a (inI R j st g μ Dw o) (inK K o) Y ∈ _
  by_cases hDY : D ⊆ Y
  · rw [kRed_of_sub _ _ hDY]
    refine πab_mem_osub (sum_mem fun A hA => mul_mem (prod_mem fun b hb => ?_)
      (prod_mem fun Z hZ => ?_))
    · have hAY := (mem_sY.1 hA).1
      have hbY : blockSet (L := L) (N := N) j b ⊆ Y :=
        blockSet_subset hY.1 (image_subset_image sdiff_subset hb)
      exact osub_mono (nbhd_mono hbY) (mul_mem (Obs2.oexp_mem (neg_mem (HL.hV b)))
        (add_mem (one_mem _) (HL.hW b)))
    · have hAY := (mem_sY.1 hA).1
      exact osub_mono (nbhd_mono ((subset_of_mem_comp hZ).trans hAY.1))
        (HL.hK Z (isConn_of_mem_comp hAY.2 hZ))
  · rw [kRed_of_not _ _ hDY]; exact zero_mem _

end Red

section Hist

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)

/-- **The reduced state at scale `N_h + 1` is local.** -/
theorem obsLocInv_redTop {Nh : ℕ} (hV : ∀ j < Nh, ValidAt R j) (hVL : ValidAtL R Nh)
    (hVN : LastN.ValidLast R (Nh + 1)) (o₀ : ObsSt c L N) (h0 : ObsLocInv P 0 o₀)
    (t : Hist.Seq (Xs R)) (D : Finset (Lam 2 L N)) :
    ObsLocInv P (Nh + 1) (redTop R P o₀ D Nh t) := by
  have hρ0 : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hcore : ∀ i ≤ Nh, ValidCore R i := fun i hi => by
    rcases Nat.lt_or_ge i Nh with h | h
    · exact (hV i h).toValidCore
    · rw [show i = Nh by omega]; exact hVL.2
  have hRI := rawInv_histU R hV hVL t
  have hl : ObsLocInv P (Nh + 1) (obsHist R P o₀ (Nh + 1) t) :=
    obsLocInv_hist R P o₀ h0 t (Nh + 1) fun i hi => ⟨hcore i (by omega), hRI i (by omega)⟩
  have hD : (histOut R Nh t).D ∈ BSub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).2.1
  have hKm : (histOut R Nh t).K ∈ ASub (L := L) (N := N) (Nh + 1) :=
    (RawInv.stepL hVL (rawInv_hist R hρ0 Nh hV t) (t Nh).1 (t Nh).2.1 (rawD_mem R _ _)
      (rawK_mem R _ _)).2.2
  exact obsLocInv_redSt_last hVN (hRI (Nh + 1) le_rfl) hD hKm hl

end Hist

end

end PtCorr2
