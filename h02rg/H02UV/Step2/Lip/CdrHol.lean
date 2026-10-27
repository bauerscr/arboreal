import Step2.Map.DCov
import Step2.Lip.LipW

/-!
# The dressed covariances as a holomorphic family

For the decomposition of `FRD`, `ζ ↦ C'_{j+1}(ζ) = Z_{j+1} Γ^int_{j+1}` (`Cdr`) with
`ζ = (ζ_0, …, ζ_j)` is a holomorphic family on the polydisc `|ζ_i| < ζ̄` (`dressed_family`).
On the closed polydisc it satisfies `GoodCov2` with the field scale at `|ζ| = ζ̄`, and it is
translation invariant. These are the hypotheses of the covariance-Lipschitz bounds
(`Kplus_lip_cov`, `RemW_lip_cov`, `TrL_lip_cov`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

theorem TInv_kmat (w : DressedFRD.Sym d (L ^ N)) :
    TInv (d := d) (L := L) (N := N) (DressedFRD.kmat w) := fun t x y => by
  simp only [DressedFRD.kmat, add_sub_add_right_eq_sub]

/-- **The dressed covariances form a holomorphic family satisfying `GoodCov2`.** -/
theorem dressed_family (P : PtFamily) (hd : 2 ≤ d) (hL7 : 7 ≤ L) :
    ∃ cS : ℝ, 0 ≤ cS ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (msq : ℝ), 1 ≤ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ j, j + 1 < N →
      let D₀ : DressedFRD.Data d (L ^ N) := ⟨L, N, msq, DressedFRD.frdC P msq L N, 0⟩
      (∀ x y, DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => Cdr (D₀.Dz z) j x y)
        {z | ∀ i, ‖z i‖ < ζbar}) ∧
      ∀ z : Fin (j + 1) → ℂ, (∀ i, ‖z i‖ ≤ ζbar) →
        GoodCov2 (d := d) (L := L) (N := N) j (ellDr d L cS K ζbar j) (Cdr (D₀.Dz z) j) ∧
        TInv (Cdr (D₀.Dz z) j) ∧ CSym (d := d) (L := L) (N := N) (Cdr (D₀.Dz z) j) ∧
        ∀ x y, Cdr (D₀.Dz z) j x y = Cdr (D₀.Dz z) j y x := by
  have hq : 2 ≤ 2 * pPhi d := by simp only [pPhi]; omega
  obtain ⟨cS, hcS, hS⟩ := DressedFRD.frd_stdFull P (d := d) hd hL7 (q := 2 * pPhi d)
    (M := 2 * pPhi d + d + 1) le_rfl
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := DressedFRD.thm_main_hol (d := d) hd hq hL7
    (M := 2 * pPhi d + d + 1) le_rfl hcS
  -- `K ≥ 0` is not part of `thm_main_hol`; use `max K 0`
  refine ⟨cS, hcS, ζbar, hζ, hζ8, max K 0, le_max_right _ _, ?_⟩
  intro N msq hN hmsq hmsq' j hj D₀
  have hS' := hS (L ^ N) N msq hN rfl hmsq
  have h := hK (L ^ N) D₀ rfl rfl hS' hmsq'
  have hC : ∀ k π s m, D₀.C k (symmDual π s m) = D₀.C k m := fun k π s m =>
    frdC_symm P _ _ _ _ π s m
  refine ⟨fun x y => ?_, fun z hz => ?_⟩
  · -- holomorphy
    have hG := fun m => (h.2 j (by simp only [D₀]; omega) m).1
    have hZ : DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => (D₀.Dz z).Z (j + 1))
        {z | ∀ i, ‖z i‖ < ζbar} := fun z₀ _ =>
      (DressedFRD.Data.Hol.Z_mem (D := D₀) (z₀ := z₀) (j + 1)).differentiableWithinAt
    simp only [Cdr, DressedFRD.kmat, DressedFRD.kern]
    refine (differentiableOn_const _).mul (DifferentiableOn.fun_sum fun m _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (hZ.mul (hG m)).mul (differentiableOn_const _)
  · -- `GoodCov2`, invariance, symmetry
    have hzi : ∀ i, ‖(D₀.Dz z).ζ i‖ ≤ ζbar := fun i => by
      show ‖DressedFRD.Data.ext z i‖ ≤ ζbar
      unfold DressedFRD.Data.ext
      split_ifs
      · exact hz _
      · simp [hζ.le]
    have hc := (hK (L ^ N) (D₀.Dz z) rfl rfl hS' hmsq').1 hzi j (show j < N by omega)
    have hC' : ∀ k π s m, (D₀.Dz z).C k (symmDual π s m) = (D₀.Dz z).C k m := hC
    have hMz : (D₀.Dz z).Mz (j + 1) ≤ ζbar :=
      DressedFRD.Data.Mz_le hζ.le fun i _ => hzi i
    have hg := goodCov2_dressed (d := d) (L := L) (N := N) (D₀.Dz z) rfl rfl hS' (by omega)
      (fun i => (hzi i).trans (by linarith)) hc hj le_rfl
    refine ⟨?_, TInv_kmat _, Cdr_CSym hC' j, Cdr_symm hC' j⟩
    refine hg.mono ?_
    unfold ellDr
    gcongr ?_ * _ * _
    refine Real.sqrt_le_sqrt ?_
    have hM0 : 0 ≤ (D₀.Dz z).Mz (j + 1) := DressedFRD.Data.Mz_nonneg _
    have h1 : K * (D₀.Dz z).Mz (j + 1) ≤ max K 0 * (D₀.Dz z).Mz (j + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left K 0) hM0
    have h2 : max K 0 * (D₀.Dz z).Mz (j + 1) ≤ max K 0 * ζbar :=
      mul_le_mul_of_nonneg_left hMz (le_max_right K 0)
    linarith

end

end Step2
