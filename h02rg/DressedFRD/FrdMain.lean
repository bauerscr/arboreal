import DressedFRD.Instance
import DressedFRD.Holo

/-!
# `thm:main` for the decomposition of `FRD`, in every `d ≥ 2`

`thm_main_frd`: for any `P : PtFamily` (for instance `FRD.PtF.prePt.toPtFamily`), the dressed
decomposition built from the pieces `frdC P m² L N` of `FRD.Decomp` satisfies the conclusions of
`thm:main`(i), (iii)–(vi) for all `N ≥ 1`, `0 < m² ≤ L^{-2(N-1)}`, `n = L^N` and
`|ζ_i| ≤ ζ̄`, and is holomorphic in `ζ` (`thm:main`(ii)). `frd_Gint_real` is the reality.
-/

namespace DressedFRD

noncomputable section

open Finset FRD Data ComplexConjugate

variable (P : PtFamily)

/-- `thm:main` for the decomposition of `FRD`. -/
theorem thm_main_frd {d q L : ℕ} (hd : 2 ≤ d) (hq : 2 ≤ q) (hL : 7 ≤ L) :
    ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧ ∃ K : ℝ, ∀ (n : ℕ) [NeZero n] (N : ℕ) (msq : ℝ)
      (ζ : ℕ → ℂ), 1 ≤ N → n = L ^ N → 0 < msq → msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      let D : Data d n := ⟨L, N, msq, frdC P msq L N, ζ⟩
      ((∀ i, ‖ζ i‖ ≤ ζbar) → ∀ j, j < N → D.Concl q ζbar K j) ∧
      ∀ j, j < N → ∀ m,
        DifferentiableOn ℂ (fun z : Fin (j + 1) → ℂ => (D.Dz z).Gint j m)
          {z | ∀ i, ‖z i‖ < ζbar} := by
  obtain ⟨cS, hcS, hS⟩ := frd_stdFull P (d := d) hd hL (q := q) (M := q + d + 1) le_rfl
  obtain ⟨ζbar, hζ, hζ8, K, hK⟩ := thm_main_hol (d := d) hd hq hL (M := q + d + 1) le_rfl hcS
  refine ⟨ζbar, hζ, hζ8, K, fun n _ N msq ζ hN hn hmsq hmsq' => ?_⟩
  have h := hK n ⟨L, N, msq, frdC P msq L N, ζ⟩ rfl hn (hS n N msq hN hn hmsq) hmsq'
  exact ⟨h.1, fun j hj m => (h.2 j hj m).1⟩

/-- `thm:main`(ii), reality, for the decomposition of `FRD`. -/
theorem frd_Gint_real {d n : ℕ} [NeZero n] {L N : ℕ} {msq : ℝ} {ζ : ℕ → ℂ} {j : ℕ}
    (hζ : ∀ i ≤ j, conj (ζ i) = ζ i) :
    (⟨L, N, msq, frdC P msq L N, ζ⟩ : Data d n).Gint j ∈ realSub :=
  Gint_mem (fun k m => frdC_even P k m) hζ

end

end DressedFRD
