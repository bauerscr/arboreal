import PtCorr2.Pair.ShareABHist2
import Obs2.Flow.GradAB1

/-!
# The `hVo` input with a per-block base point

`PtCorr2.hVo_of_coeffs` measures the gradient part of every `V'_j(B)_{ab}` from `a`. A block that
contains only `b` (or is based at `b` by the localisations of `loc^{ab}`) is better measured from `b`:
the coefficient bound `Obs2.tNorm_of_ab_le` holds with the two points exchanged (the mass `m₂` does
not depend on the base point). Here the base point may be chosen per scale and block.

* **`oTo_wM_le_massP`**: `oTo_wM_le_mass` with base `P.a` or `P.b`;
* **`hVo_of_coeffsP`**: the `hVo` input of `obs_histFromABL_wM` from per-block mass bounds `ρ_j`
  and gradient/`M₄` bounds `γ_j` with respect to either base point.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD Obs2 Flow2 Flow2.Hist LocObs

variable {L N : ℕ} [NeZero L]

/-- **The `wM` size with either base point** (`ε = 0`). -/
theorem oTo_wM_le_massP {c : Obs.Case} {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb) (j : ℕ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (X : Finset (Lam 2 L N)) {a b : Lam 2 L N} (hab : a ≠ b)
    {F : OE c (Lam 2 L N)} (hF : F ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))))
    (hN : (F : SA c (Lam 2 L N)).ab ∈ NX ({a, b} : Set (Lam 2 L N)))
    (hS : IsSym (F : SA c (Lam 2 L N)).ab) (hε : ε (F : SA c (Lam 2 L N)).ab = 0) {ρ γ : ℝ}
    (hρ : ‖mass2 (F : SA c (Lam 2 L N)).ab‖ ≤ ρ)
    (hγ : gradM4Sz X a b ((L : ℝ) ^ j) ℓ (F : SA c (Lam 2 L N)).ab ≤ γ ∨
      gradM4Sz X b a ((L : ℝ) ^ j) ℓ (F : SA c (Lam 2 L N)).ab ≤ γ) :
    oTo (wM Ma Mb) j ℓ F ≤ ENNReal.ofReal ((Ma * Mb)⁻¹ * (ρ * (ℓ * ℓ) + γ)) := by
  rcases hγ with h | h
  · exact oTo_wM_le_mass hMa hMb j hℓ X hab hF hN hS hε hρ h
  · have hN' : (F : SA c (Lam 2 L N)).ab ∈ NX ({b, a} : Set (Lam 2 L N)) := by
      rwa [Set.pair_comm]
    exact oTo_wM_le_mass hMa hMb j hℓ X (Ne.symm hab) hF hN' hS hε hρ h

/-- **The `hVo` input of `obs_histFromABL_wM` with a per-block base point.** -/
theorem hVo_of_coeffsP (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (P : ObsPts 2 L N)
    (hab : P.a ≠ P.b) (j₀ : ℕ) (o₀ : ObsSt .two L N) (t : Hist.Seq (Xs R)) (n : ℕ)
    (Ma Mb : ℕ → ℝ) (hMa : ∀ j, 0 < Ma j) (hMb : ∀ j, 0 < Mb j) (m ρ γ : ℕ → ℝ)
    (X : Finset (Lam 2 L N)) (hℓ : ∀ j, 0 < histS R j t)
    (hAB : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      (obsHistFrom R P j₀ o₀ j t).V b ∈ (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))))
    (hN : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab ∈
        NX ({P.a, P.b} : Set (Lam 2 L N)))
    (hS : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      IsSym ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab)
    (hε : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab = 0)
    (hρ : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      ‖mass2 ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab‖ ≤ ρ j)
    (hγ : ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      gradM4Sz X P.a P.b ((L : ℝ) ^ j) (histS R j t)
          ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab ≤ γ j ∨
        gradM4Sz X P.b P.a ((L : ℝ) ^ j) (histS R j t)
          ((obsHistFrom R P j₀ o₀ j t).V b : SA .two (Lam 2 L N)).ab ≤ γ j)
    (hm : ∀ j, j₀ ≤ j → j < n →
      (Ma j * Mb j)⁻¹ * (ρ j * (histS R j t * histS R j t) + γ j) ≤ m j) :
    ∀ j, j₀ ≤ j → j < n → ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM (Ma j) (Mb j)) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤
        ENNReal.ofReal (m j) := fun j hj hjn b hb =>
  (oTo_wM_le_massP (hMa j) (hMb j) j (hℓ j) X hab (hAB j hj hjn b hb) (hN j hj hjn b hb)
    (hS j hj hjn b hb) (hε j hj hjn b hb) (hρ j hj hjn b hb) (hγ j hj hjn b hb)).trans
    (ENNReal.ofReal_le_ofReal (hm j hj hjn))

end

end PtCorr2
