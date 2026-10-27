import Step.Decomp

/-!
# Notation for the estimates of Section `sec:step`

* `dplus d = (d-2)/2 ∧ 1`;
* `wnorm j ℓ A U F = A^{(|𝓑_j(U)| - 2^d)_+} ‖F‖_{T_j(ℓ)}`, so that
  `‖K‖_j = sup_{U ∈ 𝒞_j} wnorm j ℓ_j A U (K(U))` (`Knorm_eq_iSup`).
-/

namespace Step

noncomputable section

open Finset Grassmann Loc FRD

variable {d L N : ℕ} [NeZero L]

/-- `(d - 2)/2 ∧ 1`. -/
def dplus (d : ℕ) : ℝ := min (((d : ℝ) - 2) / 2) 1

/-- The weighted norm `A^{(|𝓑_j(U)| - 2^d)_+} ‖F‖_{T_j(ℓ)}` of `e:K-norm`. -/
def wnorm (j : ℕ) (ℓ A : ℝ) (U : Finset (Lam d L N)) (F : EvR (Lam d L N)) : ENNReal :=
  ENNReal.ofReal (A ^ (nb j U - 2 ^ d)) * Tj d (L : ℝ) j ℓ (F : Alg d L N)

theorem Knorm_eq_iSup (j : ℕ) (ℓ A : ℝ) (K : Act d L N) :
    Knorm j ℓ A K = ⨆ U ∈ connSets (L := L) (N := N) j, wnorm j ℓ A U (K U) := rfl

theorem wnorm_le_Knorm {j : ℕ} {ℓ A : ℝ} {K : Act d L N} {U : Finset (Lam d L N)}
    (hU : IsConn j U) : wnorm j ℓ A U (K U) ≤ Knorm j ℓ A K := by
  classical
  refine le_iSup₂_of_le (f := fun U _ => wnorm j ℓ A U (K U)) U ?_ le_rfl
  simp [connSets, hU]

end

end Step
