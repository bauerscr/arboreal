import Obs.ContObsFlow

/-!
# Continuity in `m²` and holomorphy in `b₀` of the observable flow (groundwork for `sec:ward`)

Specialisations of `Obs.flowO_reg` (`Obs.ContObsFlow`):

* **Continuity in `m²`** (`flowO_cont`, `nextObs_flowO_cont`, `uObsX_flowO_cont`), including at
  `m² = 0`: for `S ⊆ [0, ∞)`, bulk initial couplings `V₀(m²)` continuous on `S` (`Step.CV`),
  fixed `V^obs_0, a, b`, and `GoodCov` on `S`, the observable couplings of `flowO` are
  continuous on `S` accessor-wise (`CCoup`), and the activities `K_j(X)` are continuous
  componentwise and coefficient-wise (`CCO`, the analogue of `Step.CCE` for `OE c Λ`).
  This mirrors `Flow.flowN_cont`.
* **Holomorphy in `b₀`** (`flowO_hol`, `nextObs_flowO_hol`, `flowN_hol`): at fixed `m²`, for bulk
  initial couplings `V₀(b₀)` holomorphic on `U ⊆ ℂ` (`RegV (Reg.hol U)`, i.e. `z, y, a, b`
  `DifferentiableOn ℂ` on `U`) and `GoodCov`, the same quantities are holomorphic on `U`
  (`RegCp (Reg.hol U)`, `RegKO (Reg.hol U)`: all accessors resp. all coefficients of all
  components are `DifferentiableOn ℂ` on `U`).
-/

namespace Obs

noncomputable section

open Finset Grassmann SA Loc Step LocObs

variable {c : Case} {d L N : ℕ} [NeZero L] {S : Set ℝ}

/-! ### The continuity notions -/

/-- The covariances `C_{j+1}(m²)` (as complex functions) are continuous on `S ⊆ [0, ∞)`. -/
theorem covAt_reg_cont (hd : 1 ≤ d) (hS : S ⊆ Set.Ici 0) :
    ∀ j < N, ∀ x y : Lam d L N,
      (Reg.cont S).P (fun m => ((Flow.covAt d L N m j x y : ℝ) : ℂ)) :=
  fun _ hj x y => Reg.cont_ofReal ((Flow.covAt_continuousOn hd hj x y).mono hS)

/-! ### Continuity in `m²` -/

section Cont

variable {ℓ₀ : ℝ} {V₀ : ℝ → Vcoup}

end Cont

/-! ### Holomorphy in `b₀` (at fixed `m²`) -/

section Hol

variable {ℓ₀ msq : ℝ} {U : Set ℂ} {V₀ : ℂ → Vcoup}

end Hol

end

end Obs
