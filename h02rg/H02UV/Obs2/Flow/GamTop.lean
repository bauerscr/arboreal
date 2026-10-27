import Obs2.Flow.GamChain2

/-!
# The `γ` constant of one step for an arbitrary covariance (the last step)

`gamA_succ` computes the `σ_a` constant of one step of the observable map along the bulk history.
The same computation works for any covariance `C` and any `V` of the form `α + βψ̄_aψ_a`, in
particular for the last step (covariance `stCovN`, `PtCorr2.uOutNO`):

  **`ε((u_{j+1}(Λ))_a) = ∑_Bε(V(B)_a) + β·C(a,a) - ρ`** (`eps_uXO_univ_a`),

`β = betaTot2 j V`, `ρ = gamRemG` (the activity and second-order part, as `gamRem2`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 LocObs Flow2

variable {d L N : ℕ} [NeZero L]

/-- The remainder of the `γ` step for general `C, V, W, K` (`gamRem2` along the history). -/
def gamRemG (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N) : ℂ :=
  ∑ b ∈ blockIdx (L := L) (N := N) j,
    (ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) +
      ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b)
        (blockSet (L := L) (N := N) j b)
        (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a))

/-- **The `σ_a` constant of one step, any covariance**:
`ε(u_{j+1}(Λ)_a) = ∑_Bε(V(B)_a) + β·C(a,a) - ρ`. -/
theorem eps_uXO_univ_a (P : ObsPts d L N) (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)
    (V W : OFam .two d L N) (K : OAct .two d L N)
    (hV : ∀ b, Loc2Form P.a (V b : SA .two (Lam d L N)).a) :
    ε (uXO P j C V W K univ : SA .two (Lam d L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, ε (V b : SA .two (Lam d L N)).a +
        betaTot2 j V * C P.a P.a - gamRemG P j C V W K := by
  have hu : (uXO P j C V W K univ : SA .two (Lam d L N)).a =
      ∑ b ∈ blockIdx (L := L) (N := N) j, (upO P j C V W K b : SA .two (Lam d L N)).a := by
    rw [uXO, AddSubmonoidClass.coe_finsetSum, sum_a]; rfl
  have hb : ∀ b ∈ blockIdx (L := L) (N := N) j,
      ε (upO P j C V W K b : SA .two (Lam d L N)).a =
      ε (V b : SA .two (Lam d L N)).a + mass2 (V b : SA .two (Lam d L N)).a * C P.a P.a -
        (ε (expLC C (Q2O P j K b : SA .two (Lam d L N)).a) +
          ε (locAp Obs.Case.two P.a (Step2.Bp (L := L) (N := N) j b)
            (blockSet (L := L) (N := N) j b)
            (SXO j C V W (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam d L N)).a)) := by
    intro b _
    rw [upO_a, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, uVpO_a, map_sub,
      map_sub, eps_expLC_loc2 (hV b)]
    ring
  rw [hu, map_sum, sum_congr rfl hb, sum_sub_distrib, sum_add_distrib, ← sum_mul]
  rfl

end

end Obs2
