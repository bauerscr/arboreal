import Obs2.Est.Step2O
import Obs2.Est.LinBoundAB
import Obs2.Est.BlockOAB5

/-!
# The second-order step on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.Step2O`)

**`step2O_tsAB`**: `Obs2.step2O_ts` for inputs in `abSub` (`V(B)`, `𝒲(B)`, `K(X)`), `K(X)`
anchored at `X` (`Obs2.anc`), all four components local (`CmpInA`), and finite weights with
`w.Sub` (in place of `w_ab = 0` and the one-point support hypotheses): for every connected
`(j+1)`-polymer `U`,

  `A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖K_{j+1}(U) - K^{(2)}(U)‖_{T_{j+1}(ℓ')}
     ≤ C₀ (L^{d-3} + A^{-η}) k + C₁ (ḡ³ + ḡ k + k²)`.

Same proof (Cauchy estimates, now for the four pairings `F_∅, F_a, F_b, F_{ab}`, `oTj_eq4`),
with the crude bound `Knext2O_crude_tsAB` and the contraction of the linear part
`Llin2O_ab_bound` (`Obs2.Est.LinBoundAB`, via `Llin2O_KconnO`: `𝓛(K)` only sees connected
polymers).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step Step2 FRD PolyAux ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case}

/-! ### Components and pairings -/

theorem oTj_eq4 {w : Wt} (j : ℕ) (ℓ : ℝ) (F : OE c (Lam d L N)) :
    oTj d L w j ℓ (F : SA c (Lam d L N)) = Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).e +
      w.a * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).a +
      w.b * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).b +
      w.ab * Tj d (L : ℝ) j ℓ (F : SA c (Lam d L N)).ab := rfl

/-! ### Restriction to connected polymers -/

theorem KconnO_of_conn {k : ℕ} {K : OAct c d L N} {X : Finset (Lam d L N)} (hX : IsConn k X) :
    KconnO k K X = K X := by
  classical
  simp only [KconnO, if_pos hX]

theorem KconnO_mem_ab {k : ℕ} {K : OAct c d L N}
    (hK : ∀ X, IsConn k X → K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N)))) :
    ∀ X, KconnO k K X ∈ (abSub : Subalgebra ℂ (OE c (Lam d L N))) := by
  classical
  intro X
  by_cases hX : IsConn k X
  · rw [KconnO_of_conn hX]; exact hK X hX
  · simp only [KconnO, if_neg hX]; exact zero_mem _

/-- `𝓛(K)` only sees `K` on connected polymers. -/
theorem Llin2O_KconnO (P : ObsPts d L N) {j : ℕ} (hN : j + 1 < N)
    (C : Matrix (Lam d L N) (Lam d L N) ℂ) (K : OAct c d L N) (U : Finset (Lam d L N)) :
    Llin2O P j C K U = Llin2O P j C (KconnO j K) U := by
  classical
  rw [Llin2O_eq P j C K hN U, Llin2O_eq P j C (KconnO j K) hN U]
  congr 1
  · refine sum_congr rfl fun X hX => ?_
    have h := (mem_filter.1 hX).2.1
    rw [KconnO_of_conn ⟨h.1, h.2.1⟩]
  · refine sum_congr rfl fun X hX => ?_
    rw [KconnO_of_conn (mem_filter.1 hX).2.1]

/-! ### Scaling -/

/-! ### The theorem -/

end

end Obs2
