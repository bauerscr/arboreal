import Obs2.Est.BlockO5
import Obs2.Est.BlockOAB4
import Obs2.Est.KObs2

/-!
# The crude bound on the `σ_aσ_b` sector (`ab` copy of `Obs2.Est.BlockO5`)

**`Knext2O_crude_tsAB`**: `Obs2.Knext2O_crude_ts` for inputs in `abSub` with all four components
local (`CmpInA`) and any weights with `w.Sub` (in place of `w_ab = 0`): under the same smallness
hypotheses, `A^{(|𝓑_{j+1}(U)| - 2^d)_+} ‖K_{j+1}(U)‖_{T_{j+1}(ℓ')} ≤ 1` in the full norm. The
localisation bound is `exists_LocO2_ab_bound`, its locality `bho_hloclAB`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

/-- **`BHOAB.hlocl` holds for `LocO2`** (the `ab` part of `Loc_{X,Y}F` lies in `𝒩({a, b})`). -/
theorem bho_hloclAB {d L N : ℕ} [NeZero L] {c : Obs.Case} (hd : 1 ≤ d) (P : ObsPts d L N)
    (j : ℕ) : ∀ X Y : Finset (Lam d L N), IsPolymer j Y → ∀ F : OE c (Lam d L N),
      CmpInA (↑(nbhd j Y ∪ {P.a, P.b}) : Set (Lam d L N)) (LocO2 P X Y F : SA c (Lam d L N)) := by
  intro X Y hY F
  refine ⟨bho_hlocl hd P j X Y hY F, NX_mono ?_ (locABtXY_mem P X Y _)⟩
  intro z hz
  rcases hz with rfl | rfl <;> simp

end

end Obs2
