import Obs2.Est.BlockO1
import Obs2.Est.EstNormAB

/-!
# The two-scale bounds for `θ` with sources, any weights (`ab` copy of `Obs2.Est.BlockO1`)

With all four components local (`CmpInA`) the Pauli two-scale bounds for `θF` hold for any
weights (`oNorm_le_cmp`): `thetaO_block_le2A`, `thetaO_conn_le2A`, and `thetaO_le2A` (the copy of
`Obs2.thetaO_le2` of `BlockO3`).
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case} {w : Wt}

section Pauli

variable (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ')
  (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
include hd hL hj hℓ' hℓC hsum

theorem thetaO_block_le2A {b : Fin d → ℕ} {F : OE c (Lam d L N)}
    (hF : CmpInA (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (F : SA c (Lam d L N))) :
    oT2 w j ℓ' ℓC (thetaO F : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp ?_ ?_ ?_ ?_
  · rw [coe_thetaO, thetaS_e]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.e
  · rw [coe_thetaO, thetaS_a]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.a
  · rw [coe_thetaO, thetaS_b]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.b
  · rw [coe_thetaO, thetaS_ab]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.ab

theorem thetaO_conn_le2A {X : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : CmpInA (nbhd j X : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oT2 w j ℓ' ℓC (thetaO F : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d ^ nb j X) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp ?_ ?_ ?_ ?_
  · rw [coe_thetaO, thetaS_e]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.e
  · rw [coe_thetaO, thetaS_a]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.a
  · rw [coe_thetaO, thetaS_b]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.b
  · rw [coe_thetaO, thetaS_ab]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.ab

theorem thetaO_le2A {Y : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : CmpInA (↑Y : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oT2 w j ℓ' ℓC (thetaO F : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.pq d ^ nb j Y) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp ?_ ?_ ?_ ?_
  · rw [coe_thetaO, thetaS_e]; exact Step2.theta_succ_le2 hd hL hj hF.e hℓ' hℓC hsum
  · rw [coe_thetaO, thetaS_a]; exact Step2.theta_succ_le2 hd hL hj hF.a hℓ' hℓC hsum
  · rw [coe_thetaO, thetaS_b]; exact Step2.theta_succ_le2 hd hL hj hF.b hℓ' hℓC hsum
  · rw [coe_thetaO, thetaS_ab]; exact Step2.theta_succ_le2 hd hL hj hF.ab hℓ' hℓC hsum

end Pauli

end

end Obs2
