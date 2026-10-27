import Obs2.Map.OSNorm
import Obs2.Est.EstNorm
import Step2.Map.Block

/-!
# Two-scale bounds for `θ` and `ι` with sources

The doubled-algebra norm with sources is `oNorm (T2 ℓ' ℓ_C) w`, the two-scale norm
`T(ℓ' ⊔ ℓ_C)` of `Step2.Map.TNorm2` in each component. Componentwise from the bulk bounds of
`Step2.Map.Block` (single-source weights `w_ab = 0`, since the `ab` components need not be local):

* `thetaO_block_le2`: `‖θ F‖_{T_{j+1}(ℓ' ⊔ ℓ_C)} ≤ Q₁ ‖F‖_{T_j(ℓ)}` for `F` with components in
  `𝒩(B^□)`;
* `thetaO_conn_le2`: `‖θ F‖ ≤ Q₁^{|𝓑_j(X)|} ‖F‖_{T_j(ℓ)}` for components in `𝒩(X^□)`;
* `inclO_le2`: `‖ι F‖_{T_{j+1}(ℓ' ⊔ ℓ_C)} ≤ ‖F‖_{T_{j+1}(ℓ')}`.
-/

set_option linter.unusedSectionVars false

namespace Obs2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc Step FRD ENNReal

variable {d L N : ℕ} [NeZero L] {c : Obs.Case} {w : Wt}

/-- The two-scale norm with sources on the doubled algebra at scale `j + 1`. -/
abbrev oT2 (w : Wt) (j : ℕ) (ℓ' ℓC : ℝ) (F : SA c (Lam d L N ⊕ Lam d L N)) : ℝ≥0∞ :=
  oNorm (Step2.T2 (Dir d) (pPhi d) ((L : ℝ) ^ (j + 1)) ℓ' ℓC) w F

section Pauli

variable (hd : 1 ≤ d) (hL : pauliL0 d ≤ L) {j : ℕ} (hj : j < N) {ℓ ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ')
  (hℓC : 0 < ℓC) (hsum : ℓ' + ℓC ≤ 2 * ℓ)
include hd hL hj hℓ' hℓC hsum

theorem thetaO_block_le2 (hw0 : w.ab = 0) {b : Fin d → ℕ} {F : OE c (Lam d L N)}
    (hF : CmpIn (nbhd j (blockSet (L := L) (N := N) j b) : Set (Lam d L N))
      (F : SA c (Lam d L N))) :
    oT2 w j ℓ' ℓC (thetaO F : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp3 hw0 ?_ ?_ ?_
  · rw [coe_thetaO, thetaS_e]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.e
  · rw [coe_thetaO, thetaS_a]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.a
  · rw [coe_thetaO, thetaS_b]; exact Step2.theta_block_le2 hd hL hj hℓ' hℓC hsum hF.b

theorem thetaO_conn_le2 (hw0 : w.ab = 0) {X : Finset (Lam d L N)} {F : OE c (Lam d L N)}
    (hF : CmpIn (nbhd j X : Set (Lam d L N)) (F : SA c (Lam d L N))) :
    oT2 w j ℓ' ℓC (thetaO F : SA c (Lam d L N ⊕ Lam d L N)) ≤
      ENNReal.ofReal (Step2.Q1 d ^ nb j X) * oTj d L w j ℓ (F : SA c (Lam d L N)) := by
  refine oNorm_le_cmp3 hw0 ?_ ?_ ?_
  · rw [coe_thetaO, thetaS_e]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.e
  · rw [coe_thetaO, thetaS_a]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.a
  · rw [coe_thetaO, thetaS_b]; exact Step2.theta_conn_le2 hd hL hj hℓ' hℓC hsum hF.b

end Pauli

theorem inclO_le2 {j : ℕ} {ℓ' ℓC : ℝ} (hℓ' : 0 < ℓ') (F : OE c (Lam d L N)) :
    oT2 w j ℓ' ℓC (inclO F : SA c (Lam d L N ⊕ Lam d L N)) ≤
      oTj d L w (j + 1) ℓ' (F : SA c (Lam d L N)) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  refine oNorm_le_cmp' ?_ ?_ ?_ ?_
  · rw [coe_inclO, inclS_e]; exact Step2.T2_incl_le hh hℓ' _
  · rw [coe_inclO, inclS_a]; exact Step2.T2_incl_le hh hℓ' _
  · rw [coe_inclO, inclS_b]; exact Step2.T2_incl_le hh hℓ' _
  · rw [coe_inclO, inclS_ab]; exact Step2.T2_incl_le hh hℓ' _

end

end Obs2
