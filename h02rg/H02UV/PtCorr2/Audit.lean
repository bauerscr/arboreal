import PtCorr2

/-!
# Audit of the `PtCorr2` library

Point correlations along the flow: Ward identity, susceptibility, zero mode, one-point function.

Run with `lake env lean H02UV/PtCorr2/Audit.lean` (after `lake build PtCorr2`). Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

-- keep-set roots (outline theorems)
#print axioms PtCorr2.ward2
#print axioms PtCorr2.suscept2
#print axioms PtCorr2.suscept2_dressed
#print axioms PtCorr2.thm_ward_flow_onept
#print axioms PtCorr2.thm_zero_mode_flow
#print axioms PtCorr2.prop_ZNN2

-- important intermediate results
#print axioms PtCorr2.lastN_full_ZVK
#print axioms PtCorr2.fin_bounds
#print axioms PtCorr2.zeroModeOut_of_glue
#print axioms PtCorr2.zero_mode_t
#print axioms PtCorr2.hist_omega_traj
#print axioms PtCorr2.c2_formula
#print axioms PtCorr2.ward2_atilde
#print axioms PtCorr2.dress_suscept
#print axioms PtCorr2.thm_ward_flow_rho
#print axioms PtCorr2.onept_avg0_h0
