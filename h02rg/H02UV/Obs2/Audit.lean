import Obs2

/-!
# Audit of the `Obs2` library

The observable step (`prop:gamma`, the observable localisation and block bounds).

Run with `lake env lean H02UV/Obs2/Audit.lean` (after `lake build Obs2`). Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

-- keep-set roots (outline theorems)
#print axioms Obs2.prop_gamma
#print axioms Obs2.exists_locABt_contract
#print axioms Obs2.locABt_m4
#print axioms Obs2.LocO2_evalO
#print axioms Obs2.obsHist_coal
#print axioms Obs2.obsHist_coal_valid
#print axioms Obs2.mass2_VpO_a
#print axioms Obs2.VpO_a_one
#print axioms Obs2.K_term_bound
#print axioms Obs2.lin_iter
#print axioms Obs2.renorm_bound

-- important intermediate results
#print axioms Obs2.oTj_FCO_le
#print axioms Obs2.exists_LocO2_obs_bound
#print axioms Obs2.LocO2_cmpIn
#print axioms Obs2.exists_odd_contract_pt
#print axioms Obs2.exists_even_contract_pt
#print axioms Obs2.mu_step_one
#print axioms Obs2.mu_step_two
#print axioms Obs2.total_step
#print axioms Obs2.total_mu_one
#print axioms Obs2.total_mu_two
#print axioms Obs2.wTad_step
#print axioms Obs2.tauC_TI
