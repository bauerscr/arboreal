import Step2

/-!
# Audit of the `Step2` library

The second-order RG step (`thm:step`), the flow theorems (`thm:flow`) and the master hypothesis packages.

Run with `lake env lean H02UV/Step2/Audit.lean` (after `lake build Step2`). Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

-- keep-set roots (outline theorems)
#print axioms Step2.thm_flow_final
#print axioms Step2.thm_flow_complete_band
#print axioms Step2.thm_flow_complete2
#print axioms Step2.W_contract_d2
#print axioms Step2.Kplus_lip_cov
#print axioms Step2.Kplus_holC
#print axioms Step2.Wnext2_holC
#print axioms Step2.Vnext2_holC
#print axioms Step2.Wnext2_lip
#print axioms Step2.Wnext2_latsym
#print axioms Step2.Last.Wnext2_latsym
#print axioms Step2.Vnext2_latsym
#print axioms Step2.Last.Vnext2_latsym
#print axioms Step2.Kplus_latsym
#print axioms Step2.Last.Kplus_latsym
#print axioms Step2.covProps
#print axioms Step2.expLC_four
#print axioms Step2.omegaC_full_step
#print axioms Step2.FlowSeq.kappaS_g
#print axioms Step2.FlowSeq.beta_bound
#print axioms Step2.FlowSeq.bubble_explicit
#print axioms Step2.Wact_sub_Wlin_bound
#print axioms Step2.prop_C5
#print axioms Step2.prop_last_d2

-- important intermediate results
#print axioms Step2.step2
#print axioms Step2.step2_d2
#print axioms Step2.flow_master_hyp0LZD
#print axioms Step2.flow_master_hyp0
#print axioms Step2.flow_finalZ_hyp0_zetaX
#print axioms Step2.flow_complete2_hyp0X
-- the master theorem of the flow-theorem chain (`H02UV/Step2/Flow/FlowMaster.lean`)
#print axioms Step2.flow_master
