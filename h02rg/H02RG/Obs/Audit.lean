import Obs

/-!
# Audit of the `Obs` library (Section `sec:obs-flow` of `h02rg.tex`)

Run with `lake env lean H02RG/Obs/Audit.lean` (after `lake build`).  Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

open Obs

/-! ## Source fields, norms, observable coupling constants (`sec:obsfields`) -/

#print Obs.SA                 -- `F = F_∅ + σ_a F_a + σ_b F_b + σ_a σ_b F_ab` (both cases)
#print Obs.OE                 -- even elements: a commutative ring
#check @Obs.oT_mul_le         -- product property of the weighted norm `e:Tphi-obs`
#check @Obs.normj_succ_le     -- `e:Tphi-obs-ub`
#print Obs.Coup1              -- observable coupling constants, Case (1)
#print Obs.Coup2              -- observable coupling constants, Case (2)

/-! ## The free observable flow (`sec:obs-free`) -/

#check @Obs.freeStep_one      -- `lem:Vobs-flow-free`, Case (1)
#check @Obs.freeStep_two      -- `lem:Vobs-flow-free`, Case (2)
#check @Obs.corr_one          -- `e:s5cora`
#check @Obs.corr_two_a        -- `e:s5corb1`
#check @Obs.corr_two_ab       -- `e:s5corb2`
#check @Obs.frd_warmup_conclusion  -- `e:warmupcor-conclusion`

/-! ## Localisation with observables (`sec:locobs`) -/

#check @Obs.LocObs.locObs_bound     -- `prop:Loc-obs` (i)
#check @Obs.LocObs.locObs_contract  -- `prop:Loc-obs` (ii)
#check @Obs.LocObs.locAB_eq_sum     -- `prop:Loc-obs` (iii)
#check @Obs.LocObs.locAB_image      -- `prop:Loc-obs` (iv)

/-! ## The generic RG step and the observable RG map (`sec:rgmap-ext`) -/

#check @Obs.Gen.ZVK_G
#check @Obs.Gen.KnextG_union
#check @Obs.bulk_KnextO       -- the bulk component is the bulk map
#check @Obs.ZVK_obs'          -- `prop:ZVK` with observables
#check @Obs.KnextO_union      -- factorisation
#check @Obs.flowO_consist     -- `prop:consistency` with observables

/-! ## Theorem `thm:step-obs` and the flow (`sec:tyler-renorm-group`, `sec:flow-obs`) -/

#check @Obs.stepObs           -- Theorem `thm:step-obs`
#check @Obs.Vobs_recursion_one  -- `lem:Vobs-recursion`
#check @Obs.Vobs_recursion_two
#check @Obs.Vobs_bd           -- `lem:Vobs-bd`
#check @Obs.flowObs           -- Proposition `prop:flow-obs`
#check @Obs.flowObs_of_thm_flow

/-! ## Observable flow: partner independence, translation covariance, `N`-independence -/

#check @Obs.flowO_b_indep     -- the `a` slot does not depend on the partner `b`
#check @Obs.flowO_transl      -- translation covariance
#check @Obs.a_ctr_consist     -- `a` slot `N`-independence
#check @Obs.b_consist         -- `b` slot `N`-independence
#check @Obs.pair_consist      -- pair `N`-independence

/-! ## Axioms -/

#print axioms Obs.frd_warmup_conclusion
#print axioms Obs.LocObs.locObs_contract
#print axioms Obs.ZVK_obs'
#print axioms Obs.KnextO_union
#print axioms Obs.flowO_consist
#print axioms Obs.stepObs
#print axioms Obs.Vobs_bd
#print axioms Obs.flowObs
#print axioms Obs.flowObs_of_thm_flow
#print axioms Obs.flowO_b_indep
#print axioms Obs.flowO_transl
#print axioms Obs.pair_consist
