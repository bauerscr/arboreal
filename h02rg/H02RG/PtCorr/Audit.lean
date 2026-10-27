import PtCorr

/-!
# Audit of the `PtCorr` library (Section `sec:obs` of `h02rg.tex`)

Run with `lake env lean H02RG/PtCorr/Audit.lean` (after `lake build`).  Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

open PtCorr

/-! ## Integration of the zero mode (`lem:ZNN-obs`) -/

#check @PtCorr.flowO_fact        -- factorisation of `K_{j+1}` along the observable flow
#check @PtCorr.ZNNO_eq           -- `Z̃_{N,N} = e^{-u^obs_N} 𝔼_{t_N Q_N} θ (e^{-V_N} + K_N)`
#check @PtCorr.bulk_ZtO
#check @PtCorr.c1m_ZtO_a_one     -- Case (1) components
#check @PtCorr.ε_ZtO_ab_one
#check @PtCorr.kOne_bounds
#check @PtCorr.ε_ZtO_a_two       -- Case (2) components
#check @PtCorr.ε_ZtO_ab_two
#check @PtCorr.kTwo_bounds

/-! ## Correlation functions and the λ^{(1)} identity -/

#check @PtCorr.avg_one_eq'
#check @PtCorr.avg_two_a_eq'
#check @PtCorr.avg_two_ab_eq'
#check @PtCorr.avg_transl
#check @PtCorr.c1m_RcO_Gobs_one_a

/-! ## `lem:1pt`, `prop:1pt`, `lem:2pt`, `prop:2pt` -/

#check @PtCorr.lamOne_bound      -- `λ^{(1)}_{x,j} = λ₀ + O(λ₀ b₀ L^{-κ j})` at finite `N`
#check @PtCorr.prop_1pt          -- `prop:1pt` (finite-`N` couplings)
#check @PtCorr.lem_2pt_one       -- `e:2pt-a`
#check @PtCorr.lem_2pt_two       -- `e:2pt-b`

/-! ## Axioms -/

#print axioms PtCorr.flowO_fact
#print axioms PtCorr.ZNNO_eq
#print axioms PtCorr.kTwo_bounds
#print axioms PtCorr.avg_two_ab_eq'
#print axioms PtCorr.c1m_RcO_Gobs_one_a
#print axioms PtCorr.lamOne_bound
#print axioms PtCorr.prop_1pt
#print axioms PtCorr.lem_2pt_one
#print axioms PtCorr.lem_2pt_two
