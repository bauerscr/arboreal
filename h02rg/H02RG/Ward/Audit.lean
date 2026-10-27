import Ward.MainAll
import H02RG.Main.Theorems
import Ward.CorWardMain
import Ward.ObsLimitTrunc

/-!
# Audit of the `Ward` library (Section `sec:ward` of `h02rg.tex`), including the
infinite-volume limits of the observable couplings

Run with `lake env lean H02RG/Ward/Audit.lean` (after building the modules).  Expected axioms:
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- the model
#check @Ward.bridge_avg          -- the bridge `ℍ^{0|2}` ↔ `ψ`-model
#check @H02.prop_h02_forest      -- `prop:h02-forest` (ghost identities)
-- infinite-volume limits of the observable couplings and their point independence
#check @Ward.lamA2_rate
#check @Ward.gamA2_rate
#check @Ward.qN_rate
#check @Ward.qN2_rate
#check @Ward.avg_pbp_tendsto
#check @Ward.avg_two_tendsto
#check @Ward.trunc_tendsto
#check @Ward.LamA_eq_LamB
#check @Ward.GamA_zero_sub_green
#check @Ward.Qone_zero_sub_green
#check @Ward.Qtwo_zero_add_green
-- corollaries of sec:ward and sec:finvol
#check @Ward.cor_ward            -- `cor:ward` (i), (ii)
#check @Ward.cor_macro           -- `cor:macro`
#check @Ward.cor_anm0            -- `cor:anm0`
#check @Ward.cor_conn4pt         -- `cor:conn4pt`
#check @Ward.cor_aNlimit         -- `cor:aNlimit` (`λθ = 1`)
-- main theorems (in `H02RG/Main/Theorems.lean`)
#check @H02RG.thm_forest_macro    -- `thm:forest-macro`
#check @H02RG.thm_h02             -- `thm:h02`
#check @H02RG.thm_forests0        -- `thm:forests0` (without `θ² = ζ`)
#check @H02RG.thm_forests         -- `thm:forests` (without the identities)
#print Ward.AllBody
#check @H02RG.thm_all             -- all four with shared constants and the identities

#print axioms Ward.bridge_avg
#print axioms H02.prop_h02_forest
#print axioms Ward.LamA_eq_LamB
#print axioms Ward.Qtwo_zero_add_green
#print axioms Ward.cor_ward
#print axioms Ward.cor_macro
#print axioms Ward.cor_anm0
#print axioms Ward.cor_conn4pt
#print axioms Ward.cor_aNlimit
#print axioms H02RG.thm_forest_macro
#print axioms H02RG.thm_h02
#print axioms H02RG.thm_forests0
#print axioms H02RG.thm_forests
#print axioms H02RG.thm_all
