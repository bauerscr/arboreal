import Psi4

/-!
# Audit of the `Psi4` library (Section `sec:proofs` of `h02rg.tex`)

Run with `lake env lean H02RG/Psi4/Audit.lean` (after `lake build`).  Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

#check @Psi4.VE_univ_sumParts'   -- summation by parts: `y₀(∇ψ,∇ψ̄) + z₀/2(…) = (y₀+z₀)(∇ψ,∇ψ̄)`
#check @PtCorr.setup             -- one common flow for all statements
#check @PtCorr.setupW            -- the common flow with reality and torus independence
#print Psi4.avgM                 -- `⟨·⟩_{m², s₀, a₀, b₀}`
#check @Psi4.thm_psi4_full       -- Theorem `thm:psi4-full` (Tier 1)
#check @Psi4.thm_psi4            -- Theorem `thm:psi4` (Tier 1; corrected `e:psi4-00`)

#print axioms Psi4.VE_univ_sumParts'
#print axioms PtCorr.setup
#print axioms PtCorr.setupW
#print axioms Psi4.thm_psi4_of
#print axioms Psi4.thm_psi4_full
#print axioms Psi4.thm_psi4
