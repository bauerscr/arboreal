import H02UV.Main.Theorems

/-!
# Audit of `h02uv-lean.tex` (the arboreal gas in `d = 2`, continuum limit at fixed `β_R`)

The Lean statements of `h02uv-lean.tex`: the mass-shift identity (`H02UV/Spin2/Final/Arboreal.lean`)
and the two theorems (`H02UV/Main/Theorems.lean`), with `#check` and `#print axioms`, and the
definitions used in their statements. The audit of all Lean-proved statements of
`summaries/h02uv-outline.tex` is `H02UV/Audit.lean`.

Run with `lake env lean Audit/H02UV.lean` after `lake build`. Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

/-! ## Mass-shift identity -/

-- At h = 0, `⟨ψ̄_0ψ_x⟩` with covariance `(−Δ+m²)^{-1}` and `a₀ = b − m²` does not depend on
-- `m² > 0`; `b⟨ψ̄_0ψ_x⟩ = P_{1/b}[0 ↔ x]` (arboreal gas).
#check Spin2.avg0_mass_indep
#print axioms Spin2.avg0_mass_indep
#check Spin2.avg0_eq_Pconn
#print axioms Spin2.avg0_eq_Pconn

/-! ## Theorems -/

-- Per-N clause (outline Thms 1.1 + 1.2 for the arboreal gas): `β_ε`, `(β_j)` with `ArbScale`
-- and `ArbShort`; `m²` is chosen internally.
#check H02UV.thm_arboreal_multiscale
#print axioms H02UV.thm_arboreal_multiscale

-- thm:limit-fixed: a sequence `β_N` with the per-N conclusions; `f_N` equicontinuous, a
-- subsequential limit `G` on `𝕋 ∖ {0}` with the short-distance law.
#check H02UV.thm_arboreal_limit_fixed
#print axioms H02UV.thm_arboreal_limit_fixed

/-! ## Definitions used in the statements of the main theorems (`h02uv-lean.tex`)

The conclusions `ArbScale` (Thms 1.1, 1.2) and `ArbShort` (short distances) of
`thm_arboreal_multiscale`, the normalised two-point function `arbF`, equicontinuity `ClEqui` and
the short-distance law `csA`, `csRate` of `thm_arboreal_limit_fixed`, and the objects they use:
`β₁ = 3/(2π)`, the scale `j(x)`, the connection probability `P_β[0 ↔ x]`, the lattice embedding
of the torus `𝕋` and the norms. -/

#print Spin2.ArbScale
#print Spin2.ArbShort
#print Spin2.arbF
#print Spin2.ClEqui
#print Spin2.csA
#print Spin2.csRate
#print Spin2.betaOne
#print Spin2.jPhys
#print Spin2.eucl
#print Spin2.Pconn
#print Step2.betaL
#print Loc.Lam
#print H02.arborealProb
#print H02.ghostW
#print Cont.torusNorm
#print Cont.torusRep
#print Cont.latPt
#print Cont.latPtN
#print Cont.clSgn
