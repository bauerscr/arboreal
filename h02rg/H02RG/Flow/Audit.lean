import Flow

/-!
# Audit of the `Flow` library (Section `sec:flow` of `h02rg.tex`, and the torus independence
part of Proposition `prop:consistency`)

Run with `lake env lean H02RG/Flow/Audit.lean` (after `lake build`).  Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

open Flow Step Loc Grassmann FRD

/-! ## Proposition `prop:consistency`: independence of the torus -/

#print Flow.emb               -- `Λ_N → Λ_M`, `x ↦ rep(x) mod L^M`
#print Flow.Compat            -- compatibility of activities near the origin
#check @Flow.Cfrd_emb
#check @Flow.uVnext_consist
#check @Flow.Knext_consist

/-! ## The infinite volume spaces -/

#print Flow.KFam              -- compatible families of torus activities (a Banach space)
#check @Flow.KFam.differentiableOn_of_coeff

/-! ## The stable manifold theorem -/

#print Flow.System
#check @Flow.System.Bounds.existsUnique_stable
#check @Flow.System.Bounds.norm_orbit_stableMap_le
#check @Flow.System.Bounds.differentiableOn_stableMap_smul
#check @Flow.continuous_stableMap

/-! ## Theorem `thm:flow` and Corollary `cor:flow-finvol` -/

#print Flow.flowN             -- the renormalisation group flow on `Λ_N`
#check @Flow.thm_flow
#check @Flow.thm_flow_real   -- with reality `V₀^c(m², b̄₀) = conj V₀^c(m², b₀)`

/-! ## Axioms -/

#print axioms Flow.uVnext_consist
#print axioms Flow.Knext_consist
#print axioms Flow.System.Bounds.existsUnique_stable
#print axioms Flow.thm_flow
#print axioms Flow.thm_flow_real
