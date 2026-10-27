import H02RG.Main.Theorems

/-!
# Audit of `h02rg-lean.tex` (the arboreal gas / `H^{0|2}` model in `d ≥ 3`)

The Lean theorems stated in `h02rg-lean.tex` (all in `H02RG/Main/Theorems.lean`), with
`#check` and `#print axioms`, and the definitions used in their statements. The audit of all
main statements of `src/h02rg.tex` (Sections 1–2) is `H02RG/Audit.lean`.

Run with `lake env lean Audit/H02RG.lean` after `lake build`. Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

/-! ## Theorems -/

-- thm:all, part (A) (`h02rg.tex` thm:forest-macro): finite torus, h = 0,
-- `P_β[0 ↔ x] = ζ(β) + c₀(β)/(β|x|^{d-2}) + O(β⁻¹|x|^{-(d-2+κ)}) + O(β⁻¹ L^{-κN})`.
#check H02RG.thm_forest_macro
#print axioms H02RG.thm_forest_macro

-- thm:all, part (B) (`h02rg.tex` thm:h02): the `H^{0|2}` model, `lim_{h↓0} lim_N`.
#check H02RG.thm_h02
#print axioms H02RG.thm_h02

-- thm:all, part (C) (`h02rg.tex` thm:forests0): the percolation probability `θ_d(β)`.
#check H02RG.thm_forests0
#print axioms H02RG.thm_forests0

-- thm:all, part (D) (`h02rg.tex` thm:forests): truncated connection probabilities.
#check H02RG.thm_forests
#print axioms H02RG.thm_forests

-- thm:all: (A)–(D) with one shared set of constants, and (E) `ζ = θ²`, `c₂θ²/c₁² = 1`,
-- `c₀ = 2c₁`, `c₀ = 2c_d`.
#check H02RG.thm_all
#print axioms H02RG.thm_all

/-! ## Definitions used in the statements of the main theorems (`h02rg-lean.tex`)

The statement predicates of `thm_forest_macro` (`FMBody`), `thm_h02` (`H02Body`), `thm_forests0`
(`F0Body`), `thm_forests` (`FBody`) and `thm_all` (`AllBody`), and the objects they use: the
torus `Λ_N`, the ghost weights and the arboreal-gas probability, the `H^{0|2}` expectation, the
Euclidean norm and the constant `c_d` of the Green function asymptotics. -/

#print Ward.FMBody
#print Ward.H02Body
#print Ward.F0Body
#print Ward.FBody
#print Ward.AllBody
#print Ward.eNorm
#print Ward.nnW
#print Ward.toT
#print Loc.Lam
#print H02.ghostW
#print H02.arborealProb
#print H02.forestWeight
#print H02.Zforest
#print H02.expect
#print H02.avg
#print H02.z
#print FRD.GreenAsymp.cd
