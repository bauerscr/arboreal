import Loc

/-!
# Audit of the `Loc` library (Section `sec:Loc` of `h02rg.tex`)

Run with `lake env lean Loc/Audit.lean` (after `lake build`).  Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

open Loc Grassmann FRD

/-! ## Definitions -/

#print Loc.IsSmall       -- small sets `𝒮_j`
#print Loc.nbhd          -- `X^□`
#print Loc.Vcoup.eval    -- `V(X)` (`e:VX`)
#print Loc.VXspace       -- `(ℂ ⊕ 𝒱^∅)(X)`
#print Loc.Mono          -- the local monomials
#print Loc.stencil
#print Loc.Qpoly         -- the test polynomials
#print Loc.mu
#print Loc.Amat
#print Loc.locCoef
#print Loc.LocXY         -- `Loc_{X,Y}`
#print Loc.LocX          -- `Loc_X`
#print Loc.AffAut        -- lattice automorphisms
#print Loc.Jsym          -- the symplectic symmetry `ψ ↦ ψ̄, ψ̄ ↦ -ψ`

/-! ## Defining property and `prop:Loc` -/

#check @Loc.mu_LocX           -- `Loc_X F` has the same test-polynomial pairings as `F`
#check @Loc.LocXY_mem         -- `Loc_{X,Y} : 𝒩(X^□) → 𝒩(Y^□)`
#check @Loc.Loc_bound         -- (i)
#check @Loc.Loc_contract      -- (ii)
#check @Loc.LocX_eq_sum       -- (iii)
#check @Loc.AffAut.LocXY_aut  -- (iv)
#check @Loc.LocXY_Jsym        -- `J`-equivariance
#check @Loc.Loc_image         -- (v)

/-! ## Examples -/

#check @Loc.LocXY_psiPow      -- Example (i)
#check @Loc.LocX_psiPow
#check @Loc.LocXY_exF         -- Example (ii)
#check @Loc.LocX_exF

#print axioms Loc.mu_LocX
#print axioms Loc.LocXY_mem
#print axioms Loc.Loc_bound
#print axioms Loc.Loc_contract
#print axioms Loc.LocX_eq_sum
#print axioms Loc.AffAut.LocXY_aut
#print axioms Loc.LocXY_Jsym
#print axioms Loc.Loc_image
#print axioms Loc.LocX_psiPow
#print axioms Loc.LocXY_exF
#print axioms Loc.LocX_exF

-- every dimension
#print axioms Loc.Loc_bound_gen
#print axioms Loc.exists_contract_bound_gen

/-! ## Pauli exclusion (`lem:pauli` of `h02uv-outline.tex`) -/

#print axioms Loc.pauli_abstract
#print axioms Loc.pauli
#print axioms Loc.card_nearB_le
#print axioms Loc.pauli_EC

/-! ## The localisation of `d = 2` and `lem:loc2` of `h02uv-outline.tex` -/

#print Loc.mu4           -- the quartic pairing
#print Loc.mono4         -- `(∇_i ψ)(∇_k ψ̄) ψ ψ̄`
#print Loc.Loc4XY        -- the quartic marginal part of the localisation
#print Loc.Loc2XY        -- `Loc2_{X,Y} = Loc_{X,Y} + Loc4_{X,Y}`
#print axioms Loc.mu4_sub_Loc2X
#print axioms Loc.exists_Loc2XY_bound
#print axioms Loc.exists_four_bound
#print axioms Loc.exists_large_bound
#print axioms Loc.loc2_contract
