import Suscept

/-!
# Audit of the `Suscept` library (Section `sec:suscept` of `h02rg.tex`)

Run with `lake env lean H02RG/Suscept/Audit.lean` (after `lake build Suscept`).  Expected axioms:
`propext`, `Classical.choice`, `Quot.sound`.
-/

open Suscept Flow Step Loc Grassmann FRD

/-! ## Notation: `e:avgV0`, `e:ZNN-def`, restriction to constant fields -/

#print Suscept.Cov            -- `C = (-Δ + m²)^{-1}`
#print Suscept.Z0             -- `Z_0 = e^{-V_0(Λ)}`
#print Suscept.ZNN            -- `Z_{N,N} = 𝔼_C θ Z_0`
#print Suscept.uN             -- `u_N = ∑_{j<N} u_{j+1}`
#print Suscept.ZtNN           -- `Z̃_{N,N} = e^{u_N|Λ|} Z_{N,N}`
#print Suscept.Rc             -- restriction to constant fields
#print Suscept.avgV
#check @Suscept.psiC_eq       -- `ψ = |Λ|^{-1} ∑_x ψ_x`
#check @Suscept.Rc_psi
#check @Suscept.Rc_even       -- even elements restrict to `F⁰ + F² ψψ̄`
#print Suscept.c2             -- `F² = ∑_{x,y} F_{(x,+),(y,-)}`
#print Suscept.kN0            -- `k_N^0`
#print Suscept.kN2            -- `k_N^2`
#print Suscept.atN            -- `ã_{N,N} = a_N - k_N^2/|Λ|`
#print Suscept.utN            -- `ũ_{N,N} = k_N^0 + ã_{N,N} t_N`

/-! ## `e:S4C` and `e:ZNN-def` -/

#check @Suscept.Cov_eq        -- `C = C_1 + ⋯ + C_{N-1} + C_N + t_N Q_N`
#check @Suscept.Cov_row_sum   -- `∑_y C_{xy} = m^{-2}`
#check @Suscept.ZNN_eq        -- `Z_{N,N} = e^{-u_N|Λ|} 𝔼_{t_N Q_N} θ (e^{-V_N(Λ)} + K_N(Λ))`
#check @Suscept.ZtNN_eq
#check @Suscept.EC_Z0         -- `𝔼_C[Z_0] = e^{-u_N|Λ|}(1 + ũ_{N,N})`

/-! ## Proposition `prop:ZNN` -/

#check @Suscept.prop_ZNN      -- `e:ZNN`
#check @Suscept.kN0_le        -- `e:ZNN-bd`
#check @Suscept.kN2_le        -- `e:ZNN-bd`
#check @Suscept.prop_ZNN_cont -- continuity in `m²`
#check @Flow.flowN_cont
#check @Flow.goodCov_covAt

/-! ## Proposition `prop:suscept` -/

#check @Suscept.sum_omega_psibar_psi
#check @Suscept.sum_EC_Z0_psibar_psi
#check @Suscept.prop_suscept  -- `e:suscept-atilde`
#check @Suscept.sec_suscept

/-! ## Axioms -/

#print axioms Suscept.Rc_even
#print axioms Suscept.ZNN_eq
#print axioms Suscept.prop_ZNN
#print axioms Suscept.kN0_le
#print axioms Suscept.kN2_le
#print axioms Suscept.prop_ZNN_cont
#print axioms Suscept.prop_suscept
#print axioms Suscept.sec_suscept
