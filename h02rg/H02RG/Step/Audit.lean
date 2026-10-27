import Step

/-!
# Audit of the `Step` library (Sections `sec:symmetries`, `sec:polymers`, `sec:step-def` and
`sec:step` of `h02rg.tex`)

All algebras are over `ℂ` (complex coupling constants `u ∈ ℂ`, `V ∈ ℂ^4`); covariances, norms
and constants are real.

Run with `lake env lean H02RG/Step/Audit.lean` (after `lake build Step`).  Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

open Step Loc Grassmann FRD

/-! ## Definitions -/

#print Step.EvR          -- the even subalgebra (a commutative ring)
#print Step.Pj           -- `𝒫_j(W)`
#print Step.Comp         -- connected components
#print Step.clo          -- the closure `X̄`
#print Step.IsGen        -- the lattice automorphisms
#print Step.PresBlocks
#print Step.Kext         -- `K(X) = ∏_{Y ∈ Comp(X)} K(Y)`
#print Step.InK          -- `K ∈ 𝒦^∅_j` (with `J`-invariance)
#print Step.Zj           -- `Z_j` (`e:ZVK`)
#print Step.Qb           -- `Q(B)` (`e:Q-def`)
#print Step.Jb           -- `J(B, X)` (`e:J-defB`, `e:J-def`)
#print Step.uVnext       -- `(u_{j+1}, V_{j+1})` (`e:V+-def`)
#print Step.dI           -- `δI(B)` (`e:deltaI`)
#print Step.Ktil         -- `K̃`
#print Step.Kchk         -- `Ǩ`
#print Step.GCond        -- `𝒢(U)`
#print Step.Knext        -- `K_{j+1}(U)` (`e:K+-def`)
#print Step.Vnorm        -- `‖V‖_j` (`e:V-norm`)
#print Step.Knorm        -- `‖K‖_j` (`e:K-norm`)
#print Step.GoodCov      -- hypotheses on `C_{j+1}`

/-! ## Section `sec:symmetries` -/

#check @Step.EC_autAlg2      -- `𝔼_C` commutes with automorphisms preserving `C`
#check @Step.theta_autAlg
#check @Step.EC_Jsym2        -- ... and with `J` for symmetric `C`
#check @Step.isSymG_iff_scal -- `U(1)` invariance as invariance under scaling
#check @Step.EC_scal
#check @Step.EC_mem_NX       -- locality of `𝔼_C`
#check @Step.IsGen.exists_form
#check @Step.IsGen.eval_img  -- `E V(X) = V(E X)`

/-! ## Section `sec:polymers` -/

#check @Step.comp_eq_of_partition
#check @Step.isSmall_clo
#check @Step.comb1           -- Lemma `lem:comb1`
#check @Step.comb2
#check @Step.card_small_containing
#check @Step.card_clo_eq_le

/-! ## Section `sec:step-def` -/

#check @Step.EC_theta_eval_eq -- `𝔼_C θ V(X) = u|X| + V'(X)` explicitly
#check @Step.Qb_mem           -- `Q(B) ∈ (ℂ ⊕ 𝒱^∅)(B)` (by `prop:Loc` (iv), (v))
#check @Step.uVnext_spec      -- Definition `def:V+` holds on every block
#check @Step.coup_injective
#check @Step.ZVK              -- Proposition `prop:ZVK`: `𝔼 θ Z_j = Z_{j+1}`
#check @Step.Knext_union      -- ... factorisation
#check @Step.InK_Knext        -- ... `K_{j+1} ∈ 𝒦_{j+1}`
#check @Step.ZVK'
#check @Step.uVnext_local     -- Proposition `prop:consistency` (locality)
#check @Step.Knext_local

/-! ## Section `sec:step` -/

#check @Step.Knext_eq_decomp  -- `e:KminuscL`
#check @Step.coupling_bounds  -- `E:Q`, `E:vj`, `e:step-V`
#check @Step.smallset_bound   -- Proposition `prop:SmallSetLin`
#check @Step.largeset_bound   -- Proposition `prop:LargeSetLin`
#check @Step.nonlinear_bound  -- Lemma `lem:Ri-bd`
#check @Step.step             -- Theorem `thm:step`
#check @Step.goodCov_Cfrd     -- the covariances `C_{j+1}` of `sec:frd` satisfy `GoodCov`
#check @Step.goodCov_CfrdN    -- ... and `C_N` for the last step
#check @Step.Knext_continuousOn_msq  -- continuity in `m² ≥ 0`
#check @Step.uVnext_continuousOn_msq

/-! ## `thm:step`: the maps are entire, with bounded derivatives -/

#check @Step.Knext_hol        -- `K_{j+1}` is holomorphic in `(V_j, K_j)`
#check @Step.uVnext_lin       -- `(u_{j+1}, V_{j+1})` is linear in `(V_j, K_j)`
#check @Step.step_deriv       -- derivative, Lipschitz and linearisation bounds
#check @Step.coupling_deriv

/-! ## Axioms -/

#print axioms Step.comb1
#print axioms Step.ZVK
#print axioms Step.ZVK'
#print axioms Step.InK_Knext
#print axioms Step.Knext_local
#print axioms Step.uVnext_spec
#print axioms Step.step
#print axioms Step.goodCov_Cfrd
#print axioms Step.goodCov_CfrdN
#print axioms Step.Knext_continuousOn_msq
#print axioms Step.uVnext_continuousOn_msq
#print axioms Step.step_deriv
#print axioms Step.Knext_hol
