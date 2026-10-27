import PtCorr2.Zero.Restrict
import Obs2.Map.Ops

/-!
# The zero mode of the last scale with source fields

At the last scale the zero mode `t_raw Q` is integrated exactly (`Rc_ECC_cstC_even`). With source
fields (`Obs.SA`, `F = F_∅ + σ_aF_a + σ_bF_b + σ_aσ_bF_ab`) the integration acts componentwise
(`Obs2.ECCO`, `Obs.thetaO`). The components that are even elements of the Grassmann algebra are
integrated by the same formula:

* `Rc_ECCO_cstC_e`, `Rc_ECCO_cstC_ab` (both cases): the bulk and the `σ_aσ_b` components;
* `Rc_ECCO_cstC_two` (Case 2, commuting sources, all four components even): also `F_a`, `F_b`;
* `eps_ECCO_cstC`: the readout `ε((𝔼_{cQ}θF)_•) = ε(F_•) - c F_•²` (`F_•² = c2 F_•`).

So, once an observable final object `F` at scale `N` is available, its contribution to the
one-point function `⟨ψ̄_aψ_a⟩` (Case 2, component `a`) and to the two-point function (component
`ab`, both cases) after the zero mode is `ε(F_•) - t_raw F_•²`, the analogue of
`1 + ũ_{N,N} = ε(F_∅) - t_raw F_∅²` (`prop_ZNN2`).
-/

namespace PtCorr2

noncomputable section

open Finset Grassmann Suscept Step Obs Obs.SA Obs2

set_option linter.unusedSectionVars false

variable {Λ : Type*} [DecidableEq Λ] [Fintype Λ] [Nonempty Λ] {c : Obs.Case}

/-- The `ε`-readout of `Rc_ECC_cstC_even`: `ε(𝔼_{cQ}θF) = ε F - c F²` for even `F`. -/
theorem eps_ECC_cstC_even (cc : ℂ) {F : Grassmann.N Λ} (hF : inv' F = F) :
    ε (ECC (cstC Λ cc) (theta F)) = ε F - cc * c2 F := by
  have h := congrArg ε (Rc_ECC_cstC_even (Λ := Λ) cc hF)
  rwa [ε_Rc, map_add, map_smul, ε_PP, smul_zero, add_zero, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply] at h

/-- Bulk component: `Rc (𝔼_{cQ}θF)_∅ = (ε F_∅ - c F_∅²) + F_∅² ψψ̄`. -/
theorem Rc_ECCO_cstC_e (cc : ℂ) (F : OE c Λ) :
    Rc Λ ((ECCO (cstC Λ cc) (thetaO F) : SA c Λ).e) =
      algebraMap ℂ (Grassmann.N Λ) (ε (F : SA c Λ).e - cc * c2 (F : SA c Λ).e) +
        c2 (F : SA c Λ).e • (psiC Λ * psibarC Λ) :=
  Rc_ECC_cstC_even cc (mem_OEv.1 F.2).1

/-- `σ_aσ_b` component (both cases): `Rc (𝔼_{cQ}θF)_ab = (ε F_ab - c F_ab²) + F_ab² ψψ̄`. -/
theorem Rc_ECCO_cstC_ab (cc : ℂ) (F : OE c Λ) :
    Rc Λ ((ECCO (cstC Λ cc) (thetaO F) : SA c Λ).ab) =
      algebraMap ℂ (Grassmann.N Λ) (ε (F : SA c Λ).ab - cc * c2 (F : SA c Λ).ab) +
        c2 (F : SA c Λ).ab • (psiC Λ * psibarC Λ) :=
  Rc_ECC_cstC_even cc (mem_OEv.1 F.2).2.2.2

/-- In Case 2 the components `F_a`, `F_b` of an even element are even. -/
theorem obsTwo_a_b_even (F : OE .two Λ) :
    inv' (F : SA .two Λ).a = (F : SA .two Λ).a ∧ inv' (F : SA .two Λ).b = (F : SA .two Λ).b := by
  obtain ⟨-, h2, h3, -⟩ := mem_OEv.1 F.2
  simp only [Case.s_two, one_smul] at h2 h3
  exact ⟨h2, h3⟩

/-- **Case 2, the source components**: `Rc (𝔼_{cQ}θF)_a = (ε F_a - c F_a²) + F_a² ψψ̄`, and the
same for `b`. -/
theorem Rc_ECCO_cstC_two (cc : ℂ) (F : OE .two Λ) :
    Rc Λ ((ECCO (cstC Λ cc) (thetaO F) : SA .two Λ).a) =
        algebraMap ℂ (Grassmann.N Λ) (ε (F : SA .two Λ).a - cc * c2 (F : SA .two Λ).a) +
          c2 (F : SA .two Λ).a • (psiC Λ * psibarC Λ) ∧
      Rc Λ ((ECCO (cstC Λ cc) (thetaO F) : SA .two Λ).b) =
        algebraMap ℂ (Grassmann.N Λ) (ε (F : SA .two Λ).b - cc * c2 (F : SA .two Λ).b) +
          c2 (F : SA .two Λ).b • (psiC Λ * psibarC Λ) :=
  ⟨Rc_ECC_cstC_even cc (obsTwo_a_b_even F).1, Rc_ECC_cstC_even cc (obsTwo_a_b_even F).2⟩

/-- **The readout after the zero mode**: `ε((𝔼_{cQ}θF)_•) = ε(F_•) - c F_•²` for the bulk and
`σ_aσ_b` components (both cases), and for `σ_a`, `σ_b` in Case 2. -/
theorem eps_ECCO_cstC (cc : ℂ) (F : OE c Λ) :
    ε ((ECCO (cstC Λ cc) (thetaO F) : SA c Λ).e) = ε (F : SA c Λ).e - cc * c2 (F : SA c Λ).e ∧
      ε ((ECCO (cstC Λ cc) (thetaO F) : SA c Λ).ab) =
        ε (F : SA c Λ).ab - cc * c2 (F : SA c Λ).ab :=
  ⟨eps_ECC_cstC_even cc (mem_OEv.1 F.2).1, eps_ECC_cstC_even cc (mem_OEv.1 F.2).2.2.2⟩

theorem eps_ECCO_cstC_two (cc : ℂ) (F : OE .two Λ) :
    ε ((ECCO (cstC Λ cc) (thetaO F) : SA .two Λ).a) =
        ε (F : SA .two Λ).a - cc * c2 (F : SA .two Λ).a ∧
      ε ((ECCO (cstC Λ cc) (thetaO F) : SA .two Λ).b) =
        ε (F : SA .two Λ).b - cc * c2 (F : SA .two Λ).b :=
  ⟨eps_ECC_cstC_even cc (obsTwo_a_b_even F).1, eps_ECC_cstC_even cc (obsTwo_a_b_even F).2⟩

end

end PtCorr2
