module

public import ArborealDecay.BCHS
public import ArborealDecay.TLaw

/-!
# The BCHS identities (A) and (C) in the form consumed by `ArborealDecay.Final`

Packages `ArborealDecay.BCHS.Z_eq_Zforest` and `ArborealDecay.BCHS.expect_Hinv_eq`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay.TLaw

theorem identityA :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm) :=
  fun _ _ _ w hW hconn ρ => ArborealDecay.BCHS.Z_eq_Zforest w hW hconn ρ

theorem identityC :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ) :=
  fun _ _ _ w hW hconn ρ i j => ArborealDecay.BCHS.expect_Hinv_eq w hW hconn ρ i j

end ArborealDecay.Provider

end
