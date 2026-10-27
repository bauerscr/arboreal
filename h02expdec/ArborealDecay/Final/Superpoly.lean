module

public import ArborealDecay.Final.Common
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.Frozen.TorusUniform
public import ArborealDecay.Frozen.TorusEuclNorm
public import ArborealDecay.Frozen.EdgeWeightsMap
public import ArborealDecay.Frozen.SupNorm
public import ArborealDecay.Frozen.AnnulusCollapse

/-!
# Final assembly: `superpoly_finite`, `superpoly_torus` from (A), (C)
-/

@[expose] public section

namespace ArborealDecay.Final

open ArborealDecay.TLaw ArborealDecay.Wiring ArborealDecay.CondComb ArborealDecay.Bridge

/-- Frozen `superpoly_finite`, conditional only on (A), (C). -/
theorem superpoly_finite_of_AC
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (W : ArborealDecay.EdgeWeights Λ),
        (∀ x y : Λ, W.w x y ≠ 0 → ArborealDecay.IsNN x y) →
        (∀ x y : Λ, W.w x y ≤ β) →
        ∀ x z : Λ, ArborealDecay.twoPoint W x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + ArborealDecay.supDist x z) ^ 2)) := by
  obtain ⟨A, a, hA0, ha0, h⟩ := ArborealDecay.Superpoly.superpoly_finite_of_inputs hW_lib
    (fun B hB => ArborealDecay.Annulus.annulus_of_inputs hA hC B hB) β hβ
  refine ⟨A, a, hA0, ha0, fun Λ W hnn hle x z => ?_⟩
  rw [twoPoint_eq]
  exact h Λ W.w W.symm W.nonneg hnn hle x z

/-- Frozen `superpoly_torus`, conditional only on (A), (C). -/
theorem superpoly_torus_of_AC
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (L : ℕ) [NeZero L] (W : ArborealDecay.EdgeWeights (ZMod L × ZMod L)),
        (∀ x y, W.w x y ≠ 0 → ArborealDecay.IsTorusNN L x y) →
        (∀ x y, W.w x y ≤ β) →
        ∀ x z, ArborealDecay.twoPoint W x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + ArborealDecay.torusSupDist L x z) ^ 2)) := by
  obtain ⟨A, a, hA0, ha0, h⟩ := ArborealDecay.Superpoly.superpoly_torus_of_inputs hW_lib
    (fun B hB => ArborealDecay.Annulus.annulus_of_inputs hA hC B hB) β hβ
  refine ⟨A, a, hA0, ha0, fun L _ W hnn hle x z => ?_⟩
  rw [twoPoint_eq]
  exact h L W.w W.symm W.nonneg hnn hle x z

end ArborealDecay.Final

end
