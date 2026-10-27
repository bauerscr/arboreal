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
# Final assembly: `annulus_bound` from (A), (C)
-/

@[expose] public section

namespace ArborealDecay.Final

open ArborealDecay.TLaw ArborealDecay.Wiring ArborealDecay.CondComb ArborealDecay.Bridge

/-- Frozen `annulus_bound`, conditional only on (A), (C). -/
theorem annulus_bound_of_AC
    (hA : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ ρ : V,
        Z w ρ (3 / 2) = ENNReal.ofReal (H02.Zforest w hW.symm))
    (hC : ∀ (V : Type) [Fintype V] [DecidableEq V] (w : V → V → ℝ) (hW : IsWGraph w),
      (supportGraph w).Connected → ∀ (ρ : V) (i j : {x // x ≠ ρ}),
        expect w ρ (3 / 2) (fun τ => (TLaw.Hmat w ρ (TLaw.ext ρ τ))⁻¹ i j) =
          H02.arborealProb w hW.symm (fun F => F.Reachable i j ∧ ¬ F.Reachable i ρ))
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
        (∀ z ∈ Λ, (r : ℤ) ≤ ArborealDecay.supNorm z ∧ ArborealDecay.supNorm z ≤ 2 * r) →
        ∀ W : ArborealDecay.EdgeWeights Λ,
          (∀ x y : Λ, W.w x y ≠ 0 → ArborealDecay.IsNN x y) →
          (∀ x y : Λ, W.w x y ≤ β) →
          ArborealDecay.twoPoint (W.map (ArborealDecay.annulusCollapse r Λ))
            (Sum.inl false) (Sum.inl true) ≤ C * (r : ℝ) ^ (-κ) := by
  obtain ⟨C, κ, hC0, hκ, h⟩ := ArborealDecay.Annulus.annulus_of_inputs hA hC β hβ
  refine ⟨C, κ, hC0, hκ, fun r hr Λ hΛ W hnn hle => ?_⟩
  rw [twoPoint_eq, arborealProb_congr (map_w_eq W (ArborealDecay.annulusCollapse r Λ))
    (ArborealDecay.Surgery.mapW_symm W.symm _)]
  exact h r hr Λ hΛ W.w W.symm W.nonneg hnn hle

end ArborealDecay.Final

end
