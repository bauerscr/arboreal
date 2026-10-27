module

public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.EdgeWeightsMap
public import ArborealDecay.Frozen.SupNorm
public import ArborealDecay.Frozen.AnnulusCollapse
public import ArborealDecay.Final
public import ArborealDecay.Provider.BCHSInputs

/-!
# Provider for the frozen anchor `ArborealDecay.annulus_bound`

Proves the exact frozen statement from `ArborealDecay.Final.annulus_bound_of_AC`,
discharging the BCHS identities (A), (C) with `ArborealDecay.BCHS`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay

/-- **Proposition `prop:annulus`** (note L833–841): uniform over all nearest-neighbour
subgraphs of the annulus with weights at most `β`. -/
theorem annulus_bound (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧
      ∀ (r : ℕ), 2 ≤ r → ∀ (Λ : Finset (ℤ × ℤ)),
        (∀ z ∈ Λ, (r : ℤ) ≤ supNorm z ∧ supNorm z ≤ 2 * r) →
        ∀ W : EdgeWeights Λ,
          (∀ x y : Λ, W.w x y ≠ 0 → IsNN x y) →
          (∀ x y : Λ, W.w x y ≤ β) →
          twoPoint (W.map (annulusCollapse r Λ)) (Sum.inl false) (Sum.inl true) ≤
            C * (r : ℝ) ^ (-κ) :=
  ArborealDecay.Final.annulus_bound_of_AC identityA identityC β hβ

end ArborealDecay.Provider

end
