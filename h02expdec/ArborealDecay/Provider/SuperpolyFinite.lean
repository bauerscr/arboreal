module

public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Final
public import ArborealDecay.Provider.BCHSInputs

/-!
# Provider for the frozen anchor `ArborealDecay.superpoly_finite`

Proves the exact frozen statement from `ArborealDecay.Final.superpoly_finite_of_AC`,
discharging the BCHS identities (A), (C) with `ArborealDecay.BCHS`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay

/-- **Proposition `prop:superpoly`, finite subgraphs** (note L924–933). -/
theorem superpoly_finite (β : ℝ) (hβ : 0 ≤ β) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (W : EdgeWeights Λ),
        (∀ x y : Λ, W.w x y ≠ 0 → IsNN x y) →
        (∀ x y : Λ, W.w x y ≤ β) →
        ∀ x z : Λ, twoPoint W x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + supDist x z) ^ 2)) :=
  ArborealDecay.Final.superpoly_finite_of_AC identityA identityC β hβ

end ArborealDecay.Provider

end
