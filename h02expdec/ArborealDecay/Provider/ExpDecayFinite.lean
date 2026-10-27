module

public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsNN
public import ArborealDecay.Frozen.SupDist
public import ArborealDecay.Final
public import ArborealDecay.Provider.BCHSInputs

/-!
# Provider for the frozen anchor `ArborealDecay.expDecay_finite`

Proves the exact frozen statement from `ArborealDecay.Final.expDecay_finite_of_AC`,
discharging the BCHS identities (A), (C) with `ArborealDecay.BCHS`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay

/-- **Theorem `thm:main`, finite subgraphs of `ℤ²`** (note L81–87). -/
theorem expDecay_finite (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Λ : Finset (ℤ × ℤ)) (W : EdgeWeights Λ),
        (∀ x y : Λ, W.w x y ≠ 0 → IsNN x y) →
        (∀ x y : Λ, W.w x y ≤ β) →
        ∀ x y : Λ, twoPoint W x y ≤ 2 * Real.exp (-c * supDist x y) :=
  ArborealDecay.Final.expDecay_finite_of_AC identityA identityC β hβ

end ArborealDecay.Provider

end
