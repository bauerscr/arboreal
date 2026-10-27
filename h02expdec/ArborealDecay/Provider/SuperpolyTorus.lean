module

public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.Final
public import ArborealDecay.Provider.BCHSInputs

/-!
# Provider for the frozen anchor `ArborealDecay.superpoly_torus`

Proves the exact frozen statement from `ArborealDecay.Final.superpoly_torus_of_AC`,
discharging the BCHS identities (A), (C) with `ArborealDecay.BCHS`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay

/-- **Proposition `prop:superpoly`, torus** (note L934). -/
theorem superpoly_torus (β : ℝ) (hβ : 0 ≤ β) :
    ∃ A a : ℝ, 0 < A ∧ 0 < a ∧
      ∀ (L : ℕ) [NeZero L] (W : EdgeWeights (ZMod L × ZMod L)),
        (∀ x y, W.w x y ≠ 0 → IsTorusNN L x y) →
        (∀ x y, W.w x y ≤ β) →
        ∀ x z, twoPoint W x z ≤
          min 1 (A * Real.exp (-a * Real.log (2 + torusSupDist L x z) ^ 2)) :=
  ArborealDecay.Final.superpoly_torus_of_AC identityA identityC β hβ

end ArborealDecay.Provider

end
