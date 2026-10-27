module

public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.IsTorusNN
public import ArborealDecay.Frozen.TorusSupDist
public import ArborealDecay.Final
public import ArborealDecay.Provider.BCHSInputs

/-!
# Provider for the frozen anchor `ArborealDecay.expDecay_torus`

Proves the exact frozen statement from `ArborealDecay.Final.expDecay_torus_of_AC`,
discharging the BCHS identities (A), (C) with `ArborealDecay.BCHS`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay

/-- **Theorem `thm:main`, torus** (note L88–89). -/
theorem expDecay_torus (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (W : EdgeWeights (ZMod L × ZMod L)),
        (∀ x y, W.w x y ≠ 0 → IsTorusNN L x y) →
        (∀ x y, W.w x y ≤ β) →
        ∀ x y, twoPoint W x y ≤ 2 * Real.exp (-c * torusSupDist L x y) :=
  ArborealDecay.Final.expDecay_torus_of_AC identityA identityC β hβ

end ArborealDecay.Provider

end
