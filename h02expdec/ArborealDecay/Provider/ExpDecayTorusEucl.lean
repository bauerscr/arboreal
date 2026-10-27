module

public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.TorusUniform
public import ArborealDecay.Frozen.TorusEuclNorm
public import ArborealDecay.Final
public import ArborealDecay.Provider.BCHSInputs

/-!
# Provider for the frozen anchor `ArborealDecay.expDecay_torus_eucl`

Proves the exact frozen statement from `ArborealDecay.Final.expDecay_torus_eucl_of_AC`,
discharging the BCHS identities (A), (C) with `ArborealDecay.BCHS`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay

/-- **Theorem `thm:main`, Euclidean consequence** (note L89–93): uniform in `L`. -/
theorem expDecay_torus_eucl (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (L : ℕ) [NeZero L] (x : ZMod L × ZMod L),
        twoPoint (torusUniform L β hβ) 0 x ≤ C * Real.exp (-c * torusEuclNorm L x) :=
  ArborealDecay.Final.expDecay_torus_eucl_of_AC identityA identityC β hβ

end ArborealDecay.Provider

end
