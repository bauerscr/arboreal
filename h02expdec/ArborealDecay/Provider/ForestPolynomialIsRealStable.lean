module

public import ArborealDecay.Frozen.IsRealStable
public import ArborealDecay.Bridge

/-!
# Provider for the frozen anchor `ForestPolynomialIsRealStable`

Proves the exact frozen statement from the verified libraries via `ArborealDecay.Bridge`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay ArborealDecay.Bridge

variable {V : Type*} [Fintype V]

theorem forestPolynomial_isRealStable (W : EdgeWeights V) :
    IsRealStable (forestPolynomial W) := by
  classical
  rw [forestPolynomial_eq]
  exact ArborealDecay.ForestPoly.forestPolynomial_isRealStable W.w W.symm W.nonneg

end ArborealDecay.Provider

end
