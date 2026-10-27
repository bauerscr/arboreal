module

public import ArborealDecay.ForestPoly.Defs
public import ArborealDecay.ForestPoly.Gaussian
public import ArborealDecay.ForestPoly.Operator
public import ArborealDecay.ForestPoly.Stable

/-!
# The forest polynomial `P_G`: operator identity and real stability

* `ArborealDecay.ForestPoly.operator_identity` (note lem:operator-identity, Grassmann proof):
  `P_G = ∏_{{i,j}} (1 - β_ij ∂ᵢ ∂ⱼ) D_G`.
* `ArborealDecay.ForestPoly.forestPolynomial_isRealStable` (note lem:PG-stable).
-/
