module

import ArborealDecay.Frozen.ExpDecayFinite
import ArborealDecay.Frozen.ExpDecayTorus
import ArborealDecay.Frozen.ExpDecayTorusEucl

/-!
# Audit of `h02expdec-lean.tex` (exponential decay for the arboreal gas in `d = 2`)

The three theorems stated in `h02expdec-lean.tex` (`ArborealDecay/Frozen/ExpDecay*.lean`), with
`#check` and `#print axioms`, and the definitions used in their statements. Not part of the
`ArborealDecay` library (nothing imports it).

Run with `lake env lean Audit/ExpDecay.lean` after `lake build`. Expected axioms: `propext`,
`Classical.choice`, `Quot.sound`.
-/

/-! ## Theorems -/

-- thm:finite: finite `Λ ⊆ ℤ²`, nearest-neighbour weights `0 ≤ w ≤ β`:
-- `τ_{Λ,w}(x, y) ≤ 2 exp(−c d_∞(x, y))`.
#check ArborealDecay.expDecay_finite
#print axioms ArborealDecay.expDecay_finite

-- thm:torus: the same on `𝕋_L = (ℤ/Lℤ)²`, uniformly in `L ≥ 1`, toroidal `ℓ^∞` distance.
#check ArborealDecay.expDecay_torus
#print axioms ArborealDecay.expDecay_torus

-- thm:euclidean: constant weight `β` on `𝕋_L`: `P_{L,β}(0 ↔ x) ≤ C exp(−c |x|_{2,L})`.
#check ArborealDecay.expDecay_torus_eucl
#print axioms ArborealDecay.expDecay_torus_eucl

/-! ## Definitions used in the statements -/

-- The arboreal gas: weights, forest weight, partition function, event probability, two-point function.
#print ArborealDecay.EdgeWeights
#print ArborealDecay.forestWeight
#print ArborealDecay.partitionFunction
#print ArborealDecay.forestProb
#print ArborealDecay.twoPoint

-- Geometry of `ℤ²`.
#print ArborealDecay.IsNN
#print ArborealDecay.supDist

-- Geometry of the torus and the uniform weights.
#print ArborealDecay.IsTorusNN
#print ArborealDecay.torusSupDist
#print ArborealDecay.torusEuclNorm
#print ArborealDecay.torusUniform
