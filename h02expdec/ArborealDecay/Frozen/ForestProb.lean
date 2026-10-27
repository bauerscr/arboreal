module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestWeight
public import ArborealDecay.Frozen.PartitionFunction

/-!
# Frozen declaration `ArborealDecay.forestProb`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

open Classical in
/-- The arboreal-gas probability `μ_{G,w}(P) = Z_G(w)⁻¹ ∑_{F ∈ 𝓕(G), P F} w(F)`. -/
noncomputable def forestProb (W : EdgeWeights V) (P : SimpleGraph V → Prop) : ℝ :=
  (∑ F : SimpleGraph V with F.IsAcyclic ∧ P F, forestWeight W F) / partitionFunction W

end ArborealDecay

end
