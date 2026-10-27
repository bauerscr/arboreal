module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestWeight

/-!
# Frozen declaration `ArborealDecay.partitionFunction`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

open Classical in
/-- The partition function `Z_G(w) = ∑_{F ∈ 𝓕(G)} w(F)` (eq:forest-measure). -/
noncomputable def partitionFunction (W : EdgeWeights V) : ℝ :=
  ∑ F : SimpleGraph V with F.IsAcyclic, forestWeight W F

end ArborealDecay

end
