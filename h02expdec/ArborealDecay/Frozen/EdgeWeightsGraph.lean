module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights

/-!
# Frozen declaration `ArborealDecay.EdgeWeights.graph`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

/-- The underlying simple graph `G` of the weights: `ij ∈ E ↔ i ≠ j ∧ w_{ij} ≠ 0`. -/
def EdgeWeights.graph (W : EdgeWeights V) : SimpleGraph V where
  Adj i j := i ≠ j ∧ W.w i j ≠ 0
  symm := ⟨fun i j h => ⟨h.1.symm, by rw [W.symm]; exact h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

end ArborealDecay

end
