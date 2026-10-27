module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestProb

/-!
# Frozen declaration `ArborealDecay.twoPoint`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

/-- The two-point connectivity `τ_G(x,y) = μ_{G,w}(x ↔ y)`. -/
noncomputable def twoPoint (W : EdgeWeights V) (x y : V) : ℝ :=
  forestProb W fun F => F.Reachable x y

end ArborealDecay

end
