module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestWeight

/-!
# Frozen declaration `ArborealDecay.forestPolynomial`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

open Classical in
/-- The vertex-field forest polynomial `P_G(h)` (eq:PG-def). -/
noncomputable def forestPolynomial (W : EdgeWeights V) : MvPolynomial V ℝ :=
  ∑ F : SimpleGraph V with F.IsAcyclic, MvPolynomial.C (forestWeight W F) *
    ∏ T : F.ConnectedComponent,
      (1 + ∑ i with F.connectedComponentMk i = T, MvPolynomial.X i)

end ArborealDecay

end
