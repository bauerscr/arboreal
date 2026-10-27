module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights

/-!
# Frozen declaration `ArborealDecay.forestWeight`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

open Classical in
/-- The weight `w(F) = ∏_{e ∈ F} w_e` of a spanning forest `F` (eq:forest-measure). -/
noncomputable def forestWeight (W : EdgeWeights V) (F : SimpleGraph V) : ℝ :=
  ∏ e ∈ F.edgeFinset, Sym2.lift ⟨W.w, W.symm⟩ e

end ArborealDecay

end
