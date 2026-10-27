module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.collapse`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

/-- Collapse `S` to a single vertex `ρ = none`. -/
def collapse [DecidableEq V] (S : Finset V) (v : V) : Option {v : V // v ∉ S} :=
  if h : v ∈ S then none else some ⟨v, h⟩

end ArborealDecay

end
