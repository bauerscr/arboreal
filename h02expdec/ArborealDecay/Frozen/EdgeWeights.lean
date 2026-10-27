module

public import Mathlib

/-!
# Frozen declaration `ArborealDecay.EdgeWeights`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

/-- Symmetric nonnegative edge weights `w_{ij}` on a vertex type `V`.

The underlying graph is the support `{ij : i ≠ j, w_{ij} ≠ 0}`: zero-weight edges are
deleted, loops are discarded (diagonal values play no role), and parallel edges are
represented by the sum of their weights (note, L77–79). -/
structure EdgeWeights (V : Type*) where
  /-- The weight `w_{ij}`. -/
  w : V → V → ℝ
  symm : ∀ i j, w i j = w j i
  nonneg : ∀ i j, 0 ≤ w i j

end ArborealDecay

end
