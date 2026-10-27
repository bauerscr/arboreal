module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights

/-!
# Frozen declaration `ArborealDecay.EdgeWeights.map`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

open Classical in
/-- Identification of vertices along `f : V → V'` (`G/S`, `G/(a=b)`, `G/A`): the edge
weights between distinct image vertices are summed (parallel edges summed), and edges whose
endpoints are identified become loops and are discarded. -/
noncomputable def EdgeWeights.map {V' : Type*} (W : EdgeWeights V) (f : V → V') :
    EdgeWeights V' where
  w a b := if a = b then 0 else ∑ u with f u = a, ∑ v with f v = b, W.w u v
  symm a b := by
    by_cases h : a = b
    · simp [h]
    · simp only [h, Ne.symm h, ite_false]; rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => W.symm _ _
  nonneg a b := by
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => W.nonneg _ _

end ArborealDecay

end
