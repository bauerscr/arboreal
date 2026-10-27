-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.EdgeWeightsGraph
public import ArborealDecay.Frozen.EdgeWeightsMap
public import ArborealDecay.Frozen.Collapse
public import ArborealDecay.Provider.SeparatorWiring

/-!
# Frozen declaration `ArborealDecay.separator_wiring`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

/-- **Proposition `prop:separator-wiring`** (note L484–491). -/
theorem separator_wiring [DecidableEq V] (W : EdgeWeights V) (a b : V) (S : Finset V)
    (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : W.graph.Walk a b, ∃ s ∈ S, s ∈ p.support) :
    twoPoint W a b ≤ twoPoint (W.map (collapse S)) (collapse S a) (collapse S b) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.separator_wiring W a b S ha hb hsep
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
