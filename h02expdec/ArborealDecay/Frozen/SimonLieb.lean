-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestProb
public import ArborealDecay.Frozen.TwoPoint
public import ArborealDecay.Frozen.EdgeWeightsGraph
public import ArborealDecay.Provider.SimonLieb

/-!
# Frozen declaration `ArborealDecay.simon_lieb`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

open Classical in
/-- **Proposition `prop:Simon-Lieb`** (note L1036–1044). -/
theorem simon_lieb (W : EdgeWeights V) (D : Finset V) (x z : V) (hx : x ∈ D)
    (hz : z ∉ D) :
    twoPoint W x z ≤
      ∑ u ∈ D, ∑ v ∈ Dᶜ, if W.graph.Adj u v then
        forestProb W (fun F => F.Adj u v) * twoPoint W x u * twoPoint W v z else 0 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.simon_lieb W D x z hx hz
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
