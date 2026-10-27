module

public import ArborealDecay.Frozen.EdgeWeightsGraph
public import ArborealDecay.Bridge
public import ArborealDecay.SimonLieb

/-!
# Provider for the frozen anchor `SimonLieb`

Proves the exact frozen statement from the verified libraries via `ArborealDecay.Bridge`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay ArborealDecay.Bridge

variable {V : Type*} [Fintype V]

open Classical in
theorem simon_lieb (W : EdgeWeights V) (D : Finset V) (x z : V) (hx : x ∈ D)
    (hz : z ∉ D) :
    twoPoint W x z ≤
      ∑ u ∈ D, ∑ v ∈ Dᶜ, if W.graph.Adj u v then
        forestProb W (fun F => F.Adj u v) * twoPoint W x u * twoPoint W v z else 0 := by
  simp only [twoPoint_eq, forestProb_eq]
  convert ArborealDecay.SimonLieb.simon_lieb W.symm W.nonneg D x z hx hz using 4; exact Iff.rfl

end ArborealDecay.Provider

end
