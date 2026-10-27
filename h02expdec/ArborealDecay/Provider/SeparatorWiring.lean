module

public import ArborealDecay.Frozen.EdgeWeightsGraph
public import ArborealDecay.Frozen.Collapse
public import ArborealDecay.Bridge
public import ArborealDecay.Wiring

/-!
# Provider for the frozen anchor `SeparatorWiring`

Proves the exact frozen statement from the verified libraries via `ArborealDecay.Bridge`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay ArborealDecay.Bridge

variable {V : Type*} [Fintype V]

/-- **Proposition `prop:separator-wiring`** (note L484–491). -/
theorem separator_wiring [DecidableEq V] (W : EdgeWeights V) (a b : V) (S : Finset V)
    (ha : a ∉ S) (hb : b ∉ S)
    (hsep : ∀ p : W.graph.Walk a b, ∃ s ∈ S, s ∈ p.support) :
    twoPoint W a b ≤ twoPoint (W.map (collapse S)) (collapse S a) (collapse S b) := by
  rw [twoPoint_eq, twoPoint_eq]
  have h := ArborealDecay.Wiring.separator_wiring W.w W.symm W.nonneg a b S ha hb
    (fun p => by obtain ⟨s, hs, hm⟩ := hsep p; exact ⟨s, hm, hs⟩)
  convert h using 2
  · exact map_w_eq W (collapse S)
  · rfl

end ArborealDecay.Provider

end
