module

public import ArborealDecay.Bridge
public import ArborealDecay.SimonLieb

/-!
# Provider for the frozen anchor `IncidentNC`

Proves the exact frozen statement from the verified libraries via `ArborealDecay.Bridge`.
-/

@[expose] public section

namespace ArborealDecay.Provider

open ArborealDecay ArborealDecay.Bridge

variable {V : Type*} [Fintype V]

theorem incident_NC (W : EdgeWeights V) (A : SimpleGraph V) (hA : A.IsAcyclic)
    (p i q j : V) (hpq : A.Reachable p q) (hef : s(p, i) ≠ s(q, j)) :
    forestProb W (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet ∧ s(q, j) ∈ F.edgeSet) *
        forestProb W (fun F => A ≤ F) ≤
      forestProb W (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet) *
        forestProb W (fun F => A ≤ F ∧ s(q, j) ∈ F.edgeSet) := by
  classical
  simp only [forestProb_eq]
  exact ArborealDecay.SimonLieb.incident_NC W.symm W.nonneg A hA p i q j hpq hef

end ArborealDecay.Provider

end
