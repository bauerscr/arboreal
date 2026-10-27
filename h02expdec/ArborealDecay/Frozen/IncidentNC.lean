-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestProb
public import ArborealDecay.Provider.IncidentNC

/-!
# Frozen declaration `ArborealDecay.incident_NC`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

/-- **Proposition `prop:incident-NC`**, with conditioning on a forest `A` (note L259–267),
stated multiplied through by `μ(A ⊆ F)²`. `e = pi`, `f = qj` are distinct edges incident to a
common vertex of `G/A` (`p` and `q` lie in one tree of `A`; `A = ⊥` is the unconditional case). -/
theorem incident_NC (W : EdgeWeights V) (A : SimpleGraph V) (hA : A.IsAcyclic)
    (p i q j : V) (hpq : A.Reachable p q) (hef : s(p, i) ≠ s(q, j)) :
    forestProb W (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet ∧ s(q, j) ∈ F.edgeSet) *
        forestProb W (fun F => A ≤ F) ≤
      forestProb W (fun F => A ≤ F ∧ s(p, i) ∈ F.edgeSet) *
        forestProb W (fun F => A ≤ F ∧ s(q, j) ∈ F.edgeSet) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.incident_NC W A hA p i q j hpq hef
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
