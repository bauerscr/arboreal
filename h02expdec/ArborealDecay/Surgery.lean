module

public import ArborealDecay.Surgery.Defs
public import ArborealDecay.Surgery.Fibre
public import ArborealDecay.Surgery.Crit
public import ArborealDecay.Surgery.Core
public import ArborealDecay.Surgery.Bij
public import ArborealDecay.Surgery.Contract
public import ArborealDecay.Surgery.Cond
public import ArborealDecay.Surgery.Lift
public import ArborealDecay.Surgery.Cone
public import ArborealDecay.Surgery.Glue
public import ArborealDecay.Surgery.Union

/-!
# Graph surgery for the arboreal gas

* `ArborealDecay.Surgery.contract_sum`, `contract_sum_event`, `contract_pin_event`: contraction of
  a conditioned forest (`prop:incident-NC`), with the pushed-forward weights `mapW`;
  `condProb_adj`, `condProb_adj_adj`: conditional edge probabilities on the contraction.
* `Zforest_cone`, `cone_sum_event`, `arborealProb_cone`: vertex deletion, `Z_G = P_H(h)`.
* `sum_union_event`, `Zforest_union`, `arborealProb_union`, `arborealProb_reachable_union`:
  factorisation over a one-vertex union.
-/
