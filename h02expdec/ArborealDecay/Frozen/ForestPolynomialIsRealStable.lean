-- FROZEN_ANCHOR_PREFIX_BEGIN
module

public import Mathlib
public import ArborealDecay.Frozen.EdgeWeights
public import ArborealDecay.Frozen.ForestPolynomial
public import ArborealDecay.Frozen.IsRealStable
public import ArborealDecay.Provider.ForestPolynomialIsRealStable

/-!
# Frozen declaration `ArborealDecay.forestPolynomial_isRealStable`

Source: `h02expdec.tex`. Author-approved; see `FROZEN_MANIFEST.json`.
-/

@[expose] public section

namespace ArborealDecay

variable {V : Type*} [Fintype V]

/-- **Lemma `lem:PG-stable`** (note L194–196). -/
theorem forestPolynomial_isRealStable (W : EdgeWeights V) :
    IsRealStable (forestPolynomial W) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact ArborealDecay.Provider.forestPolynomial_isRealStable W
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end ArborealDecay

end
-- FROZEN_ANCHOR_SUFFIX_END
