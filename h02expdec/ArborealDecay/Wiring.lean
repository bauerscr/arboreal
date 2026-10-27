module

public import ArborealDecay.Wiring.Expand
public import ArborealDecay.Wiring.Poly
public import ArborealDecay.Wiring.PolyProps
public import ArborealDecay.Wiring.Stable
public import ArborealDecay.Wiring.Star
public import ArborealDecay.Wiring.Contract
public import ArborealDecay.Wiring.Events
public import ArborealDecay.Wiring.Indep
public import ArborealDecay.Wiring.Gamma
public import ArborealDecay.Wiring.Main

/-!
# Separator-wiring monotonicity (`prop:separator-wiring`)

Aggregator.  Main results (namespace `ArborealDecay.Wiring`):

* `separator_wiring_of_stable`: `τ_G(a, b) ≤ τ_{G/S}(a, b)` for a vertex separator `S`, assuming
  real stability of the forest polynomial (`hstab`);
* `separator_wiring`: the unconditional statement.

Route: `p(x, y, s)` is `P_G` with the vertex variables outside `{a, b} ∪ S` set to zero
(`Wiring.Poly`, `Wiring.Stable`: stable, multi-affine, positive coefficients); the squarefree
coefficients of `p` are `∑_F w(F) [labelled vertices in distinct components of F]` (`coeff_wpoly`);
the forest bijection with `Γ = G/S` (`Wiring.Star`, `Wiring.Contract`, `Wiring.Events`) and the
one-vertex-union independence (`Wiring.Gamma`, `Wiring.Indep`) give `eq:p-topS`; then the stable
separator lemma (`ArborealDecay.Separator.stable_separator`) with `A = 1/r_a`, `B = 1/r_b`.
-/
