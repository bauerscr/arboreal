module

public import ArborealDecay.Superpoly.MapW
public import ArborealDecay.Superpoly.Equiv
public import ArborealDecay.Superpoly.Restrict
public import ArborealDecay.Superpoly.Level
public import ArborealDecay.Superpoly.Iter
public import ArborealDecay.Superpoly.Chain
public import ArborealDecay.Superpoly.Setup
public import ArborealDecay.Superpoly.Wired
public import ArborealDecay.Superpoly.Window
public import ArborealDecay.Superpoly.Annulus
public import ArborealDecay.Superpoly.Piece
public import ArborealDecay.Superpoly.PieceBound
public import ArborealDecay.Superpoly.Arith
public import ArborealDecay.Superpoly.Core
public import ArborealDecay.Superpoly.Diag
public import ArborealDecay.Superpoly.Finite
public import ArborealDecay.Superpoly.TorusPos
public import ArborealDecay.Superpoly.Torus

/-!
# Nested separators give the superpolynomial bound (§7)

Assembly of `prop:superpoly` from two inputs proved elsewhere:

* `(W)` separator-wiring monotonicity (`prop:separator-wiring`), and
* `(AN)` the wired-annulus bound (`prop:annulus`),

both taken as hypotheses in the `_of_inputs` theorems.

* `ArborealDecay.Superpoly.superpoly_finite_of_inputs`: finite nearest-neighbour subgraphs of `ℤ²`.
* `ArborealDecay.Superpoly.superpoly_torus_of_inputs`: the torus `(ℤ/L)²`.

Method: all separators (level sets of the sup-distance to the centre, radii `2^k r₀`) are wired
on one ambient type `Fin (m+1) ⊕ V` (`wireIter_of_inputs`, successive wirings compose:
`mapW_comp`), the wired graph factors over the chain of terminals (`chain_le`), and each
factor is a wired annulus (`piece_bound_of_inputs`).
-/
