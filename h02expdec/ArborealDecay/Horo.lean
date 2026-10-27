module

public import ArborealDecay.Horo.Diffeo
public import ArborealDecay.Horo.Dot
public import ArborealDecay.Horo.Shift
public import ArborealDecay.Horo.Rescale
public import ArborealDecay.Horo.Schwartz
public import ArborealDecay.Horo.MultiShift
public import ArborealDecay.Horo.ShiftFun
public import ArborealDecay.Horo.SuperChange
public import ArborealDecay.Horo.TSide

/-!
# Horospherical coordinates (BCHS Proposition 2.9, first layers)

The bosonic horospherical diffeomorphism and its Jacobian, the `ℍ^{2|4}` inner product in
horospherical coordinates, invariance of Lebesgue integrals under nilpotent changes of generators
`x ↦ x + g(x) n`, the rescaling `ξ = eᵗψ` of odd generators, the full horospherical change of
generators (2.73) with Berezinian `z e^{−3t}` (`integral_berezin_horo_H24`), and the
`s`-integration on the `(t, s)` side (`integral_exp_neg_Htil`, `integral_ss_exp_neg_Htil`).
See `docs/design/horo.md`.
-/
