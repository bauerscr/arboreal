module

public import ArborealDecay.TLaw.Defs
public import ArborealDecay.TLaw.Elem
public import ArborealDecay.TLaw.Integral
public import ArborealDecay.TLaw.Finite
public import ArborealDecay.TLaw.PosDef
public import ArborealDecay.TLaw.Steps
public import ArborealDecay.TLaw.Sabot
public import ArborealDecay.TLaw.Cor

/-!
# The pinned `t`-law and BCHS Lemma 4.1

Aggregator for `ArborealDecay/TLaw/*`: the pinned `t`-law of supplement `def:tlaw`
(`ArborealDecay.TLaw.density`, `Z`, `expect`), the tree expansion of `D` (`D_eq_treeSum`),
positivity (`D_pos`, `Lmat_posDef`, `Hmat_posDef`), change of root (`D_root_change`),
finiteness of exponential moments (`lintegral_exp_mul_density_lt_top`, `Z_lt_top`), the
elementary inequalities of `lem:elem`, BCHS Lemma 4.1 (`sabot`, `sabot_bchs`) and
`cor:sabot` (`sabot_two_thirds`, `sabot_one_third`). See `docs/design/tlaw.md`.
-/
