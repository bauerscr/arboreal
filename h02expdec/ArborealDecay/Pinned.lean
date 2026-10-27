module

public import ArborealDecay.Pinned.Unpinned
public import ArborealDecay.Pinned.Pinning
public import ArborealDecay.Pinned.Transport
public import ArborealDecay.Pinned.Main
public import ArborealDecay.Pinned.Relabel
public import ArborealDecay.Pinned.TreeEval
public import ArborealDecay.Pinned.ForestInsert
public import ArborealDecay.Pinned.Ghost

/-!
# The `ℍ^{0|2}` pinned Green-event identity (supplement §7)

Main results (namespace `ArborealDecay.Pinned`):
* `thm_H02_pinned` (supplement `thm:H02-pinned` (iii)),
  `thm_H02_pinned_denominator` (i), `thm_H02_pinned_numerator` (ii);
* `cor_pinned_fermion` (`cor:pinned-fermion`), `lem_pinning` (`lem:pinning`);
* `expect_ξη_forest`, `lem_ghost_Z`, `lem_ghost_event` (`lem:ghost` (iii));
* `lem_leaf` (`lem:leaf`), `prop_tree_eval` (`prop:tree-eval` (i), (ii)),
  `int0_eq_zero_of_odd` (`lem:berezin` (e)).
-/
