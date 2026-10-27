import Obs.MapEval
import Obs.MapLoc
import Obs.MapCoupling
import Obs.MapDef
import Obs.MapSupp
import Obs.MapFlow
import Obs.MapTri

/-!
# The renormalisation group map with observables (Section `sec:rgmap-ext`)

* `Obs.MapEval`: the block-additive (split) evaluation of observable coupling constants
  (deviation from `e:VobsX`, which is not additive over blocks);
* `Obs.MapLoc`: the extended (block diagonal) `Loc`, `Q(B)`, `J(B, X)`, and the image of
  `Q^obs(B)` (`QobsO_eq`);
* `Obs.MapCoupling`: `P^obs` (`e:Pobs-def`), Definition `def:V+obs` (`RHS_eq`, `sum_RHS_eq`),
  the next coupling constants `nextObs`, Lemma `lem:Pjj+1` (`PobsBB_eq`);
* `Obs.MapDef`: the observable renormalisation group map as an instance of the generic map
  (`obsA`, `obsI`, `KnextO`), its upper-triangular structure (`bulk_KnextO`),
  Proposition `prop:ZVK` (`ZVK_obs`, `ZVK_obs'`), and `def:V+`/`def:V+obs` together
  (`uVfull_spec`);
* `Obs.MapSupp`: supports with observables, locality and `U(1)` invariance of `K_{j+1}`
  (`InKO_KnextO`), factorisation (`KnextO_union`, `KnextO_eq_KextG`);
* `Obs.MapTri`: upper-triangular structure of the `a` component (`killO_KnextO`);
* `Obs.MapFlow`: the `ab` components vanish below the coalescence scale (`flow_ab`,
  `flow_ab_coal`).
-/
