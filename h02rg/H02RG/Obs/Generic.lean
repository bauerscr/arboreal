import Obs.GenericDefs
import Obs.GenericZVK
import Obs.GenericDecomp
import Obs.GenericStructure
import Obs.GenericBridge

/-!
# The generic renormalisation group map (Section `sec:obs-flow`)

The renormalisation group map of Section `sec:step-def` over general commutative
`ℂ`-algebras `R`, `R2` with `θ, ι : R →ₐ[ℂ] R2` and `E : R2 →ₗ[ℂ] R`, so that it applies both
to the bulk and to the algebra with observables.

* `Obs.GenericDefs`: the data (`RGAlg`, `RGIngr`) and the map (`KnextG`, `ZjG`, `ZnextG`, …);
* `Obs.GenericZVK`: Proposition `prop:ZVK`, `E θ Z_j = Z_{j+1}` (`ZVK_G`);
* `Obs.GenericDecomp`: `K_{j+1} = 𝓛 + 𝓡¹ + 𝓡² + 𝓡³` (`KnextG_eq_decomp`);
* `Obs.GenericStructure`: factorisation over non-touching polymers (`KnextG_union`,
  `KnextG_eq_KextG`, `ZVK_G'`), the membership principle (`SuppHyp.KnextG_mem`) and
  compatibility with homomorphisms (`map_KnextG`, `map_ZnextG`, …);
* `Obs.GenericBridge`: the bulk map of `Step` is the instance `bulkA C`, `bulkI j C V K`
  (`KnextG_bulk`, `ZjG_bulk`, `ZnextG_bulk`, `ZVK_bulk`, `Knext_union_bulk`, `ZVK'_bulk`).
-/
