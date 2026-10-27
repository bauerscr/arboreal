import Spin2.Pair.PairFinal5
import Spin2.Pair.PairDef5eD
import Spin2.Final.FinalMultiscale

/-!
# The final assembly with the non-seed pair layer (`PairDefSizesNF`)

* **`FwPairConclND`**, **`fw_pairAbove5_atD`**, **`fw_pairAbove5_MFD'`**: `PairFinal5ConclD`,
  `pairAbove_final5_atD`, `pairAbove_final5_MFD'` without `GamLastRem(S)` (copies; `GamTopBd`
  from `MasterFacts.fw_gamTopBdD`, as `fw_pairAbove_atD` does for `pairAbove_final4_atD`).
* **`fwKE5`**, **`fwK5`**, **`MasterFacts.fw_multiscale_traj5`**: `fw_multiscale_traj` (copy) from
  `FwPairConclND`, pair inputs `PairDefSizesNF c_d` and `PairZeroRemAB e₁ e₂`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

end MasterFacts

end

end Spin2
