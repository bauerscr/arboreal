import Spin2.Master.MasterAllRel
import Spin2.Master.MasterAllWK
import Spin2.Master.MasterAllGB
import Spin2.Master.MasterAllLastW
import Spin2.Master.MasterAllLastK
import Spin2.Master.MasterAllLastL1
import Spin2.Master.MasterAllTop
import Spin2.Master.MasterAllLastO
import Spin2.Master.MasterAllBase
import Spin2.Master.MasterAllConst
import Spin2.Master.MasterAllPairU
import Spin2.Master.MasterAllPairW

/-!
# The consolidated master theorem: `MasterFacts` and `thm_master_all`

`MasterFacts L` bundles, for **one** set of constants (those of `MasterCore L`, i.e. one call of
`thm_flow_masterLZ` with `allAReq`/`allEReq`), all exports of the existing master variants
(`thm_flow_master*`, `thm_case2_pair*`, `thm_case2_top(L)`, `thm_case2_pairLT`,
`thm_case2_pairLIZW(U/W/K/KA)`) and in addition the exposed intermediate facts `RelBaseConcl`
(per-scale relative bounds up to `N_h`), `TopRelConcl` (the `ℓ¹` error `E_{N_h}`) and the whole
`MasterCore` (all constants, `StepBounds`, `ApHyp`/mass/`BandF1` along every trajectory, the
destructured `ε`-requirements).

**Use.** New results under the master constants should be proved as lemmas
`(D : MasterCore L) → …` or `(M : MasterFacts L) → …` (see `Spin2/MasterAllCor` for examples), and
not by copying the construction. A new conclusion block that needs the full local context of the old
master proofs can be added as a new `MasterCore.*` lemma with the same prelude (one file per block;
`Spin2/Master/MasterAllLoop` etc.).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **All facts of the consolidated master construction** at `L`. The constants are those of
`core`; the derived constants are `MasterCore.ce`, `B₁`, `B₂`, `B₃`, `cq`, `B'`, `Bk`, `cδ`, `cRel`
(`= c_δc_R²`), `cw`, `cGB`, `cWL`, `cKL`, `cρ`, `cWo` (`= 3C₁ + 1`), `ιW`. -/
structure MasterFacts (L : ℕ) [NeZero L] : Type where
  core : MasterCore L
  flow : FlowC2Concl L core.ℓ core.A core.ρ core.κ core.cg core.cm core.cT core.ε core.Ke core.Cf
    core.Cb
  eps_le : core.ε ≤ 1
  KZ_nonneg : 0 ≤ core.KZ
  spin : SpinConcl L core.ℓ core.A core.ρ core.κ core.cg core.cm core.cT core.ε core.Ke core.KZ
    core.KG
  mag : MagConcl L core.ℓ core.A core.ρ core.κ core.cg core.cm core.cT core.ε core.Ke core.KZ
    core.KG
  valid : ValidConcl L core.ℓ core.A core.ρ core.κ core.cg core.cm core.cT core.ε
  gmono : GMonoConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε
  ginc : GIncConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε
  lastValid : LastValidConcl L core.ℓ core.ρ
  zeroT : ZeroTOk L core.ρ
  jet : ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ LastJetBd L (core.A / 2) r₀
  loop : LoopConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.B₁ core.B₂ core.B₃
    core.cq core.B'
  cRel_nonneg : 0 ≤ core.cRel
  rel : RelConcl2 L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cRel
  relG : RelConcl2G L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cRel
  Bk_nonneg : 0 ≤ core.Bk
  cδ_nonneg : 0 ≤ core.cδ
  cWo_ge : 1 ≤ core.cWo
  relBase : RelBaseConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cWo core.c
    core.Bk
  topRel : TopRelConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cδ core.c
  cw_nonneg : 0 ≤ core.cw
  wk : WKConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cw
  cGB_nonneg : 0 ≤ core.cGB
  gamBulk : GamBulkConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cGB
  tad : TadConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.ce
  cρ_nonneg : 0 ≤ core.cρ
  top : TopConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cρ
  lastO : LastObsConcl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cWo
  cWL_nonneg : 0 ≤ core.cWL
  lastW : LastObsConclW L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cWL
  cKL_nonneg : 0 ≤ core.cKL
  lastK : LastObsConclK L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.cKL
  lastL1 : LastL1Concl L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε
  pairInitU : PairInitConclU L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε
  ιW_ge : 1 ≤ core.ιW
  pairInitW : PairInitConclW L core.ℓ core.A core.ρ core.κ core.cm core.cT core.ε core.ιW

/-- Assembly of `MasterFacts` from the block lemmas. -/
def MasterCore.toFacts {L : ℕ} [NeZero L] (D : MasterCore L) : MasterFacts L where
  core := D
  flow := D.hC2
  eps_le := D.hε1
  KZ_nonneg := D.hKZ
  spin := D.hSp
  mag := magConcl_of (by exact_mod_cast (by have := D.hL49; omega : 2 ≤ L)) D.hε1 D.hKZ D.hKG D.hSp
  valid := D.hVC
  gmono := gMonoConcl_of (by have := D.hL49; omega) D.hC2.2.2.2.2.2.2.1.le
    (fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      ⟨(D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).1.h6,
        (D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2⟩)
  ginc := gIncConcl_of (by have := D.hL49; omega) D.hC2.2.2.2.2.2.2.1.le
    (fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      ⟨(D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).1.h6,
        (D.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2⟩)
  lastValid := D.hLV
  zeroT := D.hZT
  jet := D.hAJ
  loop := D.loopConcl
  cRel_nonneg := D.consts_nonneg.1
  rel := D.relConcl2
  relG := D.relConcl2G
  Bk_nonneg := D.consts_nonneg.2.2.2.2.2.2.1
  cδ_nonneg := D.consts_nonneg.2.2.2.2.2.2.2.1
  cWo_ge := D.consts_nonneg.2.2.2.2.2.1
  relBase := D.relBase
  topRel := D.topRel
  cw_nonneg := D.consts_nonneg.2.1
  wk := D.wkConcl
  cGB_nonneg := D.consts_nonneg.2.2.2.2.2.2.2.2.1
  gamBulk := D.gamBulkConcl
  tad := D.tadConcl
  cρ_nonneg := D.consts_nonneg.2.2.2.2.1
  top := D.topConcl
  lastO := D.lastObsConcl
  cWL_nonneg := D.consts_nonneg.2.2.1
  lastW := D.lastObsConclW
  cKL_nonneg := D.consts_nonneg.2.2.2.1
  lastK := D.lastObsConclK
  lastL1 := D.lastL1Concl
  pairInitU := D.pairInitConclU
  ιW_ge := D.consts_nonneg.2.2.2.2.2.2.2.2.2
  pairInitW := D.pairInitConclW

/-- **The consolidated master theorem.** For all large `L` there is one set of constants
(`MasterFacts.core`) for which all exports of all existing master variants hold, together with
`RelBaseConcl`, `TopRelConcl` and the bulk data of `MasterCore`. -/
theorem thm_master_all : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Nonempty (MasterFacts L) := by
  obtain ⟨L₀, hL₀⟩ := masterCore_exists
  exact ⟨L₀, fun L _ hL => (hL₀ L hL).map MasterCore.toFacts⟩

end

end Spin2
