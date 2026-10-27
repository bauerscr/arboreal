import Spin2.Gam.LastL1M
import Spin2.Pair.PairInitW
import PtCorr2.Zero.EpsFlow
import Spin2.Gam.GamTopFullL
import Spin2.Case2.Case2RelPairLT
import Spin2.Master.AbwReq
import Spin2.H0.H0WinConcl
import Spin2.H0.H0SlackReq
import Spin2.Pair.PairEReq

/-!
# The consolidated master construction: `MasterCore`

One call of `thm_flow_masterLZW` (`thm_flow_masterLZ` + `WinHyp`) with the conjunction of all existing requirements:

* `Aext L A`: `2 ≤ A`, `obsAReq` (the `K^{obs}` chain), `kabAReq` (the unreduced `ab` chain) and the
  regulator requirement `A/2 ≥ A₀` of `PtCorr2.finG_jets_le` (`LastJetBd`);
* `Eext L A c c' ε`: `c2RelReqU` (= `c2RelReq` + `kabCond`), `gbEReq`, `topReq`.
* the requirements of the reduced `ab` chain with per-scale weights (`Spin2/Master/AbwReq`): `abwAReq` in
  `allAReq`, `abwEReq` in `allEReq` (fields `C₀a … hSX` at the end of `MasterCore`);
* the `V`-step requirement `abwEReqV` (`Spin2/Master/AbwReq`, appended to `allEReq`; field `hEv`);
* route (a1): the flow construction is `thm_flow_masterLZW` (= `thm_flow_masterLZ` + `WinHyp`, the
  hypotheses of the windowed flow), `GlueD` (last two steps along every trajectory in `D_ε`),
  `SpinConclD` (the trajectory clauses of `SpinConcl` in `D_ε`); fields `hWin`, `hGD`, `hSpD` (last).

`MasterCore L` bundles **everything** the existing master proofs (`thm_case2_pairLIZWKA`,
`thm_case2_topL`, `thm_case2_pairLT`, `thm_case2_pairLIZWU`, `thm_case2_pairLIZWW`) obtain before
their first conclusion block: the outer constants (`nu_sharp`, `prod_raw_step`, `kobs_bounds`,
`wobs_bounds`, `kobs_bounds_U`, `wobs_raw_fullWU`), the output of `thm_flow_masterLZ` (constants,
`FlowC2Concl`, `SpinConcl`, `ValidConcl`, `LastValidConcl`, `ZeroTOk`, `StepBounds`, `ApHyp`, mass,
`BandF1`) and the destructured `ε`-requirements at `c = c_R`. Every conclusion block is a separate
lemma `MasterCore.*` (files `Spin2/Master/MasterAll*`), and `MasterFacts` (`Spin2/Master/MasterAllFacts`)
collects them. **`masterCore_exists`** is the only place where the flow construction is run.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- The combined requirement on `A` (all existing `Aext`'s). -/
def allAReq (C₀o ηo : ℝ) (Lo : ℕ) (C₀u ηu : ℝ) (Lu Lj : ℕ) (C₀a ηa : ℝ) (La : ℕ) (L : ℕ)
    (A : ℝ) : Prop :=
  ((2 ≤ A ∧ obsAReq C₀o ηo Lo L A ∧ kabAReq C₀u ηu Lu L A) ∧
    ∀ _h : NeZero L, Lj ≤ L → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ LastJetBd L (A / 2) r₀) ∧
    abwAReq C₀a ηa La L A

/-- The combined requirement on `ε` (all existing `Eext`'s, `topReq` included). -/
def allEReq (Cq Cl cS C₀o ηo Kw : ℝ) (Lo : ℕ) (Cpf εpf : ℕ → ℝ) (C₀u ηu : ℝ) (Lu : ℕ)
    (C₀a ηa Kwa : ℝ) (La : ℕ) (L : ℕ) (A c c' ε : ℝ) : Prop :=
  c2RelReqU Cq Cl cS C₀o ηo Kw Lo Cpf εpf C₀u ηu Lu L A c c' ε ∧ gbEReq L A c c' ε ∧
    topReq L A c c' ε ∧ abwEReq C₀a ηa Kwa La L A c c' ε ∧ abwEReqV C₀a ηa Kwa La L A c c' ε

/-- **The data of the consolidated master construction at `L`** (see the module docstring). The
field names are those of the local hypotheses in the existing master proofs. -/
structure MasterCore (L : ℕ) [NeZero L] : Type where
  (Cq Cl cS : ℝ)
  (hCq : 0 ≤ Cq)
  (hCl : 0 ≤ Cl)
  (hcS : 1 ≤ cS)
  (hNu : NuSharp L Cq Cl cS)
  (Cpf εpf : ℕ → ℝ)
  (hCpf : ∀ L, 0 ≤ Cpf L)
  (hPB : PObsBounds L (Cpf L) (εpf L))
  (C₀o ηo : ℝ)
  (hC₀o : 0 ≤ C₀o)
  (hηo : 0 < ηo)
  (Kw : ℝ)
  (hKw : 0 ≤ Kw)
  (C₀u ηu : ℝ)
  (hC₀u : 0 ≤ C₀u)
  (hηu : 0 < ηu)
  (Cw : ℝ)
  (hCw : 0 ≤ Cw)
  (hWw : WObsBoundsU L Cw)
  (Lo Lu : ℕ)
  (hLo : Lo ≤ L)
  (hLuL : Lu ≤ L)
  (hLc : 144 * C₀o + 12 * Kw + 8 ≤ (Lo : ℝ))
  (hLb : prodLb ≤ (Lo : ℝ))
  (hL49 : 49 ≤ L)
  (hLpl : pauliL0 2 ≤ L)
  (hlog : gbLog ≤ Real.log L)
  (ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ)
  (hC2 : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb)
  (hε1 : ε ≤ 1)
  (hKZ : 0 ≤ KZ)
  (hKG : 0 ≤ KG)
  (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
  (hA2 : 2 ≤ A)
  (hAx : obsAReq C₀o ηo Lo L A)
  (hAu : kabAReq C₀u ηu Lu L A)
  (hAJ : ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ LastJetBd L (A / 2) r₀)
  (hVC : ValidConcl L ℓ A ρ κ cg cm cT ε)
  (hLV : LastValidConcl L ℓ ρ)
  (hZT : ZeroTOk L ρ)
  (C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ)
  (hSBx : StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx)
  (hXm : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 → R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ApHyp (R.withMsq m) ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧ (∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧ BandF1 (R.withMsq m) Nh κ cg cm cT ε)
  (c : ℝ)
  (hc : c = cR (⟨Pc, 0, ℓ, A, 0, ρ⟩ : RGPar 2 L 1) ((L : ℝ) ^ 2) cm C₂x)
  (ζbar K cS2 : ℝ)
  (hζ0 : 0 < ζbar)
  (hK : 0 ≤ K)
  (hcS2 : 0 ≤ cS2)
  (hLc' : LcProp L ζbar K cS2)
  (hζε : 2 * ceff L c * ε ≤ ζbar)
  (hcε : c * ε ≤ 1)
  (hc'ε : 8 * cx κ cT * ε ≤ 1)
  (hβε : betaL L * ε ≤ 1 / 2)
  (hsm : c2Bp Cq Cl cS L K cS2 c (cx κ cT) * ε ≤ 1 / 8)
  (hgε7 : (max (c2Bp Cq Cl cS L K cS2 c (cx κ cT)) 0 + 1) * ε ≤ 1 / 7)
  (hBτε : 4 * ceff L (max c 2) * (max (c2Bp Cq Cl cS L K cS2 c (cx κ cT)) 0 + 1) * ε ≤ 1 / 2)
  (hεp : c * ε ≤ εpf L)
  (ε₀ C₁k : ℝ)
  (hε₀ : 0 < ε₀)
  (hC₁k : 0 ≤ C₁k)
  (hKB : KObsBounds L A C₀o ηo ε₀ C₁k)
  (hsmk : C₁k * (2 + 2 * (8 * cx κ cT) + 64 * kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) * (c * ε) ≤ 1 / 72)
  (hεε : c * ε ≤ ε₀)
  (hεk : (8 * cx κ cT + 64 * kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) * (c * ε) ≤ ε₀)
  (C₁w ε₁ : ℝ)
  (hC₁w : 0 ≤ C₁w)
  (hε₁ : 0 < ε₁)
  (hWB : WObsBounds L Kw C₁w ε₁)
  (hC₁ε : C₁w * (c * ε) ≤ 1 / 12)
  (hε₁' : c * ε ≤ ε₁)
  (hcδε : c2dF L (Cpf L) (c2Bp Cq Cl cS L K cS2 c (cx κ cT)) C₁w (kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) c * c ^ 2 * (4 / betaL L) * ε ≤ 1 / 8)
  (hkab : kabCond L A C₀u ηu (8 * kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) (3 * C₁w + 1) c (cx κ cT) ε)
  (ζg Kg : ℝ)
  (hζg0 : 0 < ζg)
  (hKg : 0 ≤ Kg)
  (hCp : CpProp L ζg Kg)
  (hζg : 2 * ceff L c * ε ≤ ζg)
  (hKgε : Kg * (2 * ceff L c * ε) ≤ 1)
  (htopR : topReq L A c (cx κ cT) ε)
  (C₀a ηa Kwa : ℝ)
  (La : ℕ)
  (hC₀a : 0 ≤ C₀a)
  (hηa : 0 < ηa)
  (hKwa : 0 ≤ Kwa)
  (hLa : La ≤ L)
  (hLwa : Kwa / L ≤ 1 / 12)
  (hAa : abwAReq C₀a ηa La L A)
  (hEa : abwEReq C₀a ηa Kwa La L A c (cx κ cT) ε)
  (hSX : SXOBoundsAB L)
  (hEv : abwEReqV C₀a ηa Kwa La L A c (cx κ cT) ε)
  (hWin : WinHyp L ℓ A ρ κ cg cm cT ε)
  (hGD : GlueD L ℓ A ρ κ cm cT ε Cf Cb)
  (hSpD : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
  (hGN : GlueNuD L ℓ A ρ κ cm cT ε)
  (hcmF : cm = 3 * (L : ℝ) ^ 2 * (16 * ℓ ^ 2 / 49) + 8 * ℓ ^ 2 / 49 + 1)
  (hH0E : h0EReq L ℓ ρ Cf cm ε)
  (ε₀a C₁ka C₁wa ε₁a : ℝ)
  (hEaB : abwEReqB C₀a ηa Kwa L A c (cx κ cT) ε ε₀a C₁ka C₁wa ε₁a)
  (hWpo : WpOBoundsAB L cwClo cwClb)
  (hpowF : (1 + cWblk 2 L cwClb * (c * ε)) ^ (L ^ 2) ≤ 2)
  (hloopF : pl6XR L (Cpf L) (c2Bp Cq Cl cS L K cS2 c (cx κ cT)) C₁w
      (kB (kθ0 L A C₀o ηo) C₁k (8 * cx κ cT)) c *
    pl6ΘR L A C₀a ηa (cx κ cT) C₁ka C₁wa C₁wa cwClo cwClb (c2Bp Cq Cl cS L K cS2 c (cx κ cT)) c ε ≤
      1 / 2)

namespace MasterCore

variable {L : ℕ} [NeZero L] (D : MasterCore L)

/-- `c_eff = 3β + 7 + 9c_R`. -/
def ce : ℝ := ceff L D.c
/-- The constants of `LoopConcl`. -/
def B₁ : ℝ := bubB L D.ce D.K D.cS2
def B₂ : ℝ := nuB L D.Cq D.Cl D.cS (cx D.κ D.cT) D.c D.ce
def B₃ : ℝ := 9 / 64 * D.ce ^ 2
def cq : ℝ := 7 * D.ce
def B' : ℝ := c2Bp D.Cq D.Cl D.cS L D.K D.cS2 D.c (cx D.κ D.cT)
/-- The source constant `B = kB(θ₀, C₁, 8c_x)` of the `K^{obs}` chain. -/
def Bk : ℝ := kB (kθ0 L D.A D.C₀o D.ηo) D.C₁k (8 * cx D.κ D.cT)
def cgb : ℝ := c2gF D.B' D.c
def cP : ℝ := prodCP2 L (D.Cpf L)
/-- The `c_δ` of the relative recursion (`RelConcl2` holds with `c_δ c_R²`). -/
def cδ : ℝ := c2dF L (D.Cpf L) D.B' D.C₁w D.Bk D.c
def cRel : ℝ := D.cδ * D.c ^ 2
def cw : ℝ := max D.c 0 * (128 * (csN 2 : ℝ) * (3 * D.C₁w + 1) * D.Bk * (9 / 8 * D.ℓ ^ 2 + 1) +
    2 * (cBn : ℝ) * Q1 2 * (3 * D.C₁w + 1) * (9 / 8 * D.ℓ ^ 2))
def cGB : ℝ := gbK L D.ℓ (max (cmu ((L : ℝ) ^ 2) D.cm) 0) (16 * D.ℓ ^ 2 / 49)
def cWL : ℝ := 2 * (3 * D.C₁w + 1) * max D.c 0
def cKL : ℝ := 6 * D.Bk * (3 * D.C₁w + 1) * max D.c 0
def cρ : ℝ := (256 * (csN 2 : ℝ) * (3 * D.C₁w + 1) * D.Bk + 2 * (cBn : ℝ) * Q1 2 * (3 * D.C₁w + 1)) *
    (9 / 8 * D.ℓ ^ 2) + gbKb L D.ℓ (max (cmu ((L : ℝ) ^ 2) D.cm) 0) (16 * D.ℓ ^ 2 / 49)
/-- The constant `3C₁ + 1` of the `𝒲^{obs}` bounds. -/
def cWo : ℝ := 3 * D.C₁w + 1
def ιW : ℝ := iotaW L D.Cw (3 * D.C₁w + 1)

end MasterCore

/-- **The per-scale relative bounds along the observable flow** (the conclusion of
`PtCorr2.obs_hist_rel2_baseX` at horizon `N_h`): along every admissible trajectory, for every point
configuration `P` and observable coupling `V` with `γ_a = 0`, `μ_a ≠ 0`, and every `j ≤ N_h`:
`β_j ≠ 0`, `∑_B|m₂V_j(B)_a| ≤ 2|β_j|`, and the `𝒲^{obs}`/`K^{obs}` block bounds
`c_W r_j·2s_j²|β_j|`, `16c_WB r_j²·s_j²|β_j|` (`r_j = cǧ_j`). -/
def RelBaseConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cW c Bk : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.ga V = 0 →
    Obs2.OCoup2.mua V ≠ 0 → 0 < Nh → ∀ j ≤ Nh,
    0 < ‖bt2 R P V m b μ₀ j‖ ∧
    Obs2.shA2 (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) j ≤ 2 * ‖bt2 R P V m b μ₀ j‖ ∧
    WbHc (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
      (cW * (c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) *
        (2 * PtCorr2.histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R P V m b μ₀ j‖)) ∧
    KbHc (R.withMsq m) P (Obs2.obsInit .two V P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) j
      (16 * cW * Bk * (c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ 2 *
        (PtCorr2.histS (R.withMsq m) j (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
          ‖bt2 R P V m b μ₀ j‖))

/-- **The `ℓ¹` error of the step `N_h`** (`E_{N_h}`; the conclusion of
`PtCorr2.obs_hist_rel2_top`/`RelRec.E_top` at the index `N_h`): along every admissible trajectory,
for every `P` and `V` with `γ_a = 0`, `μ_a ≠ 0`: `|𝔫^{(2)}_{N_h}| ≤ 1/8` and
`|∑_{B_+}err_{N_h}(B_+)| ≤ c_δ(cǧ_{N_h})²|β_{N_h}(1 − 𝔫^{(2)}_{N_h})|`. -/
def TopRelConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cδ c : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.ga V = 0 →
    Obs2.OCoup2.mua V ≠ 0 →
    ‖nn2 R P V m b μ₀ Nh‖ ≤ 1 / 8 ∧
    ‖err2 R P V m b μ₀ Nh‖ ≤ cδ * (c * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ^ 2 *
      ‖bt2 R P V m b μ₀ Nh * (1 - nn2 R P V m b μ₀ Nh)‖

set_option maxHeartbeats 4000000 in
/-- **The consolidated master construction exists** for all large `L`: one call of
`thm_flow_masterLZ` with `allAReq`/`allEReq`. -/
theorem masterCore_exists : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → Nonempty (MasterCore L) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hnu⟩ := nu_sharp
  obtain ⟨Cpf, εpf, L₀p, hCpf, hPf⟩ := prod_raw_step
  obtain ⟨C₀o, ηo, L₀k, hC₀o, hηo, hk⟩ := kobs_bounds
  obtain ⟨Kw, L₀w, hKw, hw⟩ := wobs_bounds
  obtain ⟨C₀u, ηu, L₀u, hC₀u, hηu, hku⟩ := kobs_bounds_U
  obtain ⟨Lw, hLwB⟩ := wobs_raw_fullWU
  obtain ⟨Lj, hLj⟩ := PtCorr2.finG_jets_le
  obtain ⟨C₀a, ηa, L₀a, hC₀a, hηa, hka⟩ := kobs_bounds_ABL
  obtain ⟨Kwa, L₀wa, hKwa, hwa⟩ := wobs_bounds_AB
  obtain ⟨Ls, hLs⟩ := sxo_bounds_AB
  obtain ⟨La, hLad⟩ : ∃ La : ℕ, La = max (max L₀a L₀wa) (⌈144 * C₀a + 1⌉₊) := ⟨_, rfl⟩
  have hLa0 : L₀a ≤ La := hLad ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLa1 : L₀wa ≤ La := hLad ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLa2 : 144 * C₀a + 1 ≤ (La : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (hLad ▸ le_max_right _ _ : ⌈144 * C₀a + 1⌉₊ ≤ La))
  obtain ⟨Lu, hLud⟩ : ∃ Lu : ℕ, Lu = max L₀u (⌈144 * (3 * C₀u) + 1⌉₊) := ⟨_, rfl⟩
  have hLu0 : L₀u ≤ Lu := hLud ▸ le_max_left _ _
  have hLu1 : 144 * (3 * C₀u) + 1 ≤ (Lu : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (hLud ▸ le_max_right _ _ : ⌈144 * (3 * C₀u) + 1⌉₊ ≤ Lu))
  obtain ⟨Lo, hLod⟩ : ∃ Lo : ℕ, Lo = max (max L₀k L₀w)
      (max (⌈144 * C₀o + 12 * Kw⌉₊ + 8) (max L₀p ⌈prodLb⌉₊)) := ⟨_, rfl⟩
  have hLk : L₀k ≤ Lo := hLod ▸ le_trans (le_max_left _ _) (le_max_left _ _)
  have hLw' : L₀w ≤ Lo := hLod ▸ le_trans (le_max_right _ _) (le_max_left _ _)
  have hLp : L₀p ≤ Lo := hLod ▸ le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hLb : prodLb ≤ (Lo : ℝ) := by
    have h1 : ⌈prodLb⌉₊ ≤ Lo := hLod ▸ le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hLc8 : ⌈144 * C₀o + 12 * Kw⌉₊ + 8 ≤ Lo :=
    hLod ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hLc : 144 * C₀o + 12 * Kw + 8 ≤ (Lo : ℝ) := by
    have h2 := Nat.le_ceil (144 * C₀o + 12 * Kw)
    have h3 : ((⌈144 * C₀o + 12 * Kw⌉₊ + 8 : ℕ) : ℝ) ≤ Lo := by exact_mod_cast hLc8
    push_cast at h3
    linarith
  have h7 : 7 ≤ Lo := by omega
  obtain ⟨L₀, hL₀⟩ := thm_flow_masterLZW (allAReq C₀o ηo Lo C₀u ηu Lu Lj C₀a ηa La)
    (fun L => by
      obtain ⟨A₀, hA₀⟩ := obsAReq_ev hC₀o hηo hk hLk (by linarith) L
      obtain ⟨A₁, hA₁⟩ := kabAReq_ev hC₀u hηu hku hLu0 hLu1 L
      obtain ⟨A₃, hA₃⟩ := abwAReq_ev hC₀a hηa hka hLa0 hLa2 L
      by_cases hLL : Lj ≤ L ∧ L ≠ 0
      · haveI : NeZero L := ⟨hLL.2⟩
        obtain ⟨A₂, -, hA₂'⟩ := hLj L hLL.1
        refine ⟨max (max (max 2 (max A₀ A₁)) (2 * A₂)) A₃, fun A hA' => ?_⟩
        have hA := le_trans (le_max_left _ _) hA'
        refine ⟨⟨⟨?_, hA₀ A ?_, hA₁ A ?_⟩, fun _ _ => hA₂' (A / 2) ?_⟩,
          hA₃ A (le_trans (le_max_right _ _) hA')⟩
        · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
        · exact le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
            (le_max_left _ _)) hA
        · exact le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
            (le_max_left _ _)) hA
        · have := le_trans (le_max_right _ _) hA; linarith
      · refine ⟨max (max 2 (max A₀ A₁)) A₃, fun A hA' => ?_⟩
        have hA := le_trans (le_max_left _ _) hA'
        exact ⟨⟨⟨le_trans (le_max_left _ _) hA,
          hA₀ A (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hA),
          hA₁ A (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA)⟩,
          fun h hL => absurd ⟨hL, h.out⟩ hLL⟩, hA₃ A (le_trans (le_max_right _ _) hA')⟩)
    (fun L A c c' ε => allEReq Cq Cl cS C₀o ηo Kw Lo Cpf εpf C₀u ηu Lu C₀a ηa Kwa La L A c c' ε ∧
      pairEReq Cq Cl cS C₀o ηo Kw Lo Cpf εpf C₀u ηu Lu C₀a ηa Kwa La L A c c' ε)
    (fun L A c c' => ((c2RelReqU_ev Cq Cl cS Cpf εpf hw hLw' h7
      (fun L _ hL => (hPf L (hLp.trans hL)).1) L A c c').and
        ((gbEReq_ev L A c c').and ((topReq_ev L A c c').and ((abwEReq_ev hwa hLa1 L A c c').and
          (abwEReqV_ev hwa hLa1 L A c c'))))).and
      (pairEReq_ev Cq Cl cS Cpf εpf hw hLw' h7 (fun L _ hL => (hPf L (hLp.trans hL)).1) hwa hLa1
        L A c c'))
    (fun L ℓ ρ Cf cm ε => ∀ _h : NeZero L, h0EReq L ℓ ρ Cf cm ε)
    (fun L ℓ ρ Cf cm => by
      by_cases hL0 : L = 0
      · exact Filter.Eventually.of_forall fun _ h => absurd hL0 h.out
      · haveI : NeZero L := ⟨hL0⟩
        filter_upwards [h0EReq_ev L ℓ ρ Cf cm] with ε hε
        exact fun _ => hε)
  obtain ⟨-, -, Lwp, hLwp⟩ := cw_wpo_spec
  refine ⟨max Lwp (max L₀ (max Lo (max 49 (max ⌈pauliL0 2⌉₊ (max gbL0 (max Lu (max Lw
    (max Lj (max La (max Ls ⌈12 * Kwa⌉₊)))))))))), fun L _ hL' => ?_⟩
  have hLwpL : Lwp ≤ L := le_trans (le_max_left _ _) hL'
  have hL := le_trans (le_max_right _ _) hL'
  have hL₀L : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLo : Lo ≤ L := by omega
  have hL49 : 49 ≤ L := by omega
  have hLpl : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by
    have : ⌈pauliL0 2⌉₊ ≤ L := by omega
    exact_mod_cast this)
  have hLg : gbL0 ≤ L := by omega
  have hLuL : Lu ≤ L := by omega
  have hLwL : Lw ≤ L := by omega
  have hLjL : Lj ≤ L := by omega
  have hLaL : La ≤ L := by omega
  have hLsL : Ls ≤ L := by omega
  have hLwa : Kwa / L ≤ 1 / 12 := by
    have h1 : ⌈12 * Kwa⌉₊ ≤ L := by omega
    have h2 : 12 * Kwa ≤ (L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h1)
    have h3 : (0 : ℝ) < L := Nat.cast_pos.2 (by omega)
    rw [div_le_iff₀ h3]; linarith
  have hlog := log_ge_gbLog hLg
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hNu := hnu L hL8 hLpl
  obtain ⟨Cw, hCw, hWw⟩ := hLwB L hLwL
  obtain ⟨-, hPB⟩ := hPf L (hLp.trans hLo)
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp,
    ⟨⟨⟨hA2, hAx, hAu⟩, hAJ'⟩, hAa⟩, ⟨hcmF, hH0E⟩, hVC, hLV, hZT, hWin, hGD, hSpD, hGN, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx,
    hXm⟩ := hL₀ L hL₀L
  have hAJ := hAJ' inferInstance hLjL
  obtain ⟨ζbar, K, cS2, ε₀, C₁k, C₁w, ε₁, ε₀a, C₁ka, C₁wa, ε₁a,
    ⟨hζ0, hK, hcS2, hLc', hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp,
    hε₀, hC₁k, hKB, hsmk, hεε, hεk, hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab⟩, hEaB, hpowF, hloopF⟩ :=
    (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).2 hLo hAx hLuL hAu (by omega) hAa
  obtain ⟨ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, -⟩ := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.1 (by omega)
  have htopR := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.2.1
  have hEa := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.2.2.1
  have hEv := (hEx ⟨Pc, 0, ℓ, A, 0, ρ⟩ rfl).1.2.2.2.2
  set c := cR (⟨Pc, 0, ℓ, A, 0, ρ⟩ : RGPar 2 L 1) ((L : ℝ) ^ 2) cm C₂x with hc
  exact ⟨
    ⟨Cq, Cl, cS, hCq, hCl, hcS, hNu, Cpf, εpf, hCpf, hPB, C₀o, ηo, hC₀o, hηo, Kw, hKw, C₀u, ηu,
      hC₀u, hηu, Cw, hCw, hWw, Lo, Lu, hLo, hLuL, hLc, hLb, hL49, hLpl, hlog, ℓ, A, ρ, κ, cg, cm,
      cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hA2, hAx, hAu, hAJ, hVC, hLV, hZT, C₀x,
      ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hXm, c, hc, ζbar, K, cS2, hζ0, hK, hcS2, hLc',
      hζε, hcε, hc'ε, hβε, hsm, hgε7, hBτε, hεp, ε₀, C₁k, hε₀, hC₁k, hKB, hsmk, hεε, hεk, C₁w, ε₁,
      hC₁w, hε₁, hWB, hC₁ε, hε₁', hcδε, hkab, ζg, Kg, hζg0, hKg, hCp, hζg, hKgε, htopR,
      C₀a, ηa, Kwa, La, hC₀a, hηa, hKwa, hLaL, hLwa, hAa, hEa, hLs L hLsL, hEv, hWin, hGD, hSpD, hGN, hcmF, hH0E inferInstance,
      ε₀a, C₁ka, C₁wa, ε₁a, hEaB, hLwp L hLwpL, hpowF, hloopF⟩
  ⟩

/-! ### Route (a1): the `D_ε` forms of the master conclusions

The conclusion blocks below are proved along every trajectory in `D_ε` up to `N_h` (`…D`); the
`Admissible` forms are their projections (`…D.adm`). -/

/-- `LoopConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def LoopConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), 0 ≤ B₁ + B₂ + B₃ ∧
    Case2Bulk R P Nh m b μ₀ B₁ B₂ B₃ cq ∧ Case2Loop R P V Nh m b μ₀ (B₁ + B₂ + B₃) B' cq

theorem LoopConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' : ℝ}
    (h : LoopConclD L ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B') : LoopConcl L ℓ A ρ κ cm cT ε B₁ B₂ B₃ cq B' := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `RelConcl2G` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def RelConcl2GD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cδ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two),
    Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ

/-- `WKConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def WKConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cw : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.mua V ≠ 0 →
  ∀ k < Nh, ‖Obs2.gamWK2 (R.withMsq m) P (Obs2.obsInit .two V P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k‖ ≤
    cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖bt2 R P V m b μ₀ k‖ *
      ‖gamT R m b μ₀ k‖

theorem WKConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cw : ℝ}
    (h : WKConclD L ℓ A ρ κ cm cT ε cw) : WKConcl L ℓ A ρ κ cm cT ε cw := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `GamBulkConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def GamBulkConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε ce : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    GamBulkRelA R Nh m b μ₀ ce

theorem GamBulkConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε ce : ℝ}
    (h : GamBulkConclD L ℓ A ρ κ cm cT ε ce) : GamBulkConcl L ℓ A ρ κ cm cT ε ce := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `TopConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def TopConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cρ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ P : Obs2.ObsPts 2 L N,
    Case2TopStep R P (zV b) Nh m b μ₀ ∧
    ‖Obs2.gamRem2 (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh‖ ≤
      cρ * ‖bt2 R P (zV b) m b μ₀ Nh‖ *
        (zH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) (Nh + 1))⁻¹

theorem TopConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cρ : ℝ}
    (h : TopConclD L ℓ A ρ κ cm cT ε cρ) : TopConcl L ℓ A ρ κ cm cT ε cρ := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `LastObsConclW` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def LastObsConclWD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cW : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ P : Obs2.ObsPts 2 L N, 0 < Nh →
    WbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Nh + 1) (cW * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R P (zV b) m b μ₀ Nh‖)

theorem LastObsConclWD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cW : ℝ}
    (h : LastObsConclWD L ℓ A ρ κ cm cT ε cW) : LastObsConclW L ℓ A ρ κ cm cT ε cW := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `LastObsConclK` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def LastObsConclKD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cK : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ P : Obs2.ObsPts 2 L N, 0 < Nh →
    KbHc (R.withMsq m) P (Obs2.obsInit .two (zV b) P) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Nh + 1) (cK * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 *
        histS (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ^ 2 *
        ‖bt2 R P (zV b) m b μ₀ Nh‖)

theorem LastObsConclKD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cK : ℝ}
    (h : LastObsConclKD L ℓ A ρ κ cm cT ε cK) : LastObsConclK L ℓ A ρ κ cm cT ε cK := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `LastL1Concl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def LastL1ConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ P : Obs2.ObsPts 2 L N, ‖nn2 R P (zV b) m b μ₀ Nh‖ ≤ 1 / 7 →
    Obs2.shA2 (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two (zV b) P)
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) (Nh + 1) ≤ 3 * ‖bt2 R P (zV b) m b μ₀ (Nh + 1)‖

theorem LastL1ConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε : ℝ}
    (h : LastL1ConclD L ℓ A ρ κ cm cT ε) : LastL1Concl L ℓ A ρ κ cm cT ε := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `TadConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def TadConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε ct : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    0 ≤ ct ∧
    (∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two) (i k : ℕ), i < k → k ≤ Nh →
      ‖Obs2.tadInc2 P (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
          (Obs2.histVO2 (R.withMsq m) P (Obs2.obsInit .two V P)
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) i k‖ ≤
        ct * (2 / (L : ℝ)) ^ (k - i) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1) ∧
    ∀ i ≤ Nh, ct * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ i).1 ≤ 1

theorem TadConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε ct : ℝ}
    (h : TadConclD L ℓ A ρ κ cm cT ε ct) : TadConcl L ℓ A ρ κ cm cT ε ct := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

open Obs Obs.SA LocObs Obs2 ENNReal in
/-- `PairInitConclW` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def PairInitConclWD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε ι : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ x : Lam 2 L N, 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    0 < pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) ∧
    0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
      (Obs.coal L (0 : Lam 2 L N) x) ∧
    ∀ Y : Finset (Lam 2 L N),
        ENNReal.ofReal (A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) Y - 2 ^ 2)) *
            Tj 2 (L : ℝ) (Obs.coal L (0 : Lam 2 L N) x)
              (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
                (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
              ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K Y : SA .two (Lam 2 L N)).ab ≤
          ENNReal.ofReal (pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x) *
            pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x) * (2 * ι * A) ^ ((L + 18) ^ 2))

theorem PairInitConclWD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε ι : ℝ}
    (h : PairInitConclWD L ℓ A ρ κ cm cT ε ι) : PairInitConclW L ℓ A ρ κ cm cT ε ι := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1


/-- `RelConcl2` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def RelConcl2D (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε cδ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ (P : Obs2.ObsPts 2 L N) (V : Obs2.OCoup .two), Obs2.OCoup2.ga V = 0 →
    Obs2.OCoup2.mua V ≠ 0 → Case2Rel R P V Nh m b μ₀ cδ

theorem RelConcl2D.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cδ : ℝ}
    (h : RelConcl2D L ℓ A ρ κ cm cT ε cδ) : RelConcl2 L ℓ A ρ κ cm cT ε cδ := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1


end

end Spin2
