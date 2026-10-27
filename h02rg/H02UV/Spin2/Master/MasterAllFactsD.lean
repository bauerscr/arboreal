import Spin2.Master.MasterAllFacts
import Spin2.H0.H0WinConcl
import Spin2.Pair.PairSeedW

/-!
# Route (a1): the `MasterFacts` conclusions along every trajectory in `D_ε`

The master conclusions of `MasterFacts` are stated along `Admissible` trajectories
(`μ_{N_h} = 0`). Their proofs use only the domain condition `∀ j ≤ N_h, InD3 … (traj b μ₀ j)`;
the conclusion blocks `MasterCore.*` are therefore proved in the `D_ε` form (`MasterCore.*D`,
`Spin2/Master/MasterAll*`), the `Admissible` forms being their projections `…D.adm`. This file exposes the
`D_ε` forms as accessors of `M : MasterFacts L` with the same argument order as the `Admissible`
fields (`M.loopD` for `M.loop`, …), so that a proof along admissible trajectories becomes a proof
along windowed trajectories by replacing `M.x … hadm` with `M.xD … hD` and `hadm.1` with `hD`:

`loopD`, `relGD`, `wkD`, `gamBulkD`, `tadD`, `topD`, `lastWD`, `lastKD`, `lastL1D`,
`pairInitWD`, `gmonoD`, `gincD`, `spinD` (`SpinConclD`), `magD` (`MagConclD`), `glueD`
(`GlueD`), `lamD` (`LamConclD`, from `lamConcl_at`), and the `D_ε` forms `pairSeed_hK0D` (of
`pairSeed_hK0`), `magAt_ofD` (of `magAt_of`), `hLam_case2D` (of `hLam_case2`, via
`hLam_case2_at`), `wk_inputsD` (of `wk_inputs`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- `LamConcl` along windowed trajectories from `SpinConclD` (`lamConcl_at`). -/
theorem lamConcl_ofD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (h : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    LamConclD L ℓ A ρ κ cg cm cT ε Ke := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
  obtain ⟨hLS, -⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  exact lamConcl_at hL2 hε1 R hNh hm (hLS m hm b μ₀ hD) hD

/-- `hLam_case2` along windowed trajectories. -/
theorem hLam_case2D {L N : ℕ} [NeZero L] {R : RGPar 2 L N} [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {P : Obs2.ObsPts 2 L N} {V : Obs2.OCoup .two} {ℓ A ρ κ cg cm cT ε Ke : ℝ}
    (hLC : LamConclD L ℓ A ρ κ cg cm cT ε Ke)
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = ℓ) (hRA : R.A = A) (hRρ : R.ρ = ρ)
    {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    {B B' cq cδ : ℝ} (hB : 0 ≤ B) (hcδ : 0 ≤ cδ) (hmu : Obs2.OCoup2.mua V ≠ 0)
    (hrel : Case2Rel R P V Nh m b μ₀ cδ) (hloop : Case2Loop R P V Nh m b μ₀ B B' cq) :
    HLam R Nh m b μ₀ (lamHat2 R P V m b μ₀)
      (lamRelK (betaL L) cg B B' cq cδ (eRange (betaL L) Ke 1) 4) :=
  hLam_case2_at (hLC N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b μ₀ hD) hNh hB hcδ hmu hrel
    hloop

/-- `magAt_of` along windowed trajectories. -/
theorem magAt_ofD {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hMC : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = ℓ) (hRA : R.A = A) (hRρ : R.ρ = ρ) (hN : 1 ≤ N)
    {Nh : ℕ} (hNh : Nh + 2 ≤ N) {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) :
    MagAt R Nh m b μ₀ (fun Kl => spinMK L cg Ke KZ Kl KG 0) :=
  fun lam Kl hKl hl j hj => hMC N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD lam Kl hKl hl j hj

/-- `wk_inputs` along windowed trajectories. -/
theorem wk_inputsD {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε cw : ℝ}
    (hW : WKConclD L ℓ A ρ κ cm cT ε cw)
    (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc) (hi0 : R.i₀ = 0)
    (hRℓ : R.ℓ = ℓ) (hRA : R.A = A) (hRρ : R.ρ = ρ) (hN : 2 ≤ N) (Nh : ℕ) (hNh : Nh + 2 = N)
    (m : ℝ) (hm : m ∈ mRange L N) (b μ₀ : ℝ)
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) :
    GamWKRel R Nh m b μ₀ cw ∧ GamWKRelS R Nh m b μ₀ cw ∧ GamWKTop R Nh m b μ₀ cw ∧
      ∀ x : Lam 2 L N, ∀ k < Nh, ‖gamWKMir R m b μ₀ x k‖ ≤
        cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btMir R m b μ₀ x k‖ *
          ‖gamT R m b μ₀ k‖ := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have H := hW N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD
  refine ⟨fun x _ hj k hk => H (ptsX x) (zV b) (zV_mua_ne hb) k (lt_of_lt_of_le hk hj),
    fun x _ hj k hk => H (ptsS x) (zV b) (zV_mua_ne hb) k (lt_of_lt_of_le hk hj),
    fun x _ _ _ k hk => H (ptsX x) (zV b) (zV_mua_ne hb) k hk,
    fun x k hk => H (ptsS x) (zV b) (zV_mua_ne hb) k hk⟩

open Obs Obs.SA LocObs Obs2 ENNReal in
/-- `pairSeed_hK0` along windowed trajectories (same proof). -/
theorem pairSeed_hK0D {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε ι : ℝ}
    (hP : PairInitConclWD L ℓ A ρ κ cm cT ε ι)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hRP : R.P = Pc) (hi : R.i₀ = 0)
    (hℓ : R.ℓ = ℓ) (hA : R.A = A) (hρ : R.ρ = ρ) (hN : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N)
    {m : ℝ} (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j))
    (x : Lam 2 L N) (h1 : 1 ≤ Obs.coal L (0 : Lam 2 L N) x)
    (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    0 < pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        (Obs.coal L (0 : Lam 2 L N) x) ∧
      0 < pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
        (Obs.coal L (0 : Lam 2 L N) x) ∧
      ∀ X, IsConn (Obs.coal L (0 : Lam 2 L N) x) X →
        ENNReal.ofReal ((R.withMsq m).A ^ (nb (Obs.coal L (0 : Lam 2 L N) x) X - 2 ^ 2)) *
          oTo (wM (pM (R.withMsq m) (ptsX x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x))
            (pM (R.withMsq m) (ptsS x) (zV0 b) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
              (Obs.coal L (0 : Lam 2 L N) x)))
            (Obs.coal L (0 : Lam 2 L N) x)
            (histS (R.withMsq m) (Obs.coal L (0 : Lam 2 L N) x)
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))
            ((oRed R m b μ₀ (dxStd (L := L) (N := N)) x).K X) ≤
          ENNReal.ofReal ((2 * ι * A) ^ ((L + 18) ^ 2)) := by
  obtain ⟨hpa, hpb, hK⟩ := hP N R hRP hi hℓ hA hρ hN Nh hNh m hm b μ₀ hD x h1 hj
  refine ⟨hpa, hpb, ?_⟩
  have hab : ObsAbInv (Obs.coal L (0 : Lam 2 L N) x) (oRed R m b μ₀ (dxStd (L := L) (N := N)) x) :=
    obsAbInv_redSt _ _ _ _ _ _ _ _ _ _
  have hAm : (R.withMsq m).A = A := hA
  have e : ∀ n : ℕ, ENNReal.ofReal ((R.withMsq m).A ^ n) = ENNReal.ofReal (A ^ n) := fun n => by
    rw [hAm]
  exact hK0_of_ab_le hab hpa hpb fun Y _ => by rw [e]; exact hK Y

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

theorem loopD : LoopConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
    M.core.B₁ M.core.B₂ M.core.B₃ M.core.cq M.core.B' := M.core.loopConclD
theorem relGD : RelConcl2GD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
    M.core.cRel := M.core.relConcl2GD
theorem wkD : WKConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
    M.core.cw := M.core.wkConclD
theorem gamBulkD : GamBulkConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε M.core.cGB := M.core.gamBulkConclD
theorem tadD : TadConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
    M.core.ce := M.core.tadConclD
theorem topD : TopConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
    M.core.cρ := M.core.topConclD
theorem lastWD : LastObsConclWD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε M.core.cWL := M.core.lastObsConclWD
theorem lastKD : LastObsConclKD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε M.core.cKL := M.core.lastObsConclKD
theorem lastL1D : LastL1ConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε := M.core.lastL1ConclD
theorem pairInitWD : PairInitConclWD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε M.core.ιW := M.core.pairInitConclWD
theorem gmonoD : GMonoConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε :=
  gMonoConcl_ofD (by have := M.core.hL49; omega) M.core.hC2.2.2.2.2.2.2.1.le
    (fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      ⟨(M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).1.h6,
        (M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2⟩)
theorem gincD : GIncConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT
    M.core.ε :=
  gIncConcl_ofD (by have := M.core.hL49; omega) M.core.hC2.2.2.2.2.2.2.1.le
    (fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      ⟨(M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).1.h6,
        (M.core.hXm N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm).2.2⟩)
theorem spinD : SpinConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cg M.core.cm M.core.cT
    M.core.ε M.core.Ke M.core.KZ M.core.KG := M.core.hSpD
theorem magD : MagConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cg M.core.cm M.core.cT
    M.core.ε M.core.Ke M.core.KZ M.core.KG :=
  magConcl_ofD (by exact_mod_cast (by have := M.core.hL49; omega : 2 ≤ L)) M.core.hε1
    M.core.hKZ M.core.hKG M.core.hSpD
theorem glueD : GlueD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
    M.core.Cf M.core.Cb := M.core.hGD
theorem lamD : LamConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cg M.core.cm M.core.cT
    M.core.ε M.core.Ke :=
  lamConcl_ofD (by exact_mod_cast (by have := M.core.hL49; omega : 2 ≤ L)) M.core.hε1
    M.core.hSpD

end MasterFacts

end

end Spin2
