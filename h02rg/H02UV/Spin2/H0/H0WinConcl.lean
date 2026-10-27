import Spin2.Multiscale.Multiscale
import Step2.Flow.FlowWin2

/-!
# Route (a1), task 2: the master conclusions along windowed trajectories

The master conclusions (`SpinConcl`, `MagConcl`, `MultiConcl`, the last two steps `GlueOut`/`BandOut`
of `FlowC2Concl`) are quantified over `Admissible` trajectories (`μ_{N_h} = 0`). On the windowed
trajectories of route (a1) (`AdmW`, `|μ_{N_h}| ≤ c₁`) only the domain condition
`∀ j ≤ N_h, InD3 … (traj b μ₀ j)` holds. The proofs use only this condition; the definitions here
are the same statements with `Admissible` replaced by the domain condition (`…D`), and the
proofs are the generalised originals (`Flow2.Hist.ginv_sharpD`, `log_trajD`, `logSum_ofD`,
`Spin2.traj_factsD`, `spinSum_ofD`, `betaAsym_ofD`, `magConcl_traj`, `multiConcl_traj`,
`Step2.flow_master_hyp0LZD`), not copies.

* `GlueD`: `GlueOut ∧ BandOut` along every trajectory in `D_ε` up to `N_h` (exported by
  `thm_flow_masterLZW` with the constants `C_f, C_b` of `FlowC2Concl`);
* `SpinConclD`: the trajectory clauses of `SpinConcl` (`LogSumD`, `SpinSumD`, `BetaAsymD`, the
  per-step band of `β_k`, `log|Z_{n+1}|`, `Γ^int`) along every trajectory in `D_ε`;
  `SpinConclD.toSpin`-type projections are by `.1` of `Admissible`;
* `MagConclD`, **`magConcl_ofD`**; `MultiConclD`, **`multiConcl_ofD`**.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- `MagConcl` (`prop:gamma` (ii)) along every trajectory in `D_ε` up to `N_h`. -/
def MagConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl →
    (∀ k < Nh, ‖lam k - ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      Kl * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
        ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) →
    ∀ j ≤ Nh,
      ‖(1 - (b : ℂ) * ∑ k ∈ range j,
          lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
        (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      spinMK L cg Ke KZ Kl KG 0 * (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1

/-- **`prop:gamma` (ii) along windowed trajectories** (`magConcl_traj`). -/
theorem magConcl_ofD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : (2 : ℝ) ≤ L)
    (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ) (hKG : 0 ≤ KG)
    (h : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD lam Kl hKl hl j hj
  obtain ⟨-, hSS, -, -, hZ, hGZ⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  exact magConcl_traj hL2 hε1 hKZ hKG R hNh hm hD (hSS m hm b μ₀ hD) (hZ m hm b μ₀ hD)
    (hGZ m hm b μ₀ hD) lam Kl hKl hl j hj

/-- `thm:multiscale` (`MultiConcl`) along every trajectory in `D_ε` up to `N_h`. -/
def MultiConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
  ∀ (lam : ℕ → ℂ) (Kl KP : ℝ), 0 ≤ Kl → 0 ≤ KP →
    HLam R Nh m b μ₀ lam Kl → RGInput R Nh m b μ₀ lam KP →
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b μ₀ jp| ≤
        multK L cg Ke KZ KG Kl KP * thetaSq R m b μ₀ jp / betaJ R m b μ₀ jp

/-- **`thm:multiscale` along windowed trajectories** (`multiConcl_traj`). -/
theorem multiConcl_ofD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ} (hL2 : 2 ≤ L)
    (hε1 : ε ≤ 1) (hSp : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMag : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    MultiConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ Nh hNh m hm b μ₀ hD lam Kl KP hKl hKP hl hrg x hx hj
  obtain ⟨-, -, -, hband, -, -⟩ := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh
  exact multiConcl_traj hL2 hε1 R hNh hm hD (hband m hm b μ₀ hD) lam Kl KP hKP
    (hMag N R hP hi0 hRℓ hRA hRρ (by omega) Nh hNh m hm b μ₀ hD lam Kl hKl hl) hrg x hx hj

end

end Spin2
