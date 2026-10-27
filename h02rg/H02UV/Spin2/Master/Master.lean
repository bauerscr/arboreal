import Spin2.Multiscale.Gamma
import Spin2.Multiscale.BetaLog
import Step2.Flow.FlowMasterHypLZ
import Step2.Flow.FlowComplete2X

/-!
# The master flow theorem: one set of constants for `thm:flow`, `sec:spin` and `thm:beta`

* `SpinConcl`: the conclusions of `thm_flow_final_spinX` for given constants (`FixedConcl`,
  `MsqConcl`, `LogSum`, `SpinSum`, `BetaAsym`, the per-step band `β_{k+1} = β_k - β + O(a_k + ǧ_k)`
  along admissible trajectories, `|Z_{n+1}| = (β_n/β_ε)^{1/3}e^{O(ǧ_n)}`, (H_Γ), `Z = |Z|`).
* `ValidConcl` (`ValidAt` below the horizon and `ǧ_{k+1} ≤ (1 + 3β/2 + c_g)ǧ_k`), `LastValidConcl`
  (`LastN.ValidLast` at `N_h + 1`), and the conclusions along every trajectory in `D_ε` up to `N_h`
  (route (a1), no final condition): `GlueD`, `GlueNuD`, `SpinConclD`; `WinHyp` (the hypotheses of
  the windowed flow).
* **`thm_flow_masterLZW`**: the one construction of the constants (`Step2.flow_master_hyp0LZD`):
  `FlowC2Concl` (`thm_flow_complete2X`, the external requirements `Aext`, `Eext`, `Gext` and the
  exported bulk data), `SpinConcl`, `ValidConcl`, `LastValidConcl`, `ZeroTOk`, `WinHyp`, `GlueD`,
  `SpinConclD`, `GlueNuD`.
* **`thm_flow_master`**: the admissible-trajectory part of `thm_flow_masterLZW` (a projection).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- The conclusions of `thm_flow_final_spinX` for given constants, together with the per-step
band `|β_{k+1} - β_k + β| ≤ K_b a_k + C_gu ǧ_k` (`β_k = 1/ǧ_k`, `a_k = zA`). -/
def SpinConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
    (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1)) ∧
    MsqConcl R κ cm cT Nh ε (mRange L N) ∧
    (∀ m ∈ mRange L N, LogSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1)) ∧
    (∀ m ∈ mRange L N, SpinSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1)) ∧
    (∀ m ∈ mRange L N, BetaAsym (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1)) ∧
    (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      ∀ k < Nh, |1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 -
          1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + betaL L| ≤
        2 * (1 + betaL L) * max Ke (betaL L / 2) * zA L m k +
          Cgu (betaL L) cg * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) ∧
    (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      ∀ n ≤ Nh,
        (rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0 ∧
        |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
            1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
          KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ∧
    (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      ∀ k < Nh,
        ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
            GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          KG * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ∧
        (rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z =
          ((‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℝ) : ℂ))

/-- `e_k ≤ max(K_e, β/2) a_k` for the (F1) errors. -/
theorem e_le_zA {e : ℕ → ℝ} {β Ke : ℝ} {L : ℕ} {m : ℝ} {Nh : ℕ}
    (h0 : ∀ j < Nh, e j ≤ 1 / 2 * β)
    (h1 : ∀ j, 1 ≤ j → e j ≤ Ke * ((((L : ℝ) ^ j) ^ 2)⁻¹ + m * ((L : ℝ) ^ (j + 1)) ^ 2))
    (hm : 0 ≤ m) {k : ℕ} (hk : k < Nh) : e k ≤ max Ke (β / 2) * zA L m k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [zA_zero, mul_one]; exact (h0 0 hk).trans (by rw [one_div_mul_eq_div]; exact le_max_right _ _)
  · rw [zA_pos L m hk1]
    refine (h1 k hk1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    positivity

/-- Validity of the steps below the horizon (`ValidAt`) and the trajectory ratio
`ǧ_{k+1} ≤ (1 + 3β/2 + c_g)ǧ_k` along admissible trajectories (exported for the observable flow). -/
def ValidConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N → ∀ m ∈ mRange L N,
    (∀ j < Nh, ValidAt (R.withMsq m) j) ∧
    ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 ≤
        (1 + 3 / 2 * betaL L + cg) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1

/-- **The last step is valid** (`LastN.ValidLast` at `N_h + 1 = N - 1`) for the given constants. -/
def LastValidConcl (L : ℕ) [NeZero L] (ℓ ρ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N), R.P = Pc → R.ℓ = ℓ → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, LastN.ValidLast (R.withMsq m) (Nh + 1)

/-- **The last two steps along every trajectory in `D_ε` up to `N_h`** (no final condition). -/
def GlueD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε Cf Cb : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
      BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)

/-- **The sharp `ν`-relation through the last two steps along every trajectory in `D_ε`**
(`Step2.glue_hist_nu`): `|L^{2N}ν_N/Z_N - L⁴μ_{N_h}| ≤ cNuLast·ǧ_{N_h}`. -/
def GlueNuD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) *
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).κ.nu /
          (lastOut (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z -
        (L : ℂ) ^ 4 * (((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).2.1 : ℝ) : ℂ)‖ ≤
      cNuLast (R.withMsq m) ((L : ℝ) ^ 2) cm ε * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1

/-- **The trajectory clauses of `SpinConcl` along every trajectory in `D_ε` up to `N_h`.** -/
def SpinConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
  ∀ Nh : ℕ, Nh + 2 ≤ N →
    (∀ m ∈ mRange L N, LogSumD (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1)) ∧
    (∀ m ∈ mRange L N, SpinSumD (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1)) ∧
    (∀ m ∈ mRange L N, BetaAsymD (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1)) ∧
    (∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
      ∀ k < Nh, |1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1 -
          1 / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + betaL L| ≤
        2 * (1 + betaL L) * max Ke (betaL L / 2) * zA L m k +
          Cgu (betaL L) cg * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) ∧
    (∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
      ∀ n ≤ Nh,
        (rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0 ∧
        |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
            1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
          KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ∧
    (∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
      ∀ k < Nh,
        ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
            GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          KG * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ∧
        (rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z =
          ((‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℝ) : ℂ))

/-- **The hypotheses of the windowed flow** at the master constants. -/
def WinHyp (L : ℕ) [NeZero L] (ℓ A ρ κ cg cm cT ε : ℝ) : Prop :=
  ∃ CL aB : ℝ, Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε) * cmu ((L : ℝ) ^ 2) cm ≤ 1 / 12 ∧
    ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧ cg * ε ≤ betaL L / 4 ∧
    CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CL ∧
    4 * sZ CL (CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε)) (Qh κ * (CL * ε)) ≤
      ((L : ℝ) ^ 2 - 1) / 4 ∧
    (∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
      MonoZCoef ((L : ℝ) ^ 2) κ CL (CL * ε) CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂) ∧
    (∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 ρ) ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
      HHyp (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh CL aB ε ∧
      ZHyp (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH (R.withMsq m)) CL
        (CL * ε) CL (CL * ε) 4 ε ∧
      MonoZHyp (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh (zetaH (R.withMsq m))
        CL (CL * ε) CL 4 ε (3 / 4)

set_option maxHeartbeats 20000000 in
/-- **The master flow theorem with the windowed-flow hypotheses exported** (the one master construction). One construction of the constants for: `thm_flow_complete2X`
(`FlowC2Concl`: `thm:flow` with the last two steps and the shooting `Re ǧ_N = 1/β_R`; the external
requirements `A ∈ Aext L`, `ε ∈ Eext …`; the exported bulk data) and `SpinConcl` (the
conclusions of `thm_flow_final_spinX` and the per-step band of `β_j`). -/
theorem thm_flow_masterLZW (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε)
    (Gext : ℕ → ℝ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hGext : ∀ (L : ℕ) (ℓ ρ Cf cm : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Gext L ℓ ρ Cf cm ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧
      ε ≤ 1 ∧ 0 ≤ KZ ∧ 0 ≤ KG ∧ SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ Aext L A ∧
      (cm = 3 * (L : ℝ) ^ 2 * (16 * ℓ ^ 2 / 49) + 8 * ℓ ^ 2 / 49 + 1 ∧ Gext L ℓ ρ Cf cm ε) ∧
      ValidConcl L ℓ A ρ κ cg cm cT ε ∧ LastValidConcl L ℓ ρ ∧ ZeroTOk L ρ ∧
      WinHyp L ℓ A ρ κ cg cm cT ε ∧ GlueD L ℓ A ρ κ cm cT ε Cf Cb ∧
      SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ GlueNuD L ℓ A ρ κ cm cT ε ∧
      ∃ C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ,
        StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx ∧
        (∀ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ → Eext L A (cR R₀ ((L : ℝ) ^ 2) cm C₂x) (cx κ cT) ε) ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
        R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
      ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
        ApHyp (R.withMsq m) ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧
        (∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧
        BandF1 (R.withMsq m) Nh κ cg cm cT ε := by
  obtain ⟨L₀, hL₀⟩ := flow_master_hyp0LZD Aext hAext Eext hEext Gext hGext
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, Cf, Cb, CNW, AZ, cz, KG, Kz, hAx, hGx, hAZ, hcz, hKG,
    hKz, C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx, hCNW, hkf, hε1, hℓ, hA, hρ, hε,
    hκ0, hκ1, hcg, hcm, hcT, hKe, hCL, hCf, hCb, hCbε, hcgε, he, ha0, hs, hC, hρ8, hspl, hZT, hcov, hVLast, h⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo, hp₂, hr₂, hz₂, hq₂⟩ := hC
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hL2n : 2 ≤ L := le_trans (le_max_right _ _) hL
  have hβ : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have heR : 0 ≤ eRange (betaL L) Ke 1 := by unfold eRange; positivity
  obtain ⟨KZ, hKZd⟩ : ∃ KZ : ℝ, KZ = logTrajK (betaL L) cg AZ (1 / 3) + AZ * 4 +
      1 / 3 * (2 * (1 + betaL L) * eRange (betaL L) Ke 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ logTrajK (betaL L) cg AZ (1 / 3) := by
    unfold logTrajK Cgu; positivity
  have hKZ : 0 ≤ KZ := by rw [hKZd]; positivity
  have hc : FinConstZ L ρ κ cg cm cT ε CL aB := ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs,
    ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo⟩⟩
  -- the conclusions of `thm_flow_complete2X`
  have hC2 : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb := by
    refine ⟨hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hCf, hCb, hCbε, hρ8, hspl,
      fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
    have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
        (eRange (betaL L) Ke 1) ∧
        (∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
          GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) ∧
            BandOut (R.withMsq m) Nh Cb (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) ∧
        StrictMonoOn (gFinB R κ cm cT Nh ε m) (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := by
      intro m hm
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, hglue, htop, -, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le
      have hmass : m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
        have := msq_horizon (L := (L : ℝ)) (by linarith) hm.2 (Nh := Nh) (k := 0) (by omega)
        simpa using this
      obtain ⟨hVL, TOP⟩ := htop hNh
      have hmono := gFin_strictMonoOn (R.withMsq m) hRℓ H HM hCo hp₂ hr₂ hz₂ hq₂ hV hVL TOP
        (fun b μ₀ hb => (hglue hNh b μ₀ hb.1).1) hCL hCf hCNW hε hε1 hL2n hkf
      refine ⟨⟨hV, H, HZ, HM, HD, e,
        { hc := hcg.le, he := he0
          hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 hmass heb hej
          F1s := F1s }⟩, fun b μ₀ hb => ⟨(hglue hNh b μ₀ hb.1).1, (hglue hNh b μ₀ hb.1).2.1⟩, ?_⟩
      refine hmono.mono fun b hb => ?_
      obtain ⟨μ, hμ, -⟩ := hb
      exact ⟨μ, hμ⟩
    obtain ⟨hFix, hMsq⟩ := flow_finalZ_of hc R hP hRρ (by omega) (by omega) le_rfl
      (fun m hm => (hyp m hm).1)
    have hcont := gFinB_contOn R (S := mRange L N) le_rfl (κ := κ) (cm := cm) (cT := cT) (ε := ε)
      (by omega) (by rw [hRρ]; exact hρ.le) (by rw [hRρ]; exact hρ8)
      (by rw [hP, hRρ]; exact hcov N (by omega)) (fun m hm => (hyp m hm).1.valid) hMsq
    obtain ⟨s1, s2⟩ := complete_shoot R hFix (fun m hm b μ₀ hb => ((hyp m hm).2.1 b μ₀ hb).2)
      hcont hε hCb hCbε
    have hmono : ∀ m ∈ mRange L N, StrictMonoOn (gFinB R κ cm cT Nh ε m)
        (Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε) := fun m hm => (hyp m hm).2.2
    refine ⟨hFix, hMsq, fun m hm => (hyp m hm).2.1, hcont, s1, s2, hmono, ?_, ?_, ?_⟩
    · intro m hm βR hβR
      obtain ⟨b, hb, hby⟩ := s1 m hm βR hβR
      refine ⟨b, ⟨hb, hby⟩, fun b' hb' => ?_⟩
      rcases lt_trichotomy b' b with hlt | heq | hgt
      · have := hmono m hm hb'.1 hb hlt; rw [hb'.2, hby] at this; exact absurd this (lt_irrefl _)
      · exact heq
      · have := hmono m hm hb hb'.1 hgt; rw [hb'.2, hby] at this; exact absurd this (lt_irrefl _)
    · intro βR hβR
      have hspec : ∀ m ∈ mRange L N, bFin R κ cm cT Nh ε m (1 / βR) ∈
          Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε ∧
          gFinB R κ cm cT Nh ε m (bFin R κ cm cT Nh ε m (1 / βR)) = 1 / βR :=
        fun m hm => bFin_spec R (s1 m hm βR hβR)
      refine ⟨hspec, contOn_shoot (U := fun m => Ufix (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε)
        (f := gFinB R κ cm cT Nh ε) hMsq.isOpen hcont hmono hspec⟩
    · intro m hm
      exact ⟨(hyp m hm).1.valid, ((h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh
        hNh.le).2.2.1 hNh).1⟩
  -- the conclusions of `thm_flow_final_spinX`
  have hSpD : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ (gamKX L cz KG Kz) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh
    have hmass : ∀ m ∈ mRange L N, m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := fun m hm => by
      have := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
        (by omega)
      simpa using this
    have hLS : ∀ m ∈ mRange L N, LogSumD (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact logSum_ofD H he hε1 hcgε he0 heb
        (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
    have hSS : ∀ m ∈ mRange L N, SpinSumD (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact spinSum_ofD H he hε1 hcgε he0 heb
        (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
    have hBA : ∀ m ∈ mRange L N, BetaAsymD (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact betaAsym_ofD H he hε1 hcgε he0 heb
        (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
    refine ⟨hLS, hSS, hBA, fun m hm b μ₀ hadm k hk => ?_, fun m hm b μ₀ hadm n hn => ?_,
      fun m hm b μ₀ hadm k hk => ?_⟩
    · -- the per-step band
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      obtain ⟨-, -, -, -, hband, -⟩ := traj_factsD H he hε1 hcgε he0 heb F1s hadm
      have h1 := e_le_zA (β := betaL L) (Ke := Ke) (L := L) (m := m) heb hej hm.1.le hk
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (1 + betaL L))
      have h3 : 2 * (1 + betaL L) * e k ≤ 2 * (1 + betaL L) * max Ke (betaL L / 2) * zA L m k :=
        h2.trans_eq (by ring)
      exact (hband k hk).trans (add_le_add h3 le_rfl)
    · obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -, -, -, hZs, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
      have hD := traj_InDh_of H hadm
      have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ.le
      have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ8
      refine ⟨Z_succ_ne_zero (R.withMsq m) hρ0' hρ8' (fun i hi => hV i (by omega)) t, ?_⟩
      have key := hLS m hm b μ₀ hadm
        (fun k => Real.log ‖(rawHist (R.withMsq m) (k + 1) t).Z‖) (fun _ => 0) (zA L m) AZ
        (betaL L / 3) hAZ (zA_nonneg L hm.1.le)
        (fun k hk => by
          have := hZs k hk t (hD (k + 1) (by omega))
          simp only [sub_self, sub_zero]
          exact this) n hn
      have hy0 : Real.log ‖(rawHist (R.withMsq m) 1 t).Z‖ = 0 := by
        rw [rawHist_one_Z, norm_one, Real.log_one]
      have hy0' : Real.log ‖(rawHist (R.withMsq m) (0 + 1) t).Z‖ = 0 := hy0
      simp only [hy0, sub_self, sub_zero] at key
      have hβne : betaL L ≠ 0 := hβ.ne'
      have hs3 : |betaL L / 3| / betaL L = 1 / 3 := by
        rw [abs_of_pos (by positivity)]; field_simp
      have hs3' : betaL L / 3 / betaL L = 1 / 3 := by field_simp
      rw [hs3, hs3'] at key
      refine key.trans (mul_le_mul_of_nonneg_right ?_ ((hD n hn).1 n le_rfl).1.le)
      rw [hKZd]
      have hsa := sum_zA_le (Ln := L) rfl hL2 hm.1.le n
      have hmn : m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := by
        refine le_trans ?_ (hmass m hm)
        refine mul_le_mul_of_nonneg_left ?_ hm.1.le
        exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2])
          (by omega)) 2
      have := Real.pi_pos
      linarith only [hsa, hmn, mul_le_mul_of_nonneg_left (by linarith only [hsa, hmn] :
        ∑ k ∈ range n, zA L m k ≤ 4) hAZ]
    · obtain ⟨⟨e, hV, -, H, -⟩, -, -, -, -, hMzb, hcov0, hval⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      have hD := traj_InDh_of H hadm
      have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ.le
      have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ8
      exact ⟨gam_hist_bound (R.withMsq m) hP hNh hcz hKG hKz hL2 hm.1.le _ hV
        (fun j hj => hMzb j hj _ (hD j hj.le)) (fun j hj => hcov0 j hj _ (hD j hj.le)) hval
        (fun j hj => ((hD j hj.le).1 j le_rfl).1.le) k hk,
        Z_eq_norm_hist (R.withMsq m) hρ0' hρ8' _ _ _ (k + 1)⟩
  have hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ (gamKX L cz KG Kz) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh
    have hmass : ∀ m ∈ mRange L N, m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := fun m hm => by
      have := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
        (by omega)
      simpa using this
    have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
        (eRange (betaL L) Ke 1) := fun m hm => by
      obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
        h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
      exact ⟨hV, H, HZ, HM, HD, e,
        { hc := hcg.le, he := he0
          hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej
          F1s := F1s }⟩
    obtain ⟨c1, c2⟩ := flow_finalZ_of hc R hP hRρ hN (by omega) le_rfl hyp
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hSpD N R hP hi0 hRℓ hRA hRρ hN Nh hNh
    exact ⟨c1, c2, fun m hm b μ₀ h => d1 m hm b μ₀ h.1, fun m hm b μ₀ h => d2 m hm b μ₀ h.1,
      fun m hm b μ₀ h => d3 m hm b μ₀ h.1, fun m hm b μ₀ h => d4 m hm b μ₀ h.1,
      fun m hm b μ₀ h => d5 m hm b μ₀ h.1, fun m hm b μ₀ h => d6 m hm b μ₀ h.1⟩
  have hVC : ValidConcl L ℓ A ρ κ cg cm cT ε := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨⟨e, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact ⟨hV, fun b μ₀ hadm k hk => (traj_facts H he hε1 hcgε he0 heb F1s hadm).2.2.2.1 k hk⟩
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, gamKX L cz KG Kz, hC2, hε1, hKZ,
    gamKX_nonneg hL2 hcz hKG hKz, hSp, hAx, ⟨hGx.1, hGx.2.1⟩, hVC,
    (fun N R hP hRℓ hRρ hN Nh hNh m hm =>
      hVLast N (R.withMsq m) hP hRℓ hRρ (by omega) hm.1 hm.2 Nh hNh), hZT,
    ⟨CL, aB, hGx.2.2, he, hcgε, ha0, hs, ⟨p, q, r, s, p₂, q₂, r₂, z₂, hCo⟩, hcov,
      fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm => by
        obtain ⟨⟨e, hV, HD, H, HZ, HM, -⟩, -⟩ :=
          h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le
        exact ⟨H, HZ, HM⟩⟩,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD =>
      ⟨((h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le).2.1 hNh b μ₀ hD).1,
        ((h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le).2.1 hNh b μ₀ hD).2.1⟩,
    hSpD,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD =>
      ((h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le).2.1 hNh b μ₀ hD).2.2,
    C₀x, ηx, εsx, CKx, C₂x, CDx, Cqx, Clx, cSx, hSBx, hEx,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm =>
      (h N (R.withMsq m) hP hi0 hRℓ hRA hRρ (by omega) hm.1 hm.2 Nh hNh.le).2.2.2.1⟩

/-- **The master flow theorem** (along admissible trajectories; a projection of
`thm_flow_masterLZW`). One construction of the constants for: `thm_flow_complete2X`
(`FlowC2Concl`: `thm:flow` with the last two steps and the shooting `Re ǧ_N = 1/β_R`; the external
requirements `A ∈ Aext L`, `ε ∈ Eext …`; the exported bulk data) and `SpinConcl` (the
conclusions of `thm_flow_final_spinX` and the per-step band of `β_j`). -/
theorem thm_flow_master (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (Eext : ℕ → ℝ → ℝ → ℝ → ℝ → Prop)
    (hEext : ∀ (L : ℕ) (A c c' : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), Eext L A c c' ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ, FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧
      ε ≤ 1 ∧ 0 ≤ KZ ∧ 0 ≤ KG ∧ SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ Aext L A ∧
      ValidConcl L ℓ A ρ κ cg cm cT ε ∧
      ∃ C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx : ℝ,
        StepBounds L A C₀x ηx εsx CKx C₂x CDx Cqx Clx cSx ∧
        (∀ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ → Eext L A (cR R₀ ((L : ℝ) ^ 2) cm C₂x) (cx κ cT) ε) ∧
      ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
        R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
      ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
        ApHyp (R.withMsq m) ((L : ℝ) ^ 2) κ cg cm cT ε εsx C₀x C₂x Cqx Clx cSx ∧
        (∀ j < Nh, |(R.withMsq m).msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) ∧
        BandF1 (R.withMsq m) Nh κ cg cm cT ε := by
  obtain ⟨L₀, h0⟩ := thm_flow_masterLZW Aext hAext Eext hEext (fun _ _ _ _ _ _ => True)
    (fun _ _ _ _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hAx, -, hVC,
    -, -, -, -, -, -, hrest⟩ := h0 L hL
  exact ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, hC2, hε1, hKZ, hKG, hSp, hAx, hVC, hrest⟩

end

end Spin2
