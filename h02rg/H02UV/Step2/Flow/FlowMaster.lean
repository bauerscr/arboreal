import Step2.Flow.FlowBase
import Step2.Flow.FlowSharp1
import Step2.Flow.FlowHor2Aux
import Step2.Flow.FlowFinalZAux
import Step2.FlowCont.FlowMsqStep
import Step2.FlowCont.FlowDiffClamp
import Flow2.Shoot
import Flow2.FixedRParamZ3
import Flow2.Complete2
import Step2.Flow.ZetaSharp5
import Step2.Flow.FlowWin2
import Step2.Map.SplitSmall
import Step2.Last.FlowLastBand2
import Step2.Last.FlowLastLip6
import Step2.Last.FlowLastF1b
import Step2.Last.ZeroTOk

/-!
# The master theorem of the `Step2/Flow` theorem chain

`flow_master`: **one** construction of the constants of the flow (`ℓ, A, ρ, κ, c_g, c_m, c_T, ε`
and the derived constants), uniform in `N`, `m²` and the horizon `N_h ≤ N - 2`, with

* an external requirement `Aext L A` on `A` (any set containing a half-line), and
* an external requirement `P L k ε` on `ε`, which may depend on all constants `k : FlowConsts`
  fixed before `ε`, and must hold for all small `ε > 0` (`∀ᶠ ε in 𝓝[>] 0, P L k ε`).

The conclusions are bundled in two structures:

* `FlowUniform L k ε`: the numerical conditions on the constants (independent of `N`, `R`,
  `N_h`), the validity of the last step, `CovContM`, `SplitSmall`, `ZeroTOk`;
* `FlowExport L k ε a_B R N_h`: everything exported for one `(N, R, N_h)`: `ValidAt`, `HDiff`,
  `HHyp`, `ZHyp`, `MonoZHyp`, the sharp (F1) with the summable `e_j`, the last two steps
  (`GlueOut`, `BandOut`, the `ν`-bound, the sharp band `BandSharp` at `N_h = N - 2`), the step
  `N_h` of the Lipschitz layer, `ApHyp` and the band (F1), and the dressed-covariance data (sharp
  `log|Z|` steps, `M_z`, `|Z C(0,0)|`, the value of `Z C(0,0)`).

The proof is the merge of the former proofs of `flow_master_hyp0LZD`
(`FlowMasterHypLZ.lean`) and `flow_band_hyp0` (`FlowCompleteBandHyp.lean`): the one-loop inputs are
the `ValidAtL` versions `HV_histU`, `HVs_histU`, `HD_histU`, `S01_histU`, and the sharp band at
`N_h = N - 2` uses `F1_rg_sharpL`. The theorems `thm_flow`, `thm_flow_sharp`, `thm_flow_hor2`,
`flow_finalZ_hyp0`, `flow_finalZ_hyp0_zetaX`, `flow_finalZ_hyp0_zeta`, `flow_complete_hyp0`,
`flow_band_hyp0`, `flow_complete2_hyp0X`, `flow_complete2_hyp0`, `flow_master_hyp0L`,
`flow_master_hyp0LZD` are corollaries (same names, same statements, in their old files).

The helpers `G_eq_kern`, `XG_value_hist` (from `ZetaSharpHypX.lean`), `pTwo`, `bMu`, `bZe`, `bWz`,
`kFin`, `BandF1` (from `FlowComplete2Hyp.lean`) and `inDh_rg_of_D` (from `FlowMasterHypLZ.lean`)
are stated here, unchanged.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-! ### Helpers (moved here unchanged) -/

section

variable {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `Z_{k+1} C_k(0, 0)` is the dressed `C'_{k+1}(0, 0)`. -/
theorem G_eq_kern (hP : R.P = Pc) {k : ℕ} (hV : ∀ i ≤ k, ValidAt R i) (t : Hist.Seq (Xs R)) :
    stZ' R (rawHist R k t) * stCov R k (rawHist R k t) 0 0 =
      DressedFRD.kern ((dData L N R.msq (zh R k t)).Z (k + 1) • (dData L N R.msq (zh R k t)).Gint k)
        0 := by
  rw [stZ'_eq_dData R hV t, stCov_eq_dData R hP t le_rfl, DressedFRD.kern_smul]
  simp only [DressedFRD.kmat, sub_zero]

end

/-- **The values of `C'_{k+1}(e₁,0)` and `C'_{k+1}(0,0)` along histories**, one `ζ̄`. -/
theorem XG_value_hist : ∀ (L : ℕ) [NeZero L], 7 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K : ℝ, 0 ≤ K ∧
    (∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) (dirVec (Sum.inl 0)) 0 -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 / ((L : ℝ) ^ k) ^ 2 +
            ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
          K * (dData L N R.msq (zh R k t)).Mz (k + 1)) ∧
    (∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) 0 0 -
            (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k) ^ 2 +
            ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
          K * (dData L N R.msq (zh R k t)).Mz (k + 1)) := by
  intro L _ hL
  obtain ⟨ζbar, hζ, K, hK⟩ := Cprime_values (q := 2) le_rfl hL
  refine ⟨ζbar, hζ, max K 0, le_max_right _ _, fun N R _ _ hP hN hm0 hm hρ k hk1 hkN hV t => ?_,
    fun N R _ _ hP hN hm0 hm hρ k hk1 hkN hV t => ?_⟩
  · have hz := (hist_dData_hyps R hP hV t).1
    rw [X_eq_kern R hP hV t]
    have h := (hK (L ^ N) N R.msq (zh R k t) hN rfl hm0 hm (fun i => (hz i).trans hρ) k hk1 hkN).2
    have hM := (dData L N R.msq (zh R k t)).Mz_nonneg (k + 1)
    have h2 : K * (dData L N R.msq (zh R k t)).Mz (k + 1) ≤
        max K 0 * (dData L N R.msq (zh R k t)).Mz (k + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    exact h.trans (by linarith only [h2])
  · have hz := (hist_dData_hyps R hP hV t).1
    rw [G_eq_kern R hP hV t]
    have h := (hK (L ^ N) N R.msq (zh R k t) hN rfl hm0 hm (fun i => (hz i).trans hρ) k hk1 hkN).1
    have hM := (dData L N R.msq (zh R k t)).Mz_nonneg (k + 1)
    have h2 : K * (dData L N R.msq (zh R k t)).Mz (k + 1) ≤
        max K 0 * (dData L N R.msq (zh R k t)).Mz (k + 1) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hM
    exact h.trans (by linarith only [h2])


/-- The explicit `p₂` of `monoZCoef_of_small_b` for `A = A_ζ = C_L`, `b_ζ = 4`, `Λ = L²`. -/
def pTwo (L : ℕ) (CL : ℝ) : ℝ := 32 * (CL + 2 * (4 + 1) * (CL + 1) + 1) / ((L : ℝ) ^ 2 - 1)

/-- The coefficient of `δǧ_{N_h}` in `|δμ_{N_h+1}|` along the cone. -/
def bMu (L : ℕ) (CL : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * pTwo L CL + CL * (4 + 2 * pTwo L CL) + 4 * (2 * (2 * CL + 1))

/-- The coefficient of `δǧ_{N_h}` in `|δζ_{N_h+1}|` along the cone. -/
def bZe (L : ℕ) (CL : ℝ) : ℝ := CL * (4 + 2 * pTwo L CL)

/-- The coefficient of `δǧ_{N_h}` in `|δ nW1H_{N_h+1}|` along the cone. -/
def bWz (L : ℕ) (ℓ CL CNW : ℝ) : ℝ := 2 * ℓ ^ 2 * bZe L CL + CNW * (2 + pTwo L CL)

/-- The constant of the last map. -/
def kFin (L : ℕ) (ℓ CL Cf CNW : ℝ) : ℝ :=
  Cf * (64 * ℓ ^ 2 + 40 / 7 * ℓ ^ 2 + 256 / 49 * (ℓ ^ 2 * bMu L CL + Cf * bWz L ℓ CL CNW))

/-- The band (F1) of the steps `j < N_h` (exported by `flow_complete2_hyp0X`). -/
def BandF1 {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (κ cg cm cT ε : ℝ) :
    Prop :=
  ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
    |(rgData R).G j t - (t j).1 - betaL L * (t j).1 ^ 2| ≤
      1 / 2 * betaL L * (t j).1 ^ 2 + cg * (t j).1 ^ 3

/-- `admissible_InDh_rg` without the final condition: trajectories of `rgData` in `D_ε` up to `N_h`
are regular (from (F1)). -/
theorem inDh_rg_of_D {L N : ℕ} [NeZero L] (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}
    (F1 : ∀ j < Nh, ∀ t, Hist.InDh Λ β δ κ cg cm cT ε j t →
      |(rgData R).G j t - (t j).1 - β * (t j).1 ^ 2| ≤ δ * β * (t j).1 ^ 2 + cg * (t j).1 ^ 3)
    {b μ₀ : ℝ} (h : ∀ j ≤ Nh, Hist.InD3 Λ κ cm cT ε (Hist.traj (rgData R) Λ b μ₀ j)) :
    ∀ j ≤ Nh, Hist.InDh Λ β δ κ cg cm cT ε j (Hist.traj (rgData R) Λ b μ₀) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨fun i hi => h i (by omega), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    have hs := ih (by omega)
    refine ⟨fun i hi => h i (by omega), fun i hi => ?_⟩
    rcases (show i = j ∨ i < j by omega) with rfl | hij
    · rw [traj_succ_rg R Λ b μ₀ i]; exact F1 i (by omega) _ hs
    · exact hs.2 i hij

/-! ### The bundles -/

/-- The constants of the flow construction that are fixed before `ε`. -/
structure FlowConsts where
  /-- the norm parameter `ℓ` -/
  ℓ : ℝ
  /-- the norm parameter `A` -/
  A : ℝ
  /-- the size `ρ` of the dressing parameters -/
  ρ : ℝ
  /-- the contraction rate `κ` of the irrelevant coordinates -/
  κ : ℝ
  /-- the cubic constant `c_g` of (F1) -/
  cg : ℝ
  /-- the constant `c_m` of (F2) -/
  cm : ℝ
  /-- the constant `c_T` of (F3) -/
  cT : ℝ
  /-- the constant `K_e` of the summable `e_j` -/
  Ke : ℝ
  /-- the Lipschitz constant `C_L` -/
  CL : ℝ
  /-- the constant `C_f` of the last two steps -/
  Cf : ℝ
  /-- the constant `C_b` of the weak band at `N - 2` -/
  Cb : ℝ
  /-- the constant `C_NW` of `nW1H` at `N - 1` -/
  CNW : ℝ
  /-- the cubic constant `C_s` of the sharp band at `N - 2` -/
  Cs : ℝ
  /-- the constant `A_Z` of the sharp `log|Z|` steps -/
  AZ : ℝ
  /-- the constant `c_z` of `M_z(j+1) ≤ 2 c_z ǧ_j` -/
  cz : ℝ
  /-- the constant `K_G` of the value of `Z C(0,0)` -/
  KG : ℝ
  /-- the bound `K_z` of `|Z C(0,0)|` -/
  Kz : ℝ
  /-- the constants of the step bounds `StepBounds L A C₀ η εs CK C₂ CD Cq Cl cS` -/
  C₀ : ℝ
  η : ℝ
  εs : ℝ
  CK : ℝ
  C₂ : ℝ
  CD : ℝ
  Cq : ℝ
  Cl : ℝ
  cS : ℝ

section Bundles

variable (L : ℕ) [NeZero L]

/-- **The uniform conclusions of `flow_master`**: the numerical conditions on the constants `k` and
`ε` (independent of `N`, `R`, `N_h`), and the `N`-uniform validity and covariance facts. -/
structure FlowUniform (k : FlowConsts) (ε : ℝ) : Prop where
  hℓ : 0 < k.ℓ
  hA : 0 < k.A
  hρ : 0 < k.ρ
  hε : 0 < ε
  hε1 : ε ≤ 1
  hκ0 : 0 ≤ k.κ
  hκ1 : k.κ < 1
  hcg : 0 < k.cg
  hcm : 0 < k.cm
  hcT : 0 < k.cT
  hKe : 0 ≤ k.Ke
  hCL : 0 ≤ k.CL
  hCf : 0 ≤ k.Cf
  hCb : 0 ≤ k.Cb
  hCNW : 0 ≤ k.CNW
  hCs : 0 ≤ k.Cs
  hAZ : 0 ≤ k.AZ
  hcz : 0 ≤ k.cz
  hKG : 0 ≤ k.KG
  hKz : 0 ≤ k.Kz
  cm_eq : k.cm = 3 * (L : ℝ) ^ 2 * (16 * k.ℓ ^ 2 / 49) + 8 * k.ℓ ^ 2 / 49 + 1
  hKhW : Kh ((1 + (L : ℝ) ^ 2) / 2) k.κ k.CL * (k.CL * ε) * cmu ((L : ℝ) ^ 2) k.cm ≤ 1 / 12
  step : StepBounds L k.A k.C₀ k.η k.εs k.CK k.C₂ k.CD k.Cq k.Cl k.cS
  hkFin : kFin L k.ℓ k.CL k.Cf k.CNW * ε ≤ 1 / 2
  hCbε : 2 * k.Cb * ε ≤ 1 / 4
  hgβ : k.cg * ε ≤ betaL L / 4
  he : ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm
  ha0 : k.CL * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) k.κ k.CL
  hs : 4 * sZ k.CL (k.CL * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) k.κ k.CL * (k.CL * ε))
      (Qh k.κ * (k.CL * ε)) ≤ ((L : ℝ) ^ 2 - 1) / 4
  mono : ∃ p q r s p₂ q₂ r₂ z₂ : ℝ,
    MonoZCoef ((L : ℝ) ^ 2) k.κ k.CL (k.CL * ε) k.CL 4 (3 / 4) p q r s p₂ q₂ r₂ z₂ ∧
      p₂ = pTwo L k.CL ∧ r₂ = 2 + p₂ ∧ z₂ = 2 * (2 * k.CL + 1) ∧ q₂ ≤ 1
  hρ8 : k.ρ ≤ 1 / 8
  split : SplitSmall Pc L k.ρ
  zeroT : ZeroTOk L k.ρ
  cov : ∀ N : ℕ, 1 ≤ N → CovContM Pc L N 2 k.ρ
  validLast : ∀ (N : ℕ) (R : RGPar 2 L N), R.P = Pc → R.ℓ = k.ℓ → R.ρ = k.ρ → 1 ≤ N →
    0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ∀ Nh : ℕ, Nh + 2 = N →
      LastN.ValidLast R (Nh + 1)

/-- **The exports of `flow_master` for one `(N, R, N_h)`** (`N_h + 2 ≤ N`). -/
structure FlowExport (k : FlowConsts) (ε aB : ℝ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)]
    [Fact (0 < R.A)] (Nh : ℕ) : Prop where
  valid : ∀ j < Nh, ValidAt R j
  HD : HDiff (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT Nh ε
  H : HHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT Nh k.CL aB ε
  HZ : ZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT Nh (zetaH R) k.CL
    (k.CL * ε) k.CL (k.CL * ε) 4 ε
  HM : MonoZHyp (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT Nh (zetaH R) k.CL
    (k.CL * ε) k.CL 4 ε (3 / 4)
  sharp : ∃ e : ℕ → ℝ, (∀ j, 0 ≤ e j) ∧
    (∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT ε j t →
      |(rgData R).G j t - (t j).1 - betaL L * (t j).1 ^ 2| ≤
        e j * (t j).1 ^ 2 + k.cg * (t j).1 ^ 3) ∧
    (∀ j < Nh, e j ≤ 1 / 2 * betaL L) ∧
    (∀ j, 1 ≤ j → e j ≤ k.Ke * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2))
  glue : Nh + 2 = N → ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) k.κ k.cm k.cT ε (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j)) →
    GlueOut R Nh k.Cf (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
      BandOut R Nh k.Cb (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
      ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ.nu /
          (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).Z -
        (L : ℂ) ^ 4 * (((traj (rgData R) ((L : ℝ) ^ 2) b μ₀ Nh).2.1 : ℝ) : ℂ)‖ ≤
        cNuLast R ((L : ℝ) ^ 2) k.cm ε * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ Nh).1 ∧
      BandSharp R Nh (betaL L) k.Ke k.Cs (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)
  top : Nh + 2 = N → ValidAtL R Nh ∧
    ∀ t t', InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT ε Nh t →
      InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT ε Nh t' →
    ∀ M, 0 ≤ M → (∀ i < Nh, (3 / 4 : ℝ) ^ (Nh - 1 - i) * dist3 (t i) (t' i) ≤ M) →
    |(rgData R).G Nh t - (rgData R).G Nh t' - ((t Nh).1 - (t' Nh).1)| ≤
      k.CL * ε * |(t Nh).1 - (t' Nh).1| +
      k.CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + k.CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ + k.CL * ε * M ∧
    |(rgData R).m Nh t - (rgData R).m Nh t'| ≤ k.CL * |(t Nh).1 - (t' Nh).1| +
      k.CL * ε * |(t Nh).2.1 - (t' Nh).2.1| + k.CL * ‖(t Nh).2.2 - (t' Nh).2.2‖ +
      k.CL * ε * M + 4 * ‖zetaH R Nh t - zetaH R Nh t'‖ ∧
    ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ ≤
      k.CL * (|(t Nh).1 - (t' Nh).1| + ‖(t Nh).2.2 - (t' Nh).2.2‖) +
      k.CL * ε * (|(t Nh).2.1 - (t' Nh).2.1| + M) ∧
    ‖nW1H R (Nh + 1) t - nW1H R (Nh + 1) t'‖ ≤
      2 * k.ℓ ^ 2 * ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ + k.CNW * M
  aph : ApHyp R ((L : ℝ) ^ 2) k.κ k.cg k.cm k.cT ε k.εs k.C₀ k.C₂ k.Cq k.Cl k.cS
  msq1 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1
  band : BandF1 R Nh k.κ k.cg k.cm k.cT ε
  zsteps : ∀ k' < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT ε (k' + 1) t →
    |Real.log ‖(rawHist R (k' + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k' + 1) t).Z‖ +
      betaL L / 3 * (t k').1| ≤ k.AZ * (t k').1 ^ 2 + k.AZ * (t k').1 * zA L R.msq k'
  Mz : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT ε j t →
    (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * k.cz * (t j).1
  covZ : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) k.κ k.cg k.cm k.cT ε j t →
    ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) 0 0‖ ≤ k.Kz
  covVal : ∀ k', 1 ≤ k' → k' + 1 < N → (∀ i ≤ k', ValidAt R i) → ∀ t : Hist.Seq (Xs R),
    ‖stZ' R (rawHist R k' t) * stCov R k' (rawHist R k' t) 0 0 -
        (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
      (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k') ^ 2 +
        ErrB * R.msq * (((L : ℝ) ^ k') ^ 2 + ((L : ℝ) ^ (k' + 1)) ^ 2)) +
      k.KG * (dData L N R.msq (zh R k' t)).Mz (k' + 1)

end Bundles

set_option maxHeartbeats 20000000 in
/-- **The master theorem of the `Step2/Flow` chain.** For all large `L` there are constants
`k : FlowConsts` fixed before `ε`, a scale `ε` and a Lipschitz constant `a_B` with `Aext L k.A`,
the external requirement `P L k ε`, the uniform conclusions `FlowUniform L k ε`, and, for every `N`,
every `R` with `P = Pc`, `i₀ = 0`, the parameters `ℓ, A, ρ` of `k`, every mass
`0 < m² ≤ L^{-2(N-1)}` and every horizon `N_h + 2 ≤ N`, the exports `FlowExport L k ε a_B R N_h`. -/
theorem flow_master (Aext : ℕ → ℝ → Prop) (hAext : ∀ L : ℕ, ∃ A₀ : ℝ, ∀ A, A₀ ≤ A → Aext L A)
    (P : ℕ → FlowConsts → ℝ → Prop) (hP : ∀ (L : ℕ) (k : FlowConsts), ∀ᶠ ε in 𝓝[>] (0 : ℝ), P L k ε) :
    ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (k : FlowConsts) (ε aB : ℝ), Aext L k.A ∧ P L k ε ∧ FlowUniform L k ε ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = k.ℓ → R.A = k.A → R.ρ = k.ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → FlowExport L k ε aB R Nh := by
  obtain ⟨C₀s, ηs, L₀s, hC₀s, hηs, hSBs⟩ := Last.rg_step_bounds
  obtain ⟨Cqg, Clg, cSg, hCqg, hClg, hcSg, hGBs⟩ := g_step_bounds
  obtain ⟨Cqb, Clb, cSb, hCqb, hClb, hcSb, hGBds⟩ := g_step_band
  obtain ⟨LN, hLN⟩ := LastN.rg_last_boundsP
  obtain ⟨C₀l, ηl, L₀l, hC₀l, hηl, C₀K, ηK, C₀W, C₀D, Cqk, Clk, cSk, Cqs, Cls, cSs, hC₀K, hηK,
    hC₀W, hC₀D, hCqk, hClk, hcSk, hCqs, hCls, hcSs, hLip⟩ := LL.lip_rg_z2
  obtain ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, hF1⟩ := F1_rg_sharp
  obtain ⟨CqL, ClL, cSL, CqDL, ClDL, hCqL, hClL, hcSL, hCqDL, hClDL, hF1L⟩ := F1_rg_sharpL
  obtain ⟨E0, hE0, hHV⟩ := HV_histU
  obtain ⟨M₀, M₂, hM₀, hM₂, hS01⟩ := S01_histU
  obtain ⟨Cqζ, Clζ, cSζ, hCqζ, hClζ, hcSζ, hZSB2⟩ := zeta_step_bounds2
  obtain ⟨C₄, hC₄, hZcov⟩ := Zcov_hist
  obtain ⟨Lz, hLzd⟩ : ∃ Lz : ℝ, Lz = 7 * (2 * C₄ + 4) * (M₀ + 1) := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, C₀ = max C₀s C₀l := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = min ηs ηl := ⟨_, rfl⟩
  have hC₀0 : 0 ≤ C₀ := hC₀ ▸ le_max_of_le_left hC₀s
  have hη0 : 0 < η := hη ▸ lt_min hηs hηl
  obtain ⟨C0, hC0d⟩ : ∃ C0, C0 = max C0sh 0 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C0 := hC0d ▸ le_max_right _ _
  have hC0sh : C0sh ≤ C0 := hC0d ▸ le_max_left _ _
  obtain ⟨Lb, hLbd⟩ : ∃ Lb : ℝ, Lb = Real.exp (4 * Real.pi / 3 * (E0 + 2 * C0 + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨KA, hKAd⟩ : ∃ KA : ℝ, KA = 32 / 7 * (8 / 7 * (6 / 5 * (8 / 7 * C₄ + 4)) * (M₀ + 1)) :=
    ⟨_, rfl⟩
  obtain ⟨Lb2, hLb2d⟩ : ∃ Lb2 : ℝ, Lb2 = Real.exp (4 * Real.pi / 3 * (KA + E0 + 2 * C0 + 1)) :=
    ⟨_, rfl⟩
  refine ⟨max (max L₀s L₀l) (max (max LN 69)
    (max 49 (max ⌈pauliL0 2⌉₊ (max (⌈32 * C₀ + 1⌉₊) (max ⌈Lb⌉₊ (max ⌈Lz⌉₊ ⌈Lb2⌉₊)))))), fun L _ hL => ?_⟩
  have hLs : L₀s ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLl : L₀l ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL'0 := le_trans (le_max_right _ _) hL
  have hLNL : LN ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL'0
  have hL69 : 69 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL'0
  have hLg : 2 ^ (2 + 4) + 4 < L := by norm_num; omega
  have hL' := le_trans (le_max_right _ _) hL'0
  have hL49 : 49 ≤ L := le_trans (le_max_left _ _) hL'
  have hL'' := le_trans (le_max_right _ _) hL'
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) hL'')
  have hL''' := le_trans (le_max_right _ _) hL''
  have hL32 : 32 * C₀ + 1 ≤ (L : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_left _ _) hL''')
  have hLb : Lb ≤ (L : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL''')
  have hLz : Lz ≤ (L : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hL''')
  have hLb2 : Lb2 ≤ (L : ℝ) := (Nat.le_ceil _).trans (by
    exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_max_right _ _))) hL''')
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  -- the band
  have hβ0 : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
    positivity
  have hband0 : E0 + 2 * C0 + 1 ≤ 1 / 2 * betaL L := by
    have hlog : Real.log Lb ≤ Real.log L :=
      Real.log_le_log (by rw [hLbd]; exact Real.exp_pos _) hLb
    rw [hLbd, Real.log_exp] at hlog
    unfold betaL
    have hpi := Real.pi_pos
    rw [show 1 / 2 * (3 * (Real.log L / (2 * Real.pi))) = 3 / (4 * Real.pi) * Real.log L by
      field_simp; ring]
    have : E0 + 2 * C0 + 1 = 3 / (4 * Real.pi) * (4 * Real.pi / 3 * (E0 + 2 * C0 + 1)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hband2 : KA + E0 + 2 * C0 + 1 ≤ 1 / 2 * betaL L := by
    have hlog : Real.log Lb2 ≤ Real.log L :=
      Real.log_le_log (by rw [hLb2d]; exact Real.exp_pos _) hLb2
    rw [hLb2d, Real.log_exp] at hlog
    unfold betaL
    have hpi := Real.pi_pos
    rw [show 1 / 2 * (3 * (Real.log L / (2 * Real.pi))) = 3 / (4 * Real.pi) * Real.log L by
      field_simp; ring]
    have : KA + E0 + 2 * C0 + 1 = 3 / (4 * Real.pi) * (4 * Real.pi / 3 * (KA + E0 + 2 * C0 + 1)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  -- the constants at scale `L`
  obtain ⟨A₀s, hA₀s, hSBA⟩ := hSBs L hLs
  obtain ⟨A₀N, hA₀N, hLNA⟩ := hLN L hLNL
  obtain ⟨C₂W, C₃, hC₂W, hC₃, hLipP⟩ := hLip L hLl
  obtain ⟨ζl, Kc, hζl, hKc, A₀l, hA₀l, hLipA⟩ := hLipP Pc
  obtain ⟨ζHV, hζHV, E1, hE1, hHVL⟩ := hHV L hL49
  obtain ⟨ζHVs, hζHVs, E1s, hE1s, hHVsL⟩ := HVs_histU L hL49
  obtain ⟨ζHD, hζHD, KB, hKB, hHDL⟩ := HD_histU L hL49
  obtain ⟨ζS, hζS, hS01L⟩ := hS01 L hL49
  obtain ⟨ζZ, hζZ, Kzc, hKzc, hZcovL⟩ := hZcov L hL49
  obtain ⟨ζCp, hζCp, KCp, hKCp, hXvL, hGvL⟩ := XG_value_hist L (by omega)
  obtain ⟨ℓv, hℓv, ζv, hζv, hζv8, hVal⟩ := validAt_concrete (L := L) Pc hL8
  obtain ⟨ℓL, hℓL, ζL, hζL, -, hValL⟩ := validAtL_concrete (L := L) Pc hLg
  obtain ⟨ℓN, hℓN, ζN, hζN, -, hValN⟩ := LastN.validLastN_concrete (L := L) Pc hL8
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ : ℝ, ℓ = max ℓv (max ℓL ℓN) := ⟨_, rfl⟩
  have hℓ : 0 < ℓ := hℓd ▸ lt_max_of_lt_left hℓv
  have hℓv' : ℓv ≤ ℓ := hℓd ▸ le_max_left _ _
  have hℓL' : ℓL ≤ ℓ := hℓd ▸ le_trans (le_max_left _ _) (le_max_right _ _)
  have hℓN' : ℓN ≤ ℓ := hℓd ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨ζc, hζc, hCov⟩ := covDiff_of_small (d := 2) (L := L) Pc le_rfl (by omega)
  obtain ⟨ζM, hζM, hCovM⟩ := covContM_small (d := 2) (L := L) Pc le_rfl (by omega)
  obtain ⟨A₀x, hA₀x⟩ := hAext L
  obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = max (max (max A₀s A₀l) (max (2 * (32 * C₀ + 1) ^ η⁻¹) A₀N)) A₀x :=
    ⟨_, rfl⟩
  have hAx : Aext L A := hA₀x A (hAd ▸ le_max_right _ _)
  have hAs : A₀s ≤ A := hAd ▸ le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAl : A₀l ≤ A := hAd ▸ le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)
  have hAκ : 2 * (32 * C₀ + 1) ^ η⁻¹ ≤ A :=
    hAd ▸ le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hAN : A₀N ≤ A := hAd ▸ le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hA2 : 2 ≤ A := hA₀l.trans hAl
  have hA0 : 0 < A := by linarith
  obtain ⟨εs, CK, C₂, CD, Cq', Cl', cS', hεs, hCK, hC₂, hCD, hCq', hCl', hcS', hSB0⟩ := hSBA A hAs
  obtain ⟨ε₁, C₁, hε₁, hC₁, hLipR⟩ := hLipA A hAl
  obtain ⟨εsN, CKN, hεsN, hCKN, hLB⟩ := hLNA A hAN
  have hGB := hGBs L hL8 hLp A hA2
  have hGBd := hGBds L hL8 hLp A hA2
  have hSBL := hSB0.mono hC₀s (hC₀ ▸ le_max_left _ _) (hη ▸ min_le_left _ _) hA2
  have hSB := hSBL.toStepBounds hLg
  have hC₀l' : C₀l ≤ C₀ := hC₀ ▸ le_max_right _ _
  have hηl' : η ≤ ηl := hη ▸ min_le_right _ _
  obtain ⟨ρ', hρd⟩ : ∃ ρ : ℝ, ρ = min (min (ζl / 2) (min ζHV ζHVs)) (min (min ζHD ζS) (min ζv (min (ζc / 2) (ζM / 2)))) :=
    ⟨_, rfl⟩
  obtain ⟨ρ₁, hρρd⟩ : ∃ ρ : ℝ, ρ = min ρ' (min ζZ (min ζL ζN)) := ⟨_, rfl⟩
  obtain ⟨ζF, hζF, hSplitF⟩ := splitSmall_exists Pc (L := L) (by omega)
  obtain ⟨ζT, hζT, hZT⟩ := zeroTOk_of_d2 (L := L) (by omega)
  obtain ⟨ρ, hρ₁⟩ : ∃ ρ : ℝ, ρ = min (min ρ₁ ζF) (min ζCp ζT) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ₁, hρρd, hρd]; positivity
  have hρρ₁ : ρ ≤ ρ₁ := hρ₁ ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρF : ρ ≤ ζF := hρ₁ ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρCp : ρ ≤ ζCp := hρ₁ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hρT : ρ ≤ ζT := hρ₁ ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hρρ' : ρ ≤ ρ' := hρρ₁.trans (hρρd ▸ min_le_left _ _)
  have hρZ : ρ ≤ ζZ := hρρ₁.trans (hρρd ▸ le_trans (min_le_right _ _) (min_le_left _ _))
  have hρL : ρ ≤ ζL := hρρ₁.trans (hρρd ▸ le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρN : ρ ≤ ζN := hρρ₁.trans (hρρd ▸ le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρl : ρ ≤ ζl / 2 := hρρ'.trans (hρd ▸ le_trans (min_le_left _ _) (min_le_left _ _))
  have hρHV : ρ ≤ ζHV :=
    hρρ'.trans (hρd ▸ le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρHVs : ρ ≤ ζHVs :=
    hρρ'.trans (hρd ▸ le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hρHD : ρ ≤ ζHD := hρρ'.trans (hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hρS : ρ ≤ ζS := hρρ'.trans (hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hρv : ρ ≤ ζv := hρρ'.trans (hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρc : ρ < ζc := by
    have : ρ ≤ ζc / 2 := hρρ'.trans (hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
    linarith
  have hρM : ρ < ζM := by
    have : ρ ≤ ζM / 2 := hρρ'.trans (hρd ▸ le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
    linarith
  have hρ8 : ρ ≤ 1 / 8 := hρv.trans hζv8
  -- `κ₁ ≤ 1/2`
  obtain ⟨κ₁, hκ₁d⟩ : ∃ κ₁, κ₁ = kap1 L A C₀ η := ⟨_, rfl⟩
  have hκ₁h : κ₁ ≤ 1 / 2 := hκ₁d ▸ kap1_le_half hC₀0 hη0 hL32 hAκ
  have hκ₁0 : 0 ≤ κ₁ := hκ₁d ▸ kap1_nonneg hC₀0 hA0
  -- the reference parameters
  obtain ⟨R₀, hR₀ℓ⟩ : ∃ R₀ : RGPar 2 L 1, R₀.ℓ = ℓ := ⟨⟨Pc, 0, ℓ, A, 0, ρ⟩, rfl⟩
  have hΛ : (1 : ℝ) < (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
    nlinarith
  obtain ⟨κ, hκd⟩ : ∃ κ, κ = (1 + κ₁) / 2 := ⟨_, rfl⟩
  have hκ1 : κ < 1 := by rw [hκd]; linarith
  have hκ0 : 0 ≤ κ := by rw [hκd]; linarith
  obtain ⟨cz, hczd⟩ : ∃ cz, cz = cZ R₀ := ⟨_, rfl⟩
  have hcz : 0 ≤ cz := by rw [hczd]; unfold cZ; positivity
  obtain ⟨cm, hcmd⟩ : ∃ cm, cm = cF2 R₀ + 1 := ⟨_, rfl⟩
  have hcm : 0 < cm := by
    rw [hcmd]; unfold cF2 cZ; positivity
  obtain ⟨cmuv, hcmud⟩ : ∃ cmuv, cmuv = cmu ((L : ℝ) ^ 2) cm := ⟨_, rfl⟩
  have hcmu : 0 < cmuv := by rw [hcmud]; unfold cmu; have := sub_pos.2 hΛ; positivity
  obtain ⟨Cb, hCbd⟩ : ∃ Cb, Cb = cB R₀ ((L : ℝ) ^ 2) cm C₂ CK CD := ⟨_, rfl⟩
  have hCb : 0 ≤ Cb := by
    rw [hCbd]; unfold cB; exact le_max_of_le_left (by positivity)
  obtain ⟨cT, hcTd⟩ : ∃ cT, cT = Cb + 1 := ⟨_, rfl⟩
  have hcT : 0 < cT := by rw [hcTd]; linarith
  obtain ⟨cxv, hcxd⟩ : ∃ cxv, cxv = cx κ cT := ⟨_, rfl⟩
  have hcx : 0 ≤ cxv := by rw [hcxd]; unfold cx; have := sub_pos.2 hκ1; positivity
  obtain ⟨cV0, hcV0d⟩ : ∃ c, c = cV R₀ ((L : ℝ) ^ 2) cm := ⟨_, rfl⟩
  have hcV0 : 0 ≤ cV0 := by
    rw [hcV0d]; unfold cV cZ; have := hcmud ▸ hcmu.le; positivity
  obtain ⟨cw, hcwd⟩ : ∃ c, c = cW R₀ ((L : ℝ) ^ 2) cm C₂ := ⟨_, rfl⟩
  have hcw : 0 ≤ cw := by rw [hcwd]; unfold cW; rw [← hcV0d]; positivity
  -- the (F1) constants
  -- the sharp `ζ` constants and the (F1) mass constant
  obtain ⟨Kz, hKzd⟩ : ∃ Kz : ℝ, Kz = C₄ * (L : ℝ) ^ 2 + 1 := ⟨_, rfl⟩
  have hKz : 0 ≤ Kz := by rw [hKzd]; positivity
  obtain ⟨cζ, hcζd⟩ : ∃ cζ : ℝ, cζ = 6 / 5 * (8 / 7 * Kz + 2) := ⟨_, rfl⟩
  have hcζ : 0 ≤ cζ := by rw [hcζd]; positivity
  obtain ⟨eA, heAd⟩ : ∃ eA, eA = 8 / 7 * cζ * (M₀ + 1) * ((L : ℝ) ^ 4)⁻¹ := ⟨_, rfl⟩
  have heA : 0 ≤ eA := by rw [heAd]; positivity
  have heA1 : 32 / 7 * eA ≤ 1 := heA1_of hC₄ hM₀
    (show (1 : ℝ) ≤ L by exact_mod_cast (show 1 ≤ L by omega)) (by rw [← hLzd]; exact hLz) hKzd hcζd heAd
  have hband : 1 + (E0 + 2 * C0) ≤ 1 / 2 * betaL L := by linarith only [hband0]
  obtain ⟨cRQ, hcRQd⟩ : ∃ c, c = f1cRQ Cl cS cxv := ⟨_, rfl⟩
  obtain ⟨cRL, hcRLd⟩ : ∃ c, c = f1cRL L Cl cV0 cw := ⟨_, rfl⟩
  obtain ⟨cRD, hcRDd⟩ : ∃ c, c = f1cRD L ClD cxv := ⟨_, rfl⟩
  obtain ⟨cES, hcESd⟩ : ∃ c, c = (24 * (2 * cz) + 3 * f1cn ℓ cmuv + 2 * (2 * betaL L + 1)) * KB :=
    ⟨_, rfl⟩
  obtain ⟨cg, hcgd⟩ : ∃ cg, cg = max (f1c3s L ℓ cz cmuv Cq cRQ cRL CqD cRD KB cES 1) 0 +
      (E1 + E1s) * (2 * cz) + 1 := ⟨_, rfl⟩
  have hcg : 0 < cg := by rw [hcgd]; positivity
  obtain ⟨K1, hK1d⟩ : ∃ K1, K1 = 32 / 7 * (8 / 7 * cζ * (M₀ + 1)) := ⟨_, rfl⟩
  have hK1 : 0 ≤ K1 := by rw [hK1d]; positivity
  -- the constants of (F1) at the step `N - 2`
  obtain ⟨emL, hemLd⟩ : ∃ e, e = 32 / 7 * (8 / 7 * cζ * (M₀ + 1) * ((L : ℝ) ^ 2)⁻¹) := ⟨_, rfl⟩
  have hemL : emL ≤ KA := by
    rw [hemLd, hKAd, hcζd, hKzd]
    exact emL_le hC₄ hM₀ (by exact_mod_cast (show 1 ≤ L by omega))
  obtain ⟨cRQL, hcRQLd⟩ : ∃ c, c = f1cRQ ClL cSL cxv := ⟨_, rfl⟩
  obtain ⟨cRLL, hcRLLd⟩ : ∃ c, c = f1cRL L ClL cV0 cw := ⟨_, rfl⟩
  obtain ⟨cRDL, hcRDLd⟩ : ∃ c, c = f1cRD L ClDL cxv := ⟨_, rfl⟩
  obtain ⟨cgL, hcgLd⟩ : ∃ c, c = max (f1c3s L ℓ cz cmuv CqL cRQL cRLL CqDL cRDL KB cES emL) 0 +
      (E1 + E1s) * (2 * cz) + 1 := ⟨_, rfl⟩
  have hcgL : 0 < cgL := by rw [hcgLd]; positivity
  -- the Lipschitz constants
  obtain ⟨cEl, hcEld⟩ : ∃ c, c = cEr ℓ cz cw cxv cmuv := ⟨_, rfl⟩
  obtain ⟨bb, hbbd⟩ : ∃ c, c = bRem L Cqk Clk cSk (7 / 8 * ℓ) ℓ ((1 + 1) * (ℓ / 4)) 2 2 2 := ⟨_, rfl⟩
  obtain ⟨b₁, hb₁d⟩ : ∃ c, c = bR1 L Cqs Cls cSs ℓ cEl cxv := ⟨_, rfl⟩
  obtain ⟨κW, hκWd⟩ : ∃ c, c = C₀W * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3) := ⟨_, rfl⟩
  obtain ⟨CL, hCLd⟩ : ∃ c, c = cLipW L ℓ bb b₁ cmuv cz cxv cw Kc C₂W κW
      (C₀K * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3 + (A / 2) ^ (-ηK))) (C₀D * ((L : ℝ) ^ 2 / (L : ℝ) ^ 3))
      C₁ C₃ cEl := ⟨_, rfl⟩
  obtain ⟨CLp, hCLpd⟩ : ∃ c, c = max CL 0 := ⟨_, rfl⟩
  have hCLp : 0 ≤ CLp := hCLpd ▸ le_max_right _ _
  have hCLle : CL ≤ CLp := hCLpd ▸ le_max_left _ _
  obtain ⟨a₁, ha₁, hmonoZ⟩ := monoZCoef_of_small_b hΛ hκ0 hκ1 hCLp hCLp (by norm_num : (0 : ℝ) ≤ 4)
    (by norm_num : (3 / 4 : ℝ) < 1)
  obtain ⟨a0, ha0d⟩ : ∃ a0, a0 = a0h ((1 + (L : ℝ) ^ 2) / 2) κ CLp := ⟨_, rfl⟩
  have ha0 : 0 < a0 := ha0d ▸ a0h_pos' hΛ hκ1 hCLp
  obtain ⟨Xs0, hXsd⟩ : ∃ X : ℝ,
      X = 4 * (CLp * (2 * CLp * (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp + Qh κ) + 2)) := ⟨_, rfl⟩
  have hL4q : 0 < ((L : ℝ) ^ 2 - 1) / 4 := by linarith
  -- `F2`
  obtain ⟨cEv, hcEvd⟩ : ∃ c, c = cE R₀ ((L : ℝ) ^ 2) κ cm cT C₂ Cq' Cl' cS' := ⟨_, rfl⟩
  obtain ⟨cRv, hcRvd⟩ : ∃ c, c = cR R₀ ((L : ℝ) ^ 2) cm C₂ := ⟨_, rfl⟩
  have hcRv : 0 ≤ cRv := by rw [hcRvd]; unfold cR; rw [← hcV0d, ← hcwd]; positivity
  have heps0 : 0 < eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm := by
    unfold eps0u
    refine lt_min (eps0_pos hβ0 hκ1 hcg) ?_
    have hb : 0 < betap (betaL L) (1 / 2) cg := by unfold betap; positivity
    have : 0 < cmu ((L : ℝ) ^ 2) cm := hcmud ▸ hcmu
    positivity
  have hκ12 : 0 < (1 - κ₁) / 2 := by linarith
  obtain ⟨cEz, hcEzd⟩ : ∃ c, c = cE R₀ ((L : ℝ) ^ 2) κ cm cT C₂ Cqζ Clζ cSζ := ⟨_, rfl⟩
  -- the constants of the last two steps
  obtain ⟨cEg, hcEgd⟩ : ∃ c, c = cE R₀ ((L : ℝ) ^ 2) κ cm cT C₂ Cqg Clg cSg := ⟨_, rfl⟩
  obtain ⟨cRNv, hcRNd⟩ : ∃ c, c = cRN R₀ ((L : ℝ) ^ 2) κ cm cT C₂ CD := ⟨_, rfl⟩
  obtain ⟨cKLv, hcKLd⟩ : ∃ c, c = cKL R₀ ((L : ℝ) ^ 2) κ cm cT C₂ CK := ⟨_, rfl⟩
  obtain ⟨Cf, hCfd⟩ : ∃ c, c = cFin R₀ ((L : ℝ) ^ 2) κ cm cT C₂ CD CK CKN := ⟨_, rfl⟩
  have hCf : 0 ≤ Cf := by
    have := (le_cFin R₀ (hcmud ▸ hcmu.le) (hcxd ▸ hcx) hC₂ hCD hCK hCKN).2.2.1
    rw [hCfd]; linarith
  obtain ⟨Cbv, hCbvd⟩ : ∃ c, c = cBand R₀ ((L : ℝ) ^ 2) κ cm cT C₂ Cqb Clb cSb := ⟨_, rfl⟩
  have hℓ24 : 0 < ℓ ^ 2 / 24 := by positivity
  obtain ⟨CNW, hCNWd⟩ : ∃ c, c = max (LL.cNW L ℓ bb Kc) 0 := ⟨_, rfl⟩
  have hCNW : 0 ≤ CNW := hCNWd ▸ le_max_right _ _
  have hCNWle : LL.cNW L ℓ bb Kc ≤ CNW := hCNWd ▸ le_max_left _ _
  -- the constant of the sharp `ζ`-steps
  have hcEz0 : 0 ≤ cEz := by
    rw [hcEzd]; unfold cE
    have := hcx; have := hcRv; have := hcSζ
    have h1 : 0 ≤ cR R₀ ((L : ℝ) ^ 2) cm C₂ := by rw [← hcRvd]; exact hcRv
    have h2 : 0 ≤ cx κ cT := by rw [← hcxd]; exact hcx
    have h3 : (0 : ℝ) ≤ cNear 2 L := Nat.cast_nonneg _
    have h4 : 0 ≤ Q1 2 := le_trans zero_le_one (one_le_Q1 (by norm_num))
    have h5 : 0 ≤ cSζ := by linarith only [hcSζ]
    positivity
  have hErr1 := ErrC1_nonneg
  have hErrB := ErrB_nonneg
  obtain ⟨AZ, hAZd⟩ : ∃ AZ : ℝ, AZ = 7 * (2 * cEz + 8 / 7 * Kz) ^ 2 + 2 * cEz + 8 / 7 * Kz +
      |betaL L / 3| + 32 / 7 * cmuv * ℓ ^ 2 * Kz + KCp * (2 * cz) +
      (2 * Real.pi)⁻¹ ^ 2 * (ErrC1 + 2 * ErrB) := ⟨_, rfl⟩
  have hAZ : 0 ≤ AZ := by
    rw [hAZd]; positivity
  obtain ⟨k, hkd⟩ : ∃ k : FlowConsts, k = ⟨ℓ, A, ρ, κ, cg, cm, cT, K1 + C0, CLp, Cf, max Cbv 0, CNW, cgL, AZ, cz, KCp, Kz, C₀, η, εs, CK, C₂, CD, Cq', Cl', cS'⟩ := ⟨_, rfl⟩
  -- the choice of `ε`
  have hℓ147 : 0 < 16 * ℓ ^ 2 / 147 := by positivity
  have hβ2 : 0 < betaL L / 2 := by linarith
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (1 * ε ≤ 1 ∧ (2 * cz) * ε ≤ ρ ∧ (8 * cM * ℓ ^ 2 * cz) * ε ≤ 1 / 2 ∧ cxv * ε ≤ 1 ∧
      cRv * ε ≤ εs ∧ (8 * cxv) * ε ≤ εs ∧ cg * ε ≤ 1 / 6 ∧ cEv * ε ≤ 16 * ℓ ^ 2 / 147 ∧
      cg * ε ≤ betaL L / 2 ∧ cRv * ε ≤ 1 ∧ (8 * cxv) * ε ≤ 1) ∧
      (f1cn ℓ cmuv * ε ≤ 1 / 8 ∧ f1cn' L ℓ cz cmuv Cq cRQ cRL * ε ≤ 1 / 8 ∧
      (ℓ ^ 2 / 7 + f1cw ℓ cmuv Cq cRQ cRL) * ε ≤ ρ ∧
      (16 / 7 * (L : ℝ) ^ 2 * (8 * ℓ ^ 2 / 49 + (L : ℝ) ^ 2 * cEv) * cmuv +
        2 * ((L : ℝ) ^ 2 * cEv)) * ε ≤ 1) ∧
      ((2 * cz) * ε ≤ 1 / 16 ∧ cDl (7 / 8 * ℓ) cz * ε ≤ 1 / 4 ∧ cEl * ε ≤ 1 / 4 ∧ cEl * ε ≤ ε₁ ∧
      (4 * cmuv * ℓ ^ 2) * ε ≤ 1 / 8 ∧
      ((cEl + 1) * cCloW L ℓ bb cmuv cxv cw Kc C₂W κW) * ε ≤ 1 / 2 ∧ cSz b₁ ℓ * ε ≤ ρ ∧
      (cSz b₁ ℓ + cSn L b₁ cz ℓ cmuv) * ε ≤ 1 / 16) ∧
      ((Cb * (1 + cxv)) * ε ≤ (1 - κ₁) / 2 ∧ CLp * ε ≤ (1 - κ₁) / 2 ∧
      1 * ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm ∧ CLp * ε ≤ a0 ∧
      cg * ε ≤ betaL L / 4) ∧
      (4 * ℓ ^ 2 * ((L : ℝ) ^ 2 * cmuv + cm)) * ε ≤ 1 / 8 ∧
      (Xs0 * ε ≤ ((L : ℝ) ^ 2 - 1) / 4 ∧ cEz * ε ≤ 1 ∧ (Kzc * (2 * cz)) * ε ≤ 1 ∧ CLp * ε ≤ a₁) ∧
      (cEg * ε ≤ ℓ ^ 2 / 24 ∧ cRNv * ε ≤ εsN ∧ (8 * cKLv) * ε ≤ εsN ∧
        (2 * max Cbv 0) * ε ≤ 1 / 4 ∧ f1cn' L ℓ cz cmuv CqL cRQL cRLL * ε ≤ 1 / 8 ∧
        (ℓ ^ 2 / 7 + f1cw ℓ cmuv CqL cRQL cRLL) * ε ≤ ρ) ∧
      kFin L ℓ CLp Cf CNW * ε ≤ 1 / 2 ∧ P L k ε ∧
      (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp * CLp * cmuv) * ε ≤ 1 / 12 ∧
      0 < ε := by
    filter_upwards [ev_lin 1 one_pos, ev_lin (2 * cz) hρ0,
      ev_lin (8 * cM * ℓ ^ 2 * cz) (by norm_num : (0 : ℝ) < 1 / 2), ev_lin cxv one_pos,
      ev_lin cRv hεs, ev_lin (8 * cxv) hεs, ev_lin cg (by norm_num : (0 : ℝ) < 1 / 6),
      ev_lin cEv hℓ147, ev_lin cg hβ2, ev_lin cRv one_pos, ev_lin (8 * cxv) one_pos,
      ev_lin (f1cn ℓ cmuv) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin (f1cn' L ℓ cz cmuv Cq cRQ cRL) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin (ℓ ^ 2 / 7 + f1cw ℓ cmuv Cq cRQ cRL) hρ0,
      ev_lin (16 / 7 * (L : ℝ) ^ 2 * (8 * ℓ ^ 2 / 49 + (L : ℝ) ^ 2 * cEv) * cmuv +
        2 * ((L : ℝ) ^ 2 * cEv)) one_pos,
      ev_lin (2 * cz) (by norm_num : (0 : ℝ) < 1 / 16),
      ev_lin (cDl (7 / 8 * ℓ) cz) (by norm_num : (0 : ℝ) < 1 / 4),
      ev_lin cEl (by norm_num : (0 : ℝ) < 1 / 4), ev_lin cEl hε₁,
      ev_lin (4 * cmuv * ℓ ^ 2) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin ((cEl + 1) * cCloW L ℓ bb cmuv cxv cw Kc C₂W κW) (by norm_num : (0 : ℝ) < 1 / 2),
      ev_lin (cSz b₁ ℓ) hρ0, ev_lin (cSz b₁ ℓ + cSn L b₁ cz ℓ cmuv) (by norm_num : (0 : ℝ) < 1 / 16),
      ev_lin (Cb * (1 + cxv)) hκ12, ev_lin CLp hκ12, ev_lin 1 heps0,
      ev_lin CLp ha0,
      ev_lin cg (by positivity : 0 < betaL L / 4),
      ev_lin (4 * ℓ ^ 2 * ((L : ℝ) ^ 2 * cmuv + cm)) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin Xs0 hL4q, ev_lin cEz one_pos, ev_lin (Kzc * (2 * cz)) one_pos, ev_lin CLp ha₁,
      ev_lin cEg hℓ24, ev_lin cRNv hεsN, ev_lin (8 * cKLv) hεsN,
      ev_lin (2 * max Cbv 0) (by norm_num : (0 : ℝ) < 1 / 4),
      ev_lin (f1cn' L ℓ cz cmuv CqL cRQL cRLL) (by norm_num : (0 : ℝ) < 1 / 8),
      ev_lin (ℓ ^ 2 / 7 + f1cw ℓ cmuv CqL cRQL cRLL) hρ0,
      ev_lin (kFin L ℓ CLp Cf CNW) (by norm_num : (0 : ℝ) < 1 / 2), hP L k,
      ev_lin (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp * CLp * cmuv) (by norm_num : (0 : ℝ) < 1 / 12),
      self_mem_nhdsWithin]
      with ε h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
        h25 h26 h27 h28 h30 z1 z2 z3 z4 g1 g2 g3 g4 g5 g6 kf hx gw h29
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, ⟨h12, h13, h14, h15⟩,
      ⟨h16, h17, h18, h19, h20, h21, h22, h23⟩, ⟨h24, h25, h26, h27, h28⟩, h30, ⟨z1, z2, z3, z4⟩,
      ⟨g1, g2, g3, g4, g5, g6⟩, kf, hx, gw, h29⟩
  obtain ⟨ε, ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩, ⟨e12, e13, e14, e15⟩,
    ⟨e16, e17, e18, e19, e20, e21, e22, e23⟩, ⟨e24, e25, e26, e27, e28⟩, e29, ⟨z1, z2, z3, z4⟩,
    ⟨eg1, eg2, eg3, eg4, eg5, eg6⟩, ekf, hPx, hWx, hε0⟩ := hev.exists
  have hε : 0 < ε := hε0
  have hKe : 0 ≤ K1 + C0 := add_nonneg hK1 hC0
  have hε1 : ε ≤ 1 := by linarith only [e1]
  have hKh : 0 ≤ Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp := by
    unfold Kh Qh; have : 0 < 1 - κ := by linarith
    have : 0 < (1 + (L : ℝ) ^ 2) / 2 - 1 := by linarith
    positivity
  have hQh : 0 ≤ Qh κ := by
    unfold Qh; have : 0 < 1 - κ := by linarith
    positivity
  have hs' : 4 * sZ CLp (CLp * ε) (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp * (CLp * ε)) (Qh κ * (CLp * ε)) ≤
      ((L : ℝ) ^ 2 - 1) / 4 := by
    have := sZ_le hCLp hKh hQh hε.le hε1
    rw [hXsd] at z1
    linarith only [this, z1, show 4 * (ε * (CLp * (2 * CLp *
      (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp + Qh κ) + 2))) =
      4 * (CLp * (2 * CLp * (Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp + Qh κ) + 2)) * ε by ring]
  refine ⟨⟨ℓ, A, ρ, κ, cg, cm, cT, K1 + C0, CLp, Cf, max Cbv 0, CNW, cgL, AZ, cz, KCp, Kz, C₀, η, εs, CK, C₂, CD, Cq', Cl', cS'⟩, ε, (CLp + Cb) * ε + 4 * (CLp + 2 * (CLp * ε)), hAx, hkd ▸ hPx,
    { hℓ := hℓ, hA := hA0, hρ := hρ0, hε := hε, hε1 := hε1, hκ0 := hκ0, hκ1 := hκ1, hcg := hcg,
      hcm := hcm, hcT := hcT, hKe := hKe, hCL := hCLp, hCf := hCf, hCb := le_max_right _ _,
      hCNW := hCNW, hCs := hcgL.le, hAZ := hAZ, hcz := hcz, hKG := hKCp, hKz := hKz
      cm_eq := by
        show cm = 3 * (L : ℝ) ^ 2 * (16 * ℓ ^ 2 / 49) + 8 * ℓ ^ 2 / 49 + 1
        rw [hcmd]; unfold cF2 cZ; rw [hR₀ℓ]
      hKhW := by
        show Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp * (CLp * ε) * cmu ((L : ℝ) ^ 2) cm ≤ 1 / 12
        rw [← hcmud]
        linarith only [hWx, show Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp * (CLp * ε) * cmuv =
          Kh ((1 + (L : ℝ) ^ 2) / 2) κ CLp * CLp * cmuv * ε by ring]
      step := hSB, hkFin := ekf, hCbε := eg4, hgβ := e28, he := by show ε ≤ eps0u ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm; linarith only [e26]
      ha0 := by show CLp * ε ≤ a0h ((1 + (L : ℝ) ^ 2) / 2) κ CLp; rw [← ha0d]; exact e27
      hs := hs', mono := hmonoZ (CLp * ε) (mul_nonneg hCLp hε.le) z4, hρ8 := hρ8
      split := hSplitF.mono hρF, zeroT := hZT ρ hρT, cov := fun N hN => hCovM N hN ρ hρM
      validLast := fun N R hP hRℓ hRρ hN hm0 hm Nh hNh2 =>
        hValN N R hP hN hm0 hm (by rw [hRℓ]; exact hℓN') (by rw [hRρ]; exact hρ0.le)
          (by rw [hRρ]; exact hρN) (Nh + 1) (by omega) }, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN hm0 hm Nh hNh
  replace hRℓ : R.ℓ = ℓ := hRℓ
  replace hRA : R.A = A := hRA
  replace hRρ : R.ρ = ρ := hRρ
  have hℓR : R.ℓ = R₀.ℓ := hRℓ.trans hR₀ℓ.symm
  have hcZR : cZ R = cz := (cZ_congr hℓR).trans hczd.symm
  have hcVR : cV R ((L : ℝ) ^ 2) cm = cV0 := (cV_congr hℓR _ _).trans hcV0d.symm
  have hcWR : cW R ((L : ℝ) ^ 2) cm C₂ = cw := (cW_congr hℓR _ _ _).trans hcwd.symm
  have hcRR : cR R ((L : ℝ) ^ 2) cm C₂ = cRv := (cR_congr hℓR _ _ _).trans hcRvd.symm
  have hcER : cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cq' Cl' cS' = cEv := (cE_congr hℓR _ _ _ _ _ _ _ _).trans hcEvd.symm
  have hcBR : cB R ((L : ℝ) ^ 2) cm C₂ CK CD = Cb := (cB_congr hℓR _ _ _ _ _).trans hCbd.symm
  have hcF2R : cF2 R = cm - 1 := by rw [cF2_congr hℓR, hcmd]; ring
  have hk1R : kap1 L R.A C₀ η = κ₁ := by rw [hRA, hκ₁d]
  have hcEzR : cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cqζ Clζ cSζ = cEz :=
    (cE_congr hℓR _ _ _ _ _ _ _ _).trans hcEzd.symm
  -- the mass
  have hLpow : ∀ j k : ℕ, j ≤ k → ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 := fun j k h =>
    pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ L by omega)) h) 2
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hmass2 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ (j + 2)) ^ 2 ≤ 1 := fun j hj =>
    msq_j2 hL1r hm0 hm (by omega)
  have hm1 : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := fun j hj => by
    have h2 : ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ (j + 2)) ^ 2 := hLpow _ _ (by omega)
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg R.msq)
    linarith only [this, hmass2 j hj]
  have hmf : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ 4)⁻¹ := fun j hj =>
    msq_j4 hL1r hm0 hm (by omega)
  -- validity and continuity
  have hV : ∀ j < Nh, ValidAt R j := fun j hj =>
    hVal N R hP hN hm0 hm (by rw [hRℓ]; exact hℓv') (by rw [hRρ]; exact hρ0.le)
      (by rw [hRρ]; exact hρv) j (by omega)
  have hcov : ∀ j < Nh, CovCont R j := fun j hj =>
    (hCov N R hP hN hm0 hm (by rw [hRρ]; exact hρc) j (by omega)).1
  have hcovd : ∀ j < Nh, CovDiff R j := fun j hj =>
    (hCov N R hP hN hm0 hm (by rw [hRρ]; exact hρc) j (by omega)).2
  -- the a priori hypotheses
  have H : ApHyp R ((L : ℝ) ^ 2) κ cg cm cT ε εs C₀ C₂ Cq' Cl' cS' :=
    { hε := hε, hε1 := by linarith only [e1], hcm := hcm.le, hcmu := hcmud ▸ hcmu.le,
      hcx := hcxd ▸ hcx, hcg := hcg.le,
      hC₀ := by rw [div_le_iff₀ hL0]; linarith only [hL32, hC₀0]
      hC₂ := hC₂, hCq := hCq', hCl := hCl', hcS := hcS'
      h1 := by rw [hcZR, hRρ]; linarith only [e2]
      h2 := by rw [hRℓ, hcZR]; linarith only [e3]
      h3 := by rw [← hcxd]; linarith only [e4]
      h4 := by rw [hcRR]; exact e5
      h5 := by rw [← hcxd]; exact e6
      h6 := e7
      h7 := by rw [hcER, hRℓ]; exact e8 }
  have Hk : ApHyp R ((L : ℝ) ^ 2) ((1 + kap1 L R.A C₀ η) / 2) cg cm cT ε εs C₀ C₂ Cq' Cl' cS' := by
    rw [hk1R, ← hκd]; exact H
  have hSBR : StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' := by rw [hRA]; exact hSB
  have hA2R : 2 ≤ R.A := by rw [hRA]; exact hA2
  have hVle : ∀ j, j < Nh → ∀ i ≤ j, ValidAt R i := fun j hj i hi => hV i (lt_of_le_of_lt hi hj)
  have hjN : ∀ j, j < Nh → j + 1 < N := fun j hj => by omega
  have hδ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hδ1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- (F2)
  have F2 := F2_rg (β := betaL L) (δ := 1 / 2) R hSBR hV hm1 hβ0.le hδ1 H
    (by rw [hcF2R, hcER, hRℓ, ← hcmud]; linarith only [e15])
  -- (Kb), (Yb)
  have Hb := rgBound_rg (κ₁ := kap1 L R.A C₀ η) (β := betaL L) (δ := 1 / 2) R hSBR hV hm1 hβ0.le
    hδ1 rfl hC₀0 hCK hCD Hk
  rw [hcBR, hk1R] at Hb
  -- the sharp inputs and (F1)
  have hcgβ : cg * ε ≤ betaL L / 2 := e9
  -- the sharp inputs
  obtain ⟨eAf, heAf⟩ : ∃ f : ℕ → ℝ, f = fun j => 8 / 7 * cζ * (M₀ + 1) * (|R.msq| * ((L : ℝ) ^ j) ^ 2) :=
    ⟨_, rfl⟩
  obtain ⟨E0f, hE0f⟩ : ∃ f : ℕ → ℝ, f = fun j =>
      if j = 0 then E0 else C0 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) :=
    ⟨_, rfl⟩
  have hE0f0 : E0f 0 = E0 := by rw [hE0f]; exact if_pos rfl
  have hE0fj : ∀ j, 1 ≤ j →
      E0f j = C0 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) := fun j hj => by
    rw [hE0f]; exact if_neg (by omega)
  have hBj : ∀ j, 0 ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 := fun j => by
    positivity
  have hE0f_nn : ∀ j, 0 ≤ E0f j := fun j => by
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hE0f0]; exact hE0
    · rw [hE0fj j hj1]; exact mul_nonneg hC0 (hBj j)
  have hE0f_le : ∀ j < Nh, E0f j ≤ E0 + 2 * C0 := fun j hj => by
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [hE0f0]; linarith only [hC0]
    · rw [hE0fj j hj1]
      have h1 : (((L : ℝ) ^ j) ^ 2)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_pow₀ (by exact_mod_cast (show 1 ≤ L by omega))))
      have h2 : R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 ≤ 1 := by
        have := hmass2 j hj
        rw [abs_of_pos hm0] at this
        exact (mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) hm0.le).trans this
      have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC0
      linarith only [h3, hE0]
  have heAf0 : ∀ j, 0 ≤ eAf j := fun j => by simp only [heAf]; positivity
  have heAf1 : ∀ j < Nh, 32 / 7 * eAf j ≤ 1 := fun j hj => by
    simp only [heAf]
    have h0 : 0 ≤ 8 / 7 * cζ * (M₀ + 1) := by positivity
    have hk := mul_le_mul_of_nonneg_left (hmf j hj) h0
    have e : 8 / 7 * cζ * (M₀ + 1) * ((L : ℝ) ^ 4)⁻¹ = eA := heAd.symm
    linarith only [hk, e, heA1]
  have hcgβ : cg * ε ≤ betaL L / 2 := e9
  have hMz : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ (M₀ + 1) * ((L : ℝ) ^ j) ^ 2 ∧
      (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cz * (t j).1 := fun j hj t ht => by
    obtain ⟨S0, S1⟩ := hS01L N R hP hN hm0 hm (by rw [hRρ]; exact hρS) j (fun i hi => hV i (by omega)) ((hV j hj).toValidAtL hLg) t
    obtain ⟨-, -, h3⟩ := HS_of_S01 R hSBR (Nh := j + 1) (fun i hi => hV i (by omega))
      (fun i hi => hm1 i (by omega)) H hβ0.le (by norm_num) hcgβ hM₀ hM₂
      (mf := |R.msq| * ((L : ℝ) ^ j) ^ 2)
      (fun i hi => mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) (abs_nonneg _))
      (Nat.lt_succ_self j) t ht S0 S1
    refine ⟨S0, ?_⟩
    rw [← hcZR]; exact h3
  have hZB2 : ZetaStepBound2 L R.A Cqζ Clζ cSζ := hZSB2 L hL8 hLp R.A hA2R
  have hZB : ZetaStepBound L R.A Cqζ Clζ cSζ := hZB2.toZSB
  have hcovZ : ∀ j < Nh, ∀ t : Hist.Seq (Xs R),
      InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) (dirVec (Sum.inl 0)) 0‖ ≤ Kz := by
    intro j hj t ht
    have h1 := hZcovL N R hP hN hm0 hm (by rw [hRρ]; exact hρZ) j (hjN j hj) (hVle j hj) t
      (dirVec (Sum.inl 0)) 0
    have h2 := (hMz j hj t ht).2
    have hgε := (ht.1 j le_rfl).2.1
    have h3 : Kzc * (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 1 := by
      have a := mul_le_mul_of_nonneg_left h2 hKzc
      have b : Kzc * (2 * cz * (t j).1) ≤ Kzc * (2 * cz) * ε := by
        have := mul_le_mul_of_nonneg_left hgε (by positivity : (0 : ℝ) ≤ Kzc * (2 * cz))
        linarith only [this, show Kzc * (2 * cz * (t j).1) = Kzc * (2 * cz) * (t j).1 by ring]
      linarith only [a, b, z3]
    rw [hKzd]; linarith only [h1, h3]
  have hζs := zeta_hist R hSBR hZB hV hm1 hβ0.le (by norm_num) H hCqζ hClζ hcSζ
    (by rw [hcEzR]; linarith only [z2]) (by rw [hcRR]; linarith only [e10])
    (by rw [← hcxd]; linarith only [e11]) hKz hcovZ
  have hcovZ0 : ∀ j < Nh, ∀ t : Hist.Seq (Xs R),
      InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) 0 0‖ ≤ Kz := by
    intro j hj t ht
    have h1 := hZcovL N R hP hN hm0 hm (by rw [hRρ]; exact hρZ) j (hjN j hj) (hVle j hj) t 0 0
    have h2 := (hMz j hj t ht).2
    have hgε := (ht.1 j le_rfl).2.1
    have h3 : Kzc * (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 1 := by
      have a := mul_le_mul_of_nonneg_left h2 hKzc
      have b : Kzc * (2 * cz * (t j).1) ≤ Kzc * (2 * cz) * ε := by
        have := mul_le_mul_of_nonneg_left hgε (by positivity : (0 : ℝ) ≤ Kzc * (2 * cz))
        linarith only [this, show Kzc * (2 * cz * (t j).1) = Kzc * (2 * cz) * (t j).1 by ring]
      linarith only [a, b, z3]
    rw [hKzd]; linarith only [h1, h3]
  have hZs : ∀ k < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε (k + 1) t →
      |Real.log ‖(rawHist R (k + 1 + 1) t).Z‖ - Real.log ‖(rawHist R (k + 1) t).Z‖ +
        betaL L / 3 * (t k).1| ≤ AZ * (t k).1 ^ 2 + AZ * (t k).1 * zA L R.msq k := by
    intro k hk t ht
    exact zs_step R hRℓ hRρ hm0 hρ0 hρ8 hcEz0 hKz hKCp hcz (fun i hi => hV i (by omega)) hcmud
      hcmu.le hAZd hε1 hcEzR
      (zeta_sharp_hist R hSBR hZB2 hV hm1 hβ0.le (by norm_num) H hCqζ hClζ hcSζ
        (by rw [hcRR]; linarith only [e10]) (by rw [← hcxd]; linarith only [e11]) k hk t ht)
      (hcovZ k hk t (InDh_mono ht)) ((hMz k hk t (InDh_mono ht)).2) ht
      (fun hk1 => hXvL N R hP hN hm0 hm (by rw [hRρ]; exact hρCp) k hk1 (hjN k hk) (hVle k hk) t)
  have HSj : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      ‖stA R (rawHist R j t) * (R.msq : ℂ) * (rawHist R j t).w1‖ ≤ eAf j * (t j).1 ∧
      (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cz * (t j).1 := fun j hj t ht => by
    obtain ⟨S0, h3⟩ := hMz j hj t ht
    have hz := hζs j hj.le t ht
    rw [← hcζd] at hz
    have h1 := HS_zeta R (hVle j hj) t (ht.1 j le_rfl).1.le hcζ hM₀ hz le_rfl S0
    exact ⟨le_of_le_of_eq h1 (by simp only [heAf]), h3⟩
  have HVf : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      |(f1Coef R j t + htad R j t).re - betaL L| ≤
        E0f j + (E1 + E1s) * (2 * cz) * (t j).1 := fun j hj t ht => by
    have hMz := (HSj j hj t ht).2
    have hg0 : 0 ≤ (t j).1 := (ht.1 j le_rfl).1.le
    have hb : 0 ≤ 2 * cz * (t j).1 := by positivity
    have e : betaL L = 3 * (Real.log L / (2 * Real.pi)) := rfl
    have e2 : (E1 + E1s) * (2 * cz) * (t j).1 = E1 * (2 * cz * (t j).1) + E1s * (2 * cz * (t j).1) := by
      ring
    rw [e, e2]
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · have h1 := hHVL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHV) 0 (fun i hi => hV i (by omega)) ((hV 0 hj).toValidAtL hLg) t
      rw [htad_zero, add_zero, hE0f0]
      have h3 := mul_le_mul_of_nonneg_left hMz hE1
      have h4 := mul_nonneg hE1s hb
      linarith only [h1, h3, h4]
    · have h1 := hHVsL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHVs) j hj1 (fun i hi => hV i (by omega)) ((hV j hj).toValidAtL hLg) t
      rw [hE0fj j hj1]
      have h2 := mul_le_mul_of_nonneg_right hC0sh (hBj j)
      have h3 := mul_le_mul_of_nonneg_left hMz hE1s
      have h4 := mul_nonneg hE1 hb
      linarith only [h1, h2, h3, h4]
  have F1s := hF1 L hL8 hLp N R C₀ η εs CK C₂ CD Cq' Cl' cS' hSBR hA2R Nh hV hm1 ((L : ℝ) ^ 2)
    (betaL L) (1 / 2) κ cg cm cT ε H hβ0 (by norm_num) hcgβ (by rw [hcRR]; linarith only [e10])
    (by rw [← hcxd]; linarith only [e11]) KB ((E1 + E1s) * (2 * cz)) 1 eAf E0f hKB heAf0 heAf1
    (fun j hj t ht => (HSj j hj t ht).1)
    (fun j hj t ht => hHDL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHD) j (fun i hi => hV i (by omega)) ((hV j hj).toValidAtL hLg) t)
    HVf
    (by rw [hRℓ, ← hcmud]; exact e12)
    (by rw [hRℓ, hcZR, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQd, ← hcRLd]; exact e13)
    (by rw [hRℓ, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQd, ← hcRLd, hRρ]; exact e14)
    (by
      rw [hRℓ, hcZR, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQd, ← hcRLd, ← hcRDd, ← hcESd, hcgd]
      have := le_max_left (f1c3s L ℓ cz cmuv Cq cRQ cRL CqD cRD KB cES 1) 0
      linarith only [this])
  -- the band (F1) with `δ = 1/2`
  have F1 : ∀ j < Nh, ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε j t →
      |(rgData R).G j t - (t j).1 - betaL L * (t j).1 ^ 2| ≤
        1 / 2 * betaL L * (t j).1 ^ 2 + cg * (t j).1 ^ 3 := fun j hj t ht => by
    have h := F1s j hj t ht
    have hb : 32 / 7 * eAf j + E0f j ≤ 1 / 2 * betaL L := by
      linarith only [heAf1 j hj, hE0f_le j hj, hband]
    have := mul_le_mul_of_nonneg_right hb (sq_nonneg (t j).1)
    linarith only [h, this]
  -- the Lipschitz bounds
  have HLip := hLipR N R hP hRA (by rw [hRρ]; exact hρl) hm0 hm C₀ η εs CK C₂ CD Cq' Cl' cS' hSBR
    hC₀l' hηl' Nh hV 1 zero_le_one le_rfl hmass2 (betaL L) (1 / 2) cg cm cT ε hβ0.le hδ1 Hk
    (by rw [hcZR]; linarith only [e16])
    (by rw [hRℓ, hcZR]; exact e17)
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld]; exact e18)
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld]; exact e19)
    (by rw [← hcmud, hRℓ]; linarith only [e20])
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hbbd, ← hκWd]
        linarith only [e21])
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hb₁d, hRρ]
        linarith only [e22])
    (by simp only [hk1R, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hb₁d]
        linarith only [e23])
  simp only [hk1R, hRA, ← hκ₁d, hRℓ, hcZR, hcWR, ← hκd, ← hcxd, ← hcmud, ← hcEld, ← hbbd, ← hb₁d,
    ← hκWd, ← hCLd] at HLip
  obtain ⟨LGd, Lmz, LZ, LT, TOP⟩ := HLip
  obtain ⟨cG, cmm, cT'⟩ := rgData_cont R hV hcov
  obtain ⟨H', HZ, HMZ⟩ := hyps_of_lipz R (Λ := (L : ℝ) ^ 2) (β := betaL L) (δ := 1 / 2)
    (κ₁ := κ₁) (cg := cg) (cm := cm) (cT := cT) (ε := ε) (Nh := Nh) (Cb := Cb) (CL := CLp) hΛ hβ0
    hδ0 (le_refl _) hκ₁0 (by linarith) hcg hcm hcT hCLp hCb (by rw [hcTd]; linarith) hε
    (by linarith only [e1])
    (by rw [← hκd, ← hcxd]; linarith only [e24]) e25
    cG cmm cT' (by rw [← hκd]; exact F1) (by rw [← hκd]; exact F2) Hb
    (by
      rw [← hκd]
      exact fun j hj t t' ht ht' M hM hh => (LGd j hj t t' ht ht' M hM hh).trans (by gcongr))
    (by
      rw [← hκd]
      exact fun j hj t t' ht ht' M hM hh => (Lmz j hj t t' ht ht' M hM hh).trans (by gcongr))
    (by
      rw [← hκd]
      exact fun j hj t t' ht ht' M hM hh => (LZ j hj t t' ht ht' M hM hh).trans (by gcongr))
    (by
      rw [← hκd]
      exact fun j hj t t' ht ht' M hM hh => ⟨(LT j hj t t' ht ht' M hM hh).1.trans (by gcongr),
        (LT j hj t t' ht ht' M hM hh).2.trans (by gcongr)⟩)
  rw [← hκd] at H' HZ HMZ
  have hcl := clamps_of_InDhs R hSBR hV hm1 hβ0.le hδ1 H
    (by rw [hcF2R, hcER, hRℓ, ← hcmud]; linarith only [e15]) hcm hΛ
    (by rw [← hcmud, hRℓ]; linarith only [e20]) (by rw [← hcmud, hRℓ]; linarith only [e29]) F1
  have HD : HDiff (rgData R) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT Nh ε :=
    ⟨fun j hj t ht => rgData_hdiffG R hV hcovd hj t (hcl j hj t ht).1 (hcl j hj t ht).2,
      fun j hj t ht => rgData_hdiffm R hV hcovd hj t (hcl j hj t ht).1 (hcl j hj t ht).2,
      fun j hj t ht => rgData_hdiffT R hV hcovd hj t (hcl j hj t ht).1⟩
  -- the last two steps
  have hglue : Nh + 2 = N → ∀ b μ₀, (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ j)) →
      GlueOut R Nh Cf (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
        BandOut R Nh (max Cbv 0) (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) ∧
        ‖(L : ℂ) ^ (2 * (Nh + 1 + 1)) * (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).κ.nu /
            (lastOut R Nh (traj (rgData R) ((L : ℝ) ^ 2) b μ₀)).Z -
          (L : ℂ) ^ 4 * (((traj (rgData R) ((L : ℝ) ^ 2) b μ₀ Nh).2.1 : ℝ) : ℂ)‖ ≤
          cNuLast R ((L : ℝ) ^ 2) cm ε * (traj (rgData R) ((L : ℝ) ^ 2) b μ₀ Nh).1 ∧
        BandSharp R Nh (betaL L) (K1 + C0) cgL (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
    intro hNh2 b μ₀ hadm
    have hVL : ValidAtL R Nh := hValL N R hP hN hm0 hm (by rw [hRℓ]; exact hℓL')
      (by rw [hRρ]; exact hρ0.le) (by rw [hRρ]; exact hρL) Nh (by omega)
    have hVN : LastN.ValidLast R (Nh + 1) := hValN N R hP hN hm0 hm (by rw [hRℓ]; exact hℓN')
      (by rw [hRρ]; exact hρ0.le) (by rw [hRρ]; exact hρN) (Nh + 1) (by omega)
    have hmL : ∀ j ≤ Nh + 1, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 := fun j hj =>
      msq_le_last hL1r hm0 hm (by omega) (by omega)
    have hSBLR : Last.StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' := by rw [hRA]; exact hSBL
    have hGBR : GStepBound L R.A Cqg Clg cSg := by rw [hRA]; exact hGB
    have hGBdR : GStepBand L R.A Cqb Clb cSb := by rw [hRA]; exact hGBd
    have hLBR : LastN.BoundsP L R.A εsN CKN := by rw [hRA]; exact hLB
    have ht := inDh_rg_of_D R F1 hadm Nh le_rfl
    have hκ₁' : kap1 L R.A C₀ η ≤ 1 := by rw [hk1R]; linarith only [hκ₁h]
    have hcEg : cE R ((L : ℝ) ^ 2) κ cm cT C₂ Cqg Clg cSg * ε ≤ R.ℓ ^ 2 / 24 := by
      rw [cE_congr hℓR, ← hcEgd, hRℓ]; exact eg1
    have hr1 : cR R ((L : ℝ) ^ 2) cm C₂ * ε ≤ 1 := by rw [hcRR]; linarith only [e10]
    have hk1 : 8 * cx κ cT * ε ≤ 1 := by rw [← hcxd]; linarith only [e11]
    -- the sharp band at `N_h`
    have hsharp : BandSharp R Nh (betaL L) (K1 + C0) cgL (traj (rgData R) ((L : ℝ) ^ 2) b μ₀) := by
      have hρR0 : 0 ≤ R.ρ := by rw [hRρ]; exact hρ0.le
      have hρR8 : R.ρ ≤ 1 / 8 := by rw [hRρ]; exact hρ8
      have hmf : |R.msq| * ((L : ℝ) ^ Nh) ^ 2 ≤ ((L : ℝ) ^ 2)⁻¹ :=
        msq_last2 hL0 (hmL (Nh + 1) le_rfl)
      have heAL : 32 / 7 * eAf Nh ≤ emL := by
        simp only [heAf, hemLd]
        have h0 : 0 ≤ 8 / 7 * cζ * (M₀ + 1) := by positivity
        have := mul_le_mul_of_nonneg_left hmf h0
        linarith only [this]
      -- the inputs at `N_h`
      have HSN : ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t →
          ‖stA R (rawHist R Nh t) * (R.msq : ℂ) * (rawHist R Nh t).w1‖ ≤ eAf Nh * (t Nh).1 := by
        intro t ht
        obtain ⟨S0, -⟩ := hS01L N R hP hN hm0 hm (by rw [hRρ]; exact hρS) Nh hV hVL t
        have hz := hζs Nh le_rfl t ht
        rw [← hcζd] at hz
        have h1 := HS_zetaU R hV hρR0 hρR8 t (ht.1 Nh le_rfl).1.le hcζ hM₀ hz le_rfl S0
        exact le_of_le_of_eq h1 (by simp only [heAf])
      have HDN : ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t →
          ‖hqTil R Nh t‖ ≤ KB ∧
            ∑ k ∈ range Nh, ((Nh : ℝ) - k + 1) * 2 ^ (Nh - k) * ‖hbTil R Nh t k‖ ≤ KB :=
        fun t _ => hHDL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHD) Nh hV hVL t
      have HVN : ∀ t, InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t →
          |(f1Coef R Nh t + htad R Nh t).re - betaL L| ≤
            E0f Nh + (E1 + E1s) * (2 * cz) * (t Nh).1 := by
        intro t ht
        have hMz := Mz_histU R hSBR hV (fun i hi => hm1 i hi) hρR0 H hβ0.le (by norm_num) hcgβ t ht
        rw [hcZR] at hMz
        have hg0 : 0 ≤ (t Nh).1 := (ht.1 Nh le_rfl).1.le
        have hb : 0 ≤ 2 * cz * (t Nh).1 := by positivity
        have e : betaL L = 3 * (Real.log L / (2 * Real.pi)) := rfl
        have e2 : (E1 + E1s) * (2 * cz) * (t Nh).1 =
            E1 * (2 * cz * (t Nh).1) + E1s * (2 * cz * (t Nh).1) := by ring
        rw [e, e2]
        rcases Nat.eq_zero_or_pos Nh with h0 | hj1
        · subst h0
          have h1 := hHVL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHV) 0 hV hVL t
          rw [htad_zero, add_zero, hE0f0]
          have h3 := mul_le_mul_of_nonneg_left hMz hE1
          have h4 := mul_nonneg hE1s hb
          linarith only [h1, h3, h4]
        · have h1 := hHVsL N R hP hi0 hN hm0 hm (by rw [hRρ]; exact hρHVs) Nh hj1 hV hVL t
          rw [hE0fj Nh hj1]
          have h2 := mul_le_mul_of_nonneg_right hC0sh (hBj Nh)
          have h3 := mul_le_mul_of_nonneg_left hMz hE1s
          have h4 := mul_nonneg hE1 hb
          linarith only [h1, h2, h3, h4]
      have F1L := hF1L L hL8 hLp N R C₀ η εs CK C₂ CD Cq' Cl' cS' hSBR hA2R Nh hV hVL
        (fun j hj => hmL j (by omega)) ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε H hβ0
        (by norm_num) hcgβ (by rw [hcRR]; linarith only [e10]) (by rw [← hcxd]; linarith only [e11])
        KB ((E1 + E1s) * (2 * cz)) emL (eAf Nh) (E0f Nh) cgL hKB (heAf0 Nh) heAL HSN HDN HVN
        (by rw [hRℓ, ← hcmud]; exact e12)
        (by rw [hRℓ, hcZR, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQLd, ← hcRLLd]; exact eg5)
        (by rw [hRℓ, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQLd, ← hcRLLd, hRρ]; exact eg6)
        (by
          rw [hRℓ, hcZR, ← hcmud, ← hcxd, hcVR, hcWR, ← hcRQLd, ← hcRLLd, ← hcRDLd, ← hcESd,
            hcgLd]
          have := le_max_left (f1c3s L ℓ cz cmuv CqL cRQL cRLL CqDL cRDL KB cES emL) 0
          linarith only [this])
        _ ht
      -- the error of the `ǧ²` term
      have hE0N : E0f Nh ≤ E0 + 2 * C0 := by
        rcases Nat.eq_zero_or_pos Nh with h0 | hj1
        · rw [h0, hE0f0]; linarith only [hC0]
        · rw [hE0fj Nh hj1]
          have h1 : (((L : ℝ) ^ Nh) ^ 2)⁻¹ ≤ 1 :=
            inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_pow₀ hL1r))
          have h2 : R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
            have := hmL (Nh + 1) le_rfl
            rwa [abs_of_pos hm0] at this
          have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC0
          linarith only [h3, hE0]
      refine ⟨32 / 7 * eAf Nh + E0f Nh, add_nonneg (mul_nonneg (by norm_num) (heAf0 Nh))
        (hE0f_nn Nh), by linarith only [heAL, hemL, hE0N, hband2], fun hj1 => ?_, F1L⟩
      have hA : 32 / 7 * eAf Nh ≤
          K1 * ((((L : ℝ) ^ Nh) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2) := by
        simp only [heAf, hK1d]
        rw [abs_of_pos hm0]
        have h1 : R.msq * ((L : ℝ) ^ Nh) ^ 2 ≤ R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) hm0.le
        have h2 : R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤
            (((L : ℝ) ^ Nh) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 := by
          have : 0 ≤ (((L : ℝ) ^ Nh) ^ 2)⁻¹ := by positivity
          linarith only [this]
        have h0 : 0 ≤ 32 / 7 * (8 / 7 * cζ * (M₀ + 1)) := by positivity
        have := mul_le_mul_of_nonneg_left (h1.trans h2) h0
        linarith only [this]
      rw [hE0fj Nh hj1]
      have e1 : (K1 + C0) * ((((L : ℝ) ^ Nh) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2) =
          K1 * ((((L : ℝ) ^ Nh) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2) +
            C0 * ((((L : ℝ) ^ Nh) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2) := by ring
      rw [e1]
      linarith only [hA]
    exact ⟨glue_hist R hSBLR hGBR hLBR hV hVL hVN hmL hβ0.le hδ1 H hκ₁' hCK hCD hCKN hCqg hClg
      hcSg hcEg hr1 hk1 (by rw [cRN_congr hℓR, ← hcRNd]; exact eg2)
      (by rw [cKL_congr hℓR, ← hcKLd]; exact eg3) (by rw [cFin_congr hℓR, ← hCfd]) _ ht,
      band_hist R hSBLR hGBR hGBdR hV hVL (fun j hj => hmL j (by omega)) hβ0.le hδ1 H hκ₁' hCK
        hCD hCqg hClg hcSg hCqb hClb hcSb hcEg hr1 hk1
        (by
          have e : cBand R ((L : ℝ) ^ 2) κ cm cT C₂ Cqb Clb cSb =
              cBand R₀ ((L : ℝ) ^ 2) κ cm cT C₂ Cqb Clb cSb := by
            unfold cBand cB1
            rw [cMu_congr hℓR, cZ_congr hℓR, cE_congr hℓR, hℓR]
          rw [e, ← hCbvd]; exact le_max_left _ _) _ ht,
      glue_hist_nu R hSBLR hGBR hLBR hV hVL hVN hmL hβ0.le hδ1 H hκ₁' hCK hCD hCKN hCqg hClg
        hcSg hcEg hr1 hk1 (by rw [cRN_congr hℓR, ← hcRNd]; exact eg2)
        (by rw [cKL_congr hℓR, ← hcKLd]; exact eg3) _ ht, hsharp⟩
  -- the step `N_h` in the Lipschitz layer
  have htop : Nh + 2 = N → ValidAtL R Nh ∧
      ∀ t t', InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t →
        InDh ((L : ℝ) ^ 2) (betaL L) (1 / 2) κ cg cm cT ε Nh t' →
      ∀ M, 0 ≤ M → (∀ i < Nh, (3 / 4 : ℝ) ^ (Nh - 1 - i) * dist3 (t i) (t' i) ≤ M) →
      |(rgData R).G Nh t - (rgData R).G Nh t' - ((t Nh).1 - (t' Nh).1)| ≤
        CLp * ε * |(t Nh).1 - (t' Nh).1| +
        CLp * ε * |(t Nh).2.1 - (t' Nh).2.1| + CLp * ‖(t Nh).2.2 - (t' Nh).2.2‖ + CLp * ε * M ∧
      |(rgData R).m Nh t - (rgData R).m Nh t'| ≤ CLp * |(t Nh).1 - (t' Nh).1| +
        CLp * ε * |(t Nh).2.1 - (t' Nh).2.1| + CLp * ‖(t Nh).2.2 - (t' Nh).2.2‖ +
        CLp * ε * M + 4 * ‖zetaH R Nh t - zetaH R Nh t'‖ ∧
      ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ ≤
        CLp * (|(t Nh).1 - (t' Nh).1| + ‖(t Nh).2.2 - (t' Nh).2.2‖) +
        CLp * ε * (|(t Nh).2.1 - (t' Nh).2.1| + M) ∧
      ‖nW1H R (Nh + 1) t - nW1H R (Nh + 1) t'‖ ≤
        2 * ℓ ^ 2 * ‖zetaH R (Nh + 1) t - zetaH R (Nh + 1) t'‖ + CNW * M := by
    intro hNh2
    have hVL : ValidAtL R Nh := hValL N R hP hN hm0 hm (by rw [hRℓ]; exact hℓL')
      (by rw [hRρ]; exact hρ0.le) (by rw [hRρ]; exact hρL) Nh (by omega)
    have hmN : |R.msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 :=
      msq_le_last hL1r hm0 hm (by omega) (by omega)
    refine ⟨hVL, fun t t' ht ht' M hM hh => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := TOP hVL hmN t t' ht ht' M hM hh
    exact ⟨a1.trans (by gcongr), a2.trans (by gcongr), a3.trans (by gcongr), a4.trans (by gcongr)⟩
  refine { valid := hV, HD := HD, H := H', HZ := HZ, HM := HMZ
           sharp := ⟨fun j => 32 / 7 * eAf j + E0f j,
             fun j => add_nonneg (mul_nonneg (by norm_num) (heAf0 j)) (hE0f_nn j), F1s,
             fun j hj => by linarith only [heAf1 j hj, hE0f_le j hj, hband], fun j hj1 => ?_⟩
           glue := hglue, top := htop, aph := H, msq1 := hm1, band := F1, zsteps := hZs
           Mz := fun j hj t ht => (hMz j hj t ht).2, covZ := hcovZ0
           covVal := fun k hk1 hkN hVk t =>
             hGvL N R hP hN hm0 hm (by rw [hRρ]; exact hρCp) k hk1 hkN hVk t }
  have hA : 32 / 7 * eAf j ≤ K1 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) := by
    simp only [heAf, hK1d]
    rw [abs_of_pos hm0]
    have h1 : R.msq * ((L : ℝ) ^ j) ^ 2 ≤ R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left (hLpow _ _ (by omega)) hm0.le
    have h2 : R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 ≤
        (((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2 := by
      have : 0 ≤ (((L : ℝ) ^ j) ^ 2)⁻¹ := by positivity
      linarith only [this]
    have h0 : 0 ≤ 32 / 7 * (8 / 7 * cζ * (M₀ + 1)) := by positivity
    have := mul_le_mul_of_nonneg_left (h1.trans h2) h0
    linarith only [this]
  show 32 / 7 * eAf j + E0f j ≤ (K1 + C0) * _
  rw [hE0fj j hj1]
  have e1 : (K1 + C0) * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) =
      K1 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) +
        C0 * ((((L : ℝ) ^ j) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (j + 1)) ^ 2) := by ring
  rw [e1]
  linarith only [hA]

/-- `flow_master` without external requirements. -/
theorem flow_master_basic : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (k : FlowConsts) (ε aB : ℝ), FlowUniform L k ε ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = k.ℓ → R.A = k.A → R.ρ = k.ρ → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
    ∀ Nh : ℕ, Nh + 2 ≤ N → FlowExport L k ε aB R Nh := by
  obtain ⟨L₀, h⟩ := flow_master (fun _ _ => True) (fun _ => ⟨0, fun _ _ => trivial⟩)
    (fun _ _ _ => True) (fun _ _ => Filter.Eventually.of_forall fun _ => trivial)
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨k, ε, aB, -, -, U, X⟩ := h L hL
  exact ⟨k, ε, aB, U, X⟩

end

end Step2
