import Spin2.Master.MasterAllFactsD
import Spin2.Gam.GamTopB
import Spin2.Gam.GamFormB

/-!
# Route (a1): the flow wrappers of the pair layer along windowed trajectories

The flow wrappers `gamTopBd_flow`, `gamLastRel(S)_flow`, `gamTopBdB_flow`, `gamTopBd_both_flow`,
`twoPtSq_of_zz1_flow`, `twoPtSq_of_gam_flow(B)` combine trajectory-level cores (`gamTopBd_of`,
`gamLastRel(S)_of`, `gamTopBdB_of`, `twoPtSq_of_zz1`, `gamFormA_of`, `zBelowU1_of_forms`,
`mmag_bound_of`, `gamFormB_of`, `twoPtNear_of`) with the instances of the global conclusions
(`SpinConcl`, `MagConcl`, `GMonoConcl`) at one admissible trajectory; their proofs use only
`hadm.1`. The `…D` versions below are the same glue with the `D_ε` forms (`SpinConclD`,
`MagConclD`, `GMonoConclD`, the domain condition) — no core is copied.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

set_option maxHeartbeats 1000000 in
/-- **`GamTopBd` along every trajectory in `D_ε` (twin of the admissible version)** (`FlowC2Concl`, `ε ≤ 1`, `MagConcl`,
`GMonoConcl`): (H_λ) for `λ` and for the pair vertex, `GamBulkRel`, `GamWKTop`, `GamLastRel` and
the smallness `K(K_λ)ǧ_j ≤ 1/2` give `GamTopBd` with `K₄ = 2(1 + K(K_p + c_γ) + c_L)`,
`c_γ = (c_e + c_w)(1 + 3K_p)`. -/
theorem gamTopBd_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hMC : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hGM : GMonoConclD L ℓ A ρ κ cm cT ε) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (lam : ℕ → ℂ) (Kl Kp ce cw cL : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ ce → 0 ≤ cw → 0 ≤ cL →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      GamBulkRel R Nh m b μ₀ ce → GamWKTop R Nh m b μ₀ cw → GamLastRel R Nh m b μ₀ cL →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBd R Nh m b μ₀ lam
        (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 + cL)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl Kp ce cw cL hKl hKp hce hcw
    hcL hl hpair hB hW hLast hsmall
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk).1, ((hD k hk).2.1).trans hε1⟩
  have ha : ∀ k < Nh, zA L m k ≤ 2 := fun k hk =>
    zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)
  have hMag := magAt_ofD R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  exact gamTopBd_of R hP hMag hm.1.le hb hval hg
    (hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD) ha hKl hKp hce hcw hcL hl hsmall
    hpair hB hW hLast

/-- **`GamLastRel` along every trajectory in `D_ε` (twin of the admissible version)** (`FlowC2Concl`, `ε ≤ 1`, `SpinConcl`,
`LastValidConcl`): `BetaLast K_β` and `GamLastRem c_r` give `GamLastRel` with
`c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`. -/
theorem gamLastRel_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ)
    (hSp : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) (hLV : LastValidConcl L ℓ ρ) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ Kβ cr : ℝ, 0 ≤ Kβ → 0 ≤ cr → BetaLast R Nh m b μ₀ Kβ → GamLastRem R Nh m b μ₀ cr →
      GamLastRel R Nh m b μ₀ (2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD Kβ cr hKβ hcr hβ hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  obtain ⟨hV, hVL⟩ := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hZ0, hZ⟩ :=
    (hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ₀ hD Nh le_rfl
  have h := gamLastRel_of R hP hb hKZ hKβ hcr hV hVL hVN (hD Nh le_rfl).1
    (((hD Nh le_rfl).2.1).trans hε1) hZ0 hZ hβ hr
  rwa [hRℓ] at h

/-- **`GamLastRelS` along every trajectory in `D_ε` (twin of the admissible version)** (as `gamLastRel_flow`). -/
theorem gamLastRelS_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ)
    (hSp : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) (hLV : LastValidConcl L ℓ ρ) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ Kβ cr : ℝ, 0 ≤ Kβ → 0 ≤ cr → BetaLastS R Nh m b μ₀ Kβ → GamLastRemS R Nh m b μ₀ cr →
      GamLastRelS R Nh m b μ₀ (2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD Kβ cr hKβ hcr hβ hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
  obtain ⟨hV, hVL⟩ := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hZ0, hZ⟩ :=
    (hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)).2.2.2.2.1 m hm b μ₀ hD Nh le_rfl
  have h := gamLastRelS_of R hP hb hKZ hKβ hcr hV hVL hVN (hD Nh le_rfl).1
    (((hD Nh le_rfl).2.1).trans hε1) hZ0 hZ hβ hr
  rwa [hRℓ] at h

set_option maxHeartbeats 1000000 in
/-- **`GamTopBdB` along every trajectory in `D_ε` (twin of the admissible version)** (`FlowC2Concl`, `ε ≤ 1`, `MagConcl`,
`GMonoConcl`): (H_λ) for `λ` and for the mirrored pair vertex, `GamRemTopS`, `GamLastRelS` and the
smallness give `GamTopBdB` with `K₄ = 2(1 + K(K_p + c_γ) + c_L)`. -/
theorem gamTopBdB_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ}
    (hε1 : ε ≤ 1) (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hMC : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hGM : GMonoConclD L ℓ A ρ κ cm cT ε) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (lam : ℕ → ℂ) (Kl Kp cγ cL : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cγ → 0 ≤ cL →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamRemTopS R Nh m b μ₀ cγ → GamLastRelS R Nh m b μ₀ cL →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBdB R Nh m b μ₀ lam (2 * (1 + max (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0 + cL)) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl Kp cγ cL hKl hKp hcγ hcL
    hl hpair hrem hLast hsmall
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk).1, ((hD k hk).2.1).trans hε1⟩
  have hMag := magAt_ofD R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  exact gamTopBdB_of R hP hMag hm.1.le hb hg
    (hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD) hKl hKp hcγ hcL hl hsmall
    hpair hrem hLast

set_option maxHeartbeats 1000000 in
/-- **`GamTopBd` at both points** along every trajectory in `D_ε` (twin of the admissible version) (`FlowC2Concl`, `ε ≤ 1`,
`SpinConcl`, `MagConcl`, `GMonoConcl`, `LastValidConcl`). Inputs: (H_λ) for `λ` and for both pair
vertices (`ptsX x`, `ptsS x`, constant `K_p`), `GamBulkRel c_e`, `GamWKTop c_w`, `GamRemTopS c_γ'`,
`BetaLast(S) K_β`, `GamLastRem(S) c_r`, and the smallness. Constants:
`c_L = 2(1 + c_r)K_β·ℓ²e^{K_Z}/14`, `K₄ = 2(1 + K(K_p + (c_e + c_w)(1 + 3K_p)) + c_L)`,
`K₄' = 2(1 + K(K_p + c_γ') + c_L)`. -/
theorem gamTopBd_both_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1) (hKZ : 0 ≤ KZ)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) (hGM : GMonoConclD L ℓ A ρ κ cm cT ε)
    (hLV : LastValidConcl L ℓ ρ) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ (lam : ℕ → ℂ) (Kl Kp ce cw cγ Kβ cr : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ ce → 0 ≤ cw → 0 ≤ cγ →
      0 ≤ Kβ → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamBulkRel R Nh m b μ₀ ce → GamWKTop R Nh m b μ₀ cw → GamRemTopS R Nh m b μ₀ cγ →
      BetaLast R Nh m b μ₀ Kβ → GamLastRem R Nh m b μ₀ cr →
      BetaLastS R Nh m b μ₀ Kβ → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      GamTopBd R Nh m b μ₀ lam
          (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14))) ∧
        GamTopBdB R Nh m b μ₀ lam
          (2 * (1 + max (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0 +
            2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14))) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl Kp ce cw cγ Kβ cr hKl hKp
    hce hcw hcγ hKβ hcr hl hpX hpS hB hW hRS hβ hr hβS hrS hsmall
  have hcL : 0 ≤ 2 * (1 + cr) * Kβ * (ℓ ^ 2 * Real.exp KZ / 14) := by positivity
  exact ⟨gamTopBd_flowD hF hε1 hL hMC hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam
      Kl Kp ce cw _ hKl hKp hce hcw hcL hl hpX hB hW
      (gamLastRel_flowD hF hε1 hKZ hSp hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
        Kβ cr hKβ hcr hβ hr) hsmall,
    gamTopBdB_flowD hε1 hL hMC hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam
      Kl Kp cγ _ hKl hKp hcγ hcL hl hpS hRS
      (gamLastRelS_flowD hF hε1 hKZ hSp hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
        Kβ cr hKβ hcr hβS hrS) hsmall⟩

/-- **`TwoPtSq` along every trajectory in `D_ε` (twin of the admissible version)** from `ZBelowU1`, `PairAboveW1`, `TwoPtNear`. -/
theorem twoPtSq_of_zz1_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (KM Mb KE KR KN KRN : ℝ), 0 ≤ KM →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      ZBelowU1 R Nh m b μ₀ lam KM → PairAboveW1 R Nh m b μ₀ lam KE KR →
      TwoPtNear (L := L) (N := N) m b μ₀ KN KRN →
      TwoPtSq R Nh m b μ₀ lam (max (KM * (2 + KM) + KE) KN)
        (max (1 + 2 * (1 + KM) * Mb + KR) KRN) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam KM Mb KE KR KN KRN hKM hMb
    hZ hE hNear
  obtain ⟨-, -, hρ0, -, -, -, -, -, -, -, -, -, -, hρ8, hspl, hrest⟩ := hF
  have hval := (hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk).1.le, ((hD k hk).2.1).trans hε1⟩
  exact twoPtSq_of_zz1 R hNh m (by rw [hRρ]; linarith) (by rw [hP, hRρ]; exact hspl)
    hm.1 hm.2 hval.1 hval.2 hL hb hh lam hKM hg hMb hZ hE hNear

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from the `γ` flow** (master constants), along every trajectory in `D_ε` (twin of
`twoPtSq_of_gam_flow`). -/
theorem twoPtSq_of_gam_flowD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl Kp cγ Kb KE KR KN KRN : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cγ → 0 ≤ Kb →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      GamRemRel R Nh m b μ₀ cγ → GamFormB R Nh m b μ₀ Kb →
      PairAboveW1 R Nh m b μ₀ lam KE KR → TwoPtNear (L := L) (N := N) m b μ₀ KN KRN →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      TwoPtSq R Nh m b μ₀ lam
        (max (zbKM L cg Ke KZ KG Kp cγ Kb Kl * (2 + zbKM L cg Ke KZ KG Kp cγ Kb Kl) + KE) KN)
        (max (1 + 2 * (1 + zbKM L cg Ke KZ KG Kp cγ Kb Kl) * zbMb L cg Ke KZ KG Kl + KR) KRN) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam Kl Kp cγ Kb KE KR KN KRN
    hKl hKp hcγ hKb hl hpair hrem hB hE hNear hsmall
  have hcg : 0 < cg := hF.2.2.2.2.2.2.1
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hb1 : b ≤ 1 := by
    have := (hD 0 (Nat.zero_le _)).2.1; rw [Hist.traj_zero] at this; exact this.trans hε1
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := fun k hk =>
    (hD k hk).1
  have hg1 : ∀ k ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ((hD k hk).2.1).trans hε1
  have hMag := magAt_ofD R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hA := gamFormA_of R hP hb hm.1.le hcγ hg hpair hrem
  have hZ := zBelowU1_of_forms R hMag hm.1.le hb hg hKl hl hsmall (add_nonneg hKp hcγ) hKb hA hB
  have hβ : 0 < betaL L := by
    have hL1 : (1 : ℝ) < L := by exact_mod_cast (show 1 < L by omega)
    have := Real.log_pos hL1
    unfold betaL; positivity
  have hCg : 0 ≤ Cgu (betaL L) cg := by unfold Cgu; positivity
  obtain ⟨-, -, hBA, -⟩ := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hΘ : ∀ k ≤ Nh, varthJ R m b μ₀ k ≤ zbTheta L cg Ke := fun k hk =>
    varth_le_pure hβ hCg hb hb1 (hg k hk) (hg1 k hk) (Nat.cast_nonneg k)
      (hBA m hm b μ₀ hD k hk)
  have hMb := mmag_bound_of R hMag (fun k hk => ⟨(hg k hk).le, hg1 k hk⟩) hKl hl hΘ hb.le
  have hKM : 0 ≤ zbKM L cg Ke KZ KG Kp cγ Kb Kl := by
    unfold zbKM
    have := le_max_right (spinMK L cg Ke KZ (Kp + cγ) KG 0) 0
    have := le_max_right (spinMK L cg Ke KZ Kb KG 0) 0
    have := le_max_right (spinMK L cg Ke KZ Kl KG 0) 0
    linarith
  exact twoPtSq_of_zz1_flowD hF hε1 hL N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam
    _ _ KE KR KN KRN hKM hMb hZ hE hNear

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from the `γ` flow, without `GamFormB` and `TwoPtNear`** (master constants), along
every trajectory in `D_ε` (twin of `twoPtSq_of_gam_flowB`):
`GamFormB` from the mirrored `0`-part (`gamFormB_of`: (H_λ) for `lamHat2` at `ptsS x` and
`GamRemRelS`), `TwoPtNear` from the model (`twoPtNear_of`, `K_N = L`, `K_{RN} = 1`). -/
theorem twoPtSq_of_gam_flowBD {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConclD L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl Kp cγ KE KR : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cγ →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamRemRel R Nh m b μ₀ cγ → GamRemRelS R Nh m b μ₀ cγ →
      PairAboveW1 R Nh m b μ₀ lam KE KR →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      TwoPtSq R Nh m b μ₀ lam
        (max (zbKM L cg Ke KZ KG Kp cγ (Kp + cγ) Kl * (2 + zbKM L cg Ke KZ KG Kp cγ (Kp + cγ) Kl)
          + KE) (L : ℝ))
        (max (1 + 2 * (1 + zbKM L cg Ke KZ KG Kp cγ (Kp + cγ) Kl) * zbMb L cg Ke KZ KG Kl + KR)
          1) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam Kl Kp cγ KE KR
    hKl hKp hcγ hl hpair hpairS hrem hremS hE hsmall
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hg : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 := fun k hk =>
    (hD k hk).1
  have hB := gamFormB_of R hP hb hm.1.le hcγ hg hpairS hremS
  have hNear := twoPtNear_of (L := L) (N := N) (by omega) hb hm.1 hh
  exact twoPtSq_of_gam_flowD hF hε1 hL hSp hMC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh
    lam Kl Kp cγ (Kp + cγ) KE KR (L : ℝ) 1 hKl hKp hcγ (add_nonneg hKp hcγ) hl hpair hrem hB hE
    hNear hsmall

end

end Spin2
