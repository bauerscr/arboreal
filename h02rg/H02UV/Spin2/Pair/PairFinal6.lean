import Spin2.Pair.PairFinal5
import Spin2.Pair.PairDef6b
import Spin2.Pair.PairZeroAB4

/-!
# The pair layer with `PairDefSizesNF` and `PairZeroRemAB` discharged

**`pairAbove_final6_MF'`**: `pairAbove_final5_MF'` without the named inputs `PairDefSizesNF c_d` and
`PairZeroRemAB e₁ e₂`, at the canonical constants of the master construction:

* the `ab` sizes at `N_h + 1` (`pairTopSizes_MF`, constant `C₁t`: one step of the `ab` chain past the
  horizon, `MasterCore.vstepTopD`), `PairTopSizesAB ((1701/1024)m̄) ((4C₁t+1)cm̄) ((4C₁t+1)m̄)`;
* the last step (`pairZeroAB_of`: the jets of `F'_N` through the swap `σ_aσ_b ↦ σ_a` and the
  jet bound `LastJetBd` of the master construction; the crude bound of the last-step defect):
  `PairZeroRemAB e₁ 1`, `e₁ = pd6e1 = (81/16)c_{Jab}c_S + m̄`, and `PairDefLastR (c_{Lab}c_Sc_u)`;
* the `ε`-tadpole (`pairDefSizesNF_of_last_MFC`): `PairDefSizesNF (c_{Lab}c_Sc_u + pd6Cf)`.

`m̄ = c_σ = pd6mbar` (`pd5mbar` and the seed condition of `pairTopSizes_MF`), defect constant
`pd6cd = c_{Lab}c_Sc_u + pd6Cf + pd5Cp + pd5CS`, `c_S = pd6cS`. New hypothesis: the mass window of
item (d), `2·(81/16)c_J(c_ρ + 4/r₀²)c_Sℓ²·mL^{2N} ≤ 1` (the analogue of `8K_A mL^{2N} ≤ 1`).
**`pairAbove_final6_at`**: the same at given constants (body of `pairAbove_final5_at`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- **The explicit `m̄ = c_σ`**: `pd5mbar` and the seed condition of `pairTopSizes_MF` (`C₁t`). -/
def pd6mbar {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ C₁w₅ C₁t : ℝ) : ℝ :=
  max (pd5mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ C₁w₅)
    (8 * pl6k0 M (pairUnitC M) / (vck C₁t * (4 * C₁t + 1)))

/-- The size constant `c_S = c_V + c_W + 8c_K + 1` of the `ab` inputs of the last step. -/
def pd6cS {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁t mbar : ℝ) : ℝ :=
  1701 / 1024 * mbar + (4 * C₁t + 1) * M.core.c * mbar + 8 * ((4 * C₁t + 1) * mbar) + 1

/-- The constant `e₁` of `PairZeroRemAB`. -/
def pd6e1 {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁t r₀ mbar : ℝ) : ℝ :=
  81 / 16 * cJab L r₀ * pd6cS M C₁t mbar + mbar

/-- The defect constant `c_{Lab}c_Sc_u + pd6Cf + pd5Cp + pd5CS`. -/
def pd6cd {L : ℕ} [NeZero L] (M : MasterFacts L) (C₁t r₀ mbar : ℝ) : ℝ :=
  cLab L * pd6cS M C₁t mbar * pairUnitC M + pd6Cf M M.core.C₁ka M.core.C₁wa mbar mbar +
    pd5Cp M M.core.C₁ka M.core.C₁wa mbar + pd5CS M M.core.C₁ka M.core.C₁wa mbar

theorem cJab_nonneg (L : ℕ) [NeZero L] {r₀ : ℝ} (hr₀ : 0 < r₀) : 0 ≤ cJab L r₀ := by
  unfold cJab
  have hL2 : (0 : ℝ) ≤ (L : ℝ) ^ 2 := by positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hcS' : 0 ≤ LastN.cSN 2 L := by unfold LastN.cSN; positivity
  have h1 : 0 ≤ cJet L := by
    unfold cJet; have := mul_nonneg hL2 (by linarith : (0 : ℝ) ≤ Q1 2); linarith
  have h2 : 0 ≤ cRho L := by
    unfold cRho
    have : 0 ≤ (L : ℝ) ^ 2 * Q1 2 ^ 2 := by positivity
    have h3 : 0 ≤ (L : ℝ) ^ 2 * LastN.cSN 2 L := by positivity
    refine mul_nonneg hL2 ?_
    nlinarith
  have := mul_nonneg h1 (add_nonneg h2 (by positivity : (0 : ℝ) ≤ 4 / r₀ ^ 2))
  have : 0 ≤ (L : ℝ) ^ 2 * (2 * Q1 2 + 2 * (L : ℝ) ^ 2 * Q1 2 ^ 2) := by positivity
  linarith

theorem pd6cS_nonneg {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁t mbar : ℝ} (hC₁t : 0 ≤ C₁t)
    (hc : 0 ≤ M.core.c) (hm : 0 ≤ mbar) : 0 ≤ pd6cS M C₁t mbar := by
  unfold pd6cS
  have : 0 ≤ (4 * C₁t + 1) * M.core.c * mbar := by positivity
  positivity

/-- The conclusion of `pairAbove_final6_at` (`PairFinal5Concl` without `PairDefSizesNF` and
`PairZeroRemAB`, with the mass window of item (d)). -/
def PairFinal6Concl {L : ℕ} [NeZero L] (M : MasterFacts L) (Kt r₀ C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ C₁t : ℝ) :
    Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μ₀ →
    b ≤ μ₀ + m →
  ∀ (lam : ℕ → ℂ) (Kl cr : ℝ), 0 ≤ Kl → 0 ≤ cr →
    HLam R Nh m b μ₀ lam Kl →
    GamLastRem R Nh m b μ₀ cr → GamLastRemS R Nh m b μ₀ cr →
    (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
  ∀ Mb : ℝ,
    (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
    (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) + 9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
        cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 / 2 →
    Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 →
    8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 →
    2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ M.core.ρ →
    8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2 →
    PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 →
    4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2 →
    cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀ →
    2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
        pd6cS M C₁t (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) * M.core.ℓ ^ 2) * m *
      (L : ℝ) ^ (2 * N) ≤ 1 →
    PairAboveW1 R Nh m b μ₀ lam
      ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) * (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
        (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) + pd6cd M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + (4 * 1 + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t)) + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t))) * (2 * (1 + max (spinMK L M.core.cg M.core.Ke M.core.KZ (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
          2 * (1 + cr) * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14)))) ((4 * 1 + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t)) + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t))) * Mb)

set_option maxHeartbeats 8000000 in
/-- **`pairAbove_final6_MF'` at given constants** (the body of `pairAbove_final5_at`, with
`PairDefSizesNF` and `PairZeroRemAB` discharged: `pairTopSizes_MF` (constant `C₁t`) →
`pairZeroAB_of` → `pairDefSizesNF_of_last_MFC`). -/
theorem pairAbove_final6_at {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁v C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁v : 0 ≤ C₁v) (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo)
    (hClb : 0 ≤ Clb) :
    ∃ Kt r₀ C₁v₅ C₁t : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁v₅ ∧ 0 ≤ C₁t ∧
    (PJClosedP M C₁v C₁k C₁w C₁w' Clo Clb → pl6X M * pl6Θ M C₁k C₁w C₁w' Clo Clb ≤ 1 / 2 →
      PairFinal6Concl M Kt r₀ C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ C₁t) := by
  obtain ⟨C₁v₅, hC₁v₅, hVBt⟩ := pairVB_top_MF M
  obtain ⟨C₁t, hC₁t, hTop⟩ := pairTopSizes_MF M
  unfold PairFinal6Concl
  have hL49 : 49 ≤ L := M.core.hL49
  have hLpl : pauliL0 2 ≤ L := M.core.hLpl
  have hF := M.flow
  have hε1 := M.eps_le
  have hSp := M.spin
  have hMC := M.mag
  have hLoop := M.loop
  have hcδ := M.cRel_nonneg
  have hRelG := M.relG
  have hcw := M.cw_nonneg
  have hWK := M.wk
  have hce := M.cGB_nonneg
  have hGB := M.gamBulk
  have hKZ := M.KZ_nonneg
  have hGM := M.gmono
  have hLV := M.lastValid
  have hGI := M.ginc
  have hZT := M.zeroT
  have hcWL := M.cWL_nonneg
  have hLW := M.lastW
  obtain ⟨r₀, hr₀, hr₀1, hJ⟩ := M.jet
  have hcKL := M.cKL_nonneg
  have hLKo := M.lastK
  have hLA1 := M.lastL1
  have hTopC := M.top
  set ℓ := M.core.ℓ with hℓd
  set A := M.core.A with hAd
  set ρ := M.core.ρ with hρd
  set κ := M.core.κ with hκd
  set cg := M.core.cg with hcgd
  set cm := M.core.cm with hcmd
  set cT := M.core.cT with hcTd
  set ε := M.core.ε with hεd
  set Ke := M.core.Ke with hKed
  set Cf := M.core.Cf with hCfd
  set Cb := M.core.Cb with hCbd
  set KZ := M.core.KZ with hKZd
  set KG := M.core.KG with hKGd
  set B₁ := M.core.B₁ with hB₁d
  set B₂ := M.core.B₂ with hB₂d
  set B₃ := M.core.B₃ with hB₃d
  set cq := M.core.cq with hcqd
  set B' := M.core.B' with hB'd
  set cδ := M.core.cRel with hcδd
  set cw := M.core.cw with hcwd
  set ce := M.core.cGB with hced
  set cWL := M.core.cWL with hcWLd
  set cKL := M.core.cKL with hcKLd
  set ct := M.core.ce with hctd
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  set Kp := max (lamRelK (betaL L) cg (B₁ + B₂ + B₃) B' cq cδ (eRange (betaL L) Ke 1) 4) 0
    with hKpd
  have hKp : 0 ≤ Kp := le_max_right _ _
  obtain ⟨Kt, hKt, hZTl⟩ := PtCorr2.lastOut_zeroT hZT
  refine ⟨Kt, r₀, C₁v₅, C₁t, hKt, hr₀, hr₀1, hC₁v₅, hC₁t, ?_⟩
  intro hJC hloop N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl cr hKl hcr hl
    hr hrS hsmall Mb hMb hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hmAB
  set cσ := pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t with hcσd
  have hσ5 : pd5mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa ≤ cσ := by
    rw [hcσd]; unfold pd6mbar; exact le_max_left _ _
  have hcσ0 : pl6mbar M C₁v C₁k C₁w C₁w' Clo Clb ≤ cσ :=
    le_trans (by unfold pd5mbar; exact le_max_left _ _) hσ5
  have htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      Case2TopStep R (ptsX x) (zV b) Nh m b μ₀ ∧ Case2TopStep R (ptsS x) (zV b) Nh m b μ₀ :=
    fun x _ _ _ => ⟨(hTopC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)).1,
      (hTopC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsS x)).1⟩
  set KA := cKAL L ℓ r₀ Cf cWL cKL 3 with hKAd
  have hl1 : LastL1 R Nh m b μ₀ 3 := fun x hx h1 hj =>
    hLA1 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x)
      ((htop x hx h1 hj).1.1.trans (by norm_num))
  have hB := hGB N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk.le).1.le, ((hadm.1 k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  -- (H_λ) for the pair vertices
  have hLC := lamConcl_of hL2 hε1 hSp
  have hpairP : ∀ P : Obs2.ObsPts 2 L N,
      HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp := by
    intro P
    obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    have h := hLam_case2 hLC hP hi0 hRℓ hRA hRρ (by omega) hm hadm hB0 hcδ (zV_mua_ne hb)
      (hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)) hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hadm.1 k hk.le).1) h (le_max_left _ _)
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ₀ cδ := fun P =>
    hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b) (zV_mua_ne hb)
  have hn : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ₀ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm P (zV b)
    exact (hl' k hk).1
  have hmono := hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  obtain ⟨-, -, hWT, hWM⟩ := wk_inputs hWK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hβ := betaLast_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).1)
  have hβS := betaLastS_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).2)
  have hRS := gamRemTopS_of R hb hKp hce hcw hval hg ha (fun x _ => hpairP _) hB hWM
  have hcγ : 0 ≤ (ce + cw) * (1 + 3 * Kp) := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hKβ : 0 ≤ 2 * (1 + 3 * Kp) := by linarith
  have hGT := gamTopBd_both_flow hF hε1 hKZ hL8 hSp hMC hGM hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    b μ₀ hadm lam Kl Kp ce cw _ _ cr hKl hKp hce hcw hcγ hKβ hcr hl (fun x _ => hpairP _)
    (fun x _ => hpairP _) (gamBulkRel_of_A R hB) hWT hRS hβ hr hβS hrS hsmall
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, hCf0, -, -, hρ8, hspl, hrest⟩ := hF
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1.le, ((hadm.1 k hk).2.1).trans hε1⟩
  -- `PairVertSum` (new)
  have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
  have hSpN := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hSS := hSpN.2.2.2.1 m hm
  have hZb := hSpN.2.2.2.2.2.2.1 m hm b μ₀ hadm
  have hMag := magAt_of R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hadm
  have hg0 : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk).1, ((hadm.1 k hk).2.1).trans hε1⟩
  have hjN : ∀ j ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := by
    intro j hj
    have key : ∀ n, j + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (j + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (j + n) (by omega))
    have := key (Nh - j) (by omega)
    rwa [show j + (Nh - j) = Nh by omega] at this
  have hS := pairVertSum_of R hP hb hKZ hKp hval hvalL (hLV N R hP hRℓ hRρ hN2 Nh hNh m hm) hg0 ha
    hjN hZb (fun x _ => hpairP _) hβ hSS hadm hβL hMag hKl hl hsmall
  rw [hRℓ] at hS
  -- the `ε_k` half: `Case2Rel`, `Case2TopStep`, `∑ǧ² ≤ 4/β`
  have hG2 : ∑ k ∈ Finset.range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ 4 / betaL L :=
    sum_gsq_le_of_inc hβL (hGI N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm)
      (hg' 0 (Nat.zero_le _)).1 (hg' Nh le_rfl).2
  have hRd := pairSectRed_of R m hval hvalL b μ₀ (pairDCov_std Nh)
  have hSeed := pairRedSeed_of R Nh m b μ₀ dxStd
  -- the joint sizes with the first summability condition discharged, the loop closed at `m̄ = cσ`
  set k₀ := pl6k0 M (pairUnitC M) with hk₀d
  have hk₀ : 0 ≤ k₀ := by
    rw [hk₀d]; unfold pl6k0
    have := M.ιW_ge; have := M.core.hA2
    exact mul_nonneg (pairUnitC_nonneg M) (pow_nonneg (by positivity) _)
  obtain ⟨Hap, -, -⟩ := M.core.hXm N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
  have hθa0 : 0 ≤ kθ0 L M.core.A M.core.C₀a M.core.ηa := by
    unfold kθ0
    have := M.core.hA2
    exact mul_nonneg M.core.hC₀a (add_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
  obtain ⟨hct, -, -⟩ := M.tad N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  have hCE := pl6CEM_nonneg M hC₁k hC₁w hC₁w' hClo hClb hθa0 Hap.hcx hct
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHist
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
    rw [← hcR]; unfold cR cV cW cZ
    have := Hap.hcmu; have := Hap.hC₂; positivity
  have hε0 : 0 ≤ M.core.ε := ((hadm.1 0 (Nat.zero_le _)).1.trans_le (hadm.1 0 (Nat.zero_le _)).2.1).le
  have hΘ : 0 ≤ pl6Θ M C₁k C₁w C₁w' Clo Clb := by
    unfold pl6Θ pl6CNM pl6CN pl6cS pl6G2
    have := pl6As_nonneg (L := L) (by linarith : (0 : ℝ) ≤ 4 * C₁w + 1)
    have := Obs2.KM4_nonneg 2 (Cc := Ccut2)
    positivity
  have hX := crErr2_one_pos M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) 0
  have hcσ1 : 1 ≤ cσ := le_trans (by unfold pl6mbar; exact le_max_of_le_right (le_max_of_le_right
    (le_max_right _ _))) hcσ0
  have hmbar : 0 < cσ := by linarith
  have hcσ : 0 ≤ cσ := hmbar.le
  have hm1 : 2 * pl6X M * (2 * pl6CEM M C₁k C₁w C₁w' Clo Clb) * k₀ ≤ cσ := by
    exact le_trans (by unfold pl6mbar; exact le_max_of_le_left (le_max_left _ _)) hcσ0
  have hdiv : ∀ a c : ℝ, 0 < a → c / a ≤ cσ → c ≤ a * cσ := fun a c ha h => by
    rw [div_le_iff₀ ha] at h; linarith
  have h8v : 8 * k₀ ≤ vck C₁v * ((4 * C₁v + 1) * cσ) := by
    have hv : 0 < vck C₁v * (4 * C₁v + 1) := mul_pos (vck_pos hC₁v) (by linarith)
    rw [← mul_assoc]
    exact hdiv _ _ hv (le_trans (by unfold pl6mbar; exact le_max_of_le_left (le_max_right _ _)) hcσ0)
  have h8 : 8 * k₀ ≤ (4 * C₁w + 1) * cσ :=
    hdiv _ _ (by linarith) (le_trans (by unfold pl6mbar; exact le_max_of_le_right (le_max_left _ _)) hcσ0)
  have h8' : 8 * k₀ ≤ (4 * C₁w' + 1) * cσ :=
    hdiv _ _ (by linarith) (by
      exact le_trans (by unfold pl6mbar; exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
        hcσ0)
  have h8v₅ : 8 * k₀ ≤ vck C₁v₅ * ((4 * C₁v₅ + 1) * cσ) := by
    have hv : 0 < vck C₁v₅ * (4 * C₁v₅ + 1) := mul_pos (vck_pos hC₁v₅) (by linarith)
    rw [← mul_assoc]
    exact hdiv _ _ hv (le_trans (by unfold pd5mbar; exact le_max_of_le_right (le_max_left _ _)) hσ5)
  have hC₁wa : 0 ≤ M.core.C₁wa := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := M.core.hEaB; exact h
  have h8w₅ : 8 * k₀ ≤ (4 * M.core.C₁wa + 1) * cσ :=
    hdiv _ _ (by linarith) (le_trans (by unfold pd5mbar; exact le_max_of_le_right (le_max_right _ _)) hσ5)
  have h8t : 8 * k₀ ≤ vck C₁t * ((4 * C₁t + 1) * cσ) := by
    have hv : 0 < vck C₁t * (4 * C₁t + 1) := mul_pos (vck_pos hC₁t) (by linarith)
    rw [← mul_assoc]
    exact hdiv _ _ hv (by rw [hcσd]; unfold pd6mbar; exact le_max_right _ _)
  have hcl := pairLoop_close (cδ := M.core.cRel) (G2 := 4 / betaL L) (ct := M.core.ce)
    (B' := max M.core.B' 0) (ca := 0) (Θ₀ := 2 * pl6CEM M C₁k C₁w C₁w' Clo Clb)
    (Θ₁ := pl6Θ M C₁k C₁w C₁w' Clo Clb) (k₀ := k₀) (S := cσ) (by positivity) hΘ hk₀ hloop
    (by rw [show 2 * crErr2 1 M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) 0 *
      (2 * pl6CEM M C₁k C₁w C₁w' Clo Clb) * k₀ = 2 * pl6X M * (2 * pl6CEM M C₁k C₁w C₁w' Clo Clb) * k₀
      from rfl]; exact hm1) le_rfl hmbar
  set cej := pl6ce M C₁k C₁w C₁w' Clo Clb (pairUnitC M) cσ with hcejd
  have hcej : 0 ≤ cej := hcl.1
  have hcrE : crErr2 cej M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) 0 ≤ cσ := hcl.2.1
  have hU := pairUnitSeed_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall
  have hJS : PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cej 0 cσ :=
    hJC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam (pairUnitC M) 0 cσ cσ hU
      (pairUnitC_nonneg M) hmbar le_rfl le_rfl h8v h8 h8'
  have hRRall := pairRRelR_of_jointSizesP3_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam
    hcej hcrE hJS
  have hRR' := hRRall.1
  -- the `V`-bounds up to `N_h + 1` and the history items of `PairDefSizesR3P`
  have hVBtop := hVBt N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam (pairUnitC M) cσ cσ hU
    hmbar le_rfl h8v₅ hRRall.2.1
  -- the last step of the reduced history: `PairZeroRemAB` and the last-step defect
  have zVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have zGl : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.1 m hm b μ₀ hadm).1
  have zρ0R : 0 ≤ R.ρ := by rw [hRρ]; exact hρpos.le
  have zKm := hZTl N (R.withMsq m) hP zρ0R (le_of_eq hRρ) hm.1 hm.2 Nh hNh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  have zmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    show |m| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]; exact h1
  have zJ' : PtCorr2.LastJetBd L (R.A / 2) r₀ := by rw [hRA]; exact hJ
  have ze2 : 8 * cM * R.ℓ ^ 2 = 8 * cM * ℓ ^ 2 := by rw [hRℓ]
  have zeT : cTauL R.ℓ Cf cWL cKL = cTauL ℓ Cf cWL cKL := by rw [hRℓ]
  have zLK : LastKRem R Nh m b μ₀ KA := by
    rw [hKAd, ← hRℓ]
    refine lastKRem_of R hNh hval hvalL zVN hLpl hL8 zmN zGl hr₀ hr₀1 zJ' hcWL hcKL hCf0
      (hg0 Nh le_rfl).1 (hg0 Nh le_rfl).2 (by rw [hRρ]; exact hs1) (by rw [ze2]; exact hs2)
      (by rw [zeT]; exact hs3) (by rw [zeT]; exact hs4) (by rw [zeT]; exact hs5)
      (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (by omega))
      (fun x hx h1 hj => hLKo N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (by omega))
      (fun x hx h1 hj => (htop x hx h1 hj).1) hl1
  have zLAp := lastOneRem_of R hNh hval hvalL zVN hLpl hL8 zGl hcWL (hg' Nh le_rfl).1
    (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (by omega))
    (fun x hx h1 hj => (htop x hx h1 hj).1) (by
      have e : R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128 = ℓ ^ 2 / 8 + ℓ ^ 4 / 128 := by rw [hRℓ]
      rw [e]; exact hsmA) zLK
  have hTS := hTop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam (pairUnitC M) cσ cσ hU hmbar
    le_rfl h8t hRRall.2.1 hVBtop
  have hβNh : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → hBeta R m b μ₀ x Nh ≠ 0 := fun x hx h1 hj =>
    (hBeta_rel_of R hNh hb x (hrel _) (hn _) (htop x hx h1 hj).1 Nh le_rfl).1
  have hvwA6 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      vwA R m b μ₀ x Nh ≤ pairUnitC M * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := fun x hx h1 hj =>
    vwA_le_mag_MF M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl hKl hl hsmall x h1 hj
      le_rfl (hβNh x hx h1 hj)
  have hMb6 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → 0 < vwB R m b μ₀ lam x := by
    intro x hx h1 hj
    have hA0 : 0 < vwA R m b μ₀ x Nh := by
      unfold vwA; rw [if_neg (hβNh x hx h1 hj)]
      have := histS_pos' (R.withMsq m) zρ0R (by show R.ρ ≤ 1 / 8; rw [hRρ]; exact hρ8)
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) Nh
      have := norm_pos_iff.2 (hβNh x hx h1 hj)
      positivity
    have h := (hA0.trans_le (hvwA6 x hx h1 hj))
    have hM0 : 0 < ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ := by
      rcases (norm_nonneg (Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x))).lt_or_eq with h' | h'
      · exact h'
      · rw [← h', mul_zero, zero_mul] at h; exact absurd h (lt_irrefl _)
    exact mul_pos hM0 (hg0 _ hj).1
  have hmAB' := hmAB
  unfold pd6cS at hmAB'
  obtain ⟨hAB, hDL⟩ := pairZeroAB_of R hNh hm.1 hval hvalL zVN hLpl hL8
    (by rw [hRA]; exact M.core.hA2) zmN zGl hr₀ hr₀1 zJ' hcWL hcKL hCf0 (hg0 Nh le_rfl).1
    (hg0 Nh le_rfl).2 (by rw [hRρ]; exact hs1) (by rw [ze2]; exact hs2) (by rw [zeT]; exact hs3)
    (by rw [zeT]; exact hs4) (by rw [zeT]; exact hs5) lam (oRed R m b μ₀ dxStd) hRd
    (mul_nonneg (by norm_num) hcσ) (mul_nonneg (mul_nonneg (by linarith) hc0) hcσ)
    (mul_nonneg (by linarith) hcσ) hTS
    (fun x hx h1 hj => (htop x hx h1 hj).1) hβNh hMb6 (pairUnitC_nonneg M) hvwA6 hRR'
    zLAp.2 zKm hmT (by
      have e : R.ℓ ^ 2 = M.core.ℓ ^ 2 := by rw [hRℓ]
      rw [e]; exact hmAB')
  have hNF := pairDefSizesNF_of_last_MFC M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl
    hKl hl hsmall cσ hmbar h8w₅ hVBtop cσ hcσ hRR' _ hDL
  have hDS := pairDefSizesR3P_of_NF_MFC M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm lam Kl
    hKl hl hsmall cσ hmbar h8w₅ hVBtop _ hNF
  set e1 := pd6e1 M C₁t r₀ cσ with he1d
  have he1 : 0 ≤ e1 := by
    rw [he1d]; unfold pd6e1
    have h1 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81 / 16) (cJab_nonneg L hr₀))
      (pd6cS_nonneg M hC₁t hc0 hcσ)
    linarith
  have hDf := pairDefSumR_of_sizes3P_MF M R hNh m b μ₀ lam hDS
  have hρ1 : R.ρ < 1 := by rw [hRρ]; linarith
  have hspl' : SplitSmall R.P L R.ρ := by rw [hP, hRρ]; exact hspl
  have hVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have hC := pairCstRelR_of_parts R hP hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hVN hL8 hb hh lam
    (oRed R m b μ₀ dxStd) hcσ (fun k hk => (hg' k hk).1) hRd hSeed
    hRR' hS hDf
  -- PR6: `PairZeroRelR` from `PairRRelR` and the last-step remainders
  have hcr' : 0 ≤ cσ := hcσ
  have hK3 : 0 ≤ (2 * (cσ + e1)) := by linarith
  have hK2 : 0 ≤ 4 * (1 : ℝ) + 2 * (cσ + e1) := by
    linarith
  -- PR6 items (a), (e): `P₀ ≠ 0` and the zero-mode constant
  have hGl : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.1 m hm b μ₀ hadm).1
  have hρ0R : 0 ≤ R.ρ := by rw [hRρ]; exact hρpos.le
  have hKl := hZTl N (R.withMsq m) hP hρ0R (le_of_eq hRρ) hm.1 hm.2 Nh hNh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)
  -- PR6 item (b): `LastKRem` from the block sizes of the last step
  have hmN : |(R.withMsq m).msq| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    show |m| * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1
    rw [abs_of_pos hm.1]; exact h1
  have hJ' : PtCorr2.LastJetBd L (R.A / 2) r₀ := by rw [hRA]; exact hJ
  have e2 : 8 * cM * R.ℓ ^ 2 = 8 * cM * ℓ ^ 2 := by rw [hRℓ]
  have eT : cTauL R.ℓ Cf cWL cKL = cTauL ℓ Cf cWL cKL := by rw [hRℓ]
  have hLK : LastKRem R Nh m b μ₀ KA := by
    rw [hKAd, ← hRℓ]
    refine lastKRem_of R hNh hval hvalL hVN hLpl hL8 hmN hGl hr₀ hr₀1 hJ' hcWL hcKL hCf0
      (hg0 Nh le_rfl).1 (hg0 Nh le_rfl).2 (by rw [hRρ]; exact hs1) (by rw [e2]; exact hs2)
      (by rw [eT]; exact hs3) (by rw [eT]; exact hs4) (by rw [eT]; exact hs5)
      (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (by omega))
      (fun x hx h1 hj => hLKo N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (by omega))
      (fun x hx h1 hj => (htop x hx h1 hj).1) hl1
  -- PR6 item (b) and the size of `εF_a`: `LastOneRem` from `LastKRem`
  have hLAp := lastOneRem_of R hNh hval hvalL hVN hLpl hL8 hGl hcWL (hg' Nh le_rfl).1
    (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm (ptsX x) (by omega))
    (fun x hx h1 hj => (htop x hx h1 hj).1) (by
      have e : R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128 = ℓ ^ 2 / 8 + ℓ ^ 4 / 128 := by rw [hRℓ]
      rw [e]; exact hsmA) hLK
  have hZR := pairZeroRemW_of_A1 R hNh hm.1 b μ₀ lam (oRed R m b μ₀ dxStd) hρ0R hρ1 hLAp.2
    hKl hmT hmA hLAp.1 hAB
  have hZ := pairZeroRelW_of R m b μ₀ lam (oRed R m b μ₀ dxStd) hcr' he1 zero_le_one
    (fun k hk => (hg' k hk).1)
    (fun x hx h1 hj => betaN_ne_of R hNh hb x (hrel _) (hn _) (htop x hx h1 hj).1) hRR' hZR
  exact pairAboveW1_of_redW R hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hL8 hb hh lam
    (oRed R m b μ₀ dxStd) hK2 hK3 hg' hMb hRd hC hZ hGT.1

set_option maxHeartbeats 8000000 in
/-- **`pairAbove_final6_MF'`: the pair layer with `PairDefSizesNF` and `PairZeroRemAB`
discharged** (at the canonical constants `C₁ka`, `C₁wa`, `cwClo`, `cwClb` of the master
construction; `m̄ = c_σ = pd6mbar`). The remaining hypotheses are those of `PairFinal5Concl` without
`PairDefSizesNF`, `PairZeroRemAB`, plus the mass window of item (d). -/
theorem pairAbove_final6_MF' {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ Kt r₀ C₁v C₁v₅ C₁t : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁v ∧ 0 ≤ C₁v₅ ∧ 0 ≤ C₁t ∧
      PairFinal6Concl M Kt r₀ C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ C₁t := by
  obtain ⟨hClo, hClb, -⟩ := cw_wpo_spec
  obtain ⟨-, hC₁k, -, -, -, -, -, hC₁w, -⟩ := M.core.hEaB
  obtain ⟨C₁v, hC₁v, hJC⟩ := pairJointSizesP3_closedC M
  obtain ⟨Kt, r₀, C₁v₅, C₁t, hKt, hr₀, hr₀1, hC₁v₅, hC₁t, H⟩ :=
    pairAbove_final6_at M hC₁v hC₁k hC₁w hC₁w hClo hClb
  exact ⟨Kt, r₀, C₁v, C₁v₅, C₁t, hKt, hr₀, hr₀1, hC₁v, hC₁v₅, hC₁t, H hJC M.core.hloopF⟩

end

end Spin2
