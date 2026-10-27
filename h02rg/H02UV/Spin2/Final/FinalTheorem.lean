import Spin2.Final.FinalBeta
import Spin2.Pair.PairFinal6
import Spin2.Pair.PairDef6bD

/-!
# The final theorem: `thm:multiscale` at `h = 0` at the shooting value, no named hypotheses

`thm_multiscale_h0_beta` (`Spin2/Final/FinalBeta`) with the pair inputs `PairDefSizesNF`, `PairZeroRemAB`
discharged by the pair layer of `Spin2/PairFinal6D`:

* **`FwPairConcl6D`**, **`fw_pairAbove6_atD`**, **`fw_pairAbove6_MFD'`**: `PairFinal6ConclD`,
  `pairAbove_final6_atD`, `pairAbove_final6_MFD'` without `GamLastRem(S)` (copies; `GamTopBd` from
  `MasterFacts.fw_gamTopBdD`, the `c_r` factor becomes `fwKG`, as `fw_pairAbove5_atD`).
* **`MasterFacts.fw_multiscale_traj6`**: `fw_multiscale_traj5` from `FwPairConcl6D`; the new mass
  window `2·(81/16)c_J(c_ρ + 4/r₀²)c_Sℓ²·m²L^{2N} ≤ 1` from `m²L^{2N} ≤ fwG6`.
* **`FwPairBd6`**, **`FwRes6`**, **`MasterFacts.fw_atG6`**, **`fb_consts6`**,
  **`MasterFacts.fw_bracket6`**, **`thm_multiscale_h0_beta6`**: the chain of `Spin2/Final/FinalBeta` with
  the pair bound `FwPairBd6` (no pair inputs; `g₀` capped by `fwG6`).
* **`thm_multiscale_final_h0`**: the final theorem. `K_p a_{N_h−1} ≤ 1/2` is replaced by `N ≥ N₀(L)`
  (the `m²` part follows from the `β_R` range), `100C_b/β_R ≤ 1` and `m² ∈ mRange` are folded into
  `g₀` and the `β_R` range.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- The conclusion of `pairAbove_final6_atD` (`PairFinal5ConclD` without `PairDefSizesNF` and
`PairZeroRemAB`, with the mass window of item (d)). -/
def FwPairConcl6D {L : ℕ} [NeZero L] (M : MasterFacts L) (Kt r₀ C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ C₁t : ℝ) :
    Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    b ≤ μ₀ + m →
  ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl →
    HLam R Nh m b μ₀ lam Kl →
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
        (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) + pd6cd M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + (4 * 1 + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t)) + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t))) * M.fwKG) ((4 * 1 + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t)) + 2 * ((pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t) + pd6e1 M C₁t r₀ (pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t))) * Mb)

set_option maxHeartbeats 8000000 in
/-- **`pairAbove_final6_MFD'` at given constants** (the body of `pairAbove_final5_atD`, with
`PairDefSizesNF` and `PairZeroRemAB` discharged). -/
theorem fw_pairAbove6_atD {L : ℕ} [NeZero L] (M : MasterFacts L) {C₁v C₁k C₁w C₁w' Clo Clb : ℝ}
    (hC₁v : 0 ≤ C₁v) (hC₁k : 0 ≤ C₁k) (hC₁w : 0 ≤ C₁w) (hC₁w' : 0 ≤ C₁w') (hClo : 0 ≤ Clo)
    (hClb : 0 ≤ Clb) :
    ∃ Kt r₀ C₁v₅ C₁t : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁v₅ ∧ 0 ≤ C₁t ∧
    (PJClosedPD6 M C₁v C₁k C₁w C₁w' Clo Clb → pl6X M * pl6Θ M C₁k C₁w C₁w' Clo Clb ≤ 1 / 2 →
      FwPairConcl6D M Kt r₀ C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ C₁t) := by
  obtain ⟨C₁v₅, hC₁v₅, hVBt⟩ := pairVB_top_MFD M
  obtain ⟨C₁t, hC₁t, hTop⟩ := pairTopSizes_MFD M
  unfold FwPairConcl6D
  have hL49 : 49 ≤ L := M.core.hL49
  have hLpl : pauliL0 2 ≤ L := M.core.hLpl
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
  set Kp := max (lamRelK (betaL L) cg (B₁ + B₂ + B₃) B' cq cδ (eRange (betaL L) Ke 1) 4) 0
    with hKpd
  have hF := M.flow
  have hε1 := M.eps_le
  have hSp := M.spinD
  have hMC := M.magD
  have hLoop := M.loopD
  have hcδ := M.cRel_nonneg
  have hRelG := M.relGD
  have hcw := M.cw_nonneg
  have hWK := M.wkD
  have hce := M.cGB_nonneg
  have hGB := M.gamBulkD
  have hKZ := M.KZ_nonneg
  have hGM := M.gmonoD
  have hLV := M.lastValid
  have hGI := M.gincD
  have hZT := M.zeroT
  have hcWL := M.cWL_nonneg
  have hLW := M.lastWD
  obtain ⟨r₀, hr₀, hr₀1, hJ⟩ := M.jet
  have hcKL := M.cKL_nonneg
  have hLKo := M.lastKD
  have hLA1 := M.lastL1D
  have hTopC := M.topD
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num; omega
  have hKp : 0 ≤ Kp := le_max_right _ _
  obtain ⟨Kt, hKt, hZTl⟩ := PtCorr2.lastOut_zeroT hZT
  refine ⟨Kt, r₀, C₁v₅, C₁t, hKt, hr₀, hr₀1, hC₁v₅, hC₁t, ?_⟩
  intro hJC hloop N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam Kl hKl hl
    hsmall Mb hMb hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hmAB
  set cσ := pd6mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa C₁t with hcσd
  have hσ5 : pd5mbar M C₁v C₁k C₁w C₁w' Clo Clb C₁v₅ M.core.C₁wa ≤ cσ := by
    rw [hcσd]; unfold pd6mbar; exact le_max_left _ _
  have hcσ0 : pl6mbar M C₁v C₁k C₁w C₁w' Clo Clb ≤ cσ :=
    le_trans (by unfold pd5mbar; exact le_max_left _ _) hσ5
  have htop : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      Case2TopStep R (ptsX x) (zV b) Nh m b μ₀ ∧ Case2TopStep R (ptsS x) (zV b) Nh m b μ₀ :=
    fun x _ _ _ => ⟨(hTopC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)).1,
      (hTopC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsS x)).1⟩
  set KA := cKAL L ℓ r₀ Cf cWL cKL 3 with hKAd
  have hl1 : LastL1 R Nh m b μ₀ 3 := fun x hx h1 hj =>
    hLA1 N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x)
      ((htop x hx h1 hj).1.1.trans (by norm_num))
  have hB := hGB N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk.le).1.le, ((hD k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  -- (H_λ) for the pair vertices
  have hLC := M.lamD
  have hpairP : ∀ P : Obs2.ObsPts 2 L N,
      HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) Kp := by
    intro P
    obtain ⟨hB0, -, hloop⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b)
    have h := hLam_case2D hLC hP hi0 hRℓ hRA hRρ (by omega) hm hD hB0 hcδ (zV_mua_ne hb)
      (hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b) (zV_mua_ne hb)) hloop
    exact hLam_mono hb hm.1.le (fun k hk => (hD k hk.le).1) h (le_max_left _ _)
  have hrel : ∀ P : Obs2.ObsPts 2 L N, Case2Rel R P (zV b) Nh m b μ₀ cδ := fun P =>
    hRelG N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b) (zV_mua_ne hb)
  have hn : ∀ P : Obs2.ObsPts 2 L N, ∀ k < Nh, ‖nn2 R P (zV b) m b μ₀ k‖ ≤ 1 / 8 := by
    intro P k hk
    obtain ⟨-, -, q, -, -, hl'⟩ := hLoop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b)
    exact (hl' k hk).1
  have hmono := hGM N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  obtain ⟨-, -, hWT, hWM⟩ := wk_inputsD hWK N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hβ := betaLast_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).1)
  have hβS := betaLastS_of R hNh hb hKp (fun x _ => hpairP _) (fun x _ => hrel _)
    (fun x _ => hn _) hg ha hmono (fun x hx h1 hj => (htop x hx h1 hj).2)
  have hRS := gamRemTopS_of R hb hKp hce hcw hval hg ha (fun x _ => hpairP _) hB hWM
  have hcγ : 0 ≤ (ce + cw) * (1 + 3 * Kp) := mul_nonneg (add_nonneg hce hcw) (by linarith)
  have hKβ : 0 ≤ 2 * (1 + 3 * Kp) := by linarith
  have hGT := M.fw_gamTopBdD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD lam hKl hl hsmall
  obtain ⟨-, -, hρpos, -, -, -, -, -, -, -, hCf0, -, -, hρ8, hspl, hrest⟩ := hF
  have hvalL := ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).2
  have hg' : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk).1.le, ((hD k hk).2.1).trans hε1⟩
  -- `PairVertSum` (new)
  have hβL : 0 < betaL L := lt_of_lt_of_le (by norm_num) (betaL_ge (by omega))
  have hSpN := hSp N R hP hi0 hRℓ hRA hRρ (by omega) Nh (by omega)
  have hSS := hSpN.2.1 m hm
  have hZb := hSpN.2.2.2.2.1 m hm b μ₀ hD
  have hMag := magAt_ofD R hMC hP hi0 hRℓ hRA hRρ (by omega) (Nh := Nh) (by omega) hm hD
  have hg0 : ∀ k ≤ Nh, 0 < (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hD k hk).1, ((hD k hk).2.1).trans hε1⟩
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
  have hS := pairVertSum_ofD R hP hb hKZ hKp hval hvalL (hLV N R hP hRℓ hRρ hN2 Nh hNh m hm) hg0 ha
    hjN hZb (fun x _ => hpairP _) hβ (hSS b μ₀ hD) hD hβL hMag hKl hl hsmall
  rw [hRℓ] at hS
  -- the `ε_k` half: `Case2Rel`, `Case2TopStep`, `∑ǧ² ≤ 4/β`
  have hG2 : ∑ k ∈ Finset.range Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤ 4 / betaL L :=
    sum_gsq_le_of_inc hβL (hGI N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD)
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
  obtain ⟨hct, -, -⟩ := M.tadD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hCE := pl6CEM_nonneg M hC₁k hC₁w hC₁w' hClo hClb hθa0 Hap.hcx hct
  have hc0 : 0 ≤ M.core.c := by
    obtain ⟨_, _, _, _, hAH⟩ := M.core.abwHistD6
    obtain ⟨hcR, -⟩ := hAH N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
    rw [← hcR]; unfold cR cV cW cZ
    have := Hap.hcmu; have := Hap.hC₂; positivity
  have hε0 : 0 ≤ M.core.ε := ((hD 0 (Nat.zero_le _)).1.trans_le (hD 0 (Nat.zero_le _)).2.1).le
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
  have hU := pairUnitSeed_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl hKl hl hsmall
  have hJS : PairJointSizesP3 R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cej 0 cσ :=
    hJC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam (pairUnitC M) 0 cσ cσ hU
      (pairUnitC_nonneg M) hmbar le_rfl le_rfl h8v h8 h8'
  have hRRall := pairRRelR_of_jointSizesP3_MFD6 M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam
    hcej hcrE hJS
  have hRR' := hRRall.1
  -- the `V`-bounds up to `N_h + 1` and the history items of `PairDefSizesR3P`
  have hVBtop := hVBt N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam (pairUnitC M) cσ cσ hU
    hmbar le_rfl h8v₅ hRRall.2.1
  -- the last step of the reduced history: `PairZeroRemAB` and the last-step defect
  have zVN := hLV N R hP hRℓ hRρ hN2 Nh hNh m hm
  have zGl : GlueOut (R.withMsq m) Nh Cf (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) :=
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD).1
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
      (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega))
      (fun x hx h1 hj => hLKo N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega))
      (fun x hx h1 hj => (htop x hx h1 hj).1) hl1
  have zLAp := lastOneRem_of R hNh hval hvalL zVN hLpl hL8 zGl hcWL (hg' Nh le_rfl).1
    (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega))
    (fun x hx h1 hj => (htop x hx h1 hj).1) (by
      have e : R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128 = ℓ ^ 2 / 8 + ℓ ^ 4 / 128 := by rw [hRℓ]
      rw [e]; exact hsmA) zLK
  have hTS := hTop N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam (pairUnitC M) cσ cσ hU hmbar
    le_rfl h8t hRRall.2.1 hVBtop
  have hβNh : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → hBeta R m b μ₀ x Nh ≠ 0 := fun x hx h1 hj =>
    (hBeta_rel_of R hNh hb x (hrel _) (hn _) (htop x hx h1 hj).1 Nh le_rfl).1
  have hvwA6 : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
      vwA R m b μ₀ x Nh ≤ pairUnitC M * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 := fun x hx h1 hj =>
    vwA_le_mag_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl hKl hl hsmall x h1 hj
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
  have hNF := pairDefSizesNF_of_last_MFCD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl
    hKl hl hsmall cσ hmbar h8w₅ hVBtop cσ hcσ hRR' _ hDL
  have hDS := pairDefSizesR3P_of_NF_MFCD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl
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
    (M.glueD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD).1
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
      (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega))
      (fun x hx h1 hj => hLKo N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega))
      (fun x hx h1 hj => (htop x hx h1 hj).1) hl1
  -- PR6 item (b) and the size of `εF_a`: `LastOneRem` from `LastKRem`
  have hLAp := lastOneRem_of R hNh hval hvalL hVN hLpl hL8 hGl hcWL (hg' Nh le_rfl).1
    (fun x hx h1 hj => hLW N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD (ptsX x) (by omega))
    (fun x hx h1 hj => (htop x hx h1 hj).1) (by
      have e : R.ℓ ^ 2 / 8 + R.ℓ ^ 4 / 128 = ℓ ^ 2 / 8 + ℓ ^ 4 / 128 := by rw [hRℓ]
      rw [e]; exact hsmA) hLK
  have hZR := pairZeroRemW_of_A1 R hNh hm.1 b μ₀ lam (oRed R m b μ₀ dxStd) hρ0R hρ1 hLAp.2
    hKl hmT hmA hLAp.1 hAB
  have hZ := pairZeroRelW_of R m b μ₀ lam (oRed R m b μ₀ dxStd) hcr' he1 zero_le_one
    (fun k hk => (hg' k hk).1)
    (fun x hx h1 hj => betaN_ne_of R hNh hb x (hrel _) (hn _) (htop x hx h1 hj).1) hRR' hZR
  exact pairAboveW1_of_redW R hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hL8 hb hh lam
    (oRed R m b μ₀ dxStd) hK2 hK3 hg' hMb hRd hC hZ hGT


set_option maxHeartbeats 8000000 in
/-- **`pairAbove_final6_MFD'` without `GamLastRem(S)`** (conclusion `FwPairConcl6D`). -/
theorem fw_pairAbove6_MFD' {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ Kt r₀ C₁v C₁v₅ C₁t : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁v ∧ 0 ≤ C₁v₅ ∧ 0 ≤ C₁t ∧
      FwPairConcl6D M Kt r₀ C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ C₁t := by
  obtain ⟨hClo, hClb, -⟩ := cw_wpo_spec
  obtain ⟨-, hC₁k, -, -, -, -, -, hC₁w, -⟩ := M.core.hEaB
  obtain ⟨C₁v, hC₁v, hJC⟩ := pairJointSizesP3_closedCD6 M
  obtain ⟨Kt, r₀, C₁v₅, C₁t, hKt, hr₀, hr₀1, hC₁v₅, hC₁t, H⟩ :=
    fw_pairAbove6_atD M hC₁v hC₁k hC₁w hC₁w hClo hClb
  exact ⟨Kt, r₀, C₁v, C₁v₅, C₁t, hKt, hr₀, hr₀1, hC₁v, hC₁v₅, hC₁t, H hJC M.core.hloopF⟩

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The coefficient of the mass window of the `ab` last step (item (d) of `pairZeroAB_of`). -/
def fwA6 (r₀ C₁v C₁v₅ C₁t : ℝ) : ℝ :=
  2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) *
    pd6cS M C₁t (pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t) *
      M.core.ℓ ^ 2)

/-- The smallness threshold `fwG` capped by the mass window of the `ab` last step. -/
def fwG6 (Kt r₀ C₁v C₁v₅ C₁t : ℝ) : ℝ :=
  min (M.fwG Kt r₀) (1 / (|M.fwA6 r₀ C₁v C₁v₅ C₁t| + 1))

theorem fwG6_pos {Kt r₀ C₁v C₁v₅ C₁t : ℝ} (hr₀ : 0 < r₀) : 0 < M.fwG6 Kt r₀ C₁v C₁v₅ C₁t :=
  lt_min (M.fwG_pos hr₀) (by positivity)

/-- The final pair constant of `FwPairConcl6D`. -/
def fwKE6 (r₀ C₁v C₁v₅ C₁t : ℝ) : ℝ :=
  (pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t) *
      (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
        (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) +
    pd6cd M C₁t r₀ (pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t) +
    (4 * 1 + 2 * ((pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t) +
        pd6e1 M C₁t r₀ (pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t)) +
      2 * ((pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t) +
        pd6e1 M C₁t r₀ (pd6mbar M C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ M.core.C₁wa C₁t))) *
      M.fwKG

/-- **The final constant `K`** of `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ Kϑ_j²/β_j` (no pair inputs). -/
def fwK6 (r₀ C₁v C₁v₅ C₁t : ℝ) : ℝ :=
  multK L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp (M.tpKP M.Kp (M.fwKE6 r₀ C₁v C₁v₅ C₁t))

set_option maxHeartbeats 4000000 in
/-- **`thm:multiscale` on one `h = 0` trajectory** from `FwPairConcl6D` (no pair inputs), with the
last-step smallness discharged by `ǧ_{N_h} ≤ fwG`, `m²L^{2N} ≤ fwG6`. -/
theorem fw_multiscale_traj6 {Kt r₀ C₁v C₁v₅ C₁t : ℝ}
    (H : FwPairConcl6D M Kt r₀ C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ C₁t)
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hG : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ M.fwG Kt r₀)
    (hmΛ : m * (L : ℝ) ^ (2 * N) ≤ M.fwG6 Kt r₀ C₁v C₁v₅ C₁t)
    (x : Lam 2 L N) (hx : x ≠ 0) (hj : Obs.coal L (0 : Lam 2 L N) x ≤ Nh) :
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
        M.fwK6 r₀ C₁v C₁v₅ C₁t * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp := by
  obtain ⟨-, -, hρ, -⟩ := M.core.hC2
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  set G := (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 with hGd
  set X := m * (L : ℝ) ^ (2 * N) with hXd
  have hG0 : 0 ≤ G := (hD Nh le_rfl).1.le
  have hX0 : 0 ≤ X := mul_nonneg hm.1.le (by positivity)
  have hmΛ' : X ≤ M.fwG Kt r₀ := hmΛ.trans (min_le_left _ _)
  set g := M.fwG Kt r₀ with hgd
  have m1 : g ≤ _ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have m2 : g ≤ _ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have m3 : g ≤ _ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have m4 : g ≤ _ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have m5 : g ≤ _ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have m6 : g ≤ _ := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have m7 : g ≤ _ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _)))
  have m8 : g ≤ _ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_right _ _)))
  have m9 : g ≤ _ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmono := M.gmonoD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD
  have hjN : ∀ j ≤ Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ G := by
    intro j hj
    have key : ∀ n, j + n ≤ Nh → (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (j + n)).1 := by
      intro n
      induction n with
      | zero => intro _; exact le_rfl
      | succ n ih => intro hn; exact (ih (by omega)).trans (hmono (j + n) (by omega))
    have := key (Nh - j) (by omega)
    rwa [show j + (Nh - j) = Nh by omega] at this
  have hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2 := fun j hj =>
    fw_le (hD j hj).1.le (((hjN j hj).trans hG).trans m9)
  set P : Obs2.ObsPts 2 L N := ptsX x with hPd
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P
  set Mb := ∑ k ∈ Finset.range (Nh + 1),
    ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) k‖ with hMbd
  have hMb : ∀ k ≤ Nh, ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) k‖ ≤ Mb :=
    fun k hk => Finset.single_le_sum (f := fun k =>
      ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) k‖) (fun i _ => norm_nonneg _)
      (Finset.mem_range.2 (by omega))
  have s1 := fw_le hG0 (hG.trans m1)
  have s2 : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 := by
    rw [mul_assoc]; exact fw_le hX0 (hmΛ'.trans m2)
  have s3 : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    rw [mul_assoc]; exact fw_le hX0 (hmΛ'.trans m3)
  have s4 : 2 * (M.core.Cf * G) ≤ M.core.ρ := by
    rw [← mul_assoc]; exact fw_le hG0 (hG.trans m4)
  have s5 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * G) ≤ 1 / 2 := by
    rw [← mul_assoc]; exact fw_le hG0 (hG.trans m5)
  have s6 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * G) ≤ 1 := by
    rw [← mul_assoc]; exact fw_le hG0 (hG.trans m6)
  have s7 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * G) ≤ r₀ ^ 2 := by
    rw [← mul_assoc]; exact fw_le hG0 (hG.trans m7)
  have s8 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * G ≤ r₀ :=
    fw_le hG0 (hG.trans m8)
  have s9 : M.fwA6 r₀ C₁v C₁v₅ C₁t * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    rw [mul_assoc]; exact fw_le hX0 (hmΛ.trans (min_le_right _ _))
  have hW1 := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (by linarith) _ M.Kp
    M.Kp_nonneg hl hsmall Mb hMb s1 s2 s3 s4 s5 s6 s7 s8 s9
  have hsq := M.twoPtSqD M.core.hL49 R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD (by linarith) _
    M.Kp_nonneg hl hW1 hsmall
  exact M.core.multiscale_h0 R hP hi0 hRℓ hRA hRρ (by omega) hm hb hD _ M.Kp_nonneg
    (M.tpKP_nonneg _ _) hl hsq x hx hj

end MasterFacts

/-- **The pair bound at `h = 0`, no pair inputs**: for every `x ≠ 0` with `j_x ≤ N_h`,
`|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ Kϑ_j²/β_j` at the physical scale `j` of `x`. -/
def FwPairBd6 {L : ℕ} [NeZero L] (K : ℝ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (Nh : ℕ) (m b : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
  ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
    jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
    |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
      K * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp

/-- `FwRes` with the pair bound `FwPairBd6`. -/
def FwRes6 {L : ℕ} [NeZero L] (M : MasterFacts L) (pW K : ℝ) {N : ℕ} (R : RGPar 2 L N)
    [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (m b μc : ℝ) : Prop :=
  (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
    |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤
      pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1)) ∧
    FwPairBd6 K R Nh m b

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

set_option maxHeartbeats 4000000 in
/-- **`fw_atG` with the pair layer `FwPairConcl6D`** (conclusion `FwRes6`, threshold `fwG6`). -/
theorem fw_atG6 {pW r₀ Kt r₁ C₁v C₁v₅ C₁t : ℝ} (hE : H0EndsConclG M pW r₀)
    (hs : pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12) (hr₁ : 0 < r₁)
    (H : FwPairConcl6D M Kt r₁ C₁v M.core.C₁ka M.core.C₁wa M.core.C₁wa cwClo cwClb C₁v₅ C₁t) :
    0 < min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.core.ε / 2) /
      (1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm)) ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.core.ε / 2) /
        (1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm)) →
      H0OnePtSmall M N Nh m r₀ (5 / 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) →
      FwRes6 M pW (M.fwK6 r₁ C₁v C₁v₅ C₁t) R Nh m b μc := by
  obtain ⟨-, -, -, hε, -, -, -, hcm, -⟩ := M.core.hC2
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  have hcμ : 0 < cmu ((L : ℝ) ^ 2) M.core.cm := by
    unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hwin := h0_win_cond hcμ hs
  set θ := 3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm with hθd
  have hθ0 : 0 ≤ θ := by positivity
  set q := 1 + 2 * |pW| * θ with hqd
  have hq1 : 1 ≤ q := by have : 0 ≤ 2 * |pW| * θ := by positivity
                         linarith
  set G6 := M.fwG6 Kt r₁ C₁v C₁v₅ C₁t with hG6d
  have hgm : 0 < min G6 (M.core.ε / 2) := lt_min (M.fwG6_pos hr₁) (by linarith)
  refine ⟨div_pos hgm (by linarith), ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV hgc hsm
  have hN2 : 2 ≤ N := by omega
  set gc := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 with hgcd
  have hgc0 : 0 ≤ gc := (hadm.1 Nh le_rfl).1.le
  have hgq : gc * q ≤ min G6 (M.core.ε / 2) := by
    rwa [le_div_iff₀ (by linarith)] at hgc
  have hpq : 1 + 2 * pW * θ ≤ q := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self pW)
      (by norm_num : (0 : ℝ) ≤ 2)) hθ0
    linarith
  have hgy : gc * (1 + 2 * pW * θ) < M.core.ε := by
    have := mul_le_mul_of_nonneg_left hpq hgc0
    have := min_le_right G6 (M.core.ε / 2)
    linarith
  have hcard : (Fintype.card (Lam 2 L N) : ℝ) = (L : ℝ) ^ (2 * N) := by
    rw [show Fintype.card (Lam 2 L N) = (L ^ N) ^ 2 from FRD.card_torus]; push_cast; ring
  obtain ⟨μl, μu, -, -, -, -, -, -, -, hD0, -, hgd⟩ := hE N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm
    b μc hb hadm (by rw [hcard]; exact hmV) hwin hgy hsm
  have e : ∀ x : ℝ, pW * (x - -x) = pW * (2 * x) := fun x => by ring
  refine ⟨hD0, by rw [← e]; exact hgd, fun x hx hj => ?_⟩
  have hG : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ G6 := by
    have h1 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 - gc ≤
        pW * (θ * gc - -(θ * gc)) := (abs_le.1 hgd).2
    have h2 : pW * (θ * gc - -(θ * gc)) ≤ |pW| * (θ * gc - -(θ * gc)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by have := mul_nonneg hθ0 hgc0; linarith)
    have e : gc * q = gc + |pW| * (θ * gc - -(θ * gc)) := by rw [hqd]; ring
    have := min_le_left G6 (M.core.ε / 2)
    linarith
  have hmΛ : m * (L : ℝ) ^ (2 * N) ≤ G6 := by
    have := min_le_left G6 (M.core.ε / 2)
    have hgq' : gc ≤ gc * q := le_mul_of_one_le_right hgc0 hq1
    linarith
  exact M.fw_multiscale_traj6 H R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD0 (hG.trans (min_le_left _ _))
    hmΛ x hx hj

end MasterFacts

set_option maxHeartbeats 4000000 in
/-- **The constants of the final theorem** (`fb_constsG` with the pair layer `FwPairConcl6D`):
`g₀ = min(g₀(fw_atG6), G₁)`, pair constant `K = fwK6`. -/
theorem fb_consts6 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (pW g₀ K : ℝ), 0 < g₀ ∧ g₀ ≤ M.core.ε / 2 ∧
      pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
    ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwRes6 M pW K R Nh m b μc := by
  obtain ⟨L₀, h⟩ := thm_master_all
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M⟩ := h L hL
  obtain ⟨pW, r₀, hs, hr₀, -, hE⟩ := M.fb_h0EndsGS
  obtain ⟨Kt, r₁, C₁v, C₁v₅, C₁t, -, hr₁, -, -, -, -, H⟩ := fw_pairAbove6_MFD' M
  obtain ⟨hg, hF⟩ := M.fw_atG6 hE hs hr₁ H
  obtain ⟨G₁, hG₁, hsm⟩ := M.fb_small hr₀
  have hθ : 0 ≤ 3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm := by
    have hL2 : (2 : ℝ) ≤ L := by
      exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
    obtain ⟨-, -, -, -, -, -, -, hcm, -⟩ := M.core.hC2
    have : 0 ≤ cmu ((L : ℝ) ^ 2) M.core.cm := by
      unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
      positivity
    positivity
  have hq : 1 ≤ 1 + 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm) := by
    have : 0 ≤ 2 * |pW| * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm) := by positivity
    linarith
  have hmin : 0 ≤ min (M.fwG6 Kt r₁ C₁v C₁v₅ C₁t) (M.core.ε / 2) := by
    by_contra hc
    exact absurd hg (not_lt.2 (div_nonpos_of_nonpos_of_nonneg (not_le.1 hc).le (by linarith)))
  have hg'ε := (div_le_self hmin hq).trans (min_le_right _ _)
  refine ⟨M, pW, _, M.fwK6 r₁ C₁v C₁v₅ C₁t, lt_min hg hG₁, (min_le_left _ _).trans hg'ε, hs, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz b μc hb hadm hmV hgc
  exact hF N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV (hgc.trans (min_le_left _ _))
    (hsm N Nh m _ hm.1.le (hadm.1 Nh le_rfl).1.le (hgc.trans (min_le_right _ _)) hmV hKz)

set_option maxHeartbeats 4000000 in
/-- **`fw_bracket` with `FwRes6`.** -/
theorem MasterFacts.fw_bracket6 {L : ℕ} [NeZero L] (M : MasterFacts L) {pW g₀ K : ℝ}
    (hgε : g₀ ≤ M.core.ε / 2) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hF : ∀ b μc : ℝ, 0 < b →
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
      m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ≤ g₀ → FwRes6 M pW K R Nh m b μc)
    (hm : m ∈ mRange L N) {b₁ b₂ μ₁ μ₂ y : ℝ}
    (hb₁ : 0 < b₁) (hb12 : b₁ ≤ b₂)
    (ha₁ : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₁ μ₁)
    (ha₂ : Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₂ μ₂)
    (hm₁ : m * (L : ℝ) ^ (2 * N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1)
    (hg₂ : (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 ≤ g₀)
    (hy₁ : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁) +
          (pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1)) +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ (b₁ - m) Nh).1 ^ 2 +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 ^ 2) ≤ y)
    (hy₂ : y ≤ gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂) -
          (pW * (2 * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1)) +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ (b₂ - m) Nh).1 ^ 2 +
            2 * M.core.Cb * (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 ^ 2)) :
    ∃ b ∈ Icc b₁ b₂, gFinH0 R Nh m b = y ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      FwPairBd6 K R Nh m b := by
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, -, -, -, -, H⟩ := M.core.hC2
  obtain ⟨hfc, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  have fc := hfc m hm
  have hg₂ε : (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 < M.core.ε := by linarith
  have hBe := fun b (hb : b ∈ Icc b₁ b₂) => fb_ufix_between fc ha₁ ha₂ hg₂ε hb
  obtain ⟨-, h1, h2⟩ := hBe b₁ ⟨le_rfl, hb12⟩
  have hb₂ : 0 < b₂ := hb₁.trans_le hb12
  obtain ⟨hD₁, hd₁, -⟩ := hF b₁ μ₁ hb₁ ha₁ hm₁ (by linarith)
  obtain ⟨hD₂, hd₂, -⟩ := hF b₂ μ₂ hb₂ ha₂ (by linarith) hg₂
  obtain ⟨b, hb, hby⟩ := M.core.h0Shoot R hP hi0 hRℓ hRA hRρ hN2 hNh hm hb12 ha₁ ha₂ hD₁ hD₂
    hd₁ hd₂ hy₁ hy₂
  obtain ⟨ham, hl, hu⟩ := hBe b hb
  obtain ⟨hD, -, hPb⟩ := hF b _ (hb₁.trans_le hb.1) ham (hm₁.trans hl) (hu.trans hg₂)
  exact ⟨b, hb, hby, hD, hPb⟩

set_option maxHeartbeats 4000000 in
/-- **`thm_multiscale_h0_beta` without pair inputs** (constants of `fb_consts6`, pair bound
`FwPairBd6`). -/
theorem thm_multiscale_h0_beta6 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (pW g₀ K : ℝ), 0 < g₀ ∧ g₀ ≤ M.core.ε / 2 ∧
      pW * cmu ((L : ℝ) ^ 2) M.core.cm ≤ 1 / 12 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, M.Kp * zA L m (Nh - 1) ≤ 1 / 2 →
    ∀ βR : ℝ, 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ / 3 →
      100 * M.core.Cb * (1 / βR) ≤ 1 →
    ∃ b, 0 < b ∧
      b ∈ Icc (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)))
        (bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2))) ∧
      gFinH0 R Nh m b = 1 / βR ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      FwPairBd6 K R Nh m b := by
  obtain ⟨L₀, h⟩ := fb_consts6
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, hg, hgε, hs, hF⟩ := h L hL
  refine ⟨M, pW, g₀, K, hg, hgε, hs, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz βR hβ hmass hyg hcy
  have hN2 : 2 ≤ N := by omega
  have hF' := hF N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm hKz
  obtain ⟨-, -, -, hε, -, -, -, -, -, -, -, hCb, -, -, -, H⟩ := M.core.hC2
  obtain ⟨hfc, -, -, -, -, hnear, hsm, -, hbF, -⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh
  have fc := hfc m hm
  have hy : 0 < 1 / βR := one_div_pos.2 hβ
  have h6 : 6 ≤ M.core.ε * βR := by
    have : 1 / βR ≤ M.core.ε / 6 := by linarith
    rw [div_le_iff₀ hβ] at this
    linarith
  have e₁ : 1 / (2 * βR) = 1 / βR / 2 := by field_simp
  have e₂ : 1 / (βR / 2) = 2 * (1 / βR) := by field_simp
  obtain ⟨U₁, G₁⟩ := (hbF (2 * βR) (by rw [div_le_iff₀ hε]; linarith)).1 m hm
  obtain ⟨U₂, G₂⟩ := (hbF (βR / 2) (by rw [div_le_iff₀ hε]; linarith)).1 m hm
  set b₁ := bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (2 * βR)) with hb₁d
  set b₂ := bFin R M.core.κ M.core.cm M.core.cT Nh M.core.ε m (1 / (βR / 2)) with hb₂d
  have N₁ := hnear m hm b₁ U₁ (2 * βR) G₁
  have N₂ := hnear m hm b₂ U₂ (βR / 2) G₂
  rw [e₁] at N₁ G₁
  rw [e₂] at N₂ G₂
  have ha₁ := fb_adm_muc U₁.choose_spec.1
  have ha₂ := fb_adm_muc U₂.choose_spec.1
  set μ₁ := Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₁
  set μ₂ := Hist.muc (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b₂
  have hb12 : b₁ ≤ b₂ := by
    by_contra hc
    have := hsm m hm U₂ U₁ (not_le.1 hc)
    rw [G₁, G₂] at this
    linarith
  have hb₁ : 0 < b₁ := (ha₁.1 0 (Nat.zero_le _)).1
  have hb₂ : 0 < b₂ := hb₁.trans_le hb12
  set g₁ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁ Nh).1 with hg₁d
  set g₂ := (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂ Nh).1 with hg₂d
  have hg₁0 : 0 ≤ g₁ := (ha₁.1 Nh le_rfl).1.le
  have hg₂0 : 0 ≤ g₂ := (ha₂.1 Nh le_rfl).1.le
  have N₁' : |g₁ - 1 / βR / 2| ≤ 4 * M.core.Cb * (1 / βR / 2) ^ 2 := N₁
  have N₂' : |g₂ - 2 * (1 / βR)| ≤ 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 := N₂
  have hs₁ := fb_s_le hs hg₁0
  have hs₂ := fb_s_le hs hg₂0
  have hcy' : 100 * M.core.Cb * (1 / βR) ≤ 1 := hcy
  -- the upper end: `ǧ^c(b₂) ≤ 3y ≤ g₀`
  have hgu₂ : g₂ ≤ 3 * (1 / βR) := by
    have hcy2 : M.core.Cb * (1 / βR) ^ 2 ≤ 1 / βR / 100 := by
      have := mul_le_mul_of_nonneg_right (show M.core.Cb * (1 / βR) ≤ 1 / 100 by linarith) hy.le
      calc M.core.Cb * (1 / βR) ^ 2 = M.core.Cb * (1 / βR) * (1 / βR) := by ring
        _ ≤ 1 / 100 * (1 / βR) := this
        _ = 1 / βR / 100 := by ring
    have e : 4 * M.core.Cb * (2 * (1 / βR)) ^ 2 = 16 * (M.core.Cb * (1 / βR) ^ 2) := by ring
    have := (abs_le.1 N₂').2
    linarith
  have hg₂g : g₂ ≤ g₀ := by linarith
  -- the lower end: `y/4 ≤ ǧ^c(b₁)`
  have hgl₁ : 1 / βR / 4 ≤ g₁ := by
    have hcy2 : M.core.Cb * (1 / βR) ^ 2 ≤ 1 / βR / 100 := by
      have := mul_le_mul_of_nonneg_right (show M.core.Cb * (1 / βR) ≤ 1 / 100 by linarith) hy.le
      calc M.core.Cb * (1 / βR) ^ 2 = M.core.Cb * (1 / βR) * (1 / βR) := by ring
        _ ≤ 1 / 100 * (1 / βR) := this
        _ = 1 / βR / 100 := by ring
    have e : 4 * M.core.Cb * (1 / βR / 2) ^ 2 = M.core.Cb * (1 / βR) ^ 2 := by ring
    have := (abs_le.1 N₁').1
    linarith
  have hm₁ : m * (L : ℝ) ^ (2 * N) ≤ g₁ := by linarith
  have hg₁g : g₁ ≤ g₀ := by
    obtain ⟨-, h1, h2⟩ := fb_ufix_between fc ha₁ ha₂ (by linarith) ⟨le_rfl, hb12⟩
    linarith
  -- the end distances
  obtain ⟨-, hd₁, -⟩ := hF' b₁ _ hb₁ ha₁ hm₁ hg₁g
  obtain ⟨-, hd₂, -⟩ := hF' b₂ _ hb₂ ha₂ (by
    obtain ⟨-, h1, h2⟩ := fb_ufix_between fc ha₁ ha₂ (by linarith) ⟨le_rfl, hb12⟩
    linarith) hg₂g
  have hy₁ := (fb_margin_lo hCb hy hcy' hg₁0 N₁' hs₁ hd₁).1
  have hy₂ := (fb_margin_hi hCb hy hcy' hg₂0 N₂' hs₂ hd₂).1
  have G₁' : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₁ μ₁) = 1 / βR / 2 := G₁
  have G₂' : gFin (R.withMsq m) Nh (traj (rgDataM R m) ((L : ℝ) ^ 2) b₂ μ₂) = 2 * (1 / βR) := G₂
  obtain ⟨b, hb, hby, hD, hPb⟩ := M.fw_bracket6 hgε R hP hi0 hRℓ hRA hRρ hN2 hNh hF' hm hb₁ hb12
    ha₁ ha₂ hm₁ hg₂g (y := 1 / βR)
    (by rw [G₁']; linarith) (by rw [G₂']; linarith)
  exact ⟨b, hb₁.trans_le hb.1, hb, hby, hD, hPb⟩

/-! ### The final theorem -/

/-- `K_p a_{N_h−1} ≤ 1/2` from `N ≥ 4 + ⌈4K_p⌉` and `K_p m²L^{2N} ≤ 1/4`. -/
theorem fin_Kz_le {L : ℕ} (hL : (2 : ℝ) ≤ L) {Kp m : ℝ} (hKp : 0 ≤ Kp) (hm : 0 ≤ m) {N : ℕ}
    (hN : 4 + ⌈4 * Kp⌉₊ ≤ N) (hmK : Kp * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / 4) :
    Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := by
  set k := N - 2 - 1 with hkd
  have hk1 : 1 ≤ k := by omega
  rw [zA_pos L m hk1, mul_add]
  have hL1 : (1 : ℝ) ≤ L := by linarith
  -- the `L^{-2k}` part
  have hpow : 1 + (k : ℝ) * ((L : ℝ) - 1) ≤ (L : ℝ) ^ k := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ (L : ℝ) - 1) k
    rwa [show 1 + ((L : ℝ) - 1) = L by ring] at this
  have hk4 : 4 * Kp ≤ (k : ℝ) := by
    have h1 : 4 * Kp ≤ (⌈4 * Kp⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈4 * Kp⌉₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show ⌈4 * Kp⌉₊ ≤ k by omega)
    linarith
  have hLk1 : 1 ≤ (L : ℝ) ^ k := one_le_pow₀ hL1
  have hLk : 4 * Kp ≤ ((L : ℝ) ^ k) ^ 2 := by
    have h1 : (k : ℝ) ≤ (L : ℝ) ^ k := by
      have : (k : ℝ) ≤ (k : ℝ) * ((L : ℝ) - 1) := le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    have h2 : (L : ℝ) ^ k ≤ ((L : ℝ) ^ k) ^ 2 := by
      rw [sq]; exact le_mul_of_one_le_left (by linarith) hLk1
    linarith
  have hpos : 0 < ((L : ℝ) ^ k) ^ 2 := by positivity
  have t1 : Kp * (((L : ℝ) ^ k) ^ 2)⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]; linarith
  -- the `m²` part
  have hle : ((L : ℝ) ^ (k + 1)) ^ 2 ≤ (L : ℝ) ^ (2 * N) := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hL1 (by omega)
  have t2 : Kp * (m * ((L : ℝ) ^ (k + 1)) ^ 2) ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hm) hKp) hmK
  linarith

/-- `m² ∈ mRange L N` from `0 < m²` and `m²L^{2N} ≤ 1`. -/
theorem fin_mRange {L : ℕ} (hL : (2 : ℝ) ≤ L) {m : ℝ} {N : ℕ} (hN : 1 ≤ N) (hm : 0 < m)
    (hmL : m * (L : ℝ) ^ (2 * N) ≤ 1) : m ∈ mRange L N := by
  refine ⟨hm, ?_⟩
  have hL0 : (0 : ℝ) < L := by linarith
  have e : (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) = ((L : ℝ) ^ (2 * (N - 1)))⁻¹ := by
    rw [Real.rpow_neg hL0.le, ← Real.rpow_natCast]
    congr 2
    push_cast [Nat.cast_sub hN]; ring
  rw [e]
  have hle : (L : ℝ) ^ (2 * (N - 1)) ≤ (L : ℝ) ^ (2 * N) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hp : 0 < (L : ℝ) ^ (2 * (N - 1)) := by positivity
  have h1 : m ≤ ((L : ℝ) ^ (2 * N))⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]; exact hmL
  exact h1.trans (inv_anti₀ hp hle)

set_option maxHeartbeats 4000000 in
/-- **Theorem `thm:multiscale` (outline) at `h = 0`, at the shooting value `β_ε = 1/b`.**
For `L ≥ L₀` there are the master construction `M`, `g₀ > 0`, `K` and `N₀` such that for
`N ≥ N₀`, every auxiliary mass `m² > 0` and every `β_R > 0` with `4m²L^{2N} ≤ 1/β_R ≤ g₀`, there is
`b > 0` with `Re ǧ_N(b, b − m²) = 1/β_R` (the renormalised coupling at the last scale is `1/β_R`), the
`h = 0` trajectory `(ǧ_j, μ_j)` from `(b, b − m²)` stays in `D_ε` up to `N − 2`, and for every
`x ≠ 0` with coalescence scale `j_x ≤ N − 2` and physical scale `j` of `x`
(`j ≤ j_x ≤ j + 1`): `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ K ϑ_j²/β_j`.
No hypotheses beyond the stated ranges. -/
theorem thm_multiscale_final_h0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ (M : MasterFacts L) (g₀ K : ℝ) (N₀ : ℕ), 0 < g₀ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → N₀ ≤ N →
    ∀ m βR : ℝ, 0 < m → 0 < βR → 4 * (m * (L : ℝ) ^ (2 * N)) ≤ 1 / βR → 1 / βR ≤ g₀ →
    ∃ b, 0 < b ∧ gFinH0 R (N - 2) m b = 1 / βR ∧
      (∀ j ≤ N - 2, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ N - 2 →
        ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
          jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
          |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
            K * thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp := by
  obtain ⟨L₀, h⟩ := thm_multiscale_h0_beta6
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, pW, g₀, K, hg, hgε, -, hF⟩ := h L hL
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := M.core.hL49; omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hCb, -⟩ := M.core.hC2
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  set g₁ := min (g₀ / 3) (min (1 / (100 * (M.core.Cb + 1))) (min (1 / (M.Kp + 1)) 1)) with hg₁d
  refine ⟨M, g₁, K, 4 + ⌈4 * M.Kp⌉₊, ?_, ?_⟩
  · refine lt_min (by linarith) (lt_min (by positivity) (lt_min (by positivity) one_pos))
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN m βR hm hβ hmass hy
  set y := 1 / βR with hyd
  have hy0 : 0 < y := one_div_pos.2 hβ
  have hX0 : 0 ≤ m * (L : ℝ) ^ (2 * N) := mul_nonneg hm.le (by positivity)
  have hyg : y ≤ g₀ / 3 := hy.trans (min_le_left _ _)
  have hyC : y ≤ 1 / (100 * (M.core.Cb + 1)) := hy.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hyK : y ≤ 1 / (M.Kp + 1) :=
    hy.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hy1 : y ≤ 1 :=
    hy.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcy : 100 * M.core.Cb * (1 / βR) ≤ 1 := by
    rw [← hyd]
    have h1 : y * (100 * (M.core.Cb + 1)) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hyC
    nlinarith
  have hmR : m ∈ mRange L N := fin_mRange hL2 (by omega) hm (by linarith)
  have hKz : M.Kp * zA L m (N - 2 - 1) ≤ 1 / 2 := by
    refine fin_Kz_le hL2 hKp hm.le hN ?_
    have h1 : y * (M.Kp + 1) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hyK
    have h2 : M.Kp * (m * (L : ℝ) ^ (2 * N)) ≤ M.Kp * (y / 4) :=
      mul_le_mul_of_nonneg_left (by linarith) hKp
    nlinarith
  obtain ⟨b, hb, -, hby, hD, hPb⟩ := hF N R hP hi0 hRℓ hRA hRρ (by omega) (N - 2) (by omega) m hmR
    hKz βR hβ hmass hyg hcy
  exact ⟨b, hb, hby, hD, hPb⟩

end

end Spin2
