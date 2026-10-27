import Spin2.Pair.PairJoint6Def
import Spin2.Pair.PairUnit
import Spin2.Pair.PairEStep4
import Spin2.H0.MasterH0Pair

/-!
# The pair layer with the `V`-step and the seed unit discharged

**`thm_pairAbove_final`**: the statement of `thm_pairAbove_red_jointP` (`Spin2/PairJoint6`) with
`PairJointSizesP c_e c_a c_σ` replaced by the `E`-step data only: per `x`, the size sequences, a
path `w` from `0` to `x`, the two sums (`≤ c_e‖M_{j_x}‖ǧ_{j_x}`, `≤ c_a`) and
**`PairESizes … c_σ x (PairVB … m̄)`**. Discharged inside: the `V`-step (`pairVStep_MF`, constant
`C₁w`), `PairUnitSeed` (`pairUnitSeed_MF`, `c_u = pairUnitC`), the assembly `pairJointSizesP_MF`.
New constant conditions: `0 < m̄`, `c_σ ≤ m̄`, `8c_u(2ι_WA)^{(L+18)²} ≤ vck(C₁w)(4C₁w+1)m̄`
(the closure of these with `crErr2 c_e … ≤ c_σ`: `Spin2/Pair/PairLoop`). The body is that of
`thm_pairAbove_red_jointP` (copied; one `MasterFacts`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

set_option maxHeartbeats 4000000 in
/-- **The body of `thm_pairAbove_final` under one `MasterFacts`, along every trajectory in `D_ε`**
(route (a1); no final condition `μ_{N_h} = 0`). The constants are those of `M`; `K_t`, `r₀`, `C₁w`
as in `thm_pairAbove_final`. The proof uses only the domain condition (the `D_ε` forms
`M.loopD`, `M.relGD`, `M.topD`, … of `Spin2/Master/MasterAllFactsD`). -/
theorem pairAbove_final_MFD {L : ℕ} [NeZero L] (M : MasterFacts L) (hL49 : 49 ≤ L)
    (hLpl : pauliL0 2 ≤ L) :
    ∃ Kt r₀ C₁w : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl cr : ℝ), 0 ≤ Kl → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      GamLastRem R Nh m b μ₀ cr → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ (cej ca cσ cd e1 e2 Mb mbar : ℝ), 0 ≤ cej → 0 ≤ cσ →
      crErr2 cej M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cσ → 0 ≤ e1 → 0 ≤ e2 →
      0 < mbar → cσ ≤ mbar → 8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
        ∃ (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
          (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
          (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
            0 ≤ Λ k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
          (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
              (2 * (Q1 2 * (cQab * κQ k) *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
                sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k +
                2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
                smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ k) ≤
            cej * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
          PairESizes R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cσ x (PairVB R m b μ₀ lam x mbar)
            κQ se so sw ηw μ cn δ e Pd F Λ Wp τ) →
      PairDefSizesR3P R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) + 9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
          cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 / 2 →
      Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 →
      8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ M.core.ρ →
      8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2 →
      PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 →
      4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2 →
      cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀ →
      PairZeroRemAB R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) e1 e2 →
      PairAboveW1 R Nh m b μ₀ lam
        (cσ * (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
          (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) + cd + (4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * (2 * (1 + max (spinMK L M.core.cg M.core.Ke M.core.KZ (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14)))) ((4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * Mb) := by
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
  obtain ⟨C₁w, hC₁w, hVS⟩ := pairVStep_MFD M
  refine ⟨Kt, r₀, C₁w, hKt, hr₀, hr₀1, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam Kl cr hKl hcr hl hr hrS
    hsmall cej ca cσ cd e1 e2 Mb mbar hcej hcσ hcrE he1 he2 hmbar hcσm hseed hMb hE hDS hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hAB
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
  have hGT := gamTopBd_both_flowD hF hε1 hKZ hL8 hSp hMC hGM hLV N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm
    b μ₀ hD lam Kl Kp ce cw _ _ cr hKl hKp hce hcw hcγ hKβ hcr hl (fun x _ => hpairP _)
    (fun x _ => hpairP _) (gamBulkRel_of_A R hB) hWT hRS hβ hr hβS hrS hsmall
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
  have hU := pairUnitSeed_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam Kl hKl hl hsmall
  have hJS : PairJointSizesP R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cej ca cσ := by
    refine pairJointSizesP_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam cej ca cσ
      (fun x hx h1 hj => ?_)
    obtain ⟨κQ, se, so, sw, ηw, μ, cn, δ, e, Pd, F, Λ, Wp, τ, w, hw, h0, hτ0, h0', hsum, hηsum,
      hPE⟩ := hE x hx h1 hj
    obtain ⟨hV0, hVs⟩ := hVS N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam (pairUnitC M) cσ
      mbar hU hmbar hcσm hseed x hx h1 hj
    exact ⟨PairVB R m b μ₀ lam x mbar, κQ, se, so, sw, ηw, μ, cn, δ, e, Pd, F, Λ, Wp, τ, w, hw, h0,
      hτ0, h0', hsum, hηsum, hV0, hVs, hPE⟩
  have hRR' := (pairRRelR_of_jointSizesP_MFD M N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD lam
    hcej hcrE hJS).1
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
  have hK2 : 0 ≤ 4 * e2 + 2 * (cσ + e1) := by
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
  have hZ := pairZeroRelW_of R m b μ₀ lam (oRed R m b μ₀ dxStd) hcr' he1 he2
    (fun k hk => (hg' k hk).1)
    (fun x hx h1 hj => betaN_ne_of R hNh hb x (hrel _) (hn _) (htop x hx h1 hj).1) hRR' hZR
  exact pairAboveW1_of_redW R hNh m hρ1 hspl' hm.1 hm.2 hval hvalL hL8 hb hh lam
    (oRed R m b μ₀ dxStd) hK2 hK3 hg' hMb hRd hC hZ hGT.1


/-- **`thm_pairAbove_red_jointP` with the `V`-step and `PairUnitSeed` discharged** (see the module
docstring). -/
theorem thm_pairAbove_final : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG ce cw Kp cδ Kt cWL cKL r₀ ct B' C₁w cu ιW : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧ 0 ≤ KZ ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      0 ≤ ce ∧ 0 ≤ cw ∧ 0 ≤ Kp ∧ 0 ≤ cδ ∧ 0 ≤ Kt ∧ 0 ≤ cWL ∧ 0 ≤ cKL ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧
      0 ≤ C₁w ∧ 0 ≤ cu ∧ 1 ≤ ιW ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl cr : ℝ), 0 ≤ Kl → 0 ≤ cr →
      HLam R Nh m b μ₀ lam Kl →
      GamLastRem R Nh m b μ₀ cr → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ (cej ca cσ cd e1 e2 Mb mbar : ℝ), 0 ≤ cej → 0 ≤ cσ →
      crErr2 cej cδ (4 / betaL L) ct (max B' 0) ca ≤ cσ → 0 ≤ e1 → 0 ≤ e2 →
      0 < mbar → cσ ≤ mbar → 8 * (cu * (2 * ιW * A) ^ ((L + 18) ^ 2)) ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ lam k‖ ≤ Mb) →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
        ∃ (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
          (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
          (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
            0 ≤ Λ k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
          (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
              (2 * (Q1 2 * (cQab * κQ k) *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2) +
                sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k +
                2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀))⁻¹ ^ 2 +
                smE R m b μ₀ (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ k) ≤
            cej * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
          PairESizes R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cσ x (PairVB R m b μ₀ lam x mbar)
            κQ se so sw ηw μ cn δ e Pd F Λ Wp τ) →
      PairDefSizesR3P R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) cd →
      (Cf * (ℓ ^ 2 / 8 + ℓ ^ 4 / 128) + 9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * cWL) +
          cKAL L ℓ r₀ Cf cWL cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 / 2 →
      Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 →
      8 * cKAL L ℓ r₀ Cf cWL cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ ρ →
      8 * cM * ℓ ^ 2 * (Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2 →
      PtCorr2.cRho L * (cTauL ℓ Cf cWL cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 →
      4 * (cTauL ℓ Cf cWL cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2 →
      cTauL ℓ Cf cWL cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀ →
      PairZeroRemAB R Nh m b μ₀ lam (oRed R m b μ₀ dxStd) e1 e2 →
      PairAboveW1 R Nh m b μ₀ lam
        (cσ * (2 * (ℓ ^ 2 * Real.exp KZ / 14 * max (1 + 3 * Kp) (2 * (1 + 3 * Kp))) *
          (6 / betaL L * (1 + max (spinTrajK (betaL L) cg 0 (eRange (betaL L) Ke 1) 0) 0) + 2)) + cd + (4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * (2 * (1 + max (spinMK L cg Ke KZ (Kp + (ce + cw) * (1 + 3 * Kp)) KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * Kp)) * (ℓ ^ 2 * Real.exp KZ / 14)))) ((4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * Mb) := by
  obtain ⟨L₀, hL₀⟩ := thm_master_all
  refine ⟨max (max L₀ 49) ⌈pauliL0 2⌉₊, fun L _ hLL => ?_⟩
  have hL := le_trans (le_max_left _ _) hLL
  have hLpl : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hLL)
  obtain ⟨M⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  obtain ⟨Kt, r₀, C₁w, hKt, hr₀, hr₀1, hC₁w, H⟩ :=
    pairAbove_final_MFD M (le_trans (le_max_right _ _) hL) hLpl
  refine ⟨M.core.ℓ, M.core.A, M.core.ρ, M.core.κ, M.core.cg, M.core.cm, M.core.cT, M.core.ε,
    M.core.Ke, M.core.Cf, M.core.Cb, M.core.KZ, M.core.KG, M.core.cGB, M.core.cw, M.Kp,
    M.core.cRel, Kt, M.core.cWL, M.core.cKL, r₀, M.core.ce, M.core.B', C₁w, pairUnitC M,
    M.core.ιW, M.flow, M.eps_le, M.KZ_nonneg, M.spin, M.mag, M.cGB_nonneg, M.cw_nonneg,
    M.Kp_nonneg, M.cRel_nonneg, hKt, M.cWL_nonneg, M.cKL_nonneg, hr₀, hr₀1, hC₁w,
    pairUnitC_nonneg M, M.ιW_ge, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
  exact H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm.1

end

end Spin2
