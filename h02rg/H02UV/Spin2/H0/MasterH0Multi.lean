import Spin2.Pair.PairFinal
import Spin2.H0.MasterH0Shoot

/-!
# Route (a1), integration of the pair layer: (H_λ), `TwoPtSq` and `thm:multiscale` at `h = 0`

All statements are along trajectories in `D_ε` up to `N_h` (no final condition), under one
`MasterFacts` (`M`), with the vertex `λ̂ = lamHat2 R P (zV b)` (`μ_a/μ_{a,0}` of the pair history at
points `P`, vertex `zV b`):

* **`MasterFacts.hLam_pairD`**: (H_λ) for `λ̂` with `K_p = M.Kp` (`LoopConclD`, `RelConcl2GD`,
  `LamConclD`, `hLam_case2D`);
* **`MasterFacts.twoPtSqD`**: `TwoPtSq` for any `λ̂` from (H_λ), `PairAboveW1` and the smallness
  (the windowed form of `twoPtSq_case2_pair` at the `MasterFacts` constants; glue of
  `twoPtSq_of_gam_flowBD`, `gamRemRel(S)_ofA`, `wk_inputsD`);
* **`MasterFacts.pairTwoPt_h0D`**: (H_λ) and `TwoPtSq` for `λ̂` from the named pair inputs of
  `thm_pairAbove_final` (`pairAbove_final_MFD` + `twoPtSqD`);
* **`MasterFacts.multiscale_h0_pair`**: on the `h = 0` trajectory `(b, b − m²)` in `D_ε`,
  `|P_{1/b}[0 ↔ x] − ϑ_j²| ≤ K ϑ_j²/β_j` at fixed `m²` from the named pair inputs
  (`MasterCore.multiscale_h0`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The `K_P` constant of `TwoPtSq` (as in `twoPtSq_case2_pair`) at the `MasterFacts` constants. -/
def tpKP (Kl KE : ℝ) : ℝ :=
  max (zbKM L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp ((M.core.cGB + M.core.cw) * (1 + 3 * M.Kp))
      (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) Kl *
    (2 + zbKM L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp ((M.core.cGB + M.core.cw) * (1 + 3 * M.Kp))
      (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) Kl) + KE) (L : ℝ)

/-- The `K_r` constant of `TwoPtSq` (as in `twoPtSq_case2_pair`) at the `MasterFacts` constants. -/
def tpKr (Kl KR : ℝ) : ℝ :=
  max (1 + 2 * (1 + zbKM L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp
      ((M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) Kl) *
    zbMb L M.core.cg M.core.Ke M.core.KZ M.core.KG Kl + KR) 1

theorem tpKP_nonneg (Kl KE : ℝ) : 0 ≤ M.tpKP Kl KE :=
  le_trans (Nat.cast_nonneg L) (le_max_right _ _)

/-- **(H_λ) for the pair vertex along windowed trajectories.** -/
theorem hLam_pairD {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) (P : Obs2.ObsPts 2 L N) :
    HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) M.Kp := by
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hB0, -, hloop⟩ := M.loopD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b)
  have h := hLam_case2D M.lamD hP hi0 hRℓ hRA hRρ (by omega) hm hD hB0 M.cRel_nonneg
    (zV_mua_ne hb) (M.relGD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD P (zV b) (zV_mua_ne hb))
    hloop
  exact hLam_mono hb hm.1.le (fun k hk => (hD k hk.le).1) h (le_max_left _ _)

set_option maxHeartbeats 4000000 in
/-- **`TwoPtSq` along windowed trajectories** from (H_λ) for `λ`, `PairAboveW1` and the
smallness (`twoPtSq_case2_pair` at the `MasterFacts` constants, `D_ε` form). -/
theorem twoPtSqD (hL49 : 49 ≤ L) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN2 : 2 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b μ₀ : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) (hh : b ≤ μ₀ + m)
    (lam : ℕ → ℂ) {Kl KE KR : ℝ} (hKl : 0 ≤ Kl) (hl : HLam R Nh m b μ₀ lam Kl)
    (hE : PairAboveW1 R Nh m b μ₀ lam KE KR)
    (hsmall : ∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ Kl M.core.KG 0) 0 *
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) :
    TwoPtSq R Nh m b μ₀ lam (M.tpKP Kl KE) (M.tpKr Kl KR) := by
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hKp : 0 ≤ M.Kp := M.Kp_nonneg
  have hB := M.gamBulkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := M.flow
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
    ⟨(hD k hk.le).1.le, ((hD k hk.le).2.1).trans M.eps_le⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  have hpairP := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD
  obtain ⟨hW, hWS, -, -⟩ := wk_inputsD M.wkD N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD
  have hpair : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) M.Kp :=
    fun x _ => hpairP (ptsX x)
  have hpairS : ∀ x : Lam 2 L N, x ≠ 0 →
      HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) M.Kp :=
    fun x _ => hpairP (ptsS x)
  have hrem := gamRemRel_ofA R hb hKp M.cGB_nonneg M.cw_nonneg hval hg ha hpair hB hW
  have hremS := gamRemRelS_ofA R hb hKp M.cGB_nonneg M.cw_nonneg hval hg ha hpairS hB hWS
  have hcγ : 0 ≤ (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp) :=
    mul_nonneg (add_nonneg M.cGB_nonneg M.cw_nonneg) (by linarith)
  exact twoPtSq_of_gam_flowBD M.flow M.eps_le (by norm_num; omega) M.spinD M.magD N R hP hi0 hRℓ
    hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh lam Kl M.Kp _ KE KR hKl hKp hcγ hl hpair hpairS hrem hremS
    hE hsmall

set_option maxHeartbeats 4000000 in
/-- **(H_λ) and `TwoPtSq` for the pair vertex along windowed trajectories from the named pair inputs
of `thm_pairAbove_final`** (one `MasterFacts`; `K_t`, `r₀`, `C₁w` as in `pairAbove_final_MFD`). -/
theorem pairTwoPt_h0D (hL49 : 49 ≤ L) (hLpl : pauliL0 2 ≤ L) :
    ∃ Kt r₀ C₁w : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) → b ≤ μ₀ + m →
    ∀ (P : Obs2.ObsPts 2 L N) (cr : ℝ), 0 ≤ cr →
      GamLastRem R Nh m b μ₀ cr → GamLastRemS R Nh m b μ₀ cr →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
    ∀ (cej ca cσ cd e1 e2 Mb mbar : ℝ), 0 ≤ cej → 0 ≤ cσ →
      crErr2 cej M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cσ → 0 ≤ e1 → 0 ≤ e2 →
      0 < mbar → cσ ≤ mbar → 8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
      (∀ k ≤ Nh, ‖Mmag R m b μ₀ (lamHat2 R P (zV b) m b μ₀) k‖ ≤ Mb) →
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
            cej * ‖Mmag R m b μ₀ (lamHat2 R P (zV b) m b μ₀) (Obs.coal L (0 : Lam 2 L N) x)‖ *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
          PairESizes R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) (oRed R m b μ₀ dxStd) cσ x (PairVB R m b μ₀ (lamHat2 R P (zV b) m b μ₀) x mbar)
            κQ se so sw ηw μ cn δ e Pd F Λ Wp τ) →
      PairDefSizesR3P R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) (oRed R m b μ₀ dxStd) cd →
      (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) + 9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
          cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ 1 / 2 →
      Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 →
      8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ M.core.ρ →
      8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 / 2 →
      PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ 1 →
      4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1) ≤ r₀ ^ 2 →
      cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ Nh).1 ≤ r₀ →
      PairZeroRemAB R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) (oRed R m b μ₀ dxStd) e1 e2 →
      HLam R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) M.Kp ∧
      TwoPtSq R Nh m b μ₀ (lamHat2 R P (zV b) m b μ₀) (M.tpKP M.Kp (cσ * (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
          (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) + cd + (4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * (2 * (1 + max (spinMK L M.core.cg M.core.Ke M.core.KZ (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14))))) (M.tpKr M.Kp ((4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * Mb)) := by
  obtain ⟨Kt, r₀, C₁w, hKt, hr₀, hr₀1, hC₁w, H⟩ := pairAbove_final_MFD M hL49 hLpl
  refine ⟨Kt, r₀, C₁w, hKt, hr₀, hr₀1, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh P cr hcr hr hrS hsmall
    cej ca cσ cd e1 e2 Mb mbar hcej hcσ hcrE he1 he2 hmbar hcσm hseed hMb hE hDS hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hAB
  have hl := M.hLam_pairD R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD P
  refine ⟨hl, M.twoPtSqD hL49 R hP hi0 hRℓ hRA hRρ hN2 hNh hm hD hh _ M.Kp_nonneg hl ?_ hsmall⟩
  exact H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hD hh _ M.Kp cr M.Kp_nonneg hcr hl hr hrS
    hsmall cej ca cσ cd e1 e2 Mb mbar hcej hcσ hcrE he1 he2 hmbar hcσm hseed hMb hE hDS hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hAB

set_option maxHeartbeats 4000000 in
/-- **`thm:multiscale` at `h = 0` at fixed `m²` from the named pair inputs** (route (a1)): on the
`h = 0` trajectory `(b, b − m²)` in `D_ε` up to `N_h` (e.g. from `H0WindowConcl`), with
`λ̂ = lamHat2 R P (zV b)`, `K_λ = M.Kp`, `K_P = M.tpKP M.Kp K_E`. -/
theorem multiscale_h0_pair (hL49 : 49 ≤ L) (hLpl : pauliL0 2 ≤ L) :
    ∃ Kt r₀ C₁w : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b : ℝ,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) →
    ∀ (P : Obs2.ObsPts 2 L N) (cr : ℝ), 0 ≤ cr →
      GamLastRem R Nh m b (b - m) cr → GamLastRemS R Nh m b (b - m) cr →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2) →
    ∀ (cej ca cσ cd e1 e2 Mb mbar : ℝ), 0 ≤ cej → 0 ≤ cσ →
      crErr2 cej M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cσ → 0 ≤ e1 → 0 ≤ e2 →
      0 < mbar → cσ ≤ mbar → 8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
      (∀ k ≤ Nh, ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) k‖ ≤ Mb) →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
        ∃ (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
          (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
          (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
            0 ≤ Λ k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
          (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
              (2 * (Q1 2 * (cQab * κQ k) *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))⁻¹ ^ 2) +
                sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k +
                2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))⁻¹ ^ 2 +
                smE R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ k) ≤
            cej * ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (Obs.coal L (0 : Lam 2 L N) x)‖ *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
          PairESizes R Nh m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (oRed R m b (b - m) dxStd) cσ x (PairVB R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) x mbar)
            κQ se so sw ηw μ cn δ e Pd F Λ Wp τ) →
      PairDefSizesR3P R Nh m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (oRed R m b (b - m) dxStd) cd →
      (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) + 9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
          cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2 →
      Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 →
      8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ →
      8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 / 2 →
      PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 →
      4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2 →
      cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀ →
      PairZeroRemAB R Nh m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (oRed R m b (b - m) dxStd) e1 e2 →
    ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
        multK L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp (M.tpKP M.Kp (cσ * (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
          (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) + cd + (4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * (2 * (1 + max (spinMK L M.core.cg M.core.Ke M.core.KZ (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14))))) *
          thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp := by
  obtain ⟨Kt, r₀, C₁w, hKt, hr₀, hr₀1, hC₁w, H⟩ := M.pairTwoPt_h0D hL49 hLpl
  refine ⟨Kt, r₀, C₁w, hKt, hr₀, hr₀1, hC₁w, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b hD P cr hcr hr hrS hsmall
    cej ca cσ cd e1 e2 Mb mbar hcej hcσ hcrE he1 he2 hmbar hcσm hseed hMb hE hDS hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hAB x hx hj
  have hb : 0 < b := by
    have := (hD 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  obtain ⟨hl, hsq⟩ := H N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b (b - m) hD (by linarith) P cr hcr
    hr hrS hsmall cej ca cσ cd e1 e2 Mb mbar hcej hcσ hcrE he1 he2 hmbar hcσm hseed hMb hE hDS hsmA hmT hmA hs1 hs2 hs3 hs4 hs5 hAB
  exact M.core.multiscale_h0 R hP hi0 hRℓ hRA hRρ (by omega) hm hb hD _ M.Kp_nonneg
    (M.tpKP_nonneg _ _) hl hsq x hx hj

end MasterFacts

/-- **`thm:multiscale` at `h = 0` (route (a1)) under one master construction**: for all large `L`
there is `M : MasterFacts L` with the `h = 0` window statement (`H0WindowConcl`, named inputs
`H0OnePtUp`, `H0SusceptExit`) and the conclusion of `MasterFacts.multiscale_h0_pair` (named pair
inputs of `thm_pairAbove_final`). -/
theorem thm_multiscale_h0 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ M : MasterFacts L, (∃ pW : ℝ, H0WindowConcl L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm
        M.core.cT M.core.ε pW) ∧
    ∃ Kt r₀ C₁w : ℝ, 0 ≤ Kt ∧ 0 < r₀ ∧ r₀ ≤ 1 ∧ 0 ≤ C₁w ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b : ℝ,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) →
    ∀ (P : Obs2.ObsPts 2 L N) (cr : ℝ), 0 ≤ cr →
      GamLastRem R Nh m b (b - m) cr → GamLastRemS R Nh m b (b - m) cr →
      (∀ j ≤ Nh, max (spinMK L M.core.cg M.core.Ke M.core.KZ M.Kp M.core.KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j).1 ≤ 1 / 2) →
    ∀ (cej ca cσ cd e1 e2 Mb mbar : ℝ), 0 ≤ cej → 0 ≤ cσ →
      crErr2 cej M.core.cRel (4 / betaL L) M.core.ce (max M.core.B' 0) ca ≤ cσ → 0 ≤ e1 → 0 ≤ e2 →
      0 < mbar → cσ ≤ mbar → 8 * (pairUnitC M * (2 * M.core.ιW * M.core.A) ^ ((L + 18) ^ 2)) ≤ vck C₁w * ((4 * C₁w + 1) * mbar) →
      (∀ k ≤ Nh, ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) k‖ ≤ Mb) →
      (∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
        Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
        ∃ (κQ se so sw ηw μ cn δ e Pd F Λ Wp : ℕ → ℝ) (τ : ℕ → ℕ → ℝ)
          (w : List (Dir 2)), Obs2.pathEnd (0 : Lam 2 L N) w = x ∧
          (∀ k, 0 ≤ κQ k ∧ 0 ≤ μ k ∧ 0 ≤ cn k ∧ 0 ≤ δ k ∧ 0 ≤ e k ∧ 0 ≤ Pd k ∧ 0 ≤ F k ∧
            0 ≤ Λ k ∧ 0 ≤ Wp k) ∧ (∀ i k, 0 ≤ τ i k) ∧
          (∀ k, 0 ≤ se k ∧ 0 ≤ so k ∧ 0 ≤ sw k ∧ 0 ≤ ηw k) ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1),
              (2 * (Q1 2 * (cQab * κQ k) *
                (PtCorr2.histS (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))⁻¹ ^ 2) +
                sw k + μ k * (w.length * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)) / (L : ℝ) ^ (k + 1))) ^ 2 * cn k +
                2 * δ k * e k * (PtCorr2.histS (R.withMsq m) k
                  (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m)))⁻¹ ^ 2 +
                smE R m b (b - m) (Obs.coal L (0 : Lam 2 L N) x) Pd F Λ Wp τ k) ≤
            cej * ‖Mmag R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (Obs.coal L (0 : Lam 2 L N) x)‖ *
              (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) (Obs.coal L (0 : Lam 2 L N) x)).1 ∧
          ∑ k ∈ Finset.Ico (Obs.coal L (0 : Lam 2 L N) x) (Nh + 1), (64 / 49 : ℝ) ^ 2 * ηw k ≤ ca ∧
          PairESizes R Nh m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (oRed R m b (b - m) dxStd) cσ x (PairVB R m b (b - m) (lamHat2 R P (zV b) m b (b - m)) x mbar)
            κQ se so sw ηw μ cn δ e Pd F Λ Wp τ) →
      PairDefSizesR3P R Nh m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (oRed R m b (b - m) dxStd) cd →
      (M.core.Cf * (M.core.ℓ ^ 2 / 8 + M.core.ℓ ^ 4 / 128) + 9 / 4 * ((PtCorr2.cBn : ℝ) * Q1 2 * M.core.cWL) +
          cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ 1 / 2 →
      Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 →
      8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 →
      2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ M.core.ρ →
      8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 / 2 →
      PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ 1 →
      4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1) ≤ r₀ ^ 2 →
      cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ r₀ →
      PairZeroRemAB R Nh m b (b - m) (lamHat2 R P (zV b) m b (b - m)) (oRed R m b (b - m) dxStd) e1 e2 →
    ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∃ jp : ℕ, (jp : ℤ) = jPhys L N (eucl x / (L : ℝ) ^ N) ∧
      jp ≤ Obs.coal L (0 : Lam 2 L N) x ∧ Obs.coal L (0 : Lam 2 L N) x ≤ jp + 1 ∧
      |Pconn L N (1 / b) x - thetaSq R m b (b - m) jp| ≤
        multK L M.core.cg M.core.Ke M.core.KZ M.core.KG M.Kp (M.tpKP M.Kp (cσ * (2 * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14 * max (1 + 3 * M.Kp) (2 * (1 + 3 * M.Kp))) *
          (6 / betaL L * (1 + max (spinTrajK (betaL L) M.core.cg 0 (eRange (betaL L) M.core.Ke 1) 0) 0) + 2)) + cd + (4 * e2 + 2 * (cσ + e1) + 2 * (cσ + e1)) * (2 * (1 + max (spinMK L M.core.cg M.core.Ke M.core.KZ (M.Kp + (M.core.cGB + M.core.cw) * (1 + 3 * M.Kp)) M.core.KG 0) 0 +
            2 * (1 + cr) * (2 * (1 + 3 * M.Kp)) * (M.core.ℓ ^ 2 * Real.exp M.core.KZ / 14))))) *
          thetaSq R m b (b - m) jp / betaJ R m b (b - m) jp := by
  obtain ⟨L₀, hL₀⟩ := thm_master_all
  refine ⟨max (max L₀ 49) ⌈pauliL0 2⌉₊, fun L _ hLL => ?_⟩
  have hL := le_trans (le_max_left _ _) hLL
  have hLpl : pauliL0 2 ≤ L :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hLL)
  obtain ⟨M⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  exact ⟨M, h0WindowConcl_of M.core.hWin, M.multiscale_h0_pair (le_trans (le_max_right _ _) hL) hLpl⟩

end

end Spin2
