import Spin2.H0.H0SlackBd
import Spin2.H0.MasterH0Ends

/-!
# Route (a1): the slack inequality of the window ends discharged; `thm:multiscale` at `h = 0`

* **`MasterCore.h0EndsC`**: `H0EndsConcl` at the canonical constants `K_T = h0KT L ρ`,
  `B = h0B L ρ` (those of the `ε`-requirement `h0EReq`, field `hH0E` of `MasterCore`);
* **`H0EndsConclF`**, **`MasterCore.h0EndsF`**: `H0EndsConcl` at `θ = (3/4)c_μ`, `c₁ = θǧ^c` with
  the slack condition (ii) discharged: it follows from `m²|Λ| ≤ ǧ^c` (new hypothesis on the mass,
  compatible with the mass window `m² ≤ c₀L^{-2N}` since `ǧ^c ≍ 1/N`), the master `c_m` (field
  `hcmF`), `L ≥ 49`, `h0EReq` and the window smallness `θ(1 + 2p_Wc_μ) < c_μ`
  (`h0Slack_win`, `cNuLast_lt_win`);
* **`thm_multiscale_h0F`**: `thm_multiscale_h0E` with `H0EndsConcl` replaced by `H0EndsConclF`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

set_option maxHeartbeats 4000000 in
/-- **`H0EndsConcl` at the canonical `K_T`, `B`, for any `p_W` with the window statement.** -/
theorem MasterCore.h0EndsCat {L : ℕ} [NeZero L] (D : MasterCore L) {pW : ℝ}
    (hX : H0WinX L D.ℓ D.A D.ρ D.κ D.cm D.cT D.ε pW) :
    H0EndsConcl D pW (h0KT L D.ρ) (h0B L D.ρ) := by
  have hM := D.h0MassC
  refine fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ θ hb hadm hc0 hc1 hθ
    hgy hsl => ?_
  obtain ⟨μl, μu, h1, h2, h3, h4, h5⟩ :=
    hX N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ θ hb hadm hc0 hc1 hθ hgy
  have hlu : μl ≤ μu := h1.trans h2
  have hg : ∀ μ ∈ Icc μl μu, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ≤
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 + pW * (c₁ - -c₁) := fun μ hμ => by
    obtain ⟨k1, -, -, k4⟩ := h5 μ hμ
    exact ⟨((k1 Nh le_rfl).1).le, by linarith [(abs_le.1 k4).2]⟩
  -- lower end
  obtain ⟨gl0, gl1⟩ := hg μl ⟨le_rfl, hlu⟩
  have hlo := (hM N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μl hb h3.1).2 (by
    rw [h3.2]; have := hsl _ gl0 gl1; linarith)
  have hex : H0SusceptExit L N m b μl μu := h0SusceptExit_of_re ⟨le_rfl, hlu⟩ hlo.2
  -- upper end
  obtain ⟨gu0, gu1⟩ := hg μu ⟨hlu, le_rfl⟩
  have hup := (hM N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μu hb h4.1).1 (by
    rw [h4.2]; exact hsl _ gu0 gu1)
  refine ⟨μl, μu, h1, h2, h3, h4, hex, fun hr => ?_⟩
  obtain ⟨hZ, -, -⟩ := D.onePtWinU R hP hi0 hRℓ hRA hRρ hN hNh hm hb h4.1 hup.1
  have hOP : H0OnePtUp L N m b μu := h0OnePtUp_of_re hb hm.1 hZ hr hup.2
  have hmem := h0_mem_window' hb hm.1 hOP hex
  obtain ⟨k1, k2, k3, k4⟩ := h5 (b - m) ⟨hmem.1.le, hmem.2⟩
  exact ⟨hOP, hmem, k1, abs_le.2 ⟨k2, k3⟩, k4⟩

/-- **`H0EndsConcl` at the canonical `K_T`, `B`.** -/
theorem MasterCore.h0EndsC {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ pW : ℝ, H0EndsConcl D pW (h0KT L D.ρ) (h0B L D.ρ) := by
  obtain ⟨pW, hX⟩ := h0WindowX_of D.hWin
  exact ⟨pW, D.h0EndsCat hX⟩

/-- **The window ends at `h = 0` with the slack condition discharged** (`θ = (3/4)c_μ`,
`c₁ = θǧ^c`; inputs: `m²|Λ| ≤ ǧ^c` and the window smallness). -/
def H0EndsConclF {L : ℕ} [NeZero L] (D : MasterCore L) (pW : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
  ∀ b μc : ℝ, 0 < b → Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μc →
    m * Fintype.card (Lam 2 L N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
    3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) D.cm) < cmu ((L : ℝ) ^ 2) D.cm →
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 * (1 + 2 * pW * (3 / 4 * cmu ((L : ℝ) ^ 2) D.cm)) < D.ε →
  ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μl (-(3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1)) ∧
    AdmW (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μu (3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) ∧
    H0SusceptExit L N m b μl μu ∧
    ((∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N m b μu (psibar 0 * psi 0) = r) →
      H0OnePtUp L N m b μu ∧ b - m ∈ Ioc μl μu ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).2.1| ≤ (3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) ∧
      |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤ pW * ((3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) - -(3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1)))


set_option maxHeartbeats 4000000 in
/-- **`H0EndsConclF` from `H0EndsConcl` at the canonical `K_T`, `B`** (any `p_W`). -/
theorem MasterCore.h0EndsFat {L : ℕ} [NeZero L] (D : MasterCore L) {pW : ℝ}
    (hE : H0EndsConcl D pW (h0KT L D.ρ) (h0B L D.ρ)) : H0EndsConclF D pW := by
  refine fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc hb hadm hmV hθ hgy => ?_
  obtain ⟨-, -, hρ, hε, -, -, -, hcm, -, -, hCf, -, -, -, hspl, -⟩ := D.hC2
  obtain ⟨hε45, hX, hu⟩ := D.hH0E
  have hL : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := D.hL49; omega)
  have hcμ : 0 < cmu ((L : ℝ) ^ 2) D.cm := by
    unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have hg := hadm.1 Nh le_rfl
  have hm0 : 0 ≤ m * (Fintype.card (Lam 2 L N) : ℝ) := mul_nonneg hm.1.le (by positivity)
  have hℓR : (R.withMsq m).ℓ = D.ℓ := hRℓ
  have hcNL : 0 ≤ cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε := by
    unfold cNuLast cNuLs cZ
    have h1 := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 16 / 7 * (L : ℝ) ^ 2 *
      (8 * (R.withMsq m).ℓ ^ 2 / 49 + 16 * (R.withMsq m).ℓ ^ 2 / 147)) hcμ.le) hε.le
    have h2 : 0 ≤ 3 * (L : ℝ) ^ 2 * (16 * (R.withMsq m).ℓ ^ 2 / 49) + 8 * (R.withMsq m).ℓ ^ 2 / 49 +
      (L : ℝ) ^ 2 * (16 * (R.withMsq m).ℓ ^ 2 / 147) := by positivity
    have h3 : 0 ≤ 16 / 7 * (L : ℝ) ^ 2 * (16 * (R.withMsq m).ℓ ^ 2 / 49) +
      3 * (R.withMsq m).ℓ ^ 2 / 7 := by positivity
    have h4 := mul_nonneg (by positivity : (0 : ℝ) ≤ (L : ℝ) ^ 2) (add_nonneg h1 h2)
    linarith
  have hK := cNuLast_lt_win (R.withMsq m) (ε := D.ε) D.hL49 (by rw [hℓR]; exact D.hcmF) hu
  have hKT := h0KT_spec (L := L) D.hZT
  have hB := h0B_spec hspl
  exact hE N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc _ (3 / 4 * cmu ((L : ℝ) ^ 2) D.cm) hb hadm
    (by have := hg.1; positivity) le_rfl hθ hgy
    (h0Slack_win hCf hcNL hKT.1 hB.1 hρ.le hcμ hg.1 hg.2.1 hm0 hmV hθ hε45 hX hK)

/-- **`H0EndsConclF` at the master constants.** -/
theorem MasterCore.h0EndsF {L : ℕ} [NeZero L] (D : MasterCore L) : ∃ pW : ℝ, H0EndsConclF D pW := by
  obtain ⟨pW, hE⟩ := D.h0EndsC
  exact ⟨pW, D.h0EndsFat hE⟩

/-- **The window condition from the window smallness.** -/
theorem h0_win_cond {c pW : ℝ} (hc : 0 < c) (hs : pW * c ≤ 1 / 12) :
    3 / 4 * c * (1 + 2 * pW * c) < c := by
  have h1 : 3 / 4 * c * (1 + 2 * pW * c) = 3 / 4 * c + 3 / 2 * (pW * c) * c := by ring
  have h2 : 3 / 2 * (pW * c) * c ≤ 3 / 2 * (1 / 12) * c :=
    mul_le_mul_of_nonneg_right (by linarith) hc.le
  linarith

/-- **`thm:multiscale` at `h = 0` with the window-end slack discharged** (`thm_multiscale_h0E` with
`H0EndsConcl` replaced by `H0EndsConclF`: inputs `r ≥ 0` at `μ₊`, `m²|Λ| ≤ ǧ^c` and the window
smallness). -/
theorem thm_multiscale_h0F : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ M : MasterFacts L, (∃ pW : ℝ, H0EndsConclF M.core pW) ∧
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
  obtain ⟨L₀, h⟩ := thm_multiscale_h0E
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, hM⟩ := h L hL
  exact ⟨M, M.core.h0EndsF, hM⟩

end

end Spin2
