import Spin2.H0.H0MassFlow
import Spin2.H0.MasterH0Multi

/-!
# Route (a1): the window ends at `h = 0` without `H0SusceptExit`, and `thm:multiscale` at `h = 0`

* **`h0WindowX_of`**: `WinHyp` gives the window (`win_interval` at targets `∓c₁`) with the
  bounds at *every* point of `[μ₋, μ₊]` (domain, `|μ_{N_h}| ≤ c₁`, `|ǧ_{N_h} − ǧ^c_{N_h}| ≤ 2p_Wc₁`),
  not only at the `h = 0` point (the body of `h0WindowConcl_of`/`h0_windowed` with the full
  conclusion of `win_interval`);
* **`H0EndsConcl`**, **`MasterCore.h0Ends`**: under the slack condition
  `h0Slack(ǧ) < L⁴c₁` for `0 ≤ ǧ ≤ ǧ^c + 2p_Wc₁` (an explicit inequality between the window size and
  the constants, see `Spin2/H0/H0MassFlow`), `H0SusceptExit` holds on the window (a theorem), and the RG
  one-point value `r ≥ 0` at `μ₊` alone gives `H0OnePtUp` and the `h = 0` trajectory in the window;
* **`thm_multiscale_h0E`**: `thm_multiscale_h0` with `H0WindowConcl` (named inputs `H0OnePtUp`,
  `H0SusceptExit`) replaced by `H0EndsConcl` (input `r ≥ 0` at `μ₊` and the slack condition).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The window statement with bounds at every point**, at a given `p_W` (the conclusion of
`h0WindowX_of`). -/
def H0WinX (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε pW : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μc c₁ θ : ℝ, 0 < b → Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μc →
      0 ≤ c₁ → c₁ ≤ θ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      θ * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) cm) < cmu ((L : ℝ) ^ 2) cm →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 * (1 + 2 * pW * θ) < ε →
    ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μl (-c₁) ∧
      AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μu c₁ ∧ ∀ μ ∈ Icc μl μu,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) ∧
      -c₁ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 ≤ c₁ ∧
      |(traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 - (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤
        pW * (c₁ - -c₁)

/-- **The window with bounds at every point, with the window smallness** (from `WinHyp`):
`p_W = K_h(C_L)·C_Lε` satisfies `p_Wc_μ ≤ 1/12`. -/
theorem h0WindowX_ofS {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε : ℝ}
    (hW : WinHyp L ℓ A ρ κ cg cm cT ε) : ∃ pW : ℝ, pW * cmu ((L : ℝ) ^ 2) cm ≤ 1 / 12 ∧
    H0WinX L ℓ A ρ κ cm cT ε pW := by
  obtain ⟨CL, aB, hsm, he, hcgε, ha0, hs, -, -, hWH⟩ := hW
  have hp0 : ∀ N (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
      0 ≤ Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε) := by
    intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    obtain ⟨H, HZ, -⟩ := hWH N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
    have hΛ2 : 1 < (1 + (L : ℝ) ^ 2) / 2 := by linarith [H.hΛ]
    exact (coef_h hΛ2 H.hκ1 HZ.hA HZ.ha ha0).1
  refine ⟨Kh ((1 + (L : ℝ) ^ 2) / 2) κ CL * (CL * ε), hsm, ?_⟩
  unfold H0WinX
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ θ hb hadm hc0 hc1 hθ hgy
  obtain ⟨H, HZ, -⟩ := hWH N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hp := hp0 N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have hg := (hadm.1 Nh le_rfl).1
  obtain ⟨w1, w2, w3⟩ := win_sym_conds hg hp (cmu_pos H.hΛ H.hcm).le hθ hgy hc0 hc1
  have hgβ : cg * ε ≤ (1 - 1 / 2) * betaL L := by linarith [H.hβ]
  have hC := coneSG_of_Z H HZ ha0 hs
  exact win_interval H he hgβ hC hb le_rfl hadm (by linarith : -c₁ ≤ 0) hc0 hp w1 w2 w3

/-- **The window with bounds at every point** (from `WinHyp`). -/
theorem h0WindowX_of {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε : ℝ}
    (hW : WinHyp L ℓ A ρ κ cg cm cT ε) : ∃ pW : ℝ,
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
    ∀ b μc c₁ θ : ℝ, 0 < b → Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μc →
      0 ≤ c₁ → c₁ ≤ θ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
      θ * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) cm) < cmu ((L : ℝ) ^ 2) cm →
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 * (1 + 2 * pW * θ) < ε →
    ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μl (-c₁) ∧
      AdmW (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μu c₁ ∧ ∀ μ ∈ Icc μl μu,
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ j)) ∧
      -c₁ ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).2.1 ≤ c₁ ∧
      |(traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 - (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤
        pW * (c₁ - -c₁) := by
  obtain ⟨pW, -, hX⟩ := h0WindowX_ofS hW
  exact ⟨pW, hX⟩

/-- **The window ends at `h = 0`** under one master construction: the lower-end input is a theorem,
the upper end needs only the RG one-point value `r ≥ 0`. -/
def H0EndsConcl {L : ℕ} [NeZero L] (D : MasterCore L) (pW KT B : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = D.ℓ → R.A = D.A → R.ρ = D.ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
  ∀ b μc c₁ θ : ℝ, 0 < b → Admissible (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μc →
    0 ≤ c₁ → c₁ ≤ θ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
    θ * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) D.cm) < cmu ((L : ℝ) ^ 2) D.cm →
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 * (1 + 2 * pW * θ) < D.ε →
    (∀ g : ℝ, 0 ≤ g → g ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 + pW * (c₁ - -c₁) →
      h0Slack L D.Cf D.ℓ (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε) KT B D.ρ g
        (m * Fintype.card (Lam 2 L N)) < (L : ℝ) ^ 4 * c₁) →
  ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧ AdmW (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μl (-c₁) ∧
    AdmW (rgDataM R m) ((L : ℝ) ^ 2) D.κ D.cm D.cT Nh D.ε b μu c₁ ∧
    H0SusceptExit L N m b μl μu ∧
    ((∃ r : ℝ, 0 ≤ r ∧ 1 - (b : ℂ) * avg0 L N m b μu (psibar 0 * psi 0) = r) →
      H0OnePtUp L N m b μu ∧ b - m ∈ Ioc μl μu ∧
      (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) D.κ D.cm D.cT D.ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
      |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).2.1| ≤ c₁ ∧
      |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤ pW * (c₁ - -c₁))

/-- **`H0EndsConcl` at the master constants.** -/
theorem MasterCore.h0Ends {L : ℕ} [NeZero L] (D : MasterCore L) :
    ∃ pW KT B : ℝ, H0EndsConcl D pW KT B := by
  obtain ⟨KT, B, -, -, hM⟩ := D.h0Mass
  obtain ⟨pW, hX⟩ := h0WindowX_of D.hWin
  refine ⟨pW, KT, B, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ θ hb hadm hc0 hc1 hθ
    hgy hsl => ?_⟩
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

/-- **`thm:multiscale` at `h = 0` with the window inputs discharged** (`thm_multiscale_h0` with
`H0WindowConcl` replaced by `H0EndsConcl`: `H0SusceptExit` is a theorem, `H0OnePtUp` follows from
`r ≥ 0` at `μ₊`). -/
theorem thm_multiscale_h0E : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ M : MasterFacts L, (∃ pW KT B : ℝ, H0EndsConcl M.core pW KT B) ∧
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
  obtain ⟨L₀, h⟩ := thm_multiscale_h0
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, hM⟩ := h L hL
  exact ⟨M, M.core.h0Ends, hM⟩

end

end Spin2
