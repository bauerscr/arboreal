import Spin2.H0.H0OnePtM

/-!
# Route (a1), input (i) discharged at the window ends; `thm:multiscale` at `h = 0` without (i)

* **`H0EndsConclG`**, **`MasterFacts.h0EndsG`**: `H0EndsConclF` with the premise (i)
  (`∃ r ≥ 0, 1 − b⟨ψ̄_0ψ_0⟩ = r` at `μ₊`) removed. In its place: `N ≥ 3` and the smallness
  `H0OnePtSmall … ((5/4)ǧ^c)` (no named input). Proof: `MasterFacts.onePt_re_win` at
  `μ₊` with `G = (5/4)ǧ^c` (margin `L⁴c₁ − S ≥ (5/4)L²ǧ^c ≥ 44G`, `cNuLast_win_margin`,
  `h0Slack_le_win`), then `onept_real_of_re` and `h0OnePtUp_of_re`;
* **`thm_multiscale_h0G`**: `thm_multiscale_h0F` with `H0EndsConclF` replaced by `H0EndsConclG`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The window ends at `h = 0` with input (i) discharged** (`H0EndsConclF` with the premise
`∃ r ≥ 0, 1 − b⟨ψ̄_0ψ_0⟩ = r` at `μ₊` replaced by `N ≥ 3` and the smallness
`H0OnePtSmall … ((5/4)ǧ^c)`). -/
def H0EndsConclG {L : ℕ} [NeZero L] (M : MasterFacts L) (pW r₀ : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = M.core.ℓ → R.A = M.core.A → R.ρ = M.core.ρ → 3 ≤ N → ∀ Nh : ℕ, Nh + 2 = N →
  ∀ m ∈ mRange L N, ∀ b μc : ℝ, 0 < b →
    Admissible (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μc →
    m * Fintype.card (Lam 2 L N) ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 →
    3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * (1 + 2 * pW * cmu ((L : ℝ) ^ 2) M.core.cm) <
      cmu ((L : ℝ) ^ 2) M.core.cm →
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 *
      (1 + 2 * pW * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm)) < M.core.ε →
    H0OnePtSmall M N Nh m r₀ (5 / 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) →
  ∃ μl μu, μl ≤ μc ∧ μc ≤ μu ∧
    AdmW (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μl
      (-(3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1)) ∧
    AdmW (rgDataM R m) ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT Nh M.core.ε b μu
      (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1) ∧
    H0SusceptExit L N m b μl μu ∧ H0OnePtUp L N m b μu ∧ b - m ∈ Ioc μl μu ∧
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j)) ∧
    |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).2.1| ≤
      3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 ∧
    |(traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 -
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1| ≤
      pW * (3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 -
        -(3 / 4 * cmu ((L : ℝ) ^ 2) M.core.cm * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1))

set_option maxHeartbeats 8000000 in
/-- **Input (i) discharged at the master constants**: `H0EndsConclG`. -/
theorem MasterFacts.h0EndsG {L : ℕ} [NeZero L] (M : MasterFacts L) :
    ∃ pW r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ H0EndsConclG M pW r₀ := by
  set D := M.core with hDd
  obtain ⟨r₀, hr₀, hr₀1, hRe⟩ := M.onePt_re_win
  obtain ⟨pW, hX⟩ := h0WindowX_of D.hWin
  have hM := D.h0MassC
  refine ⟨pW, r₀, hr₀, hr₀1, fun N R _ _ hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b μc hb hadm hmV hθ
    hgy hsm => ?_⟩
  have hN : 2 ≤ N := by omega
  obtain ⟨-, -, hρ, hε, -, -, -, hcm, -, -, hCf, -, -, -, hspl, -⟩ := D.hC2
  obtain ⟨hε45, hXc, hu⟩ := D.hH0E
  have hL : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by have := D.hL49; omega)
  have hcμ : 0 < cmu ((L : ℝ) ^ 2) D.cm := by
    unfold cmu; have : (0 : ℝ) < (L : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  set gc := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μc Nh).1 with hgcd
  set c₁ := 3 / 4 * cmu ((L : ℝ) ^ 2) D.cm * gc with hc₁d
  have hg := hadm.1 Nh le_rfl
  have hgc0 : 0 < gc := hg.1
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
  have hK := cNuLast_win_margin (R.withMsq m) (ε := D.ε) D.hL49 (by rw [hℓR]; exact D.hcmF) hu
  have hKT := h0KT_spec (L := L) D.hZT
  have hB := h0B_spec hspl
  have hsl := h0Slack_le_win (Lr := L) (cNL := cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε)
    (ℓ := D.ℓ) hCf hcNL hKT.1 hB.1 hρ.le hcμ hgc0 hg.2.1 hm0 hmV hθ hε45 hXc
  -- the margin at the upper end: `(c_ν + 2)(5/4)ǧ^c + 55ǧ^c ≤ L⁴c₁`
  have hL49 : (49 : ℝ) ≤ L := by exact_mod_cast D.hL49
  have hmarg : (cNuLast (R.withMsq m) ((L : ℝ) ^ 2) D.cm D.ε + 2) * (5 / 4 * gc) + 55 * gc ≤
      (L : ℝ) ^ 4 * c₁ := by
    have hL2 : 44 ≤ (L : ℝ) ^ 2 := by nlinarith
    have e : (L : ℝ) ^ 4 * c₁ = 3 * (L : ℝ) ^ 4 * cmu ((L : ℝ) ^ 2) D.cm * gc / 4 := by
      rw [hc₁d]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_right hK hgc0.le
    nlinarith
  -- the window
  obtain ⟨μl, μu, h1, h2, h3, h4, h5⟩ :=
    hX N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μc c₁ (3 / 4 * cmu ((L : ℝ) ^ 2) D.cm) hb hadm
      (by positivity) le_rfl hθ hgy
  have hlu : μl ≤ μu := h1.trans h2
  have hgw : ∀ μ ∈ Icc μl μu, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ Nh).1 ≤ gc + pW * (c₁ - -c₁) := fun μ hμ => by
    obtain ⟨k1, -, -, k4⟩ := h5 μ hμ
    exact ⟨((k1 Nh le_rfl).1).le, by linarith [(abs_le.1 k4).2]⟩
  -- lower end (as `h0EndsC`)
  obtain ⟨gl0, gl1⟩ := hgw μl ⟨le_rfl, hlu⟩
  have hlo := (hM N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μl hb h3.1).2 (by
    rw [h3.2]; have := (hsl _ gl0 gl1).2; linarith)
  have hex : H0SusceptExit L N m b μl μu := h0SusceptExit_of_re ⟨le_rfl, hlu⟩ hlo.2
  -- upper end: `Re r ≥ 0` from the one-point chain
  obtain ⟨gu0, gu1⟩ := hgw μu ⟨hlu, le_rfl⟩
  obtain ⟨hgu, hSu⟩ := hsl _ gu0 gu1
  obtain ⟨x, hx0, hx1⟩ := exists_coal_one (L := L) (N := N) (by have := D.hL49; omega) hN
  have hR := hRe N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μu hb h4.1 x hx0 (by omega) (by omega)
    (5 / 4 * gc) hgu hsm (by rw [h4.2]; linarith)
  obtain ⟨hZb, hre, hχ⟩ := hR
  obtain ⟨-, hr⟩ := onept_real_of_re hb hm.1 hZb hre hχ
  have hOP : H0OnePtUp L N m b μu := h0OnePtUp_of_re hb hm.1 hZb hr hχ
  have hmem := h0_mem_window' hb hm.1 hOP hex
  obtain ⟨k1, k2, k3, k4⟩ := h5 (b - m) ⟨hmem.1.le, hmem.2⟩
  exact ⟨μl, μu, h1, h2, h3, h4, hex, hOP, hmem, k1, abs_le.2 ⟨k2, k3⟩, k4⟩

/-- **`thm:multiscale` at `h = 0` with input (i) discharged** (`thm_multiscale_h0F` with
`H0EndsConclF` replaced by `H0EndsConclG`: no RG one-point input; at the upper window end only
the smallness `H0OnePtSmall`, `N ≥ 3`). -/
theorem thm_multiscale_h0G : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ M : MasterFacts L, (∃ pW r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 ∧ H0EndsConclG M pW r₀) ∧
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
  obtain ⟨L₀, h⟩ := thm_multiscale_h0F
  refine ⟨L₀, fun L _ hL => ?_⟩
  obtain ⟨M, -, hM⟩ := h L hL
  exact ⟨M, M.h0EndsG, hM⟩

end

end Spin2
