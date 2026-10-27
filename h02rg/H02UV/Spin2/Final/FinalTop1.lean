import Spin2.Pair.PairTopSeed3
import Spin2.Final.FinalTheorem

/-!
# Top coalescence on one `h = 0` trajectory with the smallness folded into a threshold

* **`FwTopBd K`**: for `x ≠ 0` with `j_x ≥ N_h + 1`, `|P_{1/b}[0 ↔ x] − ϑ_{N_h}²| ≤ Kϑ_{N_h}²/β_{N_h}`.
* **`MasterFacts.fwGT`**: `fwG` capped by the conditions of the seed at `N − 1`
  (`c_Mℓ²·4C_fǧ + 8ℓ⁴C_fǧ ≤ 1`, `2C_fǧ² ≤ 1`, `A⁴(C_fǧ³ + c_{KL}ǧ) ≤ 4/5`) and the mass window
  `2·(81/16)c_J(c_ρ + 4/r₀²)(8c_K + 1)ℓ²·m²L^{2N} ≤ 1`.
* **`MasterFacts.fw_top_trajG`**: `ǧ_{N_h}, m²L^{2N} ≤ fwGT` give `FwTopBd (fwKT c_K r₀)`
  (`fw_top_traj` with `TopSeedConclD`).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

/-- **The pair bound for `j_x ≥ N_h + 1`**, at the scale `N_h = N − 2`. -/
def FwTopBd {L : ℕ} [NeZero L] (K : ℝ) {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (Nh : ℕ) (m b : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Nh + 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
    |Pconn L N (1 / b) x - thetaSq R m b (b - m) Nh| ≤
      K * thetaSq R m b (b - m) Nh / betaJ R m b (b - m) Nh

namespace MasterFacts

variable {L : ℕ} [NeZero L] (M : MasterFacts L)

/-- The mass-window coefficient of the top `ab` last step. -/
def fwAT (r₀ cK : ℝ) : ℝ :=
  2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cK + 1) * M.core.ℓ ^ 2)

/-- The threshold of the top bound. -/
def fwGT (Kt r₀ cK : ℝ) : ℝ :=
  min (M.fwG Kt r₀)
    (min (min (1 / (|cM * M.core.ℓ ^ 2 * (4 * M.core.Cf) + 8 * M.core.ℓ ^ 4 * M.core.Cf| + 1))
        (1 / (|2 * M.core.Cf| + 1)))
      (min (4 / 5 / (|M.core.A ^ 4 * (M.core.Cf + M.core.cKL)| + 1))
        (min 1 (1 / (|M.fwAT r₀ cK| + 1)))))

theorem fwGT_pos {Kt r₀ cK : ℝ} (hr₀ : 0 < r₀) : 0 < M.fwGT Kt r₀ cK := by
  unfold fwGT
  refine lt_min (M.fwG_pos hr₀) (lt_min (lt_min ?_ ?_) (lt_min ?_ (lt_min one_pos ?_))) <;>
    positivity

set_option maxHeartbeats 4000000 in
/-- **The top bound on one `h = 0` trajectory from the threshold `fwGT`.** -/
theorem fw_top_trajG {r₀ Kt cK : ℝ} (hr₀ : 0 < r₀) (hr₀1 : r₀ ≤ 1)
    (hJ : LastJetBd L (M.core.A / 2) r₀) (hcK : 0 ≤ cK)
    (hS : TopSeedConclD L M.core.ℓ M.core.A M.core.ρ M.core.κ M.core.cm M.core.cT M.core.ε
      M.core.Cf M.core.cKL cK)
    (hZTl : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc →
      0 ≤ R.ρ → R.ρ ≤ M.core.ρ → 0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) →
      ∀ (Nh : ℕ), Nh + 2 = N → ∀ t : Flow2.Hist.Seq (Xs R),
        ‖(R.msq : ℂ) * ((lastOut R Nh t).Z * zmRaw R (Nh + 1) (lastOut R Nh t).ζ) - 1‖ ≤
          Kt * R.msq * (L : ℝ) ^ (2 * N))
    {N : ℕ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
    (hP : R.P = Pc) (hi0 : R.i₀ = 0) (hRℓ : R.ℓ = M.core.ℓ) (hRA : R.A = M.core.A)
    (hRρ : R.ρ = M.core.ρ) (hN3 : 3 ≤ N) {Nh : ℕ} (hNh : Nh + 2 = N) {m : ℝ}
    (hm : m ∈ mRange L N) {b : ℝ}
    (hD : ∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) M.core.κ M.core.cm M.core.cT M.core.ε
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) j))
    (hG : (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 ≤ M.fwGT Kt r₀ cK)
    (hmΛ : m * (L : ℝ) ^ (2 * N) ≤ M.fwGT Kt r₀ cK) :
    FwTopBd (M.fwKT cK r₀) R Nh m b := by
  obtain ⟨-, -, hρ, -⟩ := M.core.hC2
  have hN2 : 2 ≤ N := by omega
  set G := (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m) Nh).1 with hGd
  set X := m * (L : ℝ) ^ (2 * N) with hXd
  have hG0 : 0 ≤ G := (hD Nh le_rfl).1.le
  have hX0 : 0 ≤ X := mul_nonneg hm.1.le (by positivity)
  set g := M.fwG Kt r₀ with hgd
  have hGg : G ≤ g := hG.trans (min_le_left _ _)
  have hXg : X ≤ g := hmΛ.trans (min_le_left _ _)
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
  have t1 : M.fwGT Kt r₀ cK ≤ _ :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have t2 : M.fwGT Kt r₀ cK ≤ _ :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have t3 : M.fwGT Kt r₀ cK ≤ _ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have t4 : M.fwGT Kt r₀ cK ≤ 1 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have t5 : M.fwGT Kt r₀ cK ≤ _ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
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
    fw_le (hD j hj).1.le (((hjN j hj).trans hGg).trans m9)
  have s1 := fw_le hG0 (hGg.trans m1)
  have s2 : Kt * m * (L : ℝ) ^ (2 * N) ≤ 1 / 2 := by
    rw [mul_assoc]; exact fw_le hX0 (hXg.trans m2)
  have s3 : 8 * cKAL L M.core.ℓ r₀ M.core.Cf M.core.cWL M.core.cKL 3 * m * (L : ℝ) ^ (2 * N) ≤ 1 := by
    rw [mul_assoc]; exact fw_le hX0 (hXg.trans m3)
  have s4 : 2 * (M.core.Cf * G) ≤ M.core.ρ := by
    rw [← mul_assoc]; exact fw_le hG0 (hGg.trans m4)
  have s5 : 8 * cM * M.core.ℓ ^ 2 * (M.core.Cf * G) ≤ 1 / 2 := by
    rw [← mul_assoc]; exact fw_le hG0 (hGg.trans m5)
  have s6 : PtCorr2.cRho L * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * G) ≤ 1 := by
    rw [← mul_assoc]; exact fw_le hG0 (hGg.trans m6)
  have s7 : 4 * (cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * G) ≤ r₀ ^ 2 := by
    rw [← mul_assoc]; exact fw_le hG0 (hGg.trans m7)
  have s8 : cTauL M.core.ℓ M.core.Cf M.core.cWL M.core.cKL * G ≤ r₀ :=
    fw_le hG0 (hGg.trans m8)
  have hG1 : G ≤ 1 := hG.trans t4
  have hCf : 0 ≤ M.core.Cf := M.flow.2.2.2.2.2.2.2.2.2.2.1
  have u1 : cM * M.core.ℓ ^ 2 * (4 * (M.core.Cf * G)) + 8 * M.core.ℓ ^ 4 * (M.core.Cf * G) ≤ 1 := by
    have := fw_le hG0 (hG.trans t1)
    calc _ = (cM * M.core.ℓ ^ 2 * (4 * M.core.Cf) + 8 * M.core.ℓ ^ 4 * M.core.Cf) * G := by ring
      _ ≤ 1 := this
  have u2 : 2 * (M.core.Cf * G ^ 2) ≤ 1 := by
    have h := fw_le hG0 (hG.trans t2)
    have h2 : 0 ≤ 2 * M.core.Cf * G := by positivity
    calc 2 * (M.core.Cf * G ^ 2) = (2 * M.core.Cf * G) * G := by ring
      _ ≤ 1 * 1 := mul_le_mul h hG1 hG0 zero_le_one
      _ = 1 := by ring
  have u3 : M.core.A ^ 4 * (M.core.Cf * G ^ 3 + M.core.cKL * G) ≤ 4 / 5 := by
    have h := fw_le hG0 (hG.trans t3)
    have hG3 : G ^ 3 ≤ G := by
      have : G ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hA4 : 0 ≤ M.core.A ^ 4 := by positivity
    have hcKL := M.cKL_nonneg
    calc M.core.A ^ 4 * (M.core.Cf * G ^ 3 + M.core.cKL * G) ≤
          M.core.A ^ 4 * (M.core.Cf * G + M.core.cKL * G) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hA4
      _ = M.core.A ^ 4 * (M.core.Cf + M.core.cKL) * G := by ring
      _ ≤ 4 / 5 := h
  have u4 : 2 * (81 / 16 * (cJet L * (cRho L + 4 / r₀ ^ 2)) * (8 * cK + 1) * M.core.ℓ ^ 2) * m *
      (L : ℝ) ^ (2 * N) ≤ 1 := by
    rw [mul_assoc]; exact fw_le hX0 (hmΛ.trans t5)
  have hseed := hS N R hP hi0 hRℓ hRA hRρ hN3 Nh hNh m hm b (b - m) hD s4 s5 u1 u2 u3
  have hρ0R : 0 ≤ R.ρ := by rw [hRρ]; exact hρ.le
  have hK := hZTl N (R.withMsq m) hP hρ0R (le_of_eq hRρ) hm.1 hm.2 Nh hNh
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b (b - m))
  intro x hx hj
  exact M.fw_top_traj R hP hi0 hRℓ hRA hRρ hN3 hNh hm hD hr₀ hr₀1 hJ hcK hseed hK s2 s3 u4 s1 s4
    s5 s6 s7 s8 hsmall x hx hj

end MasterFacts

end

end Spin2
