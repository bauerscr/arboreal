import Spin2.Multiscale.Thm
import Step2.Flow.ZetaSharpHypX
import PtCorr2.Zero.ExactHist

/-!
# `sec:spin` (ii) with (H_Γ) and (H_φ) discharged

* `Z_eq_norm_hist`: along every trajectory of the flow (real initial data, `0 ≤ ρ ≤ 1/8`) the field
  strength is real and positive, `Z_j = |Z_j|` (`PtCorr2.traj_real`: the raw flow is real;
  `Z_{j+1} = Z_j(1 + ζ_j)`, `|ζ_j| ≤ ρ`). So the phase hypothesis (H_φ) holds with `K_φ = 0`.
* `gam_hist_bound`: `|Z_{k+1}Γ^int_{k+1}(0,0) - log L/2π| ≤ K_G(ǧ_k + a_k)` for `k < N_h`, from
  `C'_{k+1}(0,0) = log L/2π + O(L^{-2k} + m²L^{2(k+1)}) + O(M_z(k+1))` (`k ≥ 1`),
  `|C'_1(0,0)| ≤ K_z` (`k = 0`, `a_0 = 1`) and `M_z(k+1) ≤ 2c_z ǧ_k`
  (all exported by `Step2.flow_finalZ_hyp0_zetaX`).
* `thm_flow_final_spinX`: `thm_flow_final_spin` (same construction, via `flow_finalZ_hyp0_zetaX`)
  together with these two facts along the admissible trajectories.
* **`prop_gamma_M2`**: `prop_gamma_M` with (H_Γ), (H_φ) removed; only the vertex hypothesis (H_λ)
  `‖λ̂_k - (ǧ_k/b)^{1/3}‖ ≤ K_λ(ǧ_k/b)^{1/3}(ǧ_k + a_k)` (`k < N_h`) remains.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

local notation "cj" => starRingEnd ℂ

variable {L N : ℕ} [NeZero L]

theorem ErrC_nonneg' : 0 ≤ ErrC := by
  rw [ErrC]
  have := ErrA_nonneg; have := KH_nonneg; have := kap_pos; have := Ia_nonneg 3
  have := Real.pi_pos
  positivity

/-- **The field strength is real and positive along the trajectories.** -/
theorem Z_re_pos_hist (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ0 : 0 ≤ R.ρ)
    (hρ8 : R.ρ ≤ 1 / 8) (Λ b μ₀ : ℝ) :
    ∀ j, (rawHist R j (traj (rgData R) Λ b μ₀)).Z.im = 0 ∧
      0 < (rawHist R j (traj (rgData R) Λ b μ₀)).Z.re
  | 0 => by simp [rawHist]
  | j + 1 => by
    obtain ⟨hi, hr⟩ := Z_re_pos_hist R hρ0 hρ8 Λ b μ₀ j
    have hreal := (PtCorr2.traj_real R hρ0 (by linarith only [hρ8]) Λ b μ₀ (j + 1)).1.Z
    refine ⟨Complex.conj_eq_iff_im.1 hreal, ?_⟩
    rw [rawHist_succ_Z, Complex.mul_re, hi, zero_mul, sub_zero, Complex.add_re, Complex.one_re]
    have hζ : |(zetaH R j (traj (rgData R) Λ b μ₀)).re| ≤ 1 / 8 := (Complex.abs_re_le_norm _).trans
      ((absorb_le R hρ0 _ _).trans hρ8 : ‖zetaH R j (traj (rgData R) Λ b μ₀)‖ ≤ 1 / 8)
    have := (abs_le.1 hζ).1
    exact mul_pos hr (by linarith only [this])

/-- `Z_j = |Z_j|` along the trajectories. -/
theorem Z_eq_norm_hist (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hρ0 : 0 ≤ R.ρ)
    (hρ8 : R.ρ ≤ 1 / 8) (Λ b μ₀ : ℝ) (j : ℕ) :
    (rawHist R j (traj (rgData R) Λ b μ₀)).Z =
      ((‖(rawHist R j (traj (rgData R) Λ b μ₀)).Z‖ : ℝ) : ℂ) := by
  obtain ⟨hi, hr⟩ := Z_re_pos_hist R hρ0 hρ8 Λ b μ₀ j
  set Z := (rawHist R j (traj (rgData R) Λ b μ₀)).Z
  have e : Z = (Z.re : ℂ) := Complex.ext rfl (by rw [hi, Complex.ofReal_im])
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

/-- The constant of `gam_hist_bound`. -/
def gamKX (L : ℕ) (cz KG Kz : ℝ) : ℝ :=
  Kz + Real.log L / (2 * Real.pi) + (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB) + KG * (2 * cz)

theorem gamKX_nonneg {cz KG Kz : ℝ} (hL : (2 : ℝ) ≤ L) (hcz : 0 ≤ cz) (hKG : 0 ≤ KG)
    (hKz : 0 ≤ Kz) : 0 ≤ gamKX L cz KG Kz := by
  unfold gamKX
  have : 0 < Real.log L := Real.log_pos (by linarith only [hL])
  have := Real.pi_pos
  have := ErrC_nonneg'
  have := ErrB_nonneg
  positivity

/-- **(H_Γ) along a history**: `|Z_{k+1}Γ^int_{k+1}(0,0) - log L/2π| ≤ K_G(ǧ_k + a_k)`. -/
theorem gam_hist_bound (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (hP : R.P = Pc)
    {Nh : ℕ} (hNh : Nh + 2 ≤ N) {cz KG Kz : ℝ} (hcz : 0 ≤ cz) (hKG : 0 ≤ KG) (hKz : 0 ≤ Kz)
    (hL : (2 : ℝ) ≤ L) (hm0 : 0 ≤ R.msq) (t : Hist.Seq (Xs R)) (hV : ∀ j < Nh, ValidAt R j)
    (hMz : ∀ j < Nh, (dData L N R.msq (zh R j t)).Mz (j + 1) ≤ 2 * cz * (t j).1)
    (hcov0 : ∀ j < Nh, ‖stZ' R (rawHist R j t) * stCov R j (rawHist R j t) 0 0‖ ≤ Kz)
    (hval : ∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
      ‖stZ' R (rawHist R k t) * stCov R k (rawHist R k t) 0 0 -
          (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
        (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k) ^ 2 +
          ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
        KG * (dData L N R.msq (zh R k t)).Mz (k + 1))
    (hg : ∀ j < Nh, 0 ≤ (t j).1) :
    ∀ k < Nh, ‖(rawHist R (k + 1) t).Z * GamInt R k t - (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
      gamKX L cz KG Kz * ((t k).1 + zA L R.msq k) := by
  intro k hk
  have hVk : ∀ i ≤ k, ValidAt R i := fun i hi => hV i (by omega)
  rw [Z_mul_gamInt R hVk t, ← G_eq_kern R hP hVk t]
  set X := stZ' R (rawHist R k t) * stCov R k (rawHist R k t) 0 0
  set γ := Real.log L / (2 * Real.pi) with hγd
  have hγ : 0 ≤ γ := by
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL])
    have := Real.pi_pos
    positivity
  have hgk := hg k hk
  have hK0 := gamKX_nonneg hL hcz hKG hKz
  have hEC := ErrC_nonneg'
  have hEB := ErrB_nonneg
  have hp : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ ^ 2 := by have := Real.pi_pos; positivity
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [zA_zero]
    have h1 : ‖X - (γ : ℂ)‖ ≤ Kz + γ := by
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ]
      linarith only [hcov0 0 hk]
    have h2 : Kz + γ ≤ gamKX L cz KG Kz := by
      unfold gamKX
      have : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB) := by positivity
      have : 0 ≤ KG * (2 * cz) := by positivity
      linarith
    have h3 : 0 ≤ gamKX L cz KG Kz * (t 0).1 := mul_nonneg hK0 hgk
    have e : gamKX L cz KG Kz * ((t 0).1 + 1) = gamKX L cz KG Kz * (t 0).1 + gamKX L cz KG Kz := by
      ring
    rw [e]; linarith only [h1, h2, h3]
  · have h := hval k hk1 (by omega) hVk t
    rw [zA_pos L R.msq hk1]
    set x := ((L : ℝ) ^ k) ^ 2 with hx
    set y := ((L : ℝ) ^ (k + 1)) ^ 2 with hy
    have hx1 : 1 ≤ x := one_le_pow₀ (one_le_pow₀ (by linarith only [hL]))
    have hxy : x ≤ y := pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ (by linarith only [hL]) (Nat.le_succ k)) 2
    have hxi : 0 ≤ x⁻¹ := by positivity
    have hmy : 0 ≤ R.msq * y := mul_nonneg hm0 (by positivity)
    have hA : ErrC / x + ErrB * R.msq * (x + y) ≤ (ErrC + 2 * ErrB) * (x⁻¹ + R.msq * y) := by
      have e1 : ErrC / x = ErrC * x⁻¹ := div_eq_mul_inv _ _
      have h1 : ErrB * R.msq * x ≤ ErrB * (R.msq * y) := by
        have := mul_le_mul_of_nonneg_left hxy (mul_nonneg hEB hm0)
        linarith only [this]
      have h2 : 0 ≤ ErrC * (R.msq * y) := mul_nonneg hEC hmy
      have h3 : 0 ≤ ErrB * x⁻¹ := mul_nonneg hEB hxi
      have e2 : ErrB * R.msq * (x + y) = ErrB * R.msq * x + ErrB * (R.msq * y) := by ring
      have e3 : (ErrC + 2 * ErrB) * (x⁻¹ + R.msq * y) =
          ErrC * x⁻¹ + ErrC * (R.msq * y) + 2 * (ErrB * x⁻¹) + 2 * (ErrB * (R.msq * y)) := by ring
      rw [e1, e2, e3]; linarith only [h1, h2, h3]
    have hB := mul_le_mul_of_nonneg_left hA hp
    have hC := mul_le_mul_of_nonneg_left (hMz k hk) hKG
    set a := x⁻¹ + R.msq * y
    have ha : 0 ≤ a := add_nonneg hxi hmy
    have hfin : (2 * Real.pi)⁻¹ ^ 2 * ((ErrC + 2 * ErrB) * a) + KG * (2 * cz * (t k).1) ≤
        gamKX L cz KG Kz * ((t k).1 + a) := by
      have e : gamKX L cz KG Kz * ((t k).1 + a) =
          (Kz + γ) * ((t k).1 + a) + (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB) * (t k).1 +
          (2 * Real.pi)⁻¹ ^ 2 * ((ErrC + 2 * ErrB) * a) + KG * (2 * cz) * a +
          KG * (2 * cz * (t k).1) := by unfold gamKX; rw [← hγd]; ring
      rw [e]
      have : 0 ≤ (Kz + γ) * ((t k).1 + a) := by positivity
      have : 0 ≤ (2 * Real.pi)⁻¹ ^ 2 * (ErrC + 2 * ErrB) * (t k).1 := by positivity
      have : 0 ≤ KG * (2 * cz) * a := by positivity
      linarith
    linarith only [h, hB, hC, hfin]

set_option maxHeartbeats 4000000 in
/-- **`thm_flow_final_spin` with the value of `C'_{k+1}(0,0)` and the reality of `Z`**: in addition,
along the admissible trajectories, `|Z_{k+1}Γ^int_{k+1}(0,0) - log L/2π| ≤ K_G(ǧ_k + a_k)` and
`Z_{k+1} = |Z_{k+1}| > 0` (`k < N_h`). -/
theorem thm_flow_final_spinX : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ KZ ∧ 0 ≤ KG ∧ ε ≤ 1 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) ∧
      (∀ m ∈ mRange L N, LogSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1)) ∧
      (∀ m ∈ mRange L N, SpinSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1)) ∧
      (∀ m ∈ mRange L N, BetaAsym (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
        (eRange (betaL L) Ke 1)) ∧
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        ∀ n ≤ Nh,
          (rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z ≠ 0 ∧
          |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ +
              1 / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
            KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ∧
      (∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
        ∀ k < Nh,
          ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
              GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) -
              (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
            KG * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) ∧
          (rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z =
            ((‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℝ) : ℂ)) := by
  obtain ⟨L₀, hL₀⟩ := flow_finalZ_hyp0_zetaX
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, AZ, cz, KG, Kz, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCL, hcgε, he, ha0, hs, hC, hρ8, hcov, hAZ, hε1, hcz, hKG, hKz, h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hβ : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have heR : 0 ≤ eRange (betaL L) Ke 1 := by unfold eRange; positivity
  obtain ⟨KZ, hKZd⟩ : ∃ KZ : ℝ, KZ = logTrajK (betaL L) cg AZ (1 / 3) + AZ * 4 +
      1 / 3 * (2 * (1 + betaL L) * eRange (betaL L) Ke 1) := ⟨_, rfl⟩
  have hK0 : 0 ≤ logTrajK (betaL L) cg AZ (1 / 3) := by
    unfold logTrajK Cgu; positivity
  have hKZ : 0 ≤ KZ := by rw [hKZd]; positivity
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, gamKX L cz KG Kz, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm,
    hcT, hKe, hKZ, gamKX_nonneg hL2 hcz hKG hKz, hε1, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  have hc : FinConstZ L ρ κ cg cm cT ε CL aB := ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, hC⟩
  have hmass : ∀ m ∈ mRange L N, m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := fun m hm => by
    have := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simpa using this
  have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact ⟨hV, H, HZ, HM, HD, e,
      { hc := hcg.le, he := he0
        hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej
        F1s := F1s }⟩
  obtain ⟨c1, c2⟩ := flow_finalZ_of hc R hP hRρ hN (by omega) le_rfl hyp
  have hLS : ∀ m ∈ mRange L N, LogSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact logSum_of H he hε1 hcgε he0 heb
      (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
  have hSS : ∀ m ∈ mRange L N, SpinSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact spinSum_of H he hε1 hcgε he0 heb
      (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
  have hBA : ∀ m ∈ mRange L N, BetaAsym (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej, -⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact betaAsym_of H he hε1 hcgε he0 heb
      (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
  refine ⟨c1, c2, hLS, hSS, hBA, fun m hm b μ₀ hadm n hn => ?_, fun m hm b μ₀ hadm k hk => ?_⟩
  rotate_left
  · obtain ⟨e, -, hV, -, H, -, -, -, -, -, -, hMzb, hcov0, hval⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    have hD := admissible_InDh H hadm
    have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ.le
    have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ8
    exact ⟨gam_hist_bound (R.withMsq m) hP hNh hcz hKG hKz hL2 hm.1.le _ hV
      (fun j hj => hMzb j hj _ (hD j hj.le)) (fun j hj => hcov0 j hj _ (hD j hj.le)) hval
      (fun j hj => ((hD j hj.le).1 j le_rfl).1.le) k hk,
      Z_eq_norm_hist (R.withMsq m) hρ0' hρ8' _ _ _ (k + 1)⟩
  obtain ⟨e, hZs, hV, HD, H, HZ, HM, he0, F1s, heb, hej, hMzb, hcov0, hval⟩ :=
    h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hD := admissible_InDh H hadm
  have hρ0' : 0 ≤ (R.withMsq m).ρ := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ.le
  have hρ8' : (R.withMsq m).ρ ≤ 1 / 8 := by rw [show (R.withMsq m).ρ = ρ from hRρ]; exact hρ8
  refine ⟨Z_succ_ne_zero (R.withMsq m) hρ0' hρ8' (fun i hi => hV i (by omega)) t, ?_⟩
  have key := hLS m hm b μ₀ hadm
    (fun k => Real.log ‖(rawHist (R.withMsq m) (k + 1) t).Z‖) (fun _ => 0) (zA L m) AZ
    (betaL L / 3) hAZ (zA_nonneg L hm.1.le)
    (fun k hk => by
      have := hZs k hk t (hD (k + 1) (by omega))
      simp only [sub_self, sub_zero]
      exact this) n hn
  have hy0 : Real.log ‖(rawHist (R.withMsq m) 1 t).Z‖ = 0 := by
    rw [rawHist_one_Z, norm_one, Real.log_one]
  have hy0' : Real.log ‖(rawHist (R.withMsq m) (0 + 1) t).Z‖ = 0 := hy0
  simp only [hy0, sub_self, sub_zero] at key
  have hβne : betaL L ≠ 0 := hβ.ne'
  have hs3 : |betaL L / 3| / betaL L = 1 / 3 := by
    rw [abs_of_pos (by positivity)]; field_simp
  have hs3' : betaL L / 3 / betaL L = 1 / 3 := by field_simp
  rw [hs3, hs3'] at key
  refine key.trans (mul_le_mul_of_nonneg_right ?_ ((hD n hn).1 n le_rfl).1.le)
  rw [hKZd]
  have hsa := sum_zA_le (Ln := L) rfl hL2 hm.1.le n
  have hmn : m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := by
    refine le_trans ?_ (hmass m hm)
    refine mul_le_mul_of_nonneg_left ?_ hm.1.le
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2])
      (by omega)) 2
  have := Real.pi_pos
  linarith only [hsa, hmn, mul_le_mul_of_nonneg_left (by linarith only [hsa, hmn] :
    ∑ k ∈ range n, zA L m k ≤ 4) hAZ]

set_option maxHeartbeats 1000000 in
/-- **`prop:gamma` (ii), the magnetisation** (`sec:spin`): `M_j = ϑ_j(1 + O(β_j^{-1}))` with
`ϑ_j = (β_j/β_ε)^{1/3}`, conditional only on the vertex asymptotics `λ̂_k`
(`λ̂_k = (β_ε/β_k)^{1/3}(1 + O(ǧ_k + a_k))`, complex). The value of `C'_{k+1}(0,0)` and the
reality of `Z_{k+1}` are proved (`thm_flow_final_spinX`). -/
theorem prop_gamma_M2 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke KZ KG : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ KZ ∧ 0 ≤ KG ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
    ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl : ℝ), 0 ≤ Kl →
      -- the vertex: `λ̂_k = (β_ε/β_k)^{1/3}(1 + O(ǧ_k + a_k))`
      (∀ k < Nh, ‖lam k - ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
        Kl * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
          ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) →
      ∀ j ≤ Nh,
        ‖(1 - (b : ℂ) * ∑ k ∈ range j,
            lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
          (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
        spinMK L cg Ke KZ Kl KG 0 * (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_final_spinX
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, KG, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    hKG, hε1, h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, KG, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    hKG, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  obtain ⟨c1, -, -, hSS, -, hZ, hGZ⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  refine ⟨c1, fun m hm b μ₀ hadm lam Kl hKl hl j hj => ?_⟩
  set Kp : ℝ := 0 with hKpd
  have hKp : (0 : ℝ) ≤ Kp := le_rfl
  have hG := fun k (hk : k < Nh) => (hGZ m hm b μ₀ hadm k hk).1
  have hph : ∀ k < Nh, ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z -
      (‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℂ)‖ ≤
      Kp * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 *
        ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ := by
    intro k hk
    have e := (hGZ m hm b μ₀ hadm k hk).2
    rw [hKpd, zero_mul, zero_mul, norm_le_zero_iff, sub_eq_zero]
    exact e
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  set γ : ℝ := Real.log L / (2 * Real.pi) with hγd
  have hγ : 0 ≤ γ := by
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  have hg : ∀ n ≤ Nh, 0 < (t n).1 := fun n hn => (hadm.1 n hn).1
  have hgε : ∀ n ≤ Nh, (t n).1 ≤ ε := fun n hn => (hadm.1 n hn).2.1
  have hb : 0 < b := by have := hg 0 (Nat.zero_le _); rwa [ht, Hist.traj_zero] at this
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hsa : ∑ k ∈ range Nh, zA L m k ≤ 4 := by
    have := sum_zA_le (Ln := L) rfl hL2 hm.1.le Nh
    linarith only [this, hmn Nh le_rfl]
  set Kzz := (KZ + Kp) * Real.exp KZ with hKzz
  have hKzz0 : 0 ≤ Kzz := by positivity
  -- the summand
  have hT : ∀ k < Nh, ‖(b : ℂ) * lam k * GamInt (R.withMsq m) k t -
      ((betaL L / 3 * b * (((t k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 : ℝ) : ℂ)‖ ≤
      (Kl * (γ + 3 * gamK L KZ KG Kp) + gamK L KZ KG Kp) * b *
        (((t k).1 / b) ^ (1 / 3 : ℝ)) ^ 2 * ((t k).1 + zA L m k) := by
    intro k hk
    set g := (t k).1 with hgdef
    set r := (g / b) ^ (1 / 3 : ℝ) with hrd
    set Z := (rawHist (R.withMsq m) (k + 1) t).Z with hZd
    have hgk := hg k hk.le
    have hg1 : g ≤ 1 := (hgε k hk.le).trans hε1
    have hr : 0 < r := cbrt_pos (div_pos hgk hb)
    have ha0 := zA_nonneg L hm.1.le k
    have ha2 : zA L m k ≤ 2 := zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)
    obtain ⟨hZne, hZlog⟩ := hZ m hm b μ₀ hadm k hk.le
    -- `Z⁻¹ = r (1 + O(g))`
    have hlogr : Real.log r = 1 / 3 * Real.log (g / b) := Real.log_rpow (div_pos hgk hb) _
    have hZi : ‖Z⁻¹ - (r : ℂ)‖ ≤ Kzz * r * g := by
      refine near_of_log (inv_ne_zero hZne) hr hgk.le hg1 hKZ hKp ?_ ?_
      · rw [norm_inv, Real.log_inv, hlogr]
        have e : -Real.log ‖Z‖ - 1 / 3 * Real.log (g / b) =
            -(Real.log ‖Z‖ + 1 / 3 * Real.log (g / b)) := by ring
        rw [e, abs_neg]; exact hZlog
      · exact phase_inv hZne (hph k hk)
    -- `Γ = γ r (1 + O(g + a))`
    have hGam : ‖GamInt (R.withMsq m) k t - ((γ * r : ℝ) : ℂ)‖ ≤
        gamK L KZ KG Kp * r * (g + zA L m k) := by
      have e : GamInt (R.withMsq m) k t - ((γ * r : ℝ) : ℂ) =
          Z⁻¹ * (Z * GamInt (R.withMsq m) k t - (γ : ℂ)) + (γ : ℂ) * (Z⁻¹ - (r : ℂ)) := by
        have hZne' : Z ≠ 0 := hZne
        rw [mul_sub Z⁻¹, ← mul_assoc, inv_mul_cancel₀ hZne', one_mul]; push_cast; ring
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have hZin : ‖Z⁻¹‖ ≤ r * (1 + Kzz) := by
        have := norm_le_norm_add_norm_sub' Z⁻¹ (r : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] at this
        have h2 : Kzz * r * g ≤ Kzz * r := mul_le_of_le_one_right (by positivity) hg1
        linarith only [this, hZi, h2]
      have h1 : ‖Z⁻¹ * (Z * GamInt (R.withMsq m) k t - (γ : ℂ))‖ ≤
          r * (1 + Kzz) * (KG * (g + zA L m k)) := by
        rw [norm_mul]; exact mul_le_mul hZin (hG k hk) (norm_nonneg _) (by positivity)
      have h2 : ‖(γ : ℂ) * (Z⁻¹ - (r : ℂ))‖ ≤ γ * (Kzz * r * g) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hγ]
        exact mul_le_mul_of_nonneg_left hZi hγ
      have h3 : γ * (Kzz * r * g) ≤ γ * (Kzz * r * (g + zA L m k)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [ha0])
          (by positivity)) hγ
      have e2 : gamK L KZ KG Kp * r * (g + zA L m k) =
          r * (1 + Kzz) * (KG * (g + zA L m k)) + γ * (Kzz * r * (g + zA L m k)) := by
        unfold gamK; rw [← hKzz, ← hγd]; ring
      rw [e2]; linarith only [h1, h2, h3]
    have hgK : 0 ≤ gamK L KZ KG Kp := by unfold gamK; rw [← hKzz, ← hγd]; positivity
    have key := spin_term (lam := lam k) (Gam := GamInt (R.withMsq m) k t) hr.le hγ hb.le hKl hgK
      (by linarith only [hgk, ha0]) (by linarith only [hg1, ha2]) (hl k hk) hGam
    have e : betaL L / 3 = γ := by unfold betaL; rw [hγd]; ring
    rw [e]; exact key
  have hB : 0 ≤ Kl * (γ + 3 * gamK L KZ KG Kp) + gamK L KZ KG Kp := by
    have : 0 ≤ gamK L KZ KG Kp := by unfold gamK; rw [← hKzz, ← hγd]; positivity
    positivity
  have key := hSS m hm b μ₀ hadm (fun k => (b : ℂ) * lam k * GamInt (R.withMsq m) k t) (zA L m)
    _ 4 hB (zA_nonneg L hm.1.le) hsa hT j hj
  unfold spinMK
  convert key using 3
  rw [mul_sum]; congr 1; exact sum_congr rfl fun k _ => (mul_assoc _ _ _).symm


/-- **(H_λ) from the output form of `Obs2.prop_gamma`** (`s = 1`) and the phase: if
`|log‖λ̂‖ - (1/3) log(ǧ/b)| ≤ K ǧ` and `‖λ̂ - ‖λ̂‖‖ ≤ K_φ ǧ ‖λ̂‖`, then
`‖λ̂ - (ǧ/b)^{1/3}‖ ≤ (K + K_φ)e^K (ǧ/b)^{1/3}(ǧ + a)` for every `a ≥ 0`. -/
theorem lamHyp_of_log {lam : ℂ} {g b a K Kp : ℝ} (hl : lam ≠ 0) (hb : 0 < b) (hg : 0 < g)
    (hg1 : g ≤ 1) (ha : 0 ≤ a) (hK : 0 ≤ K) (hKp : 0 ≤ Kp)
    (hlog : |Real.log ‖lam‖ - 1 / 3 * Real.log (g / b)| ≤ K * g)
    (hph : ‖lam - (‖lam‖ : ℂ)‖ ≤ Kp * g * ‖lam‖) :
    ‖lam - (((g / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      (K + Kp) * Real.exp K * (g / b) ^ (1 / 3 : ℝ) * (g + a) := by
  have hr := cbrt_pos (div_pos hg hb)
  have hlogr : Real.log ((g / b) ^ (1 / 3 : ℝ)) = 1 / 3 * Real.log (g / b) :=
    Real.log_rpow (div_pos hg hb) _
  have h := near_of_log hl hr hg.le hg1 hK hKp (by rw [hlogr]; exact hlog) hph
  refine h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end

end Spin2
