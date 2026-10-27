import Spin2.Multiscale.Flow
import Step2.Flow.ZetaSharpThm

/-!
# `sec:spin` (ii): the magnetisation `M_j = ϑ_j(1 + O(ǧ_j))` along the final flow

* `GamInt R k t = Γ^int_{k+1}(0,0)`: the diagonal of the dressed covariance `Gint k` of step `k`
  along the history (`C'_{k+1} = Z_{k+1} Γ^int_{k+1}`, `Z_{k+1} = (rawHist R (k+1) t).Z`).
* `gamInt_value_hist`: `|Z_{k+1} Γ^int_{k+1}(0,0) - log L/2π| ≤ (2π)^{-2}(E_C L^{-2k} +
  E_B m²(L^{2k} + L^{2(k+1)})) + K M_z(k+1)` for `1 ≤ k`, `k + 1 < N` (`Cprime_values`, first line).
* `thm_flow_final_spin`: `thm_flow_final_Z` (verbatim, its own constants, same construction)
  together with `SpinSum` and `BetaAsym` along the admissible trajectories and `ε ≤ 1`.
* **`prop_gamma_M`**: along every admissible trajectory, for every vertex sequence `λ̂_k` with
  `λ̂_k = (β_ε/β_k)^{1/3}(1 + O(ǧ_k + a_k))` (complex; the conditional output of `prop_gamma`(λ),
  `s = 1`, with the phase), given the value `Z_{k+1}Γ^int_{k+1}(0,0) = log L/2π + O(ǧ_k + a_k)`
  and the phase `Z_{k+1}/|Z_{k+1}| = 1 + O(ǧ_k)`, the magnetisation
  `M_j = 1 - b ∑_{k<j} λ̂_k Γ^int_{k+1}(0,0)` of `e:PM` satisfies
  `|M_j - (β_j/β_ε)^{1/3}| ≤ K_M (β_j/β_ε)^{1/3}/β_j` for `j ≤ N_h`.
  The modulus `|Z_{k+1}| = (β_k/β_ε)^{1/3}e^{O(ǧ_k)}` is used unconditionally (`thm_flow_final_Z`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L N : ℕ} [NeZero L]

/-- `Γ^int_{k+1}(0,0)` along the history: the diagonal of the dressed `Gint k`. -/
def GamInt (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (k : ℕ)
    (t : Hist.Seq (Xs R)) : ℂ :=
  DressedFRD.kern ((dData L N R.msq (zh R k t)).Gint k) 0

/-- `Z_{k+1} Γ^int_{k+1}(0,0) = C'_{k+1}(0,0)`. -/
theorem Z_mul_gamInt (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] {k : ℕ}
    (hV : ∀ i ≤ k, ValidAt R i) (t : Hist.Seq (Xs R)) :
    (rawHist R (k + 1) t).Z * GamInt R k t =
      DressedFRD.kern ((dData L N R.msq (zh R k t)).Z (k + 1) •
        (dData L N R.msq (zh R k t)).Gint k) 0 := by
  rw [DressedFRD.kern_smul, ← stZ'_eq_dData R hV t]
  rfl

/-- **The value of `C'_{k+1}(0,0)` along histories** (`prop:d2`, first line). -/
theorem gamInt_value_hist : ∀ (L : ℕ) [NeZero L], 7 ≤ L →
    ∃ ζbar : ℝ, 0 < ζbar ∧ ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → 1 ≤ N →
      0 < R.msq → R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → R.ρ ≤ ζbar →
      ∀ k, 1 ≤ k → k + 1 < N → (∀ i ≤ k, ValidAt R i) → ∀ t : Hist.Seq (Xs R),
        ‖(rawHist R (k + 1) t).Z * GamInt R k t - (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
          (2 * Real.pi)⁻¹ ^ 2 * (ErrC / ((L : ℝ) ^ k) ^ 2 +
            ErrB * R.msq * (((L : ℝ) ^ k) ^ 2 + ((L : ℝ) ^ (k + 1)) ^ 2)) +
          K * (dData L N R.msq (zh R k t)).Mz (k + 1) := by
  intro L _ hL
  obtain ⟨ζbar, hζ, K, hK⟩ := Cprime_values (q := 2) le_rfl hL
  refine ⟨ζbar, hζ, max K 0, le_max_right _ _, fun N R _ _ hP hN hm0 hm hρ k hk1 hkN hV t => ?_⟩
  have hz := (hist_dData_hyps R hP hV t).1
  rw [Z_mul_gamInt R hV t]
  have h := (hK (L ^ N) N R.msq (zh R k t) hN rfl hm0 hm (fun i => (hz i).trans hρ) k hk1 hkN).1
  have hM := (dData L N R.msq (zh R k t)).Mz_nonneg (k + 1)
  have h2 : K * (dData L N R.msq (zh R k t)).Mz (k + 1) ≤
      max K 0 * (dData L N R.msq (zh R k t)).Mz (k + 1) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  exact h.trans (by linarith only [h2])

set_option maxHeartbeats 4000000 in
/-- **`thm_flow_final_Z` with the magnetisation sum and the running coupling** (`sec:spin` (ii),
`thm:beta`): the conclusions of `thm_flow_final_Z`, and `SpinSum`, `BetaAsym` along the
admissible trajectories, with one set of constants. -/
theorem thm_flow_final_spin : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke KZ : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ KZ ∧ ε ≤ 1 ∧
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
            KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) := by
  obtain ⟨L₀, hL₀⟩ := flow_finalZ_hyp0_zeta
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, CL, aB, AZ, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe,
    hCL, hcgε, he, ha0, hs, hC, hρ8, hcov, hAZ, hε1, h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
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
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    hε1, fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  have hc : FinConstZ L ρ κ cg cm cT ε CL aB := ⟨hρ, hρ8, hcov, hε, hcgε, he, ha0, hs, hC⟩
  have hmass : ∀ m ∈ mRange L N, m * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ 1 := fun m hm => by
    have := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simpa using this
  have hyp : ∀ m ∈ mRange L N, FinHypZ (R.withMsq m) Nh κ cg cm cT ε CL aB
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact ⟨hV, H, HZ, HM, HD, e,
      { hc := hcg.le, he := he0
        hE := sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej
        F1s := F1s }⟩
  obtain ⟨c1, c2⟩ := flow_finalZ_of hc R hP hRρ hN (by omega) le_rfl hyp
  have hLS : ∀ m ∈ mRange L N, LogSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact logSum_of H he hε1 hcgε he0 heb
      (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
  have hSS : ∀ m ∈ mRange L N, SpinSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact spinSum_of H he hε1 hcgε he0 heb
      (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
  have hBA : ∀ m ∈ mRange L N, BetaAsym (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
      (eRange (betaL L) Ke 1) := fun m hm => by
    obtain ⟨e, -, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩ :=
      h N (R.withMsq m) hP hi0 hRℓ hRA hRρ hN hm.1 hm.2 Nh hNh
    exact betaAsym_of H he hε1 hcgε he0 heb
      (sum_e_le hL2 hm.1.le hKe H.hβ.le he0 (hmass m hm) heb hej) F1s
  refine ⟨c1, c2, hLS, hSS, hBA, fun m hm b μ₀ hadm n hn => ?_⟩
  obtain ⟨e, hZs, hV, HD, H, HZ, HM, he0, F1s, heb, hej⟩ :=
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

/-- `a_k ≤ 2` below the horizon. -/
theorem zA_le_two {L : ℕ} (hL : (1 : ℝ) ≤ L) {m : ℝ} {k : ℕ}
    (hm : m * ((L : ℝ) ^ (k + 1)) ^ 2 ≤ 1) : zA L m k ≤ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [zA_zero]; norm_num
  rw [zA_pos L m hk]
  have h1 : (((L : ℝ) ^ k) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_pow₀ hL))
  linarith

/-- The constant of the `Γ^int` hypothesis in `prop_gamma_M`. -/
def gamK (L : ℕ) (KZ KG Kp : ℝ) : ℝ :=
  (1 + (KZ + Kp) * Real.exp KZ) * KG + Real.log L / (2 * Real.pi) * ((KZ + Kp) * Real.exp KZ)

/-- The constant of `prop_gamma_M`. -/
def spinMK (L : ℕ) (cg Ke KZ Kl KG Kp : ℝ) : ℝ :=
  spinTrajK (betaL L) cg (Kl * (Real.log L / (2 * Real.pi) + 3 * gamK L KZ KG Kp) +
    gamK L KZ KG Kp) (eRange (betaL L) Ke 1) 4

set_option maxHeartbeats 1000000 in
/-- **`prop:gamma` (ii), the magnetisation** (`sec:spin`): `M_j = ϑ_j(1 + O(β_j^{-1}))` with
`ϑ_j = (β_j/β_ε)^{1/3}`, conditional on the vertex asymptotics `λ̂_k`, the value of
`C'_{k+1}(0,0) = Z_{k+1}Γ^int_{k+1}(0,0)` and the phase of `Z_{k+1}` along the trajectory. -/
theorem prop_gamma_M : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke KZ : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ KZ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
    ∀ m ∈ mRange L N, ∀ b μ₀, Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ (lam : ℕ → ℂ) (Kl KG Kp : ℝ), 0 ≤ Kl → 0 ≤ KG → 0 ≤ Kp →
      -- the vertex: `λ̂_k = (β_ε/β_k)^{1/3}(1 + O(ǧ_k + a_k))`
      (∀ k < Nh, ‖lam k - ((((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
        Kl * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 / b) ^ (1 / 3 : ℝ) *
          ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) →
      -- the value of `C'_{k+1}(0,0)`
      (∀ k < Nh, ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z *
          GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) -
          (Real.log L / (2 * Real.pi) : ℝ)‖ ≤
        KG * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k)) →
      -- the phase of `Z_{k+1}`
      (∀ k < Nh, ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z -
          (‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ : ℂ)‖ ≤
        Kp * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 *
          ‖(rawHist (R.withMsq m) (k + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖) →
      ∀ j ≤ Nh,
        ‖(1 - (b : ℂ) * ∑ k ∈ range j,
            lam k * GamInt (R.withMsq m) k (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)) -
          (((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
        spinMK L cg Ke KZ Kl KG Kp * (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1) ^ (1 / 3 : ℝ) *
          (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_final_spin
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    hε1, h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
  obtain ⟨c1, -, -, hSS, -, hZ⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  refine ⟨c1, fun m hm b μ₀ hadm lam Kl KG Kp hKl hKG hKp hl hG hph j hj => ?_⟩
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

end

end Spin2
