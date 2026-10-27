import Step2.Flow.ZetaSharpHypX
import Step2.Flow.ZetaSharp6
import Step2.Flow.FlowFinalZ

/-!
# The field strength along the final flow: `Z_j = (β_j/β_ε)^{1/3}(1 + O(β_j^{-1}))`

`thm_flow_final_Z`: the statement of `thm_flow_final` (one set of constants for every `N`,
every horizon `N_h + 2 ≤ N`, every mass `0 < m² ≤ L^{-2(N-1)}`) together with the asymptotics of
the field strength along every admissible trajectory: for `n ≤ N_h`,

  `|log|Z_{n+1}| + (1/3) log(ǧ_n/b)| ≤ K_Z ǧ_n`,

with `K_Z` depending only on `L` (and `Z_{n+1} ≠ 0`). In the notation of `prop:gamma` (`β_n = 1/ǧ_n`,
`β_ε = 1/b`): `|Z_{n+1}| = (β_n/β_ε)^{1/3} e^{O(β_n^{-1})}`. Here `Z_{n+1} = Z_n(1 + ζ_n)` is the
normalisation of the couplings of step `n` (`ν = μ Z_{n+1}/L^{2n}`, `g = ǧ Z_{n+1}²/(1+n)`); the
statement is about `|Z|` (the phase of the complex `Z` is not controlled here).

The proof: `flow_finalZ_hyp0_zeta` (the hypothesis package of `thm_flow_final` with the sharp
one-step bound `|log|Z_{k+2}| - log|Z_{k+1}| + (β/3) ǧ_k| ≤ A_Z(ǧ_k² + ǧ_k a_k)`), and
`Flow2.Hist.log_traj` with `σ = β/3` (the band, the summable `e_k`, `∑ a_k ≤ 4`).
The constant is `K_Z = logTrajK β c_g A_Z (1/3) + 4 A_Z + (2/3)(1+β) e_R`, `e_R = eRange β K_e 1`.
The `j = 0` step (no value of `C'_1(e₁,0)`) enters through `a_0 = 1` and the crude `e_0 ≤ β/2`;
both are `O(ǧ_0) ≤ O(ǧ_n)`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- `∑_{k<n} a_k ≤ 2 + 2 m² L^{2n}`. -/
theorem sum_zA_le {L : ℝ} {Ln : ℕ} (hLn : (Ln : ℝ) = L) (hL : 2 ≤ L) {msq : ℝ} (hm : 0 ≤ msq)
    (n : ℕ) : ∑ k ∈ range n, zA Ln msq k ≤ 2 + 2 * (msq * (L ^ n) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot hn, zA_zero, zero_add]
  have e : ∀ k ∈ Finset.Ico 1 n, zA Ln msq k = ((L ^ k) ^ 2)⁻¹ + msq * (L ^ (k + 1)) ^ 2 := by
    intro k hk; rw [zA_pos Ln msq (Finset.mem_Ico.1 hk).1, hLn]
  rw [sum_congr rfl e, sum_add_distrib, ← mul_sum]
  have h1 := geom_inv_le hL n
  have h2 : ∑ k ∈ Finset.Ico 1 n, (L ^ (k + 1)) ^ 2 ≤ ∑ k ∈ range n, (L ^ (k + 1)) ^ 2 := by
    rw [range_eq_Ico]
    exact sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (Nat.zero_le 1))
      (fun _ _ _ => sq_nonneg _)
  have h3 := geom_Lsq_le hL n
  have h4 := mul_le_mul_of_nonneg_left (h2.trans h3) hm
  linarith only [h1, h4]

set_option maxHeartbeats 4000000 in
/-- **Expected result `thm:flow` with the asymptotics of the field strength** (`prop:gamma`,
the `Z_j` part). -/
theorem thm_flow_final_Z : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke KZ : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ KZ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
    ∀ Nh : ℕ, Nh + 2 ≤ N →
      (∀ m ∈ mRange L N, FixedConcl (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
          (eRange (betaL L) Ke 1)) ∧
      MsqConcl R κ cm cT Nh ε (mRange L N) ∧
      (∀ m ∈ mRange L N, LogSum (rgDataM R m) ((L : ℝ) ^ 2) (betaL L) κ cg cm cT Nh ε
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
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh => ?_⟩
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
  refine ⟨c1, c2, hLS, fun m hm b μ₀ hadm n hn => ?_⟩
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
    exact pow_le_pow_left₀ (by positivity)
      (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have h1 := mul_le_mul_of_nonneg_left (hsa.trans (by linarith only [hmn] : 2 + 2 * (m *
    ((L : ℝ) ^ n) ^ 2) ≤ 4)) hAZ
  linarith only [h1]

end

end Step2
