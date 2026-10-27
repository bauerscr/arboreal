import Obs2.Flow.Gamma1
import Step2.Flow.ZetaSharpThm

/-!
# Proposition `prop:gamma` along the final flow (conditional on the observable remainders)

`prop_gamma`: with the constants of `Step2.thm_flow_final_Z` (independent of `N`, `m²`, `N_h`),
along every admissible trajectory of the final flow (`b ∈ (0, ε]`, `β_ε = 1/b`, `β_n = 1/ǧ_n`):

* **(Z), unconditional**: `|log|Z_{n+1}| - (1/3) log(β_n/β_ε)| ≤ K_Z/β_n` for `n ≤ N_h`;
* **(λ), conditional**: every vertex sequence with `λ_{k+1} = λ_k(1 + x_k)`,
  `|x_k| ≤ min(1/4, B' ǧ_k)`, `q_0 = 0`, `|q_k| ≤ c_q ǧ_k` and
  `|Re x_k - s(β/3) ǧ_k + (q_{k+1} - q_k)| ≤ B(ǧ_k² + ǧ_k a_k)` (the flow equations of
  `μ^{(1)}` (`s = 0`) and `μ^{(2)}` (`s = 1`) with an `O(ḡ²)` remainder) satisfies
  `|log(|λ_n|/|λ_0|) - (s/3) log(β_ε/β_n)| ≤ K_λ/β_n`;
* **(ϑ), conditional**: for Case 1 (`s = 0`), `ϑ^{(1)}_n = (β_n/(β_ε |Z_{n+1}|))^{1/2} |λ_n/λ_0|`
  satisfies `|log ϑ^{(1)}_n - (1/3) log(β_n/β_ε)| ≤ (K_Z/2 + K_λ)/β_n`.

`K_λ = logTrajK β c_g (B + 7B'²) (|s|/3) + 4(B + 7B'²) + (|s|/3) 2(1+β) e_R + c_q`. All
relative errors are `O(β_n^{-1})` with constants depending on `L` (and on `B, B', c_q`); the
`j = 0` step and the summable `L^{-2j}`, `m² L^{2(j+1)}` errors are included (`a_0 = 1`,
`∑ a_k ≤ 4`, `∑ e_k ≤ e_R`). The magnetisation route (ii) of `prop:gamma` is not formalised.
-/

namespace Obs2

open Finset Step Step2 Flow2 Flow2.Hist Loc FRD Step2.D2

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **Proposition `prop:gamma`** (the `Z` part unconditional; the vertex parts conditional on the
per-step remainder bound). -/
theorem prop_gamma : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke KZ : ℝ, 0 < ℓ ∧ 0 < A ∧ 0 < ρ ∧ 0 < ε ∧ 0 ≤ κ ∧ κ < 1 ∧
      0 < cg ∧ 0 < cm ∧ 0 < cT ∧ 0 ≤ Ke ∧ 0 ≤ KZ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 1 ≤ N →
    ∀ Nh : ℕ, Nh + 2 ≤ N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
      -- (Z)
      (∀ n ≤ Nh,
        |Real.log ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖ -
            1 / 3 * Real.log (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1)| ≤
          KZ * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ∧
      -- (λ)
      (∀ (lam x : ℕ → ℂ) (q : ℕ → ℝ) (s B B' cq : ℝ), 0 ≤ B → lam 0 ≠ 0 →
        (∀ k < Nh, lam (k + 1) = lam k * (1 + x k)) → (∀ k < Nh, ‖x k‖ ≤ 1 / 4) →
        (∀ k < Nh, ‖x k‖ ≤ B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) → q 0 = 0 →
        (∀ k ≤ Nh, |q k| ≤ cq * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) →
        (∀ k < Nh, |(x k).re - s * (betaL L / 3) * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 +
            (q (k + 1) - q k)| ≤ B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
              B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k) →
        ∀ n ≤ Nh, |Real.log (‖lam n‖ / ‖lam 0‖) -
            s / 3 * Real.log ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1 / b)| ≤
          (logTrajK (betaL L) cg (B + 7 * B' ^ 2) (|s| / 3) + (B + 7 * B' ^ 2) * 4 +
            |s| / 3 * (2 * (1 + betaL L) * eRange (betaL L) Ke 1) + cq) *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) ∧
      -- (ϑ), Case 1
      (∀ (lam x : ℕ → ℂ) (q : ℕ → ℝ) (B B' cq : ℝ), 0 ≤ B → lam 0 ≠ 0 →
        (∀ k < Nh, lam (k + 1) = lam k * (1 + x k)) → (∀ k < Nh, ‖x k‖ ≤ 1 / 4) →
        (∀ k < Nh, ‖x k‖ ≤ B' * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) → q 0 = 0 →
        (∀ k ≤ Nh, |q k| ≤ cq * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1) →
        (∀ k < Nh, |(x k).re + (q (k + 1) - q k)| ≤
            B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 +
              B * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 * zA L m k) →
        ∀ n ≤ Nh,
          |Real.log (Real.sqrt ((b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) /
              ‖(rawHist (R.withMsq m) (n + 1) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀)).Z‖) *
              (‖lam n‖ / ‖lam 0‖)) -
            1 / 3 * Real.log (b / (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1)| ≤
          (KZ / 2 + (logTrajK (betaL L) cg (B + 7 * B' ^ 2) 0 + (B + 7 * B' ^ 2) * 4 + cq)) *
            (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ n).1) := by
  obtain ⟨L₀, hL₀⟩ := thm_flow_final_Z
  refine ⟨max L₀ 2, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    h⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, KZ, hℓ, hA, hρ, hε, hκ0, hκ1, hcg, hcm, hcT, hKe, hKZ,
    fun N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm => ?_⟩
  obtain ⟨-, -, hLS, hZ⟩ := h N R hP hi0 hRℓ hRA hRρ hN Nh hNh
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast le_trans (le_max_right _ _) hL
  have hβ : 0 < betaL L := by
    unfold betaL
    have : 0 < Real.log L := Real.log_pos (by linarith only [hL2])
    have := Real.pi_pos
    positivity
  set t := traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ with ht
  have hg : ∀ n ≤ Nh, 0 < (t n).1 := fun n hn => (hadm.1 n hn).1
  have hb : 0 < b := by have := hg 0 (Nat.zero_le _); rwa [ht, Hist.traj_zero] at this
  have hlogi : ∀ n ≤ Nh, Real.log (b / (t n).1) = -Real.log ((t n).1 / b) := fun n hn => by
    rw [← Real.log_inv, inv_div]
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hsa : ∀ n ≤ Nh, ∑ k ∈ range n, zA L m k ≤ 4 := fun n hn => by
    have := sum_zA_le (Ln := L) rfl hL2 hm.1.le n
    linarith only [this, hmn n hn]
  -- (λ)
  have hlam : ∀ (lam x : ℕ → ℂ) (q : ℕ → ℝ) (s B B' cq : ℝ), 0 ≤ B → lam 0 ≠ 0 →
      (∀ k < Nh, lam (k + 1) = lam k * (1 + x k)) → (∀ k < Nh, ‖x k‖ ≤ 1 / 4) →
      (∀ k < Nh, ‖x k‖ ≤ B' * (t k).1) → q 0 = 0 → (∀ k ≤ Nh, |q k| ≤ cq * (t k).1) →
      (∀ k < Nh, |(x k).re - s * (betaL L / 3) * (t k).1 + (q (k + 1) - q k)| ≤
          B * (t k).1 ^ 2 + B * (t k).1 * zA L m k) →
      ∀ n ≤ Nh, |Real.log (‖lam n‖ / ‖lam 0‖) - s / 3 * Real.log ((t n).1 / b)| ≤
        (logTrajK (betaL L) cg (B + 7 * B' ^ 2) (|s| / 3) + (B + 7 * B' ^ 2) * 4 +
          |s| / 3 * (2 * (1 + betaL L) * eRange (betaL L) Ke 1) + cq) * (t n).1 := by
    intro lam x q s B B' cq hB hl0 hrec hx4 hxg hq0 hq hre n hn
    have key := lam_ratio (hLS m hm) hβ hadm hB (zA_nonneg L hm.1.le) hl0 hrec hx4 hxg hq0 hq
      hre n hn
    refine key.trans (mul_le_mul_of_nonneg_right ?_ (hg n hn).le)
    have := mul_le_mul_of_nonneg_left (hsa n hn) (by positivity : (0 : ℝ) ≤ B + 7 * B' ^ 2)
    linarith only [this]
  refine ⟨fun n hn => ?_, hlam, ?_⟩
  · have := (hZ m hm b μ₀ hadm n hn).2
    rw [hlogi n hn]
    have e : Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ - 1 / 3 * -Real.log ((t n).1 / b) =
        Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ + 1 / 3 * Real.log ((t n).1 / b) := by ring
    rw [mul_neg, sub_neg_eq_add]; exact this
  · intro lam x q B B' cq hB hl0 hrec hx4 hxg hq0 hq hre n hn
    have h1 := hlam lam x q 0 B B' cq hB hl0 hrec hx4 hxg hq0 hq
      (fun k hk => by simpa using hre k hk) n hn
    simp only [zero_div, zero_mul, sub_zero, abs_zero, add_zero] at h1
    obtain ⟨hZne, hZn⟩ := hZ m hm b μ₀ hadm n hn
    have hZ' : |Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ -
        1 / 3 * Real.log (b / (t n).1)| ≤ KZ * (t n).1 := by
      rw [hlogi n hn]
      have e : Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ - 1 / 3 * -Real.log ((t n).1 / b) =
          Real.log ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ + 1 / 3 * Real.log ((t n).1 / b) := by
        ring
      rw [mul_neg, sub_neg_eq_add]; exact hZn
    have hZpos : 0 < ‖(rawHist (R.withMsq m) (n + 1) t).Z‖ := norm_pos_iff.2 hZne
    have hne := lam_ne_zero hl0 hrec hx4
    have hlpos : 0 < ‖lam n‖ / ‖lam 0‖ :=
      div_pos (norm_pos_iff.2 (hne n hn)) (norm_pos_iff.2 hl0)
    have h1' := h1
    exact theta_one hZpos hlpos (div_pos hb (hg n hn)) hZ' h1'

end

end Obs2
