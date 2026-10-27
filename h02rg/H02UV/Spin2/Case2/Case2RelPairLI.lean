import Step2.Flow.FlowMasterHypLZ
import Spin2.Case2.Case2RelPairL

/-!
# The increment of `ǧ` along the admissible trajectories; `thm_case2_pairLI`

* `GIncConcl`: `ǧ_k + (β/4)ǧ_k² ≤ ǧ_{k+1}` for `k < N_h` along every admissible trajectory
  (from the band (F1), `gIncConcl_of`, the same proof as `gMonoConcl_of`).
* `sum_gsq_le_of_inc`: then `∑_{k<N_h} ǧ_k² ≤ 4/β` (`Step2.sum_sq_le`, `ǧ ≤ ε ≤ 1`).
* **`thm_case2_pairLI`**: `thm_case2_pairL` with, in addition, `GIncConcl` for the same constants.
  The proof is a copy of that of `thm_case2_pairL` (one extra conjunct).
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

/-- **The increment of `ǧ`**: `ǧ_k + (β/4)ǧ_k² ≤ ǧ_{k+1}` for `k < N_h`. -/
def GIncConcl (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ →
    ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 +
        betaL L / 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1

/-- `GIncConcl` along every trajectory in `D_ε` up to `N_h` (route (a1); no final condition). -/
def GIncConclD (L : ℕ) [NeZero L] (ℓ A ρ κ cm cT ε : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
    R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
  ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
    (∀ j ≤ Nh, InD3 ((L : ℝ) ^ 2) κ cm cT ε (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j)) →
    ∀ k < Nh, (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 +
        betaL L / 4 * (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ^ 2 ≤
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1

theorem GIncConclD.adm {L : ℕ} [NeZero L] {ℓ A ρ κ cm cT ε : ℝ}
    (h : GIncConclD L ℓ A ρ κ cm cT ε) : GIncConcl L ℓ A ρ κ cm cT ε := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm
  exact h N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hadm.1

/-- `GIncConcl` from the band (F1) (`cg·ε ≤ 1/6`); same proof as `gMonoConcl_of`. -/
theorem gIncConcl_ofD {L : ℕ} [NeZero L] (hL8 : 8 ≤ L) {ℓ A ρ κ cg cm cT ε : ℝ} (hcg : 0 ≤ cg)
    (hF1 : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
      cg * ε ≤ 1 / 6 ∧ BandF1 (R.withMsq m) Nh κ cg cm cT ε) :
    GIncConclD L ℓ A ρ κ cm cT ε := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN Nh hNh m hm b μ₀ hD k hk
  obtain ⟨h6, hB⟩ := hF1 N R hP hi0 hRℓ hRA hRρ hN Nh hNh m hm
  have ht := inDh_rg_of_D (R.withMsq m) hB hD Nh le_rfl
  have hr := ht.2 k hk
  obtain ⟨hg, hgε, -, -⟩ := ht.1 k hk.le
  have hβ2 := betaL_ge hL8
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1
  set g' := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (k + 1)).1
  have hr' : |g' - g - betaL L * g ^ 2| ≤ 1 / 2 * betaL L * g ^ 2 + cg * g ^ 3 := hr
  have h3 : cg * g ^ 3 ≤ 1 / 6 * g ^ 2 := by
    have : cg * g ≤ cg * ε := mul_le_mul_of_nonneg_left hgε hcg
    have e : cg * g ^ 3 = (cg * g) * g ^ 2 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_right (this.trans h6) (sq_nonneg _)
  have h4 : 1 / 6 * g ^ 2 ≤ 1 / 4 * betaL L * g ^ 2 := by
    have := sq_nonneg g
    nlinarith
  have h5 := neg_abs_le (g' - g - betaL L * g ^ 2)
  have e : betaL L / 4 * g ^ 2 = 1 / 4 * betaL L * g ^ 2 := by ring
  rw [e]
  linarith

/-- Corollary of `gIncConcl_ofD`. -/
theorem gIncConcl_of {L : ℕ} [NeZero L] (hL8 : 8 ≤ L) {ℓ A ρ κ cg cm cT ε : ℝ} (hcg : 0 ≤ cg)
    (hF1 : ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N → ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N,
      cg * ε ≤ 1 / 6 ∧ BandF1 (R.withMsq m) Nh κ cg cm cT ε) :
    GIncConcl L ℓ A ρ κ cm cT ε :=
  (gIncConcl_ofD hL8 hcg hF1).adm

/-- `∑_{k<N_h} ǧ_k² ≤ 4/β` from the increment, `ǧ_0 > 0` and `ǧ_{N_h} ≤ 1`. -/
theorem sum_gsq_le_of_inc {g : ℕ → ℝ} {β : ℝ} (hβ : 0 < β) {Nh : ℕ}
    (hinc : ∀ k < Nh, g k + β / 4 * g k ^ 2 ≤ g (k + 1)) (h0 : 0 ≤ g 0) (hN : g Nh ≤ 1) :
    ∑ k ∈ range Nh, g k ^ 2 ≤ 4 / β := by
  have hβ' : 0 < β / 4 := by linarith
  have h1 := Step2.sum_sq_le hβ' Nh hinc
  refine h1.trans ?_
  rw [div_le_div_iff₀ hβ' hβ]
  nlinarith

end

end Spin2
