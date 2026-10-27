import Spin2.Pair.PairPR5b
import Spin2.Case2.Case2RelPairLI
import PtCorr2.Pair.PairZero

/-!
# PR6: `PairZeroRelR` from the last-scale components and `PairRRelR`

Pair observable `z̃_0z̃_x`, `j = j_x`, `M = M_j`, `ǧ = ǧ_j`. The final objects `F_N` (original pair
history, `zFin`) and `F'_N` (reduced history, `zFinR`) at the last scale are
`∏_BĨ_N(B) + K_N(Λ)` (`PtCorr2.finO_last`), and exactly (`PtCorr2.finO_last_a`,
`PtCorr2.finO_last_ab`)

  `c2(F_N)_a = β_N·P₀ + remCa`,  `c2(F'_N)_{ab} = r'_N·P'₀ + remCab`,

with `β_N`, `r'_N` the couplings produced by the last step, `P₀ = ∏_B(1 + ε𝒲_N(B)_∅)` (`zP0`), and
remainders that contain only the observable parts of `𝒲_N`, `K_N` (they vanish without
`σ_aσ_b` activity: `PtCorr2.finO_last_ab_noAct`). The constant parts `ε(F_N)_a`, `ε(F'_N)_{ab}` are
pure activity terms.

**Named input `PairZeroRemR e₁ e₂ e₃`** (the last-step remainders, relative to the coupling
`β_{a,N-1} = betaTot2 (N_h+1) (lV …)` of `PairRRelR`):
* `P₀ ≠ 0`, `‖c2(F_N)_a - β_{a,N-1}P₀‖ ≤ ½‖β_{a,N-1}‖‖P₀‖` (one-point history: the last-step flow of
  `β_a` and the `𝒲_a`, `K_a` terms);
* `‖c2(F'_N)_{ab} - r'_{N-1}P₀‖ ≤ e₁‖M‖ǧ‖β_{a,N-1}‖‖P₀‖` (`r'_{N-1} = rRN`; the last-step source of
  `r'` and the `σ_aσ_b` activity of the reduced history — the `w_{ab} > 0` layer);
* `‖ε(F'_N)_{ab}‖ ≤ e₂‖M‖²ǧ‖s‖` (reduced `σ_aσ_b` activity) and `‖ε(F_N)_a‖ ≤ e₃‖M‖‖s‖`
  (one-point activity), `s = ε(F_N)_∅ - c·c2(F_N)_∅ = s_∅(Ω)`.

**`pairZeroRelR_of`**: `PairRRelR c_r` (in particular `‖r'_{N-1}‖ ≤ c_r‖M‖ǧ‖β_{a,N-1}‖`),
`β_{a,N-1} ≠ 0`, `PairZeroRemR e₁ e₂ e₃` give `PairZeroRelR (e₂ + 2(c_r+e₁)e₃) (2(c_r+e₁))`, with
`ρ̃ = c2(F'_N)_{ab}/c2(F_N)_a ≈ r'_{N-1}/β_{a,N-1}`. `β_{a,N-1} ≠ 0` comes from `hBeta_rel_of`
(`betaN_ne_of`).
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2

variable {L N : ℕ} [NeZero L]

/-- **Zero-mode relative bound** (pure). From `‖y_a - βP₀‖ ≤ ½‖β‖‖P₀‖`,
`‖y_{ab} - rP₀‖ ≤ e₁Mg‖β‖‖P₀‖`, `‖r‖ ≤ c_rMg‖β‖`, `‖x_{ab}‖ ≤ e₂M²g‖s‖`, `‖x_a‖ ≤ e₃M‖s‖`:
`ρ = y_{ab}/y_a` has `y_{ab} = ρy_a`, `‖ρ‖ ≤ 2(c_r + e₁)Mg` and
`‖x_{ab} - ρx_a‖ ≤ (e₂ + 2(c_r + e₁)e₃)M²g‖s‖`. -/
theorem zero_rel_pure {ya yab xa xab s β r P0 : ℂ} {cr e1 e2 e3 M g : ℝ} (hβ : β ≠ 0)
    (hP : P0 ≠ 0) (hM : 0 ≤ M) (hg : 0 ≤ g) (hcr : 0 ≤ cr) (he1 : 0 ≤ e1)
    (h1 : ‖ya - β * P0‖ ≤ 1 / 2 * ‖β‖ * ‖P0‖) (h2 : ‖yab - r * P0‖ ≤ e1 * M * g * ‖β‖ * ‖P0‖)
    (hr : ‖r‖ ≤ cr * M * g * ‖β‖) (h3 : ‖xab‖ ≤ e2 * M ^ 2 * g * ‖s‖)
    (h4 : ‖xa‖ ≤ e3 * M * ‖s‖) :
    ∃ ρ : ℂ, yab = ρ * ya ∧ ‖ρ‖ ≤ 2 * (cr + e1) * M * g ∧
      ‖xab - ρ * xa‖ ≤ (e2 + 2 * (cr + e1) * e3) * M ^ 2 * g * ‖s‖ := by
  have hB : 0 < ‖β‖ * ‖P0‖ := mul_pos (norm_pos_iff.2 hβ) (norm_pos_iff.2 hP)
  have hya : 1 / 2 * (‖β‖ * ‖P0‖) ≤ ‖ya‖ := by
    have e : β * P0 = ya - (ya - β * P0) := by ring
    have := norm_sub_le ya (ya - β * P0)
    rw [← e, norm_mul] at this
    linarith
  have hya0 : ya ≠ 0 := fun h => by
    rw [h, norm_zero] at hya; linarith
  have hyab : ‖yab‖ ≤ (cr + e1) * M * g * (‖β‖ * ‖P0‖) := by
    have e : yab = r * P0 + (yab - r * P0) := by ring
    have h5 := norm_add_le (r * P0) (yab - r * P0)
    rw [← e, norm_mul] at h5
    have h6 : ‖r‖ * ‖P0‖ ≤ cr * M * g * ‖β‖ * ‖P0‖ :=
      mul_le_mul_of_nonneg_right hr (norm_nonneg _)
    nlinarith
  have hK : 0 ≤ (cr + e1) * M * g := mul_nonneg (mul_nonneg (by linarith) hM) hg
  have hρ : ‖yab / ya‖ ≤ 2 * (cr + e1) * M * g := by
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hya0)]
    nlinarith
  refine ⟨yab / ya, by field_simp, hρ, ?_⟩
  have h7 : ‖yab / ya * xa‖ ≤ 2 * (cr + e1) * M * g * (e3 * M * ‖s‖) := by
    rw [norm_mul]
    exact mul_le_mul hρ h4 (norm_nonneg _) (by nlinarith)
  calc ‖xab - yab / ya * xa‖ ≤ ‖xab‖ + ‖yab / ya * xa‖ := norm_sub_le _ _
    _ ≤ e2 * M ^ 2 * g * ‖s‖ + 2 * (cr + e1) * M * g * (e3 * M * ‖s‖) := add_le_add h3 h7
    _ = (e2 + 2 * (cr + e1) * e3) * M ^ 2 * g * ‖s‖ := by ring

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- `P₀ = ∏_B(1 + ε𝒲_N(B)_∅)`, the bulk normalisation of the block factors of the last step. -/
def zP0 (Nh : ℕ) (m b μ₀ : ℝ) (x : Lam 2 L N) : ℂ :=
  PtCorr2.blkP0 (blocks (Nh + 1) (univ : Finset (Lam 2 L N)))
    (Obs2.WpO (ptsX x) (Nh + 1) (lC R Nh m b μ₀) (lV R Nh m b μ₀ x) (lW R Nh m b μ₀ x))

/-- **Named input (PR6, the last-step remainders).** Relative to the coupling
`β_{a,N-1} = betaTot2 (N_h+1) (lV …)`: `P₀ ≠ 0`; the `c2` of the `σ_a` component of `F_N` is
`β_{a,N-1}P₀` up to `½‖β_{a,N-1}‖‖P₀‖`; the `c2` of the `σ_aσ_b` component of the reduced `F'_N` is
`r'_{N-1}P₀` up to `e₁‖M‖ǧ‖β_{a,N-1}‖‖P₀‖`; the constants `ε(F'_N)_{ab}`, `ε(F_N)_a` are bounded by
`e₂‖M‖²ǧ‖s‖`, `e₃‖M‖‖s‖`, `s = εF_∅ - c·c2F_∅`. -/
def PairZeroRemR (Nh : ℕ) (m b μ₀ : ℝ) (lam : ℕ → ℂ) (oR : Lam 2 L N → Obs2.ObsSt .two L N)
    (e1 e2 e3 : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    zP0 R Nh m b μ₀ x ≠ 0 ∧
    ‖Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a -
        Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) * zP0 R Nh m b μ₀ x‖ ≤
      1 / 2 * ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖Suscept.c2 (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab -
        rRN R Nh m b μ₀ oR x * zP0 R Nh m b μ₀ x‖ ≤
      e1 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x)‖ * ‖zP0 R Nh m b μ₀ x‖ ∧
    ‖ε (zFinR R Nh m b μ₀ oR x : Obs.SA .two (Lam 2 L N)).ab‖ ≤
      e2 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ ^ 2 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ (Obs.coal L (0 : Lam 2 L N) x)).1 *
        ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e -
          zCc R Nh m b μ₀ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e‖ ∧
    ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).a‖ ≤
      e3 * ‖Mmag R m b μ₀ lam (Obs.coal L (0 : Lam 2 L N) x)‖ *
        ‖ε (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e -
          zCc R Nh m b μ₀ * Suscept.c2 (zFin R Nh m b μ₀ x : Obs.SA .two (Lam 2 L N)).e‖

/-- **`PairZeroRelR` from `PairRRelR` and the last-step remainders** (trajectory level). -/
theorem pairZeroRelR_of {Nh : ℕ} (m b μ₀ : ℝ) (lam : ℕ → ℂ)
    (oR : Lam 2 L N → Obs2.ObsSt .two L N) {cr e1 e2 e3 : ℝ} (hcr : 0 ≤ cr) (he1 : 0 ≤ e1)
    (hg : ∀ k ≤ Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1)
    (hβ : ∀ x : Lam 2 L N, x ≠ 0 → 1 ≤ Obs.coal L (0 : Lam 2 L N) x →
      Obs.coal L (0 : Lam 2 L N) x ≤ Nh → Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0)
    (hR : PairRRelR R Nh m b μ₀ lam oR cr) (hZ : PairZeroRemR R Nh m b μ₀ lam oR e1 e2 e3) :
    PairZeroRelR R Nh m b μ₀ lam oR (e2 + 2 * (cr + e1) * e3) (2 * (cr + e1)) := by
  intro x hx h1 hj
  obtain ⟨hP, k1, k2, k3, k4⟩ := hZ x hx h1 hj
  obtain ⟨ρ, e, hρ, hε⟩ := zero_rel_pure (hβ x hx h1 hj) hP (norm_nonneg _)
    (hg _ hj) hcr he1 k1 k2 (hR x hx h1 hj).2 k3 k4
  exact ⟨ρ, e, hρ, hε⟩

/-- `β_{a,N-1} ≠ 0` from `Case2Rel`, `‖𝔫‖ ≤ 1/8` and `Case2TopStep` (`hBeta_rel_of`). -/
theorem betaN_ne_of {Nh : ℕ} (hN : Nh + 2 = N) {m b μ₀ cδ : ℝ} (hb : 0 < b) (x : Lam 2 L N)
    (hrel : Case2Rel R (ptsX x) (zV b) Nh m b μ₀ cδ)
    (hn : ∀ k < Nh, ‖nn2 R (ptsX x) (zV b) m b μ₀ k‖ ≤ 1 / 8)
    (htop : Case2TopStep R (ptsX x) (zV b) Nh m b μ₀) :
    Obs2.betaTot2 (Nh + 1) (lV R Nh m b μ₀ x) ≠ 0 := by
  rw [(rTilN_eq R Nh m b μ₀ x 0).2]
  exact (hBeta_rel_of R hN hb x hrel hn htop Nh le_rfl).2.1

end Traj

end

end Spin2
