import Ward.ObsLimit
import FRD.Green

/-!
# The value of `γ^{(2)}_{a,∞}` at `m² = 0`

`|GamA(0, b₀) - G_{ℤ^d}(0)| ≤ K |b₀|` (`GamA_zero_sub_green`), with `G_{ℤ^d} = FRD.greenZd`.

At `m² = 0` the covariance of step `j` at the centre is `c_{j+1}(0)` of `ℤ^d`, independently of
the torus (`FRD.Cj_eq_Zd`, `covAt_diag_zero`), and `∑_j c_{j+1}(0) = G_{ℤ^d}(0)`
(`FRD.hasSum_covZ_green`).  The step `γ`-increments are `λ_{a,j+1} c_{j+1}(0) + O(ℓ_j² E θ^j)`
with `|λ_{a,j+1}/λ̄ - 1| ≤ C_S C |b₀|/(1-θ)` and `|c_{j+1}(0)| ≤ ℓ_{j+1}^2`.
-/

namespace Ward

noncomputable section

open Finset Grassmann Loc Step Obs FRD PtCorr Metric Filter Topology

variable {d L : ℕ} [NeZero L] {A ℓ₀ lbar C κ : ℝ} {V₀c : ℝ → ℂ → Vcoup}

variable (d L) in
/-- `c_{j+1}(0)`: the `ℤ^d` covariance of scale `j + 1` at `0`, `m² = 0`. -/
def cZ (j : ℕ) : ℝ := covZ stdPt d 0 (Set.Ioc (lowEnd (L : ℝ) (j + 1)) ((L : ℝ) ^ (j + 1) / 2)) 0

theorem rep_zero' {N : ℕ} : rep (0 : Lam d L N) = 0 := by
  have hp := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) N
  have hz : supNormZ (0 : Zd d) = 0 := by simp [supNormZ]
  exact (eq_rep prj_zero (by rw [hz]; omega)).symm

/-- At `m² = 0`, the diagonal of the covariance of step `j` on `Λ_N`, `j + 2 ≤ N`, is `c_{j+1}(0)`. -/
theorem covAt_diag_zero (hd : 1 ≤ d) (hL : 2 ≤ L) {N j : ℕ} (hj : j + 2 ≤ N) (x : Lam d L N) :
    Flow.covAt d L N 0 j x x = cZ d L j := by
  rw [Flow.covAt_lt (by omega)]
  show Cj stdPt 0 (L : ℝ) (j + 1) x x = _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hn : (L : ℝ) ^ (j + 1) < ((L ^ N : ℕ) : ℝ) := by
    have h1 : L ^ (j + 1) < L ^ N := Nat.pow_lt_pow_right (by omega) (by omega)
    exact_mod_cast h1
  rw [Cj_eq_Zd stdPt le_rfl hd hL0 (j + 1) hn x x, sub_self, rep_zero']
  rfl

variable (H : ObsLimHyp d L A ℓ₀ V₀c lbar C κ) (hd : 1 ≤ d) {Cs : ℝ} (hCs : 0 ≤ Cs)
  (hS : StepBd d L A ℓ₀ V₀c lbar C κ Cs)
include H hd hCs hS

theorem lA_sub_lbar {msq : ℝ} (hmsq : 0 ≤ msq) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) (j : ℕ) :
    ‖lA d L V₀c lbar msq b₀ j - lbar‖ ≤ Cs * (C * lbar * ‖b₀‖) / (1 - th L κ) := by
  obtain ⟨hθ0, hθ1, -⟩ := th_facts H hd hCs hS
  have h1 := norm_sub_le_geom_tail (lA d L V₀c lbar msq b₀) (mul_nonneg hCs (E_nonneg H hd hCs hS b₀))
    hθ0 hθ1 (Nat.zero_le j) (fun k _ _ =>
      (lA_succ H hd hCs hS hmsq hb₀ k).trans (le_of_eq (by ring)))
  rw [pow_zero, mul_one] at h1
  have h0 : lA d L V₀c lbar msq b₀ 0 = lbar := rfl
  rw [h0, norm_sub_rev] at h1
  exact h1

/-- **`γ^{(2)}_{a,∞}(0) = G_{ℤ^d}(0) + O(b₀)`**. -/
theorem GamA_zero_sub_green (hd3 : 3 ≤ d) {b₀ : ℂ} (hb₀ : ‖b₀‖ ≤ lbar) :
    ‖GamA d L V₀c lbar 0 b₀ - (greenZd d 0 : ℂ)‖ ≤
      Cs * C * ℓ₀ ^ 2 * (1 + 1 / (1 - th L κ)) / (1 - rho d L) * ‖b₀‖ := by
  have hd2 : 2 ≤ d := by omega
  have hL3 := three_le_L H
  have hlb := H.fd.lbar_pos
  have hC0 := H.fd.C_nonneg
  obtain ⟨hθ0, hθ1, -⟩ := th_facts H hd hCs hS
  have h1θ : 0 < 1 - th L κ := by linarith
  have hρ0 := rho_nonneg d L
  have hρ1 := rho_lt_one hd3 (by omega) (L := L)
  have hl : (lbar : ℂ) ≠ 0 := by exact_mod_cast hlb.ne'
  -- the step bound at `(ctr, 0)` on `Λ_{j+3}`
  have hstep : ∀ j, ‖gA d L V₀c lbar 0 b₀ j / lbar - (cZ d L j : ℂ)‖ ≤
      Cs * C * ℓ₀ ^ 2 * (1 + 1 / (1 - th L κ)) * ‖b₀‖ * rho d L ^ j := by
    intro j
    have hne := ctr_ne_zero hd hL3 (N := j + 3) (by omega)
    have hg := (hS 0 le_rfl b₀ hb₀ (j + 3) 0 hne j (by omega)).2.2.1
    rw [(lA_char H hd le_rfl hb₀ (N := j + 3) (j := j) (by omega) 0).2,
      (lA_char H hd le_rfl hb₀ (N := j + 3) (j := j + 1) (by omega) 0).1,
      covAt_diag_zero hd (by omega) (N := j + 3) (j := j) (by omega)] at hg
    have hc : ‖(cZ d L j : ℂ)‖ ≤ ℓ₀ ^ 2 * rho d L ^ j := by
      have := abs_cov_le H.fd.hℓ₀ (H.fd.good (j + 3) 0 le_rfl j (by omega)) (ctr d L (j + 3))
        (ctr d L (j + 3))
      rw [covAt_diag_zero hd (by omega) (N := j + 3) (j := j) (by omega)] at this
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine this.trans ?_
      rw [ellj_sq, pow_succ]
      have := rho_le_one hd2 L
      have h2 : 0 ≤ rho d L ^ j := pow_nonneg hρ0 j
      calc ℓ₀ ^ 2 * (rho d L ^ j * rho d L) ≤ ℓ₀ ^ 2 * (rho d L ^ j * 1) := by gcongr
        _ = _ := by ring
    have hlA := lA_sub_lbar H hd hCs hS le_rfl hb₀ (j + 1)
    have e : gA d L V₀c lbar 0 b₀ j / lbar - (cZ d L j : ℂ) =
        (gA d L V₀c lbar 0 b₀ j - lA d L V₀c lbar 0 b₀ (j + 1) * (cZ d L j : ℂ)) / lbar +
          (lA d L V₀c lbar 0 b₀ (j + 1) - lbar) / lbar * (cZ d L j : ℂ) := by
      field_simp; ring
    have hθj : th L κ ^ j ≤ 1 := pow_le_one₀ hθ0 hθ1.le
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_mul, norm_div, norm_lbar H]
    have ha : ‖gA d L V₀c lbar 0 b₀ j - lA d L V₀c lbar 0 b₀ (j + 1) * (cZ d L j : ℂ)‖ / lbar ≤
        Cs * C * ℓ₀ ^ 2 * ‖b₀‖ * rho d L ^ j := by
      rw [div_le_iff₀ hlb]
      refine hg.trans ?_
      rw [ellj_sq]
      have : 0 ≤ Cs * (ℓ₀ ^ 2 * rho d L ^ j) * (C * lbar * ‖b₀‖) := by positivity
      calc Cs * (ℓ₀ ^ 2 * rho d L ^ j) * (C * lbar * ‖b₀‖ * th L κ ^ j)
          ≤ Cs * (ℓ₀ ^ 2 * rho d L ^ j) * (C * lbar * ‖b₀‖ * 1) := by gcongr
        _ = _ := by ring
    have hb : ‖lA d L V₀c lbar 0 b₀ (j + 1) - lbar‖ / lbar * ‖(cZ d L j : ℂ)‖ ≤
        Cs * C * ℓ₀ ^ 2 * (1 / (1 - th L κ)) * ‖b₀‖ * rho d L ^ j := by
      have h1 : ‖lA d L V₀c lbar 0 b₀ (j + 1) - lbar‖ / lbar ≤ Cs * C * ‖b₀‖ / (1 - th L κ) := by
        rw [div_le_iff₀ hlb]
        refine hlA.trans (le_of_eq ?_)
        ring
      calc ‖lA d L V₀c lbar 0 b₀ (j + 1) - lbar‖ / lbar * ‖(cZ d L j : ℂ)‖
          ≤ Cs * C * ‖b₀‖ / (1 - th L κ) * (ℓ₀ ^ 2 * rho d L ^ j) :=
            mul_le_mul h1 hc (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc _ ≤ Cs * C * ℓ₀ ^ 2 * ‖b₀‖ * rho d L ^ j +
          Cs * C * ℓ₀ ^ 2 * (1 / (1 - th L κ)) * ‖b₀‖ * rho d L ^ j := add_le_add ha hb
      _ = _ := by ring
  -- the two series
  have hsA : HasSum (fun j => gA d L V₀c lbar 0 b₀ j / lbar) (GamA d L V₀c lbar 0 b₀) := by
    rw [GamA]
    exact (gA_summable H hd hCs hS hd2 hd3 le_rfl hb₀).hasSum.div_const _
  have hsG : HasSum (fun j => (cZ d L j : ℂ)) (greenZd d 0 : ℂ) :=
    Complex.hasSum_ofReal.2 (hasSum_covZ_green stdPt hd3 (by exact_mod_cast (by omega : 1 < L)) 0)
  have hsum := hsA.sub hsG
  rw [← hsum.tsum_eq]
  refine (tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hρ0 hρ1).mul_left
    (Cs * C * ℓ₀ ^ 2 * (1 + 1 / (1 - th L κ)) * ‖b₀‖)) hstep).trans (le_of_eq ?_)
  ring

end

end Ward
