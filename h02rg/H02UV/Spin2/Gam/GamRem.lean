import Spin2.Multiscale.ZBelow3
import Obs2.Flow.GamRem

/-!
# `GamRemRel` from a bulk and an observable relative bound

Along the pair history (`obsInit .two (zV b) (ptsX x)`, `t = traj (rgDataM R m) L² b μ₀`), the
remainder of the `γ_0` flow splits exactly (`Obs2.gamRem2_split_hist`):

  `ρ_k = gamWKX_k + β_k·E_k`,  `E_k = ε(F_{C_k}(ψ̄_0ψ_0, V_{κ'_k}(Λ)))` (`gamBulkT`),

with `β_k = btX = -μ_{0,k}`, `C_k = Γ^{int}_{k+1}` (`histCov_gamInt`) and
`gamWKX_k = ∑_Bε(e^{ℒ_{C_k}}Q_k(B)_0) + ∑_Bε((𝔼θ𝒲_k(B))_0)` (activity and `𝒲^{obs}`).

Named inputs (exactly):
* **`GamBulkRel R N_h m b μ₀ c_e`** (bulk only, independent of `x` and of the observable):
  `∀ k < N_h, ‖E_k‖ ≤ c_e(ǧ_k + a_k)‖Γ^{int}_{k+1}(0,0)‖` (the `ν'`- and gradient lines of the
  one-loop term: `ν'_k∑_xC_k(x,0)C_k(0,x) + …`, relative `O(ǧ_k)`, `Obs2.eps_FC_pbp`);
* **`GamWKRel R N_h m b μ₀ c_w`** (the `ε` analogue of `Case2Rel`, observable sizes relative to
  the vertex): `∀ x ≠ 0, j_x ≤ N_h, k < j_x, ‖gamWKX_k‖ ≤ c_w(ǧ_k + a_k)‖β_k‖‖Γ^{int}_{k+1}(0,0)‖`.

**`gamRemRel_of`**: with (H_λ) for the pair vertex (`K_p`) these give `GamRemRel` with
`c_γ = (c_e + c_w)(1 + 3K_p)` (`|β_k| = b|λ̂_k| ≤ bθ_k(1 + 3K_p)`).
**`twoPtSq_of_gam_flow2`**: `twoPtSq_of_gam_flow` with `GamRemRel` replaced by
`GamBulkRel`, `GamWKRel`.
-/

namespace Spin2

open Step Step2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Step2.D2 Obs

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The bulk one-loop factor `E_k = ε(F_{C_k}(ψ̄_0ψ_0, V_{κ'_k}(Λ)))`. -/
def gamBulkT (m b μ₀ : ℝ) (k : ℕ) : ℂ :=
  ε (FC (Obs2.histCovO (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) (LocObs.pbp 0)
    (Vcoup (Obs2.kapH (R.withMsq m) (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k) univ))

/-- The observable part `∑_Bε(e^{ℒ_C}Q_k(B)_0) + ∑_Bε((𝔼θ𝒲_k(B))_0)` along the pair history. -/
def gamWKX (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.gamWK2 (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- **Named input (bulk)**: `‖E_k‖ ≤ c_e(ǧ_k + a_k)‖Γ^{int}_{k+1}(0,0)‖`. -/
def GamBulkRel (Nh : ℕ) (m b μ₀ ce : ℝ) : Prop :=
  ∀ k < Nh, ‖gamBulkT R m b μ₀ k‖ ≤
    ce * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖gamT R m b μ₀ k‖

/-- **Named input (observable)**: `‖gamWKX_k‖ ≤ c_w(ǧ_k + a_k)‖β_k‖‖Γ^{int}_{k+1}(0,0)‖`. -/
def GamWKRel (Nh : ℕ) (m b μ₀ cw : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ k < Obs.coal L (0 : Lam 2 L N) x, ‖gamWKX R m b μ₀ x k‖ ≤
      cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btX R m b μ₀ x k‖ *
        ‖gamT R m b μ₀ k‖

/-- **`ρ_k = gamWKX_k + β_kE_k`** along the pair history. -/
theorem gamRemX_split {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (x : Lam 2 L N) {k : ℕ} (hk : k < Nh) :
    gamRemX R m b μ₀ x k = gamWKX R m b μ₀ x k + btX R m b μ₀ x k * gamBulkT R m b μ₀ k :=
  Obs2.gamRem2_split_hist (R.withMsq m) (ptsX x) (Obs2.obsInit .two (zV b) (ptsX x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hV (Obs2.obsInit_isObs .two (zV b) (ptsX x))
    (fun b' => Obs2.obsInit_two_form _ _ b') hk

/-- **`GamRemRel` from `GamBulkRel`, `GamWKRel` and (H_λ) for the pair vertex.** -/
theorem gamRemRel_of {Nh : ℕ} {m b μ₀ Kp ce cw : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp) (hce : 0 ≤ ce)
    (hcw : 0 ≤ cw) (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRel R Nh m b μ₀ ce) (hW : GamWKRel R Nh m b μ₀ cw) :
    GamRemRel R Nh m b μ₀ ((ce + cw) * (1 + 3 * Kp)) := by
  intro x hx hj k hk
  have hkN : k < Nh := lt_of_lt_of_le hk hj
  set g := (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 with hgd
  set a := zA L m k with had
  set θ := thJ R m b μ₀ k with hθd
  set β := btX R m b μ₀ x k with hβd
  set Γ := ‖gamT R m b μ₀ k‖ with hΓd
  have hθ : 0 ≤ θ := Real.rpow_nonneg (div_nonneg (hg k hkN).1 hb.le) _
  have hga0 : 0 ≤ g + a := add_nonneg (hg k hkN).1 (ha k hkN).1
  have hga3 : g + a ≤ 3 := by linarith only [(hg k hkN).2, (ha k hkN).2]
  have hΓ : 0 ≤ Γ := norm_nonneg _
  -- `|β| ≤ bθ(1 + 3K_p)`
  have hlh : lamHat2 R (ptsX x) (zV b) m b μ₀ k = β / b := by
    unfold lamHat2; rw [show bt2 R (ptsX x) (zV b) m b μ₀ 0 = btX R m b μ₀ x 0 from rfl, btX_zero]
    rfl
  have h1 := hl x hx k hkN
  rw [hlh] at h1
  have h1' : ‖β / b - ((θ : ℝ) : ℂ)‖ ≤ Kp * θ * (g + a) := h1
  have hβb : ‖β‖ = b * ‖β / b‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb]; field_simp
  have hβ1 : ‖β / b‖ ≤ θ * (1 + 3 * Kp) := by
    have := norm_le_insert' (β / b) ((θ : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ] at this
    have h2 : Kp * θ * (g + a) ≤ Kp * θ * 3 :=
      mul_le_mul_of_nonneg_left hga3 (mul_nonneg hKp hθ)
    nlinarith
  have hβ : ‖β‖ ≤ b * θ * (1 + 3 * Kp) := by
    rw [hβb, mul_assoc]; exact mul_le_mul_of_nonneg_left hβ1 hb.le
  -- the split
  rw [gamRemX_split R hV x hkN]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have hW' := hW x hx hj k hk
  have hB' := hB k hkN
  have e1 : ‖gamWKX R m b μ₀ x k‖ + ‖β‖ * ‖gamBulkT R m b μ₀ k‖ ≤
      (ce + cw) * (g + a) * ‖β‖ * Γ := by
    have := mul_le_mul_of_nonneg_left hB' (norm_nonneg β)
    have e : ‖β‖ * (ce * (g + a) * Γ) = ce * (g + a) * ‖β‖ * Γ := by ring
    have e' : (ce + cw) * (g + a) * ‖β‖ * Γ =
        cw * (g + a) * ‖β‖ * Γ + ce * (g + a) * ‖β‖ * Γ := by ring
    rw [e'] at *
    linarith only [hW', this, e]
  refine e1.trans ?_
  have hc : 0 ≤ (ce + cw) * (g + a) := mul_nonneg (add_nonneg hce hcw) hga0
  calc (ce + cw) * (g + a) * ‖β‖ * Γ ≤ (ce + cw) * (g + a) * (b * θ * (1 + 3 * Kp)) * Γ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hc) hΓ
    _ = (ce + cw) * (1 + 3 * Kp) * θ * (g + a) * (b * Γ) := by ring

end Traj

set_option maxHeartbeats 1000000 in
/-- **`TwoPtSq` from the `γ` flow** (master constants), with `GamRemRel` replaced by the bulk
input `GamBulkRel` and the observable input `GamWKRel`. -/
theorem twoPtSq_of_gam_flow2 {L : ℕ} [NeZero L] {ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG : ℝ}
    (hF : FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb) (hε1 : ε ≤ 1)
    (hL : 2 ^ (2 + 3) + 8 * 2 < L) (hSp : SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG)
    (hMC : MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG) :
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl Kp ce cw Kb KE KR KN KRN : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ ce → 0 ≤ cw →
      0 ≤ Kb →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      GamBulkRel R Nh m b μ₀ ce → GamWKRel R Nh m b μ₀ cw → GamFormB R Nh m b μ₀ Kb →
      PairAboveW1 R Nh m b μ₀ lam KE KR → TwoPtNear (L := L) (N := N) m b μ₀ KN KRN →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      TwoPtSq R Nh m b μ₀ lam
        (max (zbKM L cg Ke KZ KG Kp ((ce + cw) * (1 + 3 * Kp)) Kb Kl *
          (2 + zbKM L cg Ke KZ KG Kp ((ce + cw) * (1 + 3 * Kp)) Kb Kl) + KE) KN)
        (max (1 + 2 * (1 + zbKM L cg Ke KZ KG Kp ((ce + cw) * (1 + 3 * Kp)) Kb Kl) *
          zbMb L cg Ke KZ KG Kl + KR) KRN) := by
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl Kp ce cw Kb KE KR KN KRN
    hKl hKp hce hcw hKb hl hpair hB hW hFB hE hNear hsmall
  have hval : ∀ j < Nh, ValidAt (R.withMsq m) j := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hrest⟩ := hF
    exact ((hrest N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh).2.2.2.2.2.2.2.2.2 m hm).1
  have hb : 0 < b := by
    have := (hadm.1 0 (Nat.zero_le _)).1; simpa [Hist.traj_zero] using this
  have hL2 : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
  have hmn : ∀ n ≤ Nh, m * ((L : ℝ) ^ n) ^ 2 ≤ 1 := fun n hn => by
    have h1 := msq_horizon (L := (L : ℝ)) (by linarith only [hL2]) hm.2 (Nh := Nh) (k := 0)
      (by omega)
    simp only [pow_zero, one_pow, inv_one] at h1
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hm.1.le) h1
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by linarith only [hL2]) (by omega)) 2
  have hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1 := fun k hk =>
    ⟨(hadm.1 k hk.le).1.le, ((hadm.1 k hk.le).2.1).trans hε1⟩
  have ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2 := fun k hk =>
    ⟨zA_nonneg L hm.1.le k, zA_le_two (by linarith only [hL2]) (hmn (k + 1) hk)⟩
  have hrem := gamRemRel_of R hb hKp hce hcw hval hg ha hpair hB hW
  exact twoPtSq_of_gam_flow hF hε1 hL hSp hMC N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh
    lam Kl Kp _ Kb KE KR KN KRN hKl hKp
    (mul_nonneg (add_nonneg hce hcw) (by linarith only [hKp])) hKb hl hpair hrem hFB hE hNear
    hsmall

end

end Spin2
