import Spin2.Gam.GamBulk
import Spin2.Gam.GamFormB

/-!
# `GamRemRel` and its mirror `GamRemRelS` from `GamBulkRelA`; `TwoPtSq` without the bulk input

* `gamWKMir`, **`GamWKRelS`** (named): the observable (`K`, `𝒲`) part of the mirrored remainder
  (points `ptsS x = (x, 0)`), relative to `β_k = btMir`, the mirror of `GamWKRel`;
* `gamRemMir_split`: `ρ^{Mir}_k = gamWKMir_k + β_kE_k(x)` (`Obs2.gamRem2_split_hist`);
* `gamRemRel_ofA`, **`gamRemRelS_ofA`**: `GamBulkRelA` (at `a = 0` resp. `a = x`), `GamWKRel`
  resp. `GamWKRelS` and (H_λ) for the vertex give `GamRemRel` resp. `GamRemRelS` with
  `c_γ = (c_e + c_w)(1 + 3K_p)`;
* **`twoPtSq_of_gam_flow3`**: one set of constants (`thm_gam_bulk`) such that along every admissible
  trajectory `TwoPtSq` follows from (H_λ) for `λ` and for the two pair vertices, `GamWKRel`,
  `GamWKRelS`, `PairAboveW1` and the smallness of `K(λ)ǧ`; `GamBulkRel`, `GamFormB`, `TwoPtNear`
  are discharged.
-/

set_option linter.unusedSectionVars false

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Set Filter Topology Step2.D2

variable {L N : ℕ} [NeZero L]

section Traj

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- The observable part of the mirrored remainder. -/
def gamWKMir (m b μ₀ : ℝ) (x : Lam 2 L N) (k : ℕ) : ℂ :=
  Obs2.gamWK2 (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) k

/-- **Named input (mirror of `GamWKRel`)**. -/
def GamWKRelS (Nh : ℕ) (m b μ₀ cw : ℝ) : Prop :=
  ∀ x : Lam 2 L N, x ≠ 0 → Obs.coal L (0 : Lam 2 L N) x ≤ Nh →
    ∀ k < Obs.coal L (0 : Lam 2 L N) x, ‖gamWKMir R m b μ₀ x k‖ ≤
      cw * ((traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k) * ‖btMir R m b μ₀ x k‖ *
        ‖gamT R m b μ₀ k‖

theorem gamRemMir_split {Nh : ℕ} {m b μ₀ : ℝ}
    (hV : ∀ i < Nh, ValidAt (R.withMsq m) i) (x : Lam 2 L N) {k : ℕ} (hk : k < Nh) :
    gamRemMir R m b μ₀ x k = gamWKMir R m b μ₀ x k + btMir R m b μ₀ x k * gamBulkA R m b μ₀ x k :=
  Obs2.gamRem2_split_hist (R.withMsq m) (ptsS x) (Obs2.obsInit .two (zV b) (ptsS x))
    (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀) hV (Obs2.obsInit_isObs .two (zV b) (ptsS x))
    (fun b' => Obs2.obsInit_two_form _ _ b') hk

/-- The common estimate: `‖W + βE‖ ≤ (c_e + c_w)(1 + 3K_p)θ(ǧ + a)b‖Γ‖`. -/
theorem rem_bound_gb {W β E lh : ℂ} {b θ g a Γ Kp ce cw : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hce : 0 ≤ ce) (hcw : 0 ≤ cw) (hθ : 0 ≤ θ) (hga0 : 0 ≤ g + a) (hga3 : g + a ≤ 3)
    (hΓ : 0 ≤ Γ) (hlh : lh = β / b) (h1 : ‖lh - ((θ : ℝ) : ℂ)‖ ≤ Kp * θ * (g + a))
    (hW : ‖W‖ ≤ cw * (g + a) * ‖β‖ * Γ) (hE : ‖E‖ ≤ ce * (g + a) * Γ) :
    ‖W + β * E‖ ≤ (ce + cw) * (1 + 3 * Kp) * θ * (g + a) * (b * Γ) := by
  rw [hlh] at h1
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
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have e1 : ‖W‖ + ‖β‖ * ‖E‖ ≤ (ce + cw) * (g + a) * ‖β‖ * Γ := by
    have := mul_le_mul_of_nonneg_left hE (norm_nonneg β)
    have e : ‖β‖ * (ce * (g + a) * Γ) = ce * (g + a) * ‖β‖ * Γ := by ring
    have e' : (ce + cw) * (g + a) * ‖β‖ * Γ =
        cw * (g + a) * ‖β‖ * Γ + ce * (g + a) * ‖β‖ * Γ := by ring
    rw [e']
    linarith only [hW, this, e]
  refine e1.trans ?_
  have hc : 0 ≤ (ce + cw) * (g + a) := mul_nonneg (add_nonneg hce hcw) hga0
  calc (ce + cw) * (g + a) * ‖β‖ * Γ ≤ (ce + cw) * (g + a) * (b * θ * (1 + 3 * Kp)) * Γ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβ hc) hΓ
    _ = (ce + cw) * (1 + 3 * Kp) * θ * (g + a) * (b * Γ) := by ring

/-- **`GamRemRel` from `GamBulkRelA`**, `GamWKRel` and (H_λ) for the pair vertex. -/
theorem gamRemRel_ofA {Nh : ℕ} {m b μ₀ Kp ce cw : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp) (hce : 0 ≤ ce)
    (hcw : 0 ≤ cw) (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRelA R Nh m b μ₀ ce) (hW : GamWKRel R Nh m b μ₀ cw) :
    GamRemRel R Nh m b μ₀ ((ce + cw) * (1 + 3 * Kp)) :=
  gamRemRel_of R hb hKp hce hcw hV hg ha hl (gamBulkRel_of_A R hB) hW

/-- **`GamRemRelS` from `GamBulkRelA`** (at `a = x`), `GamWKRelS` and (H_λ) for the mirrored
pair vertex. -/
theorem gamRemRelS_ofA {Nh : ℕ} {m b μ₀ Kp ce cw : ℝ} (hb : 0 < b) (hKp : 0 ≤ Kp)
    (hce : 0 ≤ ce) (hcw : 0 ≤ cw) (hV : ∀ i < Nh, ValidAt (R.withMsq m) i)
    (hg : ∀ k < Nh, 0 ≤ (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ∧
      (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 ≤ 1)
    (ha : ∀ k < Nh, 0 ≤ zA L m k ∧ zA L m k ≤ 2)
    (hl : ∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp)
    (hB : GamBulkRelA R Nh m b μ₀ ce) (hW : GamWKRelS R Nh m b μ₀ cw) :
    GamRemRelS R Nh m b μ₀ ((ce + cw) * (1 + 3 * Kp)) := by
  intro x hx hj k hk
  have hkN : k < Nh := lt_of_lt_of_le hk hj
  have hθ : 0 ≤ thJ R m b μ₀ k := Real.rpow_nonneg (div_nonneg (hg k hkN).1 hb.le) _
  have hga0 := add_nonneg (hg k hkN).1 (ha k hkN).1
  have hga3 : (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ k).1 + zA L m k ≤ 3 := by
    linarith only [(hg k hkN).2, (ha k hkN).2]
  have hlh : lamHat2 R (ptsS x) (zV b) m b μ₀ k = btMir R m b μ₀ x k / b := by
    unfold lamHat2
    rw [show bt2 R (ptsS x) (zV b) m b μ₀ 0 = btMir R m b μ₀ x 0 from rfl, btMir_zero]
    rfl
  rw [gamRemMir_split R hV x hkN]
  exact rem_bound_gb hb hKp hce hcw hθ hga0 hga3 (norm_nonneg _) hlh (hl x hx k hkN)
    (hW x hx hj k hk) (hB x k hkN)

end Traj

set_option maxHeartbeats 4000000 in
/-- **`TwoPtSq` from the `γ` flow with the bulk input discharged**: one set of constants with
`FlowC2Concl`, `ε ≤ 1`, `SpinConcl`, `MagConcl` such that along every admissible trajectory with
`b ≤ μ₀ + m²`, `TwoPtSq` follows from (H_λ) for `λ` and for the pair vertices at `(0, x)` and
`(x, 0)`, the observable inputs `GamWKRel`, `GamWKRelS`, `PairAboveW1` and the smallness of
`K(λ)ǧ_j`, with `c_γ = (c_e + c_w)(1 + 3K_p)`. -/
theorem twoPtSq_of_gam_flow3 : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ ℓ A ρ κ cg cm cT ε Ke Cf Cb KZ KG ce : ℝ,
      FlowC2Concl L ℓ A ρ κ cg cm cT ε Ke Cf Cb ∧ ε ≤ 1 ∧
      SpinConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧ MagConcl L ℓ A ρ κ cg cm cT ε Ke KZ KG ∧
      0 ≤ ce ∧ GamBulkConcl L ℓ A ρ κ cm cT ε ce ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)], R.P = Pc → R.i₀ = 0 →
      R.ℓ = ℓ → R.A = A → R.ρ = ρ → 2 ≤ N →
    ∀ Nh : ℕ, Nh + 2 = N → ∀ m ∈ mRange L N, ∀ b μ₀,
      Admissible (rgDataM R m) ((L : ℝ) ^ 2) κ cm cT Nh ε b μ₀ → b ≤ μ₀ + m →
    ∀ (lam : ℕ → ℂ) (Kl Kp cw KE KR : ℝ), 0 ≤ Kl → 0 ≤ Kp → 0 ≤ cw →
      HLam R Nh m b μ₀ lam Kl →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsX x) (zV b) m b μ₀) Kp) →
      (∀ x : Lam 2 L N, x ≠ 0 → HLam R Nh m b μ₀ (lamHat2 R (ptsS x) (zV b) m b μ₀) Kp) →
      GamWKRel R Nh m b μ₀ cw → GamWKRelS R Nh m b μ₀ cw →
      PairAboveW1 R Nh m b μ₀ lam KE KR →
      (∀ j ≤ Nh, max (spinMK L cg Ke KZ Kl KG 0) 0 *
        (traj (rgDataM R m) ((L : ℝ) ^ 2) b μ₀ j).1 ≤ 1 / 2) →
      TwoPtSq R Nh m b μ₀ lam
        (max (zbKM L cg Ke KZ KG Kp ((ce + cw) * (1 + 3 * Kp)) (Kp + (ce + cw) * (1 + 3 * Kp)) Kl *
          (2 + zbKM L cg Ke KZ KG Kp ((ce + cw) * (1 + 3 * Kp))
            (Kp + (ce + cw) * (1 + 3 * Kp)) Kl) + KE) (L : ℝ))
        (max (1 + 2 * (1 + zbKM L cg Ke KZ KG Kp ((ce + cw) * (1 + 3 * Kp))
          (Kp + (ce + cw) * (1 + 3 * Kp)) Kl) * zbMb L cg Ke KZ KG Kl + KR) 1) := by
  obtain ⟨L₀, hL₀⟩ := thm_gam_bulk
  refine ⟨max L₀ 49, fun L _ hL => ?_⟩
  obtain ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, ce, hF, hε1, hSp, hMC, hce, hGB⟩ :=
    hL₀ L (le_trans (le_max_left _ _) hL)
  have hL49 : 49 ≤ L := le_trans (le_max_right _ _) hL
  refine ⟨ℓ, A, ρ, κ, cg, cm, cT, ε, Ke, Cf, Cb, KZ, KG, ce, hF, hε1, hSp, hMC, hce, hGB, ?_⟩
  intro N R _ _ hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm hh lam Kl Kp cw KE KR hKl hKp hcw
    hl hpair hpairS hW hWS hE hsmall
  have hB := hGB N R hP hi0 hRℓ hRA hRρ hN2 Nh hNh m hm b μ₀ hadm
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
  have hrem := gamRemRel_ofA R hb hKp hce hcw hval hg ha hpair hB hW
  have hremS := gamRemRelS_ofA R hb hKp hce hcw hval hg ha hpairS hB hWS
  have hcγ : 0 ≤ (ce + cw) * (1 + 3 * Kp) := mul_nonneg (add_nonneg hce hcw) (by linarith)
  exact twoPtSq_of_gam_flowB hF hε1 (by norm_num; omega) hSp hMC N R hP hi0 hRℓ hRA hRρ hN2 Nh
    hNh m hm b μ₀ hadm hh lam Kl Kp _ KE KR hKl hKp hcγ hl hpair hpairS hrem hremS hE hsmall

end

end Spin2
