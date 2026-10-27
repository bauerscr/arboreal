import Step2.Flow.FlowHV
import Step2.Lip.FlowLipMain

/-!
# Elementary helpers of the `Step2/Flow` theorem chain

The small-parameter lemmas, the `ℓ`-congruences of the a priori constants, `κ₁ ≤ 1/2`, the marginal
coefficient `betaL`, and the elementary mass bounds `m² L^{2(N_h+1)} ≤ L^{-2k}`. They were in
`FlowThm.lean`, `FlowHorizon.lean` and `FlowHor2Thm.lean`, and are collected here so that the
master theorem `flow_master` (`FlowMaster.lean`) and the files it imports (`Step2/Last/*`) do not
depend on the flow theorems that are now its corollaries. Names and statements are unchanged.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2 Flow2.Hist Filter Topology Step2.D2

/-! ### Small parameters -/

theorem ev_small {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (h0 : f 0 < c) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε ≤ c :=
  nhdsWithin_le_nhds ((hf.tendsto 0).eventually (eventually_le_nhds h0))

theorem ev_lin (K : ℝ) {c : ℝ} (hc : 0 < c) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), K * ε ≤ c :=
  ev_small (f := fun ε => K * ε) (by fun_prop) (by simpa using hc)

/-! ### The constants depend on `R` only through `ℓ` -/

section Ell

variable {L N N' : ℕ} [NeZero L] {R : RGPar 2 L N} {R' : RGPar 2 L N'}

theorem cZ_congr (h : R.ℓ = R'.ℓ) : cZ R = cZ R' := by unfold cZ; rw [h]
theorem cV_congr (h : R.ℓ = R'.ℓ) (Λ cm : ℝ) : cV R Λ cm = cV R' Λ cm := by
  unfold cV; rw [h, cZ_congr h]
theorem cW_congr (h : R.ℓ = R'.ℓ) (Λ cm C₂ : ℝ) : cW R Λ cm C₂ = cW R' Λ cm C₂ := by
  unfold cW; rw [cV_congr h]
theorem cR_congr (h : R.ℓ = R'.ℓ) (Λ cm C₂ : ℝ) : cR R Λ cm C₂ = cR R' Λ cm C₂ := by
  unfold cR; rw [cV_congr h, cW_congr h]
theorem cE_congr (h : R.ℓ = R'.ℓ) (Λ κ cm cT C₂ Cq Cl cS : ℝ) :
    cE R Λ κ cm cT C₂ Cq Cl cS = cE R' Λ κ cm cT C₂ Cq Cl cS := by
  unfold cE; rw [cR_congr h, h]
theorem cB_congr (h : R.ℓ = R'.ℓ) (Λ cm C₂ CK CD : ℝ) :
    cB R Λ cm C₂ CK CD = cB R' Λ cm C₂ CK CD := by
  unfold cB; rw [cV_congr h, cW_congr h, cR_congr h]
theorem cF2_congr (h : R.ℓ = R'.ℓ) : cF2 R = cF2 R' := by
  unfold cF2; rw [cZ_congr h, h]

end Ell

theorem kap1_le_half {L : ℕ} {A C₀ η : ℝ} (hC₀ : 0 ≤ C₀) (hη : 0 < η) (hL : 32 * C₀ + 1 ≤ L)
    (hA : 2 * (32 * C₀ + 1) ^ η⁻¹ ≤ A) : kap1 L A C₀ η ≤ 1 / 2 := by
  unfold kap1
  have hB1 : (1 : ℝ) ≤ 32 * C₀ + 1 := by linarith
  have hB0 : 0 < (32 * C₀ + 1) ^ η⁻¹ := Real.rpow_pos_of_pos (by linarith) _
  have hA2 : (32 * C₀ + 1) ^ η⁻¹ ≤ A / 2 := by linarith
  have hpow : 32 * C₀ + 1 ≤ (A / 2) ^ η := by
    have h := Real.rpow_le_rpow hB0.le hA2 hη.le
    rwa [Real.rpow_inv_rpow (by linarith) hη.ne'] at h
  have hA0 : 0 < A / 2 := lt_of_lt_of_le hB0 hA2
  have e : (A / 2) ^ (-η) = ((A / 2) ^ η)⁻¹ := Real.rpow_neg hA0.le η
  have h1 : (A / 2) ^ (-η) ≤ (32 * C₀ + 1)⁻¹ := by
    rw [e]; exact inv_anti₀ (by linarith) hpow
  have hL0 : (0 : ℝ) < L := by linarith
  have h2 : (L : ℝ)⁻¹ ≤ (32 * C₀ + 1)⁻¹ := inv_anti₀ (by linarith) hL
  have h3 : 8 * C₀ * ((L : ℝ)⁻¹ + (A / 2) ^ (-η)) ≤ 8 * C₀ * (2 * (32 * C₀ + 1)⁻¹) := by
    gcongr; linarith
  refine h3.trans ?_
  rw [show 8 * C₀ * (2 * (32 * C₀ + 1)⁻¹) = 16 * C₀ / (32 * C₀ + 1) by ring,
    div_le_iff₀ (by linarith)]
  linarith

theorem kap1_nonneg {L : ℕ} {A C₀ η : ℝ} (hC₀ : 0 ≤ C₀) (hA : 0 < A) : 0 ≤ kap1 L A C₀ η := by
  unfold kap1; positivity

/-- The marginal coefficient `β₁ log L = 3 log L/(2π)`. -/
def betaL (L : ℕ) : ℝ := 3 * (Real.log L / (2 * Real.pi))

/-! ### Elementary mass bounds -/

/-- `m² ≤ L^{-2(N-1)}` and `N_h + k + 2 ≤ N` give `m² L^{2(N_h+1)} ≤ L^{-2k}`. -/
theorem msq_horizon {L : ℝ} (hL : 1 ≤ L) {msq : ℝ} {N Nh k : ℕ}
    (hm : msq ≤ L ^ (-(2 * ((N : ℝ) - 1)))) (hNh : Nh + k + 2 ≤ N) :
    msq * (L ^ (Nh + 1)) ^ 2 ≤ ((L ^ k) ^ 2)⁻¹ := by
  have hL0 : 0 < L := by linarith
  have e1 : L ^ (-(2 * ((N : ℝ) - 1))) = ((L ^ (N - 1)) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hL0.le, ← pow_mul]
    congr 1
    rw [← Real.rpow_natCast]
    congr 1
    push_cast [show 1 ≤ N by omega]
    ring
  rw [e1] at hm
  have hP : 0 < (L ^ (N - 1)) ^ 2 := by positivity
  have hsplit : L ^ (N - 1) = L ^ (Nh + 1) * L ^ k * L ^ (N - 1 - (Nh + 1) - k) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hge : L ^ (Nh + 1) * L ^ k ≤ L ^ (N - 1) := by
    rw [hsplit]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL)
  have h1 : msq * (L ^ (Nh + 1)) ^ 2 ≤ ((L ^ (N - 1)) ^ 2)⁻¹ * (L ^ (Nh + 1)) ^ 2 :=
    mul_le_mul_of_nonneg_right hm (by positivity)
  refine h1.trans ?_
  rw [inv_mul_le_iff₀ hP]
  have hk : 0 < (L ^ k) ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hk]
  calc (L ^ (Nh + 1)) ^ 2 * (L ^ k) ^ 2 = (L ^ (Nh + 1) * L ^ k) ^ 2 := by ring
    _ ≤ (L ^ (N - 1)) ^ 2 := pow_le_pow_left₀ (by positivity) hge 2

/-- For `ϑ > 0` and `L ≥ 2` there is a number of scales `k` with `L^{-2k} ≤ ϑ`. -/
theorem exists_lost_scales {L : ℝ} (hL : 2 ≤ L) {ϑ : ℝ} (hϑ : 0 < ϑ) :
    ∃ k : ℕ, ((L ^ k) ^ 2)⁻¹ ≤ ϑ := by
  have hL0 : 0 < L := by linarith
  have h1 : L⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hϑ h1
  refine ⟨k, le_of_lt (lt_of_le_of_lt ?_ hk)⟩
  rw [inv_pow]
  have hLk : 1 ≤ L ^ k := one_le_pow₀ (by linarith)
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- The mass condition of the flow theorems from `N_h + k + 2 ≤ N`, `L^{-2k} ≤ ϑ`. -/
theorem mass_of_horizon {L : ℕ} (hL : 1 ≤ L) {msq ϑ : ℝ} {N Nh k : ℕ}
    (hm : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hNh : Nh + k + 2 ≤ N)
    (hk : (((L : ℝ) ^ k) ^ 2)⁻¹ ≤ ϑ) : Nh + 2 ≤ N ∧ msq * ((L : ℝ) ^ (Nh + 1)) ^ 2 ≤ ϑ :=
  ⟨by omega, (msq_horizon (by exact_mod_cast hL) hm hNh).trans hk⟩

theorem msq_j2 {L : ℕ} (hL : (1 : ℝ) ≤ L) {msq : ℝ} (hm0 : 0 < msq) {N j : ℕ}
    (hm : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hj : j + 3 ≤ N) :
    |msq| * ((L : ℝ) ^ (j + 2)) ^ 2 ≤ 1 := by
  have h := msq_horizon hL hm (Nh := j + 1) (k := 0) (by omega)
  rw [abs_of_pos hm0]
  simpa using h

theorem msq_j4 {L : ℕ} (hL : (1 : ℝ) ≤ L) {msq : ℝ} (hm0 : 0 < msq) {N j : ℕ}
    (hm : msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1)))) (hj : j + 3 ≤ N) :
    |msq| * ((L : ℝ) ^ j) ^ 2 ≤ ((L : ℝ) ^ 4)⁻¹ := by
  have h := msq_horizon hL hm (Nh := j) (k := 1) (by omega)
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  rw [abs_of_pos hm0]
  have e1 : msq * ((L : ℝ) ^ j) ^ 2 = msq * ((L : ℝ) ^ (j + 1)) ^ 2 * (((L : ℝ) ^ 1) ^ 2)⁻¹ := by
    field_simp; ring
  have e2 : (((L : ℝ) ^ 1) ^ 2)⁻¹ * (((L : ℝ) ^ 1) ^ 2)⁻¹ = ((L : ℝ) ^ 4)⁻¹ := by
    rw [← mul_inv]; ring
  rw [e1, ← e2]
  exact mul_le_mul_of_nonneg_right h (by positivity)

theorem heA1_of {C₄ M₀ Lr Kz cζ eA : ℝ} (hC₄ : 0 ≤ C₄) (hM₀ : 0 ≤ M₀) (hL : 1 ≤ Lr)
    (hLz : 7 * (2 * C₄ + 4) * (M₀ + 1) ≤ Lr) (hKz : Kz = C₄ * Lr ^ 2 + 1)
    (hcζ : cζ = 6 / 5 * (8 / 7 * Kz + 2)) (heA : eA = 8 / 7 * cζ * (M₀ + 1) * (Lr ^ 4)⁻¹) :
    32 / 7 * eA ≤ 1 := by
  subst hKz hcζ heA
  have hL2 : 1 ≤ Lr ^ 2 := one_le_pow₀ hL
  have hL4 : 0 < Lr ^ 4 := by positivity
  have hK : 8 / 7 * (C₄ * Lr ^ 2 + 1) + 2 ≤ (2 * C₄ + 4) * Lr ^ 2 := by nlinarith
  have e : 32 / 7 * (8 / 7 * (6 / 5 * (8 / 7 * (C₄ * Lr ^ 2 + 1) + 2)) * (M₀ + 1) * (Lr ^ 4)⁻¹) =
      1536 / 245 * (8 / 7 * (C₄ * Lr ^ 2 + 1) + 2) * (M₀ + 1) / Lr ^ 4 := by
    rw [div_eq_mul_inv]; ring
  rw [e, div_le_one hL4]
  have hM1 : 0 ≤ M₀ + 1 := by linarith
  have a1 : 1536 / 245 * (8 / 7 * (C₄ * Lr ^ 2 + 1) + 2) * (M₀ + 1) ≤
      7 * ((2 * C₄ + 4) * Lr ^ 2) * (M₀ + 1) := by
    have h0 : 0 ≤ 8 / 7 * (C₄ * Lr ^ 2 + 1) + 2 := by positivity
    have := mul_le_mul_of_nonneg_right hK hM1
    nlinarith
  have a2 : 7 * ((2 * C₄ + 4) * Lr ^ 2) * (M₀ + 1) = (7 * (2 * C₄ + 4) * (M₀ + 1)) * Lr ^ 2 := by
    ring
  have a3 : (7 * (2 * C₄ + 4) * (M₀ + 1)) * Lr ^ 2 ≤ Lr * Lr ^ 2 :=
    mul_le_mul_of_nonneg_right hLz (by positivity)
  have a4 : Lr * Lr ^ 2 ≤ Lr ^ 4 := by nlinarith
  linarith only [a1, a2, a3, a4]

end

end Step2
