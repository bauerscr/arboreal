import Mathlib

/-!
# The `V`-step of the joint induction (3): the summation of the gradient sources

Pure real-number bookkeeping for the `γ_n` input of the `V`-step. With weights `w_i = M_{a,i}M_{b,i}`
(`w_i ≤ 2w_{i+1}`), field scales `ℓ_{i+1} ≤ qℓ_i`, uniform per-scale source sizes
`κ^Q_i ≤ w_iQ`, `κ^S_i ≤ w_iS` and `2|a−b|_∞ ≤ L^{j_x+1}`, the right-hand side of
`PtCorr2.gradM4Sz_hVR_block_sizesD` (with the covariance scale `ℓ_{i+1}/4`, the path length
`≤ 2|a−b|_∞` and the `M₄` sizes `μ_i` from `m4SrcX_le_sizes`) is `≤ 4w_n·Y`,
`Y = (2K_G + 3q² + 2K_M)Q + (2K_G + 3 + 2K_M)S`:

* **`geom_wsum_le`**: `∑_{j≤i≤k} c^{k−i}w_i ≤ 2w_k` for `4c ≤ 1`;
* **`gamma_budget`**: the bound above.
-/

namespace PtCorr2

open Finset

/-- **Geometric sums against doubling weights.** -/
theorem geom_wsum_le {c : ℝ} (hc0 : 0 ≤ c) (hc : 4 * c ≤ 1) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    {j : ℕ} : ∀ k, j ≤ k → (∀ i, j ≤ i → i < k → w i ≤ 2 * w (i + 1)) →
      ∑ i ∈ Ico j (k + 1), c ^ (k - i) * w i ≤ 2 * w k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro _
    rw [Nat.Ico_succ_singleton, sum_singleton, Nat.sub_self, pow_zero, one_mul]
    linarith [hw j]
  | succ k hjk ih =>
    intro hw2
    have ih := ih fun i hi hik => hw2 i hi (by omega)
    rw [sum_Ico_succ_top (by omega), Nat.sub_self, pow_zero, one_mul]
    have e : ∑ i ∈ Ico j (k + 1), c ^ (k + 1 - i) * w i =
        c * ∑ i ∈ Ico j (k + 1), c ^ (k - i) * w i := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hik : i ≤ k := by have := (mem_Ico.1 hi).2; omega
      rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]; ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left ih hc0
    have h2 := hw2 k hjk (by omega)
    have h3 := hw (k + 1)
    nlinarith

/-- `ℓ_k ≤ q^{k−i}ℓ_i` from the one-step ratio. -/
theorem ratio_iter {q : ℝ} (hq : 1 ≤ q) (ℓ : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i) {j n : ℕ}
    (hℓq : ∀ i, j ≤ i → i < n → ℓ (i + 1) ≤ q * ℓ i) :
    ∀ i k, j ≤ i → i ≤ k → k ≤ n → ℓ k ≤ q ^ (k - i) * ℓ i := by
  intro i k hi hik hkn
  induction k, hik using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
    have := ih (by omega)
    have h1 := hℓq k (by omega) (by omega)
    rw [show k + 1 - i = (k - i) + 1 by omega, pow_succ]
    have hq0 : 0 ≤ q := by linarith
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **The summation of the gradient sources of the `V`-step.** -/
theorem gamma_budget {Lr q s KG KM Q S : ℝ} (hL1 : 1 ≤ Lr) (hq : 1 ≤ q) (hq4 : 8 * q ^ 4 ≤ Lr)
    (hs : 1 ≤ s) (hKG : 0 ≤ KG) (hKM : 0 ≤ KM) (hQ : 0 ≤ Q) (hS : 0 ≤ S)
    {j n : ℕ} (ℓ w κQ κS : ℕ → ℝ) (hℓ : ∀ i, 0 < ℓ i) (hw : ∀ i, 0 < w i)
    (hℓq : ∀ i, j ≤ i → i < n → ℓ (i + 1) ≤ q * ℓ i)
    (hw2 : ∀ i, j ≤ i → i < n → w i ≤ 2 * w (i + 1))
    (hsL : 2 * s ≤ Lr ^ (j + 1))
    (hκQ : ∀ i, j ≤ i → i < n → 0 ≤ κQ i ∧ κQ i ≤ w i * Q)
    (hκS : ∀ i, j ≤ i → i < n → 0 ≤ κS i ∧ κS i ≤ w i * S) :
    ∑ i ∈ Ico j n, (q ^ 4 * Lr⁻¹) ^ (n - 1 - i) *
      ((∑ i' ∈ Ico j (i + 1), KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
          (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i')) *
        (2 * (2 * s * (ℓ (i + 1) / 4) ^ 2 / Lr ^ (i + 1)) *
            (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (ℓ (i + 1) / 4) ^ 2 * ((2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) *
            (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) +
        ((1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹)) +
          (ℓ i)⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
            (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) *
          κQ i +
        ((1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (ℓ (i + 1))⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
            (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) *
          κS i) ≤
      w n * (4 * ((2 * KG + 3 * q ^ 2 + 2 * KM) * Q + (2 * KG + 3 + 2 * KM) * S)) := by
  have hL0 : 0 < Lr := by linarith
  have hq0 : 0 < q := by linarith
  have hq4' : 1 ≤ q ^ 4 := one_le_pow₀ hq
  have hLq : q ^ 4 * Lr⁻¹ ≤ 1 / 8 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hL0]; linarith
  have hLq2 : q ^ 4 / Lr ^ 2 ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  set Y := (2 * KG + 3 * q ^ 2 + 2 * KM) * Q + (2 * KG + 3 + 2 * KM) * S with hY
  have hY0 : 0 ≤ Y := by positivity
  -- the per-scale bound `T_i ≤ w_i Y`
  have hT : ∀ i, j ≤ i → i < n →
      (∑ i' ∈ Ico j (i + 1), KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
          (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i')) *
        (2 * (2 * s * (ℓ (i + 1) / 4) ^ 2 / Lr ^ (i + 1)) *
            (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (ℓ (i + 1) / 4) ^ 2 * ((2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) *
            (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) +
        ((1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹)) +
          (ℓ i)⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
            (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) *
          κQ i +
        ((1 + 2 * s * (Lr ^ (i + 1))⁻¹) * (KG * (Lr ^ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
          (ℓ (i + 1))⁻¹ ^ 2 * (2 * (ℓ (i + 1) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
            (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹) * (2 * s * ℓ (i + 1) * (Lr ^ (i + 1))⁻¹))) *
          κS i ≤ w i * Y := by
    intro i hji hin
    have hLi : 0 < Lr ^ i := pow_pos hL0 i
    have hLi1 : 0 < Lr ^ (i + 1) := pow_pos hL0 (i + 1)
    have hsLi : 2 * s ≤ Lr ^ (i + 1) :=
      hsL.trans (pow_le_pow_right₀ hL1 (by omega))
    set ℓ1 := ℓ (i + 1) with hℓ1
    have hℓ10 : 0 < ℓ1 := hℓ _
    have hℓi0 : 0 < ℓ i := hℓ _
    set g := 2 * s * ℓ1 * (Lr ^ (i + 1))⁻¹ with hg
    have hg0 : 0 ≤ g := by positivity
    have hgℓ : g ≤ ℓ1 := by
      rw [hg, mul_comm (2 * s), mul_assoc, ← div_eq_mul_inv]
      have : 2 * s / Lr ^ (i + 1) ≤ 1 := (div_le_one hLi1).2 hsLi
      nlinarith
    set η := 2 * s * (Lr ^ (i + 1))⁻¹ with hη
    have hη0 : 0 ≤ η := by positivity
    have hη1 : η ≤ 1 := by rw [hη, ← div_eq_mul_inv]; exact (div_le_one hLi1).2 hsLi
    have hr1 : Lr ^ i * (Lr ^ (i + 1))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv]; exact (div_le_one hLi1).2 (pow_le_pow_right₀ hL1 (by omega))
    have hr0 : 0 ≤ Lr ^ i * (Lr ^ (i + 1))⁻¹ := by positivity
    have hr2 : Lr ^ (i + 1) * (Lr ^ (i + 1))⁻¹ = 1 := mul_inv_cancel₀ hLi1.ne'
    have hℓq' : ℓ1 ≤ q * ℓ i := hℓq i hji hin
    -- the `Q` coefficient
    have hBQ : (1 + η) * (KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹)) +
        (ℓ i)⁻¹ ^ 2 * (2 * (ℓ1 * g) + g * g) ≤ 2 * KG + 3 * q ^ 2 := by
      have h1 : (1 + η) * (KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹)) ≤ 2 * KG := by
        have : KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹) ≤ KG := by nlinarith
        have : 0 ≤ KG * (Lr ^ i * (Lr ^ (i + 1))⁻¹) := by positivity
        nlinarith
      have h2 : 2 * (ℓ1 * g) + g * g ≤ 3 * (ℓ1 * ℓ1) := by nlinarith
      have h3 : ℓ1 * ℓ1 ≤ q ^ 2 * (ℓ i * ℓ i) := by nlinarith
      have h4 : (ℓ i)⁻¹ ^ 2 * (ℓ i * ℓ i) = 1 := by field_simp
      have h5 : (ℓ i)⁻¹ ^ 2 * (2 * (ℓ1 * g) + g * g) ≤ 3 * q ^ 2 := by
        calc (ℓ i)⁻¹ ^ 2 * (2 * (ℓ1 * g) + g * g) ≤ (ℓ i)⁻¹ ^ 2 * (3 * (q ^ 2 * (ℓ i * ℓ i))) :=
              mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by positivity)
          _ = 3 * q ^ 2 * ((ℓ i)⁻¹ ^ 2 * (ℓ i * ℓ i)) := by ring
          _ = 3 * q ^ 2 := by rw [h4, mul_one]
      linarith
    have hBS : (1 + η) * (KG * (Lr ^ (i + 1) * (Lr ^ (i + 1))⁻¹)) +
        ℓ1⁻¹ ^ 2 * (2 * (ℓ1 * g) + g * g) ≤ 2 * KG + 3 := by
      rw [hr2, mul_one]
      have h1 : (1 + η) * KG ≤ 2 * KG := by nlinarith
      have h2 : 2 * (ℓ1 * g) + g * g ≤ 3 * (ℓ1 * ℓ1) := by nlinarith
      have h4 : ℓ1⁻¹ ^ 2 * (ℓ1 * ℓ1) = 1 := by field_simp
      have h5 : ℓ1⁻¹ ^ 2 * (2 * (ℓ1 * g) + g * g) ≤ 3 := by
        calc ℓ1⁻¹ ^ 2 * (2 * (ℓ1 * g) + g * g) ≤ ℓ1⁻¹ ^ 2 * (3 * (ℓ1 * ℓ1)) :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = 3 := by rw [mul_left_comm, h4, mul_one]
      linarith
    -- the `M₄` part
    set G := 2 * (2 * s * (ℓ1 / 4) ^ 2 / Lr ^ (i + 1)) * (ℓ1 * g) + (ℓ1 / 4) ^ 2 * (g * g)
      with hG
    have hGe : G = (3 / 4) * s ^ 2 * ℓ1 ^ 4 / (Lr ^ (i + 1)) ^ 2 := by
      rw [hG, hg]; field_simp; ring
    have hG0 : 0 ≤ G := by rw [hGe]; positivity
    have hμ : (∑ i' ∈ Ico j (i + 1), KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
          (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i')) * G ≤
        KM * (2 * w i * Q + 2 * w i * S) := by
      rw [sum_mul]
      have hit := ratio_iter hq ℓ hℓ hℓq
      have hterm : ∀ i' ∈ Ico j (i + 1),
          KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
            (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i') * G ≤
          KM * ((q ^ 4 / Lr ^ 2) ^ (i - i') * (w i' * Q) +
            (q ^ 4 / Lr ^ 2) ^ (i - i') * (w i' * S)) := by
        intro i' hi'
        obtain ⟨hji', hi'i⟩ := mem_Ico.1 hi'
        have hi'n : i' < n := by omega
        obtain ⟨hQ0, hQ1⟩ := hκQ i' hji' hi'n
        obtain ⟨hS0, hS1⟩ := hκS i' hji' hi'n
        have hℓi' := hℓ i'
        have hℓi'1 := hℓ (i' + 1)
        -- ratios
        have hra : ℓ1 ≤ q ^ (i + 1 - i') * ℓ i' := hit i' (i + 1) hji' (by omega) (by omega)
        have hrb : ℓ1 ≤ q ^ (i - i') * ℓ (i' + 1) := by
          have := hit (i' + 1) (i + 1) (by omega) (by omega) (by omega)
          rwa [show i + 1 - (i' + 1) = i - i' by omega] at this
        have hpa : (ℓ i')⁻¹ ^ 4 * ℓ1 ^ 4 ≤ (q ^ 4) ^ (i + 1 - i') := by
          have h1 : ℓ1 ^ 4 ≤ (q ^ (i + 1 - i') * ℓ i') ^ 4 :=
            pow_le_pow_left₀ hℓ10.le hra 4
          have h2 : (ℓ i')⁻¹ ^ 4 * (q ^ (i + 1 - i') * ℓ i') ^ 4 = (q ^ 4) ^ (i + 1 - i') := by
            field_simp; ring
          calc _ ≤ (ℓ i')⁻¹ ^ 4 * (q ^ (i + 1 - i') * ℓ i') ^ 4 :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = _ := h2
        have hpb : (ℓ (i' + 1))⁻¹ ^ 4 * ℓ1 ^ 4 ≤ (q ^ 4) ^ (i - i') := by
          have h1 : ℓ1 ^ 4 ≤ (q ^ (i - i') * ℓ (i' + 1)) ^ 4 :=
            pow_le_pow_left₀ hℓ10.le hrb 4
          have h2 : (ℓ (i' + 1))⁻¹ ^ 4 * (q ^ (i - i') * ℓ (i' + 1)) ^ 4 = (q ^ 4) ^ (i - i') := by
            field_simp; ring
          calc _ ≤ (ℓ (i' + 1))⁻¹ ^ 4 * (q ^ (i - i') * ℓ (i' + 1)) ^ 4 :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = _ := h2
        -- powers of `L`
        have hLa : (Lr ^ i') ^ 2 / (Lr ^ (i + 1)) ^ 2 = ((Lr ^ 2)⁻¹) ^ (i + 1 - i') := by
          rw [← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
          rw [show (i + 1) * 2 = i' * 2 + 2 * (i + 1 - i') by omega, pow_add]
          field_simp
        have hLb : (Lr ^ (i' + 1)) ^ 2 / (Lr ^ (i + 1)) ^ 2 = ((Lr ^ 2)⁻¹) ^ (i - i') := by
          rw [← pow_mul, ← pow_mul, inv_pow, ← pow_mul]
          rw [show (i + 1) * 2 = (i' + 1) * 2 + 2 * (i - i') by omega, pow_add]
          field_simp
        have hs2 : s ^ 2 / s ^ 2 = 1 := div_self (by positivity)
        have eQ : (ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' * G =
            (3 / 4) * ((ℓ i')⁻¹ ^ 4 * ℓ1 ^ 4) * ((Lr ^ i') ^ 2 / (Lr ^ (i + 1)) ^ 2) * κQ i' := by
          rw [hGe]; field_simp
        have eS : (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i' * G =
            (3 / 4) * ((ℓ (i' + 1))⁻¹ ^ 4 * ℓ1 ^ 4) *
              ((Lr ^ (i' + 1)) ^ 2 / (Lr ^ (i + 1)) ^ 2) * κS i' := by
          rw [hGe]; field_simp
        have hQ' : (ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' * G ≤
            (q ^ 4 / Lr ^ 2) ^ (i - i') * (w i' * Q) := by
          rw [eQ, hLa]
          have hx : 0 ≤ ((Lr ^ 2)⁻¹) ^ (i + 1 - i') := by positivity
          have h1 : (3 / 4) * ((ℓ i')⁻¹ ^ 4 * ℓ1 ^ 4) * ((Lr ^ 2)⁻¹) ^ (i + 1 - i') ≤
              (q ^ 4 / Lr ^ 2) ^ (i + 1 - i') := by
            rw [div_eq_mul_inv (q ^ 4) (Lr ^ 2), mul_pow]
            have : (3 / 4) * ((ℓ i')⁻¹ ^ 4 * ℓ1 ^ 4) ≤ (q ^ 4) ^ (i + 1 - i') := by
              have := (by positivity : (0 : ℝ) ≤ (ℓ i')⁻¹ ^ 4 * ℓ1 ^ 4); linarith
            exact mul_le_mul_of_nonneg_right this hx
          have h2 : (q ^ 4 / Lr ^ 2) ^ (i + 1 - i') ≤ (q ^ 4 / Lr ^ 2) ^ (i - i') := by
            rw [show i + 1 - i' = (i - i') + 1 by omega, pow_succ]
            have : 0 ≤ (q ^ 4 / Lr ^ 2) ^ (i - i') := by positivity
            nlinarith [(by positivity : (0 : ℝ) ≤ q ^ 4 / Lr ^ 2)]
          calc (3 / 4) * ((ℓ i')⁻¹ ^ 4 * ℓ1 ^ 4) * ((Lr ^ 2)⁻¹) ^ (i + 1 - i') * κQ i'
              ≤ (q ^ 4 / Lr ^ 2) ^ (i - i') * κQ i' :=
                mul_le_mul_of_nonneg_right (h1.trans h2) hQ0
            _ ≤ _ := mul_le_mul_of_nonneg_left hQ1 (by positivity)
        have hS' : (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i' * G ≤
            (q ^ 4 / Lr ^ 2) ^ (i - i') * (w i' * S) := by
          rw [eS, hLb]
          have hx : 0 ≤ ((Lr ^ 2)⁻¹) ^ (i - i') := by positivity
          have h1 : (3 / 4) * ((ℓ (i' + 1))⁻¹ ^ 4 * ℓ1 ^ 4) * ((Lr ^ 2)⁻¹) ^ (i - i') ≤
              (q ^ 4 / Lr ^ 2) ^ (i - i') := by
            rw [div_eq_mul_inv (q ^ 4) (Lr ^ 2), mul_pow]
            have : (3 / 4) * ((ℓ (i' + 1))⁻¹ ^ 4 * ℓ1 ^ 4) ≤ (q ^ 4) ^ (i - i') := by
              have := (by positivity : (0 : ℝ) ≤ (ℓ (i' + 1))⁻¹ ^ 4 * ℓ1 ^ 4); linarith
            exact mul_le_mul_of_nonneg_right this hx
          calc (3 / 4) * ((ℓ (i' + 1))⁻¹ ^ 4 * ℓ1 ^ 4) * ((Lr ^ 2)⁻¹) ^ (i - i') * κS i'
              ≤ (q ^ 4 / Lr ^ 2) ^ (i - i') * κS i' := mul_le_mul_of_nonneg_right h1 hS0
            _ ≤ _ := mul_le_mul_of_nonneg_left hS1 (by positivity)
        have e : KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' +
            (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i') * G =
            KM * ((ℓ i')⁻¹ ^ 4 * ((Lr ^ i') ^ 2 / s ^ 2) * κQ i' * G +
              (ℓ (i' + 1))⁻¹ ^ 4 * ((Lr ^ (i' + 1)) ^ 2 / s ^ 2) * κS i' * G) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (add_le_add hQ' hS') hKM
      refine (sum_le_sum hterm).trans ?_
      rw [← mul_sum, sum_add_distrib]
      have hgw' : ∑ i' ∈ Ico j (i + 1), (q ^ 4 / Lr ^ 2) ^ (i - i') * w i' ≤ 2 * w i :=
        geom_wsum_le (c := q ^ 4 / Lr ^ 2) (by positivity) (by linarith) w (fun i' => (hw i').le)
          i hji fun i' hi' hi'i => hw2 i' hi' (by omega)
      have eQ : ∑ i' ∈ Ico j (i + 1), (q ^ 4 / Lr ^ 2) ^ (i - i') * (w i' * Q) =
          (∑ i' ∈ Ico j (i + 1), (q ^ 4 / Lr ^ 2) ^ (i - i') * w i') * Q := by
        rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
      have eS : ∑ i' ∈ Ico j (i + 1), (q ^ 4 / Lr ^ 2) ^ (i - i') * (w i' * S) =
          (∑ i' ∈ Ico j (i + 1), (q ^ 4 / Lr ^ 2) ^ (i - i') * w i') * S := by
        rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
      rw [eQ, eS]
      have h1 := mul_le_mul_of_nonneg_right hgw' hQ
      have h2 := mul_le_mul_of_nonneg_right hgw' hS
      have : 0 ≤ KM := hKM
      nlinarith
    obtain ⟨hQ0, hQ1⟩ := hκQ i hji hin
    obtain ⟨hS0, hS1⟩ := hκS i hji hin
    have hwi := hw i
    have t1 := mul_le_mul hBQ hQ1 hQ0 (by positivity)
    have t2 := mul_le_mul hBS hS1 hS0 (by positivity)
    have e : w i * Y = KM * (2 * w i * Q + 2 * w i * S) +
        (2 * KG + 3 * q ^ 2) * (w i * Q) + (2 * KG + 3) * (w i * S) := by rw [hY]; ring
    rw [e]
    linarith
  -- the outer sum
  rcases Nat.eq_zero_or_pos (n - j) with hnj | hnj
  · have : Ico j n = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, sum_empty]
    exact mul_nonneg (hw n).le (by positivity)
  · have hn1 : n = (n - 1) + 1 := by omega
    have hsum : ∑ i ∈ Ico j n, (q ^ 4 * Lr⁻¹) ^ (n - 1 - i) * (w i * Y) ≤ 2 * w (n - 1) * Y := by
      have hgw := geom_wsum_le (c := q ^ 4 * Lr⁻¹) (by positivity) (by linarith) w
        (fun i' => (hw i').le) (n - 1) (by omega) fun i' hi' hi'n => hw2 i' hi' (by omega)
      rw [← hn1] at hgw
      have e2 : ∑ i ∈ Ico j n, (q ^ 4 * Lr⁻¹) ^ (n - 1 - i) * (w i * Y) =
          (∑ i ∈ Ico j n, (q ^ 4 * Lr⁻¹) ^ (n - 1 - i) * w i) * Y := by
        rw [sum_mul]
        exact sum_congr rfl fun i hi => by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_right hgw hY0
    have hwn := hw2 (n - 1) (by omega) (by omega)
    rw [← hn1] at hwn
    calc _ ≤ ∑ i ∈ Ico j n, (q ^ 4 * Lr⁻¹) ^ (n - 1 - i) * (w i * Y) :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
            (hT i (mem_Ico.1 hi).1 (mem_Ico.1 hi).2) (by positivity)
      _ ≤ 2 * w (n - 1) * Y := hsum
      _ ≤ 2 * (2 * w n) * Y := mul_le_mul_of_nonneg_right (by linarith) hY0
      _ = w n * (4 * Y) := by ring

end PtCorr2
