import Spin2.Pair.PairLoop6a
import PtCorr2.Pair.PairESz2

/-!
# The constant loop, per scale (2): the `M₄` and gradient sizes of the blocks (pure)

With the history sizes in profile form (`κ^Q_i ≤ V s_i²β_{i+1}c_QG₀(i)`,
`κ^S_i ≤ V s_i²β_{i+1}c_Sm̄r_i`, `PL6H` the ratio facts):

* **`pl6_m4`**: `μ_n·s_x²s_n²/L^{2n+2} ≤ β_{n+1}V·c_M·FO(n)`, `c_M = K_{M4}(c_Q/L² + (6/5)c_S)`
  (the per-block `M₄` size `m4RHS`; the kernel `(81/64)(64/49)L^{-2} ≤ 1/4`);
* **`pl6_lop`**: the `LopM4` term `λ_n(ℓ') ≤ 12ℓ'²s_x²s_n²/L^{2n+2}` (path length `≤ 2s_x`);
* **`pl6_grad`**: `γ_k ≤ s_k²β_{k+1}V·c_γ·FO(k)`,
  `c_γ = L((3/4)L²c_M + (2K_G/L + 243/64)c_Q + (2K_G + 3)c_S)` (the per-block gradient size
  `gradRHS`; kernel `(9/8)⁴ρ/L ≤ 1/4`).
-/

namespace Spin2

open Finset PtCorr2

noncomputable section

/-- The basic term estimate: `s_i^{-4}(L_p/s_x²)κ(s_x²s_n²/L_d) ≤ c₁c₂(L_p/L_d)β_n VG`. -/
theorem pl6_trm {si sj sn sx βi βn κ V G Lp Ld c1 c2 : ℝ} (hsi : 0 < si) (hLp : 0 ≤ Lp)
    (hLd : 0 ≤ Ld) (hκ0 : 0 ≤ κ) (hκ : κ ≤ V * (sj ^ 2 * βi) * G) (hV : 0 ≤ V) (hG : 0 ≤ G)
    (hβi : 0 ≤ βi) (hs : sj ^ 2 * sn ^ 2 ≤ c1 * si ^ 4) (hβ : βi ≤ c2 * βn) (hc1 : 0 ≤ c1) :
    si⁻¹ ^ 4 * (Lp / sx ^ 2) * κ * (sx ^ 2 * sn ^ 2 / Ld) ≤
      c1 * c2 * (Lp / Ld) * (βn * (V * G)) := by
  have h1 := pl6_div_mul_le hLp (sq_nonneg sx)
  have hsi4 : 0 ≤ si⁻¹ ^ 4 := by positivity
  calc si⁻¹ ^ 4 * (Lp / sx ^ 2) * κ * (sx ^ 2 * sn ^ 2 / Ld) =
        (Lp / sx ^ 2 * sx ^ 2) * (si⁻¹ ^ 4 * κ * sn ^ 2) / Ld := by ring
    _ ≤ Lp * (si⁻¹ ^ 4 * (V * (sj ^ 2 * βi) * G) * sn ^ 2) / Ld := by
        gcongr
    _ = (si⁻¹ ^ 4 * (sj ^ 2 * sn ^ 2)) * (Lp / Ld) * (βi * (V * G)) := by ring
    _ ≤ (si⁻¹ ^ 4 * (c1 * si ^ 4)) * (Lp / Ld) * ((c2 * βn) * (V * G)) := by
        have : 0 ≤ Lp / Ld := div_nonneg hLp hLd
        have : 0 ≤ V * G := mul_nonneg hV hG
        gcongr
    _ = c1 * c2 * (Lp / Ld) * (βn * (V * G)) := by
        field_simp

theorem pl6_t_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 2 * t + t ^ 2 ≤ 3 := by
  have : t ^ 2 ≤ 1 := by
    rw [sq]; calc t * t ≤ 1 * 1 := mul_le_mul ht1 ht1 ht0 zero_le_one
      _ = 1 := by ring
  linarith

section M4

variable {j Nh : ℕ} {L sx : ℝ} {s β r : ℕ → ℝ} (H : PL6H j Nh L sx s β r)
include H

/-- The kernel `a₁ = (81/64)(64/49)L^{-2} ≤ 1/4`. -/
theorem PL6H.a1_le : 81 / 64 * (64 / 49) * (L ^ 2)⁻¹ ≤ 1 / 4 := by
  have hL := H.hL
  have h2 : (2401 : ℝ) ≤ L ^ 2 := by nlinarith
  have : (L ^ 2)⁻¹ ≤ 1 / 2401 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; simpa using h2
  nlinarith

set_option maxHeartbeats 2000000 in
/-- **The per-block `M₄` size in profile form.** -/
theorem pl6_m4 {K₄ cQ cS V k₀ mb : ℝ} {κQ κS : ℕ → ℝ}
    (hK : 0 ≤ K₄) (hV : 0 ≤ V) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hcQ : 0 ≤ cQ) (hcS : 0 ≤ cS)
    (hQ0 : ∀ i, 0 ≤ κQ i) (hS0 : ∀ i, 0 ≤ κS i)
    (hQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (s i ^ 2 * β (i + 1)) * (cQ * pl6G0 j k₀ mb r i))
    (hS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (s i ^ 2 * β (i + 1)) * (cS * (mb * r i)))
    {n : ℕ} (hn : n ≤ Nh) :
    m4RHS L K₄ sx s κQ κS j n * (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2)) ≤
      β (n + 1) * V * (K₄ * (cQ / L ^ 2 + 6 / 5 * cS) * pl6FO j k₀ mb r n) := by
  have hL0 := H.L0
  set a := 81 / 64 * (64 / 49) * (L ^ 2)⁻¹ with had
  have ha0 : 0 ≤ a := by positivity
  have ha := H.a1_le
  unfold m4RHS
  rw [sum_mul]
  have hterm : ∀ i ∈ Ico j n, K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i +
      (s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) *
        (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2)) ≤
      β (n + 1) * V * K₄ * (cQ * (L ^ 2)⁻¹ * (a ^ (n - i) * pl6G0 j k₀ mb r i) +
        6 / 5 * cS * (a ^ (n - i) * (mb * r i))) := by
    intro i hi
    obtain ⟨hji, hin⟩ := mem_Ico.1 hi
    have hβ := H.β_up (i := i + 1) (k := n + 1) (by omega) (by omega)
    rw [show n + 1 - (i + 1) = n - i by omega] at hβ
    have hsn := H.sq_up (i := i) (k := n) hin.le
    have hsn1 := H.sq_up (i := i + 1) (k := n) hin
    have h81 : (81 / 64 : ℝ) ^ (n - (i + 1)) ≤ (81 / 64 : ℝ) ^ (n - i) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hG0 := pl6G0_nonneg (j := j) (r := r) hk hm i
    have hs2 := H.hs2 i
    have hsi := H.hs0 i
    have hsi1 := H.hs0 (i + 1)
    have hA := pl6_trm (si := s i) (sj := s i) (sn := s n) (sx := sx) (Lp := (L ^ i) ^ 2)
      (Ld := L ^ (2 * n + 2)) (c1 := (81 / 64 : ℝ) ^ (n - i)) (c2 := (64 / 49 : ℝ) ^ (n - i))
      hsi (by positivity) (by positivity) (hQ0 i) (hQ i hji (by omega)) hV
      (mul_nonneg hcQ hG0) (H.hβ0 _)
      (by rw [show s i ^ 4 = s i ^ 2 * s i ^ 2 by ring]; nlinarith [sq_nonneg (s i)])
      hβ (by positivity)
    have hB := pl6_trm (si := s (i + 1)) (sj := s i) (sn := s n) (sx := sx)
      (Lp := (L ^ (i + 1)) ^ 2) (Ld := L ^ (2 * n + 2)) (c1 := 6 / 5 * (81 / 64 : ℝ) ^ (n - i))
      (c2 := (64 / 49 : ℝ) ^ (n - i))
      hsi1 (by positivity) (by positivity) (hS0 i) (hS i hji (by omega)) hV
      (mul_nonneg hcS (mul_nonneg hm (H.hr0 i))) (H.hβ0 _)
      (by
        have h1 : s n ^ 2 ≤ (81 / 64 : ℝ) ^ (n - i) * s (i + 1) ^ 2 := hsn1.trans
          (mul_le_mul_of_nonneg_right h81 (sq_nonneg _))
        have : 0 ≤ s n ^ 2 := sq_nonneg _
        calc s i ^ 2 * s n ^ 2 ≤ (6 / 5 * s (i + 1) ^ 2) * ((81 / 64 : ℝ) ^ (n - i) *
              s (i + 1) ^ 2) := mul_le_mul hs2 h1 this (by positivity)
          _ = _ := by ring)
      hβ (by positivity)
    rw [pl6_Lpow hL0 hin.le] at hA
    rw [pl6_Lpow1 hL0 hin.le] at hB
    have ea : a ^ (n - i) = (81 / 64 : ℝ) ^ (n - i) * (64 / 49 : ℝ) ^ (n - i) *
        ((L ^ 2)⁻¹) ^ (n - i) := by rw [had, mul_pow, mul_pow]
    rw [mul_add, add_mul]
    calc K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) * (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2)) +
          K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) *
            (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2)) =
        K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i * (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2))) +
          K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i *
            (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2))) := by ring
      _ ≤ K₄ * ((81 / 64 : ℝ) ^ (n - i) * (64 / 49 : ℝ) ^ (n - i) *
            ((L ^ 2)⁻¹ * ((L ^ 2)⁻¹) ^ (n - i)) * (β (n + 1) * (V * (cQ * pl6G0 j k₀ mb r i)))) +
          K₄ * (6 / 5 * (81 / 64 : ℝ) ^ (n - i) * (64 / 49 : ℝ) ^ (n - i) *
            ((L ^ 2)⁻¹) ^ (n - i) * (β (n + 1) * (V * (cS * (mb * r i))))) := by
          gcongr
      _ = _ := by rw [ea]; ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have e : ∑ i ∈ Ico j n, (cQ * (L ^ 2)⁻¹ * (a ^ (n - i) * pl6G0 j k₀ mb r i) +
        6 / 5 * cS * (a ^ (n - i) * (mb * r i))) =
      cQ * (L ^ 2)⁻¹ * ∑ i ∈ Ico j n, a ^ (n - i) * pl6G0 j k₀ mb r i +
        6 / 5 * cS * ∑ i ∈ Ico j n, a ^ (n - i) * (mb * r i) := by
    rw [sum_add_distrib, mul_sum, mul_sum]
  rw [e]
  have h1 := pl6_conv_G0 (j := j) (r := r) ha0 ha hk hm n
  have h2 := pl6_loc_FO (j := j) (k₀ := k₀) ha0 (by linarith) hk hm H.hr0 n
  have h3 := pl6G0_le_FO (j := j) (k₀ := k₀) hm H.hr0 n
  have hFO := pl6FO_nonneg (j := j) hk hm H.hr0 n
  have hβV : 0 ≤ β (n + 1) * V * K₄ := mul_nonneg (mul_nonneg (H.hβ0 _) hV) hK
  have hc1 : 0 ≤ cQ * (L ^ 2)⁻¹ := by positivity
  have key : cQ * (L ^ 2)⁻¹ * ∑ i ∈ Ico j n, a ^ (n - i) * pl6G0 j k₀ mb r i +
        6 / 5 * cS * ∑ i ∈ Ico j n, a ^ (n - i) * (mb * r i) ≤
      (cQ / L ^ 2 + 6 / 5 * cS) * pl6FO j k₀ mb r n := by
    rw [div_eq_mul_inv cQ, add_mul]
    have := mul_le_mul_of_nonneg_left (h1.trans h3) hc1
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 / 5 * cS)
    linarith
  calc β (n + 1) * V * K₄ * (cQ * (L ^ 2)⁻¹ * ∑ i ∈ Ico j n, a ^ (n - i) * pl6G0 j k₀ mb r i +
        6 / 5 * cS * ∑ i ∈ Ico j n, a ^ (n - i) * (mb * r i)) ≤
      β (n + 1) * V * K₄ * ((cQ / L ^ 2 + 6 / 5 * cS) * pl6FO j k₀ mb r n) :=
        mul_le_mul_of_nonneg_left key hβV
    _ = _ := by ring

/-- **The `LopM4` term**: `λ_n(ℓ') ≤ 12ℓ'²s_x²s_n²/L^{2n+2}` for a path of length `≤ 2s_x`. -/
theorem pl6_lop {wl ℓ' : ℝ} (hwl0 : 0 ≤ wl) (hwl : wl ≤ 2 * sx) (hℓ : 0 ≤ ℓ') (n : ℕ) :
    2 * (wl * (s n ^ 2 / L ^ (n + 1))) * (ℓ' * (2 * sx * ℓ' * (L ^ (n + 1))⁻¹)) +
      s n ^ 2 * ((2 * sx * ℓ' * (L ^ (n + 1))⁻¹) * (2 * sx * ℓ' * (L ^ (n + 1))⁻¹)) ≤
      12 * ℓ' ^ 2 * (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2)) := by
  have hL0 := H.L0
  have hsx := H.hsx
  have e1 : (L : ℝ) ^ (2 * n + 2) = (L ^ (n + 1)) ^ 2 := by rw [← pow_mul]; ring_nf
  set u := (L ^ (n + 1))⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have e2 : sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2) = sx ^ 2 * s n ^ 2 * u ^ 2 := by
    rw [e1, hu, inv_pow, div_eq_mul_inv]
  rw [e2, div_eq_mul_inv, ← hu]
  have h1 : wl * sx ≤ 2 * sx ^ 2 := by nlinarith
  have hX : 0 ≤ s n ^ 2 * ℓ' ^ 2 * u ^ 2 := by positivity
  have e3 : 2 * (wl * (s n ^ 2 * u)) * (ℓ' * (2 * sx * ℓ' * u)) +
      s n ^ 2 * (2 * sx * ℓ' * u * (2 * sx * ℓ' * u)) =
      (4 * (wl * sx) + 4 * sx ^ 2) * (s n ^ 2 * ℓ' ^ 2 * u ^ 2) := by ring
  rw [e3]
  calc (4 * (wl * sx) + 4 * sx ^ 2) * (s n ^ 2 * ℓ' ^ 2 * u ^ 2) ≤
      (4 * (2 * sx ^ 2) + 4 * sx ^ 2) * (s n ^ 2 * ℓ' ^ 2 * u ^ 2) := by gcongr
    _ = _ := by ring

/-- The kernel of the gradient flow, `(9/8)⁴ρ/L ≤ 1/4`. -/
theorem PL6H.a2_le : (9 / 8 : ℝ) ^ 4 * L⁻¹ * pl6ρ ≤ 1 / 4 := by
  have hL := H.hL
  have : L⁻¹ ≤ 1 / 49 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; simpa using hL
  unfold pl6ρ
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The per-block gradient size in profile form.** -/
theorem pl6_grad {K₄ KG cQ cS V k₀ mb : ℝ} {κQ κS : ℕ → ℝ}
    (hK : 0 ≤ K₄) (hKG : 0 ≤ KG) (hV : 0 ≤ V) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hcQ : 0 ≤ cQ)
    (hcS : 0 ≤ cS) (hQ0 : ∀ i, 0 ≤ κQ i) (hS0 : ∀ i, 0 ≤ κS i)
    (hQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (s i ^ 2 * β (i + 1)) * (cQ * pl6G0 j k₀ mb r i))
    (hS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (s i ^ 2 * β (i + 1)) * (cS * (mb * r i)))
    {k : ℕ} (hkN : k ≤ Nh) :
    gradRHS L KG K₄ sx s κQ κS j k ≤
      s k ^ 2 * β (k + 1) * V * (L * (3 / 4 * L ^ 2 * (K₄ * (cQ / L ^ 2 + 6 / 5 * cS)) +
        (2 * KG / L + 243 / 64) * cQ + (2 * KG + 3) * cS) * pl6FO j k₀ mb r k) := by
  have hL0 := H.L0
  have hL1 : 1 ≤ L := by have := H.hL; linarith
  set cM := K₄ * (cQ / L ^ 2 + 6 / 5 * cS) with hcM
  have hcM0 : 0 ≤ cM := by positivity
  set u := (9 / 8 : ℝ) ^ 4 * L⁻¹ with hud
  have hu0 : 0 ≤ u := by positivity
  set a := u * pl6ρ with had
  have ha0 : 0 ≤ a := mul_nonneg hu0 (by unfold pl6ρ; norm_num)
  have ha : a ≤ 1 / 4 := H.a2_le
  set T := s k ^ 2 * β (k + 1) with hT
  have hT0 : 0 ≤ T := mul_nonneg (sq_nonneg _) (H.hβ0 _)
  unfold gradRHS
  have hterm : ∀ i ∈ Ico j k, u ^ (k - 1 - i) *
      ((∑ i' ∈ Ico j (i + 1), K₄ * ((s i')⁻¹ ^ 4 * ((L ^ i') ^ 2 / sx ^ 2) * κQ i' +
          (s (i' + 1))⁻¹ ^ 4 * ((L ^ (i' + 1)) ^ 2 / sx ^ 2) * κS i')) *
        (2 * (2 * sx * (s (i + 1) / 4) ^ 2 / L ^ (i + 1)) *
            (s (i + 1) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹)) +
          (s (i + 1) / 4) ^ 2 * ((2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹) *
            (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹))) +
        ((1 + 2 * sx * (L ^ (i + 1))⁻¹) * (KG * (L ^ i * (L ^ (i + 1))⁻¹)) +
          (s i)⁻¹ ^ 2 * (2 * (s (i + 1) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹)) +
            (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹))) *
          κQ i +
        ((1 + 2 * sx * (L ^ (i + 1))⁻¹) * (KG * (L ^ (i + 1) * (L ^ (i + 1))⁻¹)) +
          (s (i + 1))⁻¹ ^ 2 * (2 * (s (i + 1) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹)) +
            (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹))) *
          κS i) ≤
      T * V * L * (3 / 4 * L ^ 2 * cM * (a ^ (k - i) * pl6FO j k₀ mb r (i + 1)) +
        (2 * KG / L + 243 / 64) * cQ * (a ^ (k - i) * pl6G0 j k₀ mb r i) +
        (2 * KG + 3) * cS * (a ^ (k - i) * (mb * r i))) := by
    intro i hi
    obtain ⟨hji, hik⟩ := mem_Ico.1 hi
    set t := 2 * sx * (L ^ (i + 1))⁻¹ with htd
    have ht0 : 0 ≤ t := by have := H.hsx; positivity
    have ht1 : t ≤ 1 := H.t_le hji
    have hsi := H.hs0 i
    have hsi1 := H.hs0 (i + 1)
    have hLi : (0 : ℝ) < L ^ (i + 1) := pow_pos hL0 _
    -- the `μ` part
    have eY : 2 * (2 * sx * (s (i + 1) / 4) ^ 2 / L ^ (i + 1)) *
          (s (i + 1) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹)) +
        (s (i + 1) / 4) ^ 2 * ((2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹) *
          (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹)) =
        3 / 4 * L ^ 2 * s (i + 1) ^ 2 * (sx ^ 2 * s (i + 1) ^ 2 / L ^ (2 * (i + 1) + 2)) := by
      rw [show 2 * (i + 1) + 2 = (i + 1) + (i + 1) + 2 by ring, pow_add, pow_add]
      field_simp
      ring
    have hμ := pl6_m4 H hK hV hk hm hcQ hcS hQ0 hS0 hQ hS (n := i + 1) (by omega)
    have hμ0 : 0 ≤ m4RHS L K₄ sx s κQ κS j (i + 1) := by
      unfold m4RHS
      exact sum_nonneg fun i' _ => mul_nonneg hK (add_nonneg
        (mul_nonneg (by have := H.hs0 i'; positivity) (hQ0 i'))
        (mul_nonneg (by have := H.hs0 (i' + 1); positivity) (hS0 i')))
    have hμY : (∑ i' ∈ Ico j (i + 1), K₄ * ((s i')⁻¹ ^ 4 * ((L ^ i') ^ 2 / sx ^ 2) * κQ i' +
          (s (i' + 1))⁻¹ ^ 4 * ((L ^ (i' + 1)) ^ 2 / sx ^ 2) * κS i')) *
        (3 / 4 * L ^ 2 * s (i + 1) ^ 2 * (sx ^ 2 * s (i + 1) ^ 2 / L ^ (2 * (i + 1) + 2))) ≤
        3 / 4 * L ^ 2 * (s (i + 1) ^ 2 * β (i + 1 + 1)) * V * cM * pl6FO j k₀ mb r (i + 1) := by
      have e : (∑ i' ∈ Ico j (i + 1), K₄ * ((s i')⁻¹ ^ 4 * ((L ^ i') ^ 2 / sx ^ 2) * κQ i' +
          (s (i' + 1))⁻¹ ^ 4 * ((L ^ (i' + 1)) ^ 2 / sx ^ 2) * κS i')) =
          m4RHS L K₄ sx s κQ κS j (i + 1) := rfl
      rw [e]
      calc m4RHS L K₄ sx s κQ κS j (i + 1) *
            (3 / 4 * L ^ 2 * s (i + 1) ^ 2 * (sx ^ 2 * s (i + 1) ^ 2 / L ^ (2 * (i + 1) + 2))) =
          3 / 4 * L ^ 2 * s (i + 1) ^ 2 * (m4RHS L K₄ sx s κQ κS j (i + 1) *
            (sx ^ 2 * s (i + 1) ^ 2 / L ^ (2 * (i + 1) + 2))) := by ring
        _ ≤ 3 / 4 * L ^ 2 * s (i + 1) ^ 2 * (β (i + 1 + 1) * V * (cM * pl6FO j k₀ mb r (i + 1))) :=
          mul_le_mul_of_nonneg_left hμ (by positivity)
        _ = _ := by ring
    -- the `Z` coefficients
    have hr2 : s (i + 1) ^ 2 ≤ 81 / 64 * s i ^ 2 := by
      have := H.hs1 i; nlinarith
    have eLi : L ^ i * (L ^ (i + 1))⁻¹ = L⁻¹ := by
      rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hL0.ne'), one_mul]
    have eL1 : L ^ (i + 1) * (L ^ (i + 1))⁻¹ = 1 := mul_inv_cancel₀ hLi.ne'
    have eZ : 2 * (s (i + 1) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹)) +
        (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹) * (2 * sx * s (i + 1) * (L ^ (i + 1))⁻¹) =
        s (i + 1) ^ 2 * (2 * t + t ^ 2) := by rw [htd]; ring
    have hZQ : (1 + t) * (KG * (L ^ i * (L ^ (i + 1))⁻¹)) + (s i)⁻¹ ^ 2 *
        (s (i + 1) ^ 2 * (2 * t + t ^ 2)) ≤ 2 * KG / L + 243 / 64 := by
      rw [eLi]
      have h1 : (1 + t) * (KG * L⁻¹) ≤ 2 * KG / L := by
        have : 0 ≤ KG * L⁻¹ := by positivity
        calc (1 + t) * (KG * L⁻¹) ≤ 2 * (KG * L⁻¹) :=
              mul_le_mul_of_nonneg_right (by linarith) this
          _ = 2 * KG / L := by rw [div_eq_mul_inv (2 * KG)]; ring
      have h2 : (s i)⁻¹ ^ 2 * (s (i + 1) ^ 2 * (2 * t + t ^ 2)) ≤ 81 / 64 * 3 := by
        have e : (s i)⁻¹ ^ 2 * (s (i + 1) ^ 2 * (2 * t + t ^ 2)) =
            (s (i + 1) ^ 2 / s i ^ 2) * (2 * t + t ^ 2) := by field_simp
        rw [e]
        have h3 : s (i + 1) ^ 2 / s i ^ 2 ≤ 81 / 64 := by
          rw [div_le_iff₀ (by positivity)]; exact hr2
        have h4 : 2 * t + t ^ 2 ≤ 3 := pl6_t_le ht0 ht1
        have : 0 ≤ s (i + 1) ^ 2 / s i ^ 2 := by positivity
        have : 0 ≤ 2 * t + t ^ 2 := by positivity
        exact mul_le_mul h3 h4 (by positivity) (by norm_num)
      linarith
    have hZS : (1 + t) * (KG * (L ^ (i + 1) * (L ^ (i + 1))⁻¹)) + (s (i + 1))⁻¹ ^ 2 *
        (s (i + 1) ^ 2 * (2 * t + t ^ 2)) ≤ 2 * KG + 3 := by
      rw [eL1, mul_one]
      have e : (s (i + 1))⁻¹ ^ 2 * (s (i + 1) ^ 2 * (2 * t + t ^ 2)) = 2 * t + t ^ 2 := by
        field_simp
      rw [e]; have := pl6_t_le ht0 ht1
      have : t * KG ≤ KG := mul_le_of_le_one_left hKG ht1
      linarith
    have hZQ0 : 0 ≤ (1 + t) * (KG * (L ^ i * (L ^ (i + 1))⁻¹)) + (s i)⁻¹ ^ 2 *
        (s (i + 1) ^ 2 * (2 * t + t ^ 2)) := by positivity
    have hZS0 : 0 ≤ (1 + t) * (KG * (L ^ (i + 1) * (L ^ (i + 1))⁻¹)) + (s (i + 1))⁻¹ ^ 2 *
        (s (i + 1) ^ 2 * (2 * t + t ^ 2)) := by positivity
    -- the ratios to scale `k`
    have hR1 : s (i + 1) ^ 2 * β (i + 1 + 1) ≤ pl6ρ ^ (k - i) * T := by
      have := H.sβ_dn (i := i + 1) (k := k) hik hkN
      exact this.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ pl6ρ_ge (by omega)) hT0)
    have hR0 : s i ^ 2 * β (i + 1) ≤ pl6ρ ^ (k - i) * T := H.sβ_dn hik.le hkN
    have hku : u ^ (k - 1 - i) * pl6ρ ^ (k - i) ≤ L * a ^ (k - i) := by
      have e : a ^ (k - i) = u ^ (k - 1 - i) * u * pl6ρ ^ (k - i) := by
        rw [had, mul_pow, show k - i = (k - 1 - i) + 1 by omega, pow_succ]
      rw [e]
      have huL : 1 ≤ L * u := by
        rw [hud, mul_comm, mul_assoc, inv_mul_cancel₀ hL0.ne', mul_one]; norm_num
      have : 0 ≤ u ^ (k - 1 - i) * pl6ρ ^ (k - i) := by
        have := pl6ρ_ge; positivity
      calc u ^ (k - 1 - i) * pl6ρ ^ (k - i) = 1 * (u ^ (k - 1 - i) * pl6ρ ^ (k - i)) := by ring
        _ ≤ (L * u) * (u ^ (k - 1 - i) * pl6ρ ^ (k - i)) := by gcongr
        _ = _ := by ring
    have hFO1 := pl6FO_nonneg (j := j) hk hm H.hr0 (i + 1)
    have hG0 := pl6G0_nonneg (j := j) (r := r) hk hm i
    have hmr : 0 ≤ mb * r i := mul_nonneg hm (H.hr0 i)
    rw [eY, eZ]
    -- bound the bracket
    have hB : (∑ i' ∈ Ico j (i + 1), K₄ * ((s i')⁻¹ ^ 4 * ((L ^ i') ^ 2 / sx ^ 2) * κQ i' +
          (s (i' + 1))⁻¹ ^ 4 * ((L ^ (i' + 1)) ^ 2 / sx ^ 2) * κS i')) *
        (3 / 4 * L ^ 2 * s (i + 1) ^ 2 * (sx ^ 2 * s (i + 1) ^ 2 / L ^ (2 * (i + 1) + 2))) +
        ((1 + t) * (KG * (L ^ i * (L ^ (i + 1))⁻¹)) + (s i)⁻¹ ^ 2 *
          (s (i + 1) ^ 2 * (2 * t + t ^ 2))) * κQ i +
        ((1 + t) * (KG * (L ^ (i + 1) * (L ^ (i + 1))⁻¹)) + (s (i + 1))⁻¹ ^ 2 *
          (s (i + 1) ^ 2 * (2 * t + t ^ 2))) * κS i ≤
        pl6ρ ^ (k - i) * T * V * (3 / 4 * L ^ 2 * cM * pl6FO j k₀ mb r (i + 1) +
          (2 * KG / L + 243 / 64) * cQ * pl6G0 j k₀ mb r i + (2 * KG + 3) * cS * (mb * r i)) := by
      have hQi := hQ i hji (by omega)
      have hSi := hS i hji (by omega)
      have b1 : 3 / 4 * L ^ 2 * (s (i + 1) ^ 2 * β (i + 1 + 1)) * V * cM *
          pl6FO j k₀ mb r (i + 1) ≤ 3 / 4 * L ^ 2 * (pl6ρ ^ (k - i) * T) * V * cM *
          pl6FO j k₀ mb r (i + 1) := by gcongr
      have b2 : ((1 + t) * (KG * (L ^ i * (L ^ (i + 1))⁻¹)) + (s i)⁻¹ ^ 2 *
          (s (i + 1) ^ 2 * (2 * t + t ^ 2))) * κQ i ≤
          (2 * KG / L + 243 / 64) * (V * (pl6ρ ^ (k - i) * T) * (cQ * pl6G0 j k₀ mb r i)) := by
        calc _ ≤ (2 * KG / L + 243 / 64) * (V * (s i ^ 2 * β (i + 1)) *
              (cQ * pl6G0 j k₀ mb r i)) := by
              apply mul_le_mul hZQ hQi (hQ0 i); positivity
          _ ≤ _ := by gcongr
      have b3 : ((1 + t) * (KG * (L ^ (i + 1) * (L ^ (i + 1))⁻¹)) + (s (i + 1))⁻¹ ^ 2 *
          (s (i + 1) ^ 2 * (2 * t + t ^ 2))) * κS i ≤
          (2 * KG + 3) * (V * (pl6ρ ^ (k - i) * T) * (cS * (mb * r i))) := by
        calc _ ≤ (2 * KG + 3) * (V * (s i ^ 2 * β (i + 1)) * (cS * (mb * r i))) := by
              apply mul_le_mul hZS hSi (hS0 i); positivity
          _ ≤ _ := by gcongr
      have := hμY.trans b1
      nlinarith
    have hp : 0 ≤ u ^ (k - 1 - i) := pow_nonneg hu0 _
    have hW : 0 ≤ T * V * (3 / 4 * L ^ 2 * cM * pl6FO j k₀ mb r (i + 1) +
          (2 * KG / L + 243 / 64) * cQ * pl6G0 j k₀ mb r i + (2 * KG + 3) * cS * (mb * r i)) := by
      positivity
    calc _ ≤ u ^ (k - 1 - i) * (pl6ρ ^ (k - i) * T * V * (3 / 4 * L ^ 2 * cM *
            pl6FO j k₀ mb r (i + 1) + (2 * KG / L + 243 / 64) * cQ * pl6G0 j k₀ mb r i +
            (2 * KG + 3) * cS * (mb * r i))) := mul_le_mul_of_nonneg_left hB hp
      _ = (u ^ (k - 1 - i) * pl6ρ ^ (k - i)) * (T * V * (3 / 4 * L ^ 2 * cM *
            pl6FO j k₀ mb r (i + 1) + (2 * KG / L + 243 / 64) * cQ * pl6G0 j k₀ mb r i +
            (2 * KG + 3) * cS * (mb * r i))) := by ring
      _ ≤ (L * a ^ (k - i)) * (T * V * (3 / 4 * L ^ 2 * cM *
            pl6FO j k₀ mb r (i + 1) + (2 * KG / L + 243 / 64) * cQ * pl6G0 j k₀ mb r i +
            (2 * KG + 3) * cS * (mb * r i))) := mul_le_mul_of_nonneg_right hku hW
      _ = _ := by ring
  refine (sum_le_sum hterm).trans ?_
  rw [← mul_sum]
  have e : ∑ i ∈ Ico j k, (3 / 4 * L ^ 2 * cM * (a ^ (k - i) * pl6FO j k₀ mb r (i + 1)) +
        (2 * KG / L + 243 / 64) * cQ * (a ^ (k - i) * pl6G0 j k₀ mb r i) +
        (2 * KG + 3) * cS * (a ^ (k - i) * (mb * r i))) =
      3 / 4 * L ^ 2 * cM * ∑ i ∈ Ico j k, a ^ (k - i) * pl6FO j k₀ mb r (i + 1) +
        (2 * KG / L + 243 / 64) * cQ * ∑ i ∈ Ico j k, a ^ (k - i) * pl6G0 j k₀ mb r i +
        (2 * KG + 3) * cS * ∑ i ∈ Ico j k, a ^ (k - i) * (mb * r i) := by
    rw [sum_add_distrib, sum_add_distrib, mul_sum, mul_sum, mul_sum]
  rw [e]
  have h1 := pl6_conv_FO_succ (j := j) ha0 ha hk hm H.hr0 k
  have h2 := (pl6_conv_G0 (j := j) (r := r) ha0 ha hk hm k).trans (pl6G0_le_FO hm H.hr0 k)
  have h3 := pl6_loc_FO (j := j) (k₀ := k₀) ha0 (by linarith) hk hm H.hr0 k
  have hTVL : 0 ≤ T * V * L := by positivity
  have key : 3 / 4 * L ^ 2 * cM * ∑ i ∈ Ico j k, a ^ (k - i) * pl6FO j k₀ mb r (i + 1) +
        (2 * KG / L + 243 / 64) * cQ * ∑ i ∈ Ico j k, a ^ (k - i) * pl6G0 j k₀ mb r i +
        (2 * KG + 3) * cS * ∑ i ∈ Ico j k, a ^ (k - i) * (mb * r i) ≤
      (3 / 4 * L ^ 2 * cM + (2 * KG / L + 243 / 64) * cQ + (2 * KG + 3) * cS) *
        pl6FO j k₀ mb r k := by
    rw [add_mul, add_mul]
    have : 0 ≤ (2 * KG / L + 243 / 64) * cQ := by positivity
    have : 0 ≤ (2 * KG + 3) * cS := by positivity
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 3 / 4 * L ^ 2 * cM)
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (2 * KG / L + 243 / 64) * cQ)
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (2 * KG + 3) * cS)
    linarith
  calc T * V * L * (3 / 4 * L ^ 2 * cM * ∑ i ∈ Ico j k, a ^ (k - i) * pl6FO j k₀ mb r (i + 1) +
        (2 * KG / L + 243 / 64) * cQ * ∑ i ∈ Ico j k, a ^ (k - i) * pl6G0 j k₀ mb r i +
        (2 * KG + 3) * cS * ∑ i ∈ Ico j k, a ^ (k - i) * (mb * r i)) ≤
      T * V * L * ((3 / 4 * L ^ 2 * cM + (2 * KG / L + 243 / 64) * cQ + (2 * KG + 3) * cS) *
        pl6FO j k₀ mb r k) := mul_le_mul_of_nonneg_left key hTVL
    _ = _ := by rw [hT]; ring

end M4

end

end Spin2
