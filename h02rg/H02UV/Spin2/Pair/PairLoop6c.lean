import Spin2.Pair.PairLoop6b
import Spin2.Pair.PairLoop3
import PtCorr2.Pair.PairRecAB

/-!
# The constant loop, per scale (3): the five item groups in normal form (pure)

For the summands of the first summability condition (`pairJointSizesP3_of_VS`), with the history
sizes in profile form and the ratio facts `PL6H`, each group is `≤ V·C·NF(k)` (`NF` of
`Spin2/Pair/PairLoop6a`; `V = ‖M_{j_x}‖ǧ_{j_x}`):

* **`pl6_g1`** (`s^q`, small-set `K`): `C₁ = 2Q₁c_{Qab}a_Q`;
* **`pl6_g2`** (`s^w`, product part of `𝒲'`): `C₂ = 4L⁴c_Wc_O(6/5)(64/49)²`
  (uses `(1 + c_W r)^{L²} ≤ 2`);
* **`pl6_g3`** (`s^p`, Pauli, the cancellation form `spE3`): `C₃ = 12K_{M4}c_Q/L² +
  (24/5)c_BK_{M4}c_S` for `k < N_h`; at `k = N_h` (vertex factor only `≤ 9/8`) an extra
  first-order term `≤ V·(27/5)K_{M4}c_S·m̄·cε`;
* **`pl6_g4`** (`s^g`, gradient × near bulk `V'`): `C₄ = 8E₀(256c_γ/L + 192c_M)`;
* **`pl6_g5`** (`s^m`, memory `smE3`): `C₅ = 16c_tc_M + 2·1280K²(24/5)((9/2)⁴c_γ/L + 243c_M)E₀'
  + 1280K²(12/5)c_{Wp}`;
* **`pl6_kseq`**: the small-set recursion `kseqF` in profile form
  (`2s_j²β_jK_i ≤ s_i²β_{i+1}((128/49)P(i) + 4ρ(64/49)Bc_W m̄Q(i))`, `θρ ≤ 1/2`).
-/

namespace Spin2

open Finset PtCorr2

noncomputable section

/-- `(1 + x)^n - 1 ≤ n·x·(1 + x)^n` for `x ≥ 0`. -/
theorem pl6_pow_sub_one_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (1 + x) ^ n - 1 ≤ n * x * (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ (1 + x) ^ n := one_le_pow₀ (by linarith)
    have e : (1 + x) ^ (n + 1) - 1 = (1 + x) * ((1 + x) ^ n - 1) + x := by ring
    rw [e]; push_cast
    have : (1 + x) * ((1 + x) ^ n - 1) ≤ (1 + x) * (n * x * (1 + x) ^ n) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have : x ≤ x * (1 + x) ^ (n + 1) := by
      have : 1 ≤ (1 + x) ^ (n + 1) := one_le_pow₀ (by linarith)
      nlinarith
    rw [pow_succ]
    nlinarith

section Groups

variable {j Nh : ℕ} {L sx : ℝ} {s β r : ℕ → ℝ} (H : PL6H j Nh L sx s β r)
include H

/-- `NF` dominates the local second-order term `m̄r_k²`. -/
theorem pl6_r2_le_NF {k₀ mb : ℝ} (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (k : ℕ) :
    mb * r k ^ 2 ≤ pl6NF j k₀ mb r k := by
  unfold pl6NF; have := pl6G0_nonneg (j := j) (r := r) hk hm k; linarith

/-- **Group 1** (`s^q`). -/
theorem pl6_g1 {Q1 cQab aQ V k₀ mb κ : ℝ} {k : ℕ} (hk : k ≤ Nh) (hQ1 : 0 ≤ Q1) (hcQ : 0 ≤ cQab)
    (haQ : 0 ≤ aQ) (hV : 0 ≤ V) (hk0 : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hκ : κ ≤ V * (s k ^ 2 * β (k + 1)) * (aQ * pl6G0 j k₀ mb r k)) :
    2 * (Q1 * (cQab * (κ / β (k + 1))) * (s k)⁻¹ ^ 2) ≤
      V * (2 * Q1 * cQab * aQ * pl6NF j k₀ mb r k) := by
  have hβ := H.hβp (k + 1) (by omega)
  have hs := H.hs0 k
  have hG := pl6G0_le_NF (j := j) (k₀ := k₀) (r := r) hm k
  have hG0 := pl6G0_nonneg (j := j) (r := r) hk0 hm k
  have e : κ / β (k + 1) * (s k)⁻¹ ^ 2 ≤ V * (aQ * pl6G0 j k₀ mb r k) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hβ, inv_pow, mul_inv_le_iff₀ (by positivity)]
    calc κ ≤ V * (s k ^ 2 * β (k + 1)) * (aQ * pl6G0 j k₀ mb r k) := hκ
      _ = _ := by ring
  have hQc : 0 ≤ Q1 * cQab := mul_nonneg hQ1 hcQ
  calc 2 * (Q1 * (cQab * (κ / β (k + 1))) * (s k)⁻¹ ^ 2) =
        2 * (Q1 * cQab) * (κ / β (k + 1) * (s k)⁻¹ ^ 2) := by ring
    _ ≤ 2 * (Q1 * cQab) * (V * (aQ * pl6G0 j k₀ mb r k)) := by gcongr
    _ ≤ 2 * (Q1 * cQab) * (V * (aQ * pl6NF j k₀ mb r k)) := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 2000000 in
/-- **Group 2** (`s^w`, the product part of `𝒲'`). -/
theorem pl6_g2 {V k₀ mb cW cO so se : ℝ} {n : ℕ} {k : ℕ} (hjk : j ≤ k) (hk1 : 1 ≤ k)
    (hk : k ≤ Nh) (hV : 0 ≤ V) (hk0 : 0 ≤ k₀) (hm : 0 ≤ mb) (hcW : 0 ≤ cW) (hcO : 0 ≤ cO)
    (hn : (n : ℝ) = L ^ 2) (hso0 : 0 ≤ so)
    (hso : so ≤ V * (s (k - 1) ^ 2 * β (k - 1)) * (cO * (mb * r (k - 1))))
    (hse : se = cW * r (k - 1)) (hpow : (1 + cW * r (k - 1)) ^ n ≤ 2)
    (hmono : r (k - 1) ≤ r k) :
    2 * (L ^ 2 * so * ((1 + se) ^ n - 1) * (s k)⁻¹ ^ 2) / β (k + 1) ≤
      V * (4 * L ^ 4 * cW * cO * (6 / 5) * (64 / 49) ^ 2 * pl6NF j k₀ mb r k) := by
  have hβ := H.hβp (k + 1) (by omega)
  have hs := H.hs0 k
  have hr0 := H.hr0 (k - 1)
  have hx : 0 ≤ cW * r (k - 1) := mul_nonneg hcW hr0
  have hP : (1 + se) ^ n - 1 ≤ 2 * L ^ 2 * (cW * r (k - 1)) := by
    rw [hse]
    have := pl6_pow_sub_one_le hx n
    rw [hn] at this
    have : L ^ 2 * (cW * r (k - 1)) * (1 + cW * r (k - 1)) ^ n ≤ L ^ 2 * (cW * r (k - 1)) * 2 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    nlinarith
  have hP0 : 0 ≤ (1 + se) ^ n - 1 := by
    rw [hse]; have : 1 ≤ (1 + cW * r (k - 1)) ^ n := one_le_pow₀ (by linarith)
    linarith
  have hs2 : s (k - 1) ^ 2 ≤ 6 / 5 * s k ^ 2 := by
    have := H.hs2 (k - 1); rwa [show k - 1 + 1 = k by omega] at this
  have hβ2 : β (k - 1) ≤ (64 / 49) ^ 2 * β (k + 1) := by
    have := H.β_up (i := k - 1) (k := k + 1) (by omega) (by omega)
    rwa [show k + 1 - (k - 1) = 2 by omega] at this
  have hr2 : r (k - 1) ^ 2 ≤ r k ^ 2 := pow_le_pow_left₀ hr0 hmono 2
  have hNF := pl6_r2_le_NF H (j := j) hk0 hm k
  -- the bound
  have hβ0 := H.hβ0 (k - 1)
  have key : so * ((1 + se) ^ n - 1) ≤
      V * (6 / 5 * s k ^ 2 * ((64 / 49) ^ 2 * β (k + 1))) * (cO * (mb * r (k - 1))) *
        (2 * L ^ 2 * (cW * r (k - 1))) := by
    calc so * ((1 + se) ^ n - 1) ≤ (V * (s (k - 1) ^ 2 * β (k - 1)) * (cO * (mb * r (k - 1)))) *
          (2 * L ^ 2 * (cW * r (k - 1))) := mul_le_mul hso hP hP0 (by positivity)
      _ ≤ _ := by gcongr
  have e1 : 2 * (L ^ 2 * so * ((1 + se) ^ n - 1) * (s k)⁻¹ ^ 2) / β (k + 1) =
      2 * L ^ 2 * (so * ((1 + se) ^ n - 1)) / (s k ^ 2 * β (k + 1)) := by
    field_simp
  rw [e1, div_le_iff₀ (by positivity)]
  have hL2 : 0 ≤ 2 * L ^ 2 := by positivity
  calc 2 * L ^ 2 * (so * ((1 + se) ^ n - 1)) ≤ 2 * L ^ 2 *
        (V * (6 / 5 * s k ^ 2 * ((64 / 49) ^ 2 * β (k + 1))) * (cO * (mb * r (k - 1))) *
          (2 * L ^ 2 * (cW * r (k - 1)))) := mul_le_mul_of_nonneg_left key hL2
    _ = V * (4 * L ^ 4 * cW * cO * (6 / 5) * (64 / 49) ^ 2) * (mb * r (k - 1) ^ 2) *
          (s k ^ 2 * β (k + 1)) := by ring
    _ ≤ V * (4 * L ^ 4 * cW * cO * (6 / 5) * (64 / 49) ^ 2) * pl6NF j k₀ mb r k *
          (s k ^ 2 * β (k + 1)) := by
        have : mb * r (k - 1) ^ 2 ≤ pl6NF j k₀ mb r k :=
          (mul_le_mul_of_nonneg_left hr2 hm).trans hNF
        gcongr
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **Group 3** (`s^p`, the Pauli size after the cancellation). -/
theorem pl6_g3 {K₄ cQ cS V k₀ mb wl cB cε : ℝ} {κQ κS : ℕ → ℝ} {cν : ℕ → ℝ}
    (hK : 0 ≤ K₄) (hV : 0 ≤ V) (hk0 : 0 ≤ k₀) (hm : 0 ≤ mb) (hcQ : 0 ≤ cQ) (hcS : 0 ≤ cS)
    (hcB : 0 ≤ cB) (hwl0 : 0 ≤ wl) (hwl : wl ≤ 2 * sx)
    (hQ0 : ∀ i, 0 ≤ κQ i) (hS0 : ∀ i, 0 ≤ κS i)
    (hQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (s i ^ 2 * β (i + 1)) * (cQ * pl6G0 j k₀ mb r i))
    (hS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (s i ^ 2 * β (i + 1)) * (cS * (mb * r i)))
    (hrε : ∀ i ≤ Nh, r i ≤ cε)
    {k : ℕ} (hk : k ≤ Nh) (hν0 : 0 ≤ cν k) (hν : k < Nh → cν k ≤ cB * r k)
    (hνN : ¬ k < Nh → cν k ≤ 9 / 8) :
    spE3 j (fun i => K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1))
        (fun i => K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) / β (i + 1))
        (fun _ => 3) cν (fun k => (wl * (s k / L ^ (k + 1))) ^ 2) k ≤
      V * ((12 * K₄ * cQ / L ^ 2 + 24 / 5 * cB * K₄ * cS) * pl6NF j k₀ mb r k) +
        (if k < Nh then 0 else V * (27 / 5 * K₄ * cS * (mb * cε))) := by
  have hL0 := H.L0
  set a := 81 / 64 * (64 / 49) * (L ^ 2)⁻¹ with had
  have ha0 : 0 ≤ a := by positivity
  have ha := H.a1_le
  set T := sx ^ 2 * s k ^ 2 / L ^ (2 * k + 2) with hT
  have hT0 : 0 ≤ T := by positivity
  have hD : (wl * (s k / L ^ (k + 1))) ^ 2 ≤ 4 * T := by
    rw [hT, show 2 * k + 2 = (k + 1) * 2 by ring, pow_mul, mul_pow, div_pow]
    have : wl ^ 2 ≤ 4 * sx ^ 2 := by nlinarith [H.hsx]
    have : 0 ≤ s k ^ 2 / (L ^ (k + 1)) ^ 2 := by positivity
    calc wl ^ 2 * (s k ^ 2 / (L ^ (k + 1)) ^ 2) ≤ 4 * sx ^ 2 * (s k ^ 2 / (L ^ (k + 1)) ^ 2) := by
          gcongr
      _ = _ := by ring
  have hD0 : 0 ≤ (wl * (s k / L ^ (k + 1))) ^ 2 := sq_nonneg _
  -- the `Q` sum
  have hQt : ∀ i ∈ Ico j k, K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
      (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
      4 * K₄ * cQ * (L ^ 2)⁻¹ * V * (a ^ (k - i) * pl6G0 j k₀ mb r i) := by
    intro i hi
    obtain ⟨hji, hik⟩ := mem_Ico.1 hi
    have hβi := H.hβp (i + 1) (by omega)
    have hG0 := pl6G0_nonneg (j := j) (r := r) hk0 hm i
    have hsn := H.sq_up (i := i) (k := k) hik.le
    have h := pl6_trm (si := s i) (sj := s i) (sn := s k) (sx := sx) (βi := β (i + 1))
      (βn := β (i + 1)) (Lp := (L ^ i) ^ 2) (Ld := L ^ (2 * k + 2))
      (c1 := (81 / 64 : ℝ) ^ (k - i)) (c2 := 1) (H.hs0 i) (by positivity) (by positivity) (hQ0 i)
      (hQ i hji (by omega)) hV (mul_nonneg hcQ hG0) hβi.le
      (by rw [show s i ^ 4 = s i ^ 2 * s i ^ 2 by ring]; nlinarith [sq_nonneg (s i)])
      (by rw [one_mul]) (by positivity)
    rw [pl6_Lpow hL0 hik.le] at h
    have ea : a ^ (k - i) = (81 / 64 : ℝ) ^ (k - i) * (64 / 49 : ℝ) ^ (k - i) *
        ((L ^ 2)⁻¹) ^ (k - i) := by rw [had, mul_pow, mul_pow]
    have hX0 : 0 ≤ K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
        (64 / 49 : ℝ) ^ (k - i) := by
      have := hQ0 i; have := H.hs0 i; positivity
    calc K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
          (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
        K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
          (64 / 49 : ℝ) ^ (k - i) * (4 * T) := mul_le_mul_of_nonneg_left hD hX0
      _ = 4 * K₄ * (64 / 49 : ℝ) ^ (k - i) *
          ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i * T) / β (i + 1) := by ring
      _ ≤ 4 * K₄ * (64 / 49 : ℝ) ^ (k - i) * ((81 / 64 : ℝ) ^ (k - i) * 1 *
          ((L ^ 2)⁻¹ * ((L ^ 2)⁻¹) ^ (k - i)) * (β (i + 1) * (V * (cQ * pl6G0 j k₀ mb r i)))) /
            β (i + 1) := by gcongr
      _ = _ := by rw [ea]; field_simp
  have hSt : ∀ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) /
      β (i + 1) * (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
      24 / 5 * K₄ * cS * V * (a ^ (k - i) * (mb * r i)) := by
    intro i hi
    obtain ⟨hji, hik⟩ := mem_Ico.1 hi
    have hβi := H.hβp (i + 1) (by omega)
    have hsn1 := H.sq_up (i := i + 1) (k := k) hik
    have h81 : (81 / 64 : ℝ) ^ (k - (i + 1)) ≤ (81 / 64 : ℝ) ^ (k - i) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hs2 := H.hs2 i
    have h := pl6_trm (si := s (i + 1)) (sj := s i) (sn := s k) (sx := sx) (βi := β (i + 1))
      (βn := β (i + 1)) (Lp := (L ^ (i + 1)) ^ 2) (Ld := L ^ (2 * k + 2))
      (c1 := 6 / 5 * (81 / 64 : ℝ) ^ (k - i)) (c2 := 1) (H.hs0 (i + 1)) (by positivity)
      (by positivity) (hS0 i) (hS i hji (by omega)) hV
      (mul_nonneg hcS (mul_nonneg hm (H.hr0 i))) hβi.le
      (by
        have h1 : s k ^ 2 ≤ (81 / 64 : ℝ) ^ (k - i) * s (i + 1) ^ 2 := hsn1.trans
          (mul_le_mul_of_nonneg_right h81 (sq_nonneg _))
        have : 0 ≤ s k ^ 2 := sq_nonneg _
        calc s i ^ 2 * s k ^ 2 ≤ (6 / 5 * s (i + 1) ^ 2) * ((81 / 64 : ℝ) ^ (k - i) *
              s (i + 1) ^ 2) := mul_le_mul hs2 h1 this (by positivity)
          _ = _ := by ring)
      (by rw [one_mul]) (by positivity)
    rw [pl6_Lpow1 hL0 hik.le] at h
    have ea : a ^ (k - i) = (81 / 64 : ℝ) ^ (k - i) * (64 / 49 : ℝ) ^ (k - i) *
        ((L ^ 2)⁻¹) ^ (k - i) := by rw [had, mul_pow, mul_pow]
    have hX0 : 0 ≤ K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) / β (i + 1) *
        (64 / 49 : ℝ) ^ (k - i) := by
      have := hS0 i; have := H.hs0 (i + 1); positivity
    calc K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) / β (i + 1) *
          (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
        K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) / β (i + 1) *
          (64 / 49 : ℝ) ^ (k - i) * (4 * T) := mul_le_mul_of_nonneg_left hD hX0
      _ = 4 * K₄ * (64 / 49 : ℝ) ^ (k - i) *
          ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i * T) / β (i + 1) := by ring
      _ ≤ 4 * K₄ * (64 / 49 : ℝ) ^ (k - i) * (6 / 5 * (81 / 64 : ℝ) ^ (k - i) * 1 *
          ((L ^ 2)⁻¹) ^ (k - i) * (β (i + 1) * (V * (cS * (mb * r i))))) / β (i + 1) := by
          gcongr
      _ = _ := by rw [ea]; field_simp; ring
  -- assemble
  unfold spE3
  have eQ : (∑ i ∈ Ico j k, K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
        (64 / 49 : ℝ) ^ (k - i)) * (wl * (s k / L ^ (k + 1))) ^ 2 * 3 =
      3 * ∑ i ∈ Ico j k, K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
        (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 := by
    rw [sum_mul]; ring
  have eS : cν k * (∑ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) *
        κS i) / β (i + 1) * (64 / 49 : ℝ) ^ (k - i)) * (wl * (s k / L ^ (k + 1))) ^ 2 =
      cν k * ∑ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) /
        β (i + 1) * (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 := by
    rw [mul_assoc, sum_mul]
  rw [eQ, eS]
  have hQs := sum_le_sum hQt
  have hSs := sum_le_sum hSt
  rw [← mul_sum] at hQs hSs
  have hc1 := pl6_conv_G0 (j := j) (r := r) ha0 ha hk0 hm k
  have hG := pl6G0_le_NF (j := j) (k₀ := k₀) (r := r) hm k
  have hQf : 3 * ∑ i ∈ Ico j k, K₄ * ((s i)⁻¹ ^ 4 * ((L ^ i) ^ 2 / sx ^ 2) * κQ i) / β (i + 1) *
        (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
      V * (12 * K₄ * cQ / L ^ 2 * pl6NF j k₀ mb r k) := by
    have h0 : 0 ≤ 4 * K₄ * cQ * (L ^ 2)⁻¹ * V := by positivity
    calc _ ≤ 3 * (4 * K₄ * cQ * (L ^ 2)⁻¹ * V * ∑ i ∈ Ico j k, a ^ (k - i) * pl6G0 j k₀ mb r i) :=
          by linarith
      _ ≤ 3 * (4 * K₄ * cQ * (L ^ 2)⁻¹ * V * pl6NF j k₀ mb r k) := by
          gcongr; exact hc1.trans hG
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hloc := pl6_loc_le ha0 (by linarith) (fun i => mul_nonneg hm (H.hr0 i)) j k
  have eF : ∑ i ∈ Ico j k, (1 / 2 : ℝ) ^ (k - i) * (mb * r i) = mb * pl6F j r k := by
    unfold pl6F; rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
  rw [eF] at hloc
  have hS0' : 0 ≤ ∑ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) /
      β (i + 1) * (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 :=
    sum_nonneg fun i _ => by have := hS0 i; have := H.hs0 (i + 1); have := H.hβ0 (i + 1); positivity
  have hc24 : 0 ≤ 24 / 5 * K₄ * cS * V := by positivity
  have hSb : ∑ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) * κS i) /
      β (i + 1) * (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
      24 / 5 * K₄ * cS * V * (mb * pl6F j r k) :=
    hSs.trans (mul_le_mul_of_nonneg_left hloc hc24)
  split_ifs with hkN
  · -- `k < N_h`: the vertex factor `c_ν ≤ c_B r_k`
    have hνk := hν hkN
    have hrF := pl6_rF_le (j := j) H.hr0 k
    have hNF : mb * ((pl6Q j r k + r k ^ 2) / 2) ≤ pl6NF j k₀ mb r k := by
      unfold pl6NF pl6G0
      have := pl6P_nonneg (j := j) hk0 k; have := pl6Q_nonneg (j := j) (r := r) k
      have := sq_nonneg (r k); nlinarith
    have hS2 : cν k * ∑ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) *
          κS i) / β (i + 1) * (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
        V * (24 / 5 * cB * K₄ * cS * pl6NF j k₀ mb r k) := by
      calc _ ≤ (cB * r k) * (24 / 5 * K₄ * cS * V * (mb * pl6F j r k)) :=
            mul_le_mul hνk hSb hS0' (mul_nonneg hcB (H.hr0 k))
        _ = 24 / 5 * cB * K₄ * cS * V * (mb * (r k * pl6F j r k)) := by ring
        _ ≤ 24 / 5 * cB * K₄ * cS * V * (mb * ((pl6Q j r k + r k ^ 2) / 2)) := by
            have : 0 ≤ 24 / 5 * cB * K₄ * cS * V := by positivity
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrF hm) this
        _ ≤ 24 / 5 * cB * K₄ * cS * V * pl6NF j k₀ mb r k := by
            have : 0 ≤ 24 / 5 * cB * K₄ * cS * V := by positivity
            exact mul_le_mul_of_nonneg_left hNF this
        _ = _ := by ring
    have : V * ((12 * K₄ * cQ / L ^ 2 + 24 / 5 * cB * K₄ * cS) * pl6NF j k₀ mb r k) =
        V * (12 * K₄ * cQ / L ^ 2 * pl6NF j k₀ mb r k) +
          V * (24 / 5 * cB * K₄ * cS * pl6NF j k₀ mb r k) := by ring
    rw [this]; linarith
  · -- `k = N_h`: the vertex factor is only `≤ 9/8`
    have hF : pl6F j r k ≤ cε := by
      unfold pl6F
      have h1 : ∑ i ∈ Ico j k, (1 / 2 : ℝ) ^ (k - i) * r i ≤
          ∑ i ∈ Ico j k, (1 / 2 : ℝ) ^ (k - i) * cε :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrε i (by have := (mem_Ico.1 hi).2; omega))
          (by positivity)
      have hcε : 0 ≤ cε := (H.hr0 k).trans (hrε k hk)
      refine h1.trans ?_
      rw [← sum_mul]
      have := geom_Ico_le_one (q := 1 / 2) (by norm_num) le_rfl j k
      nlinarith
    have hS2 : cν k * ∑ i ∈ Ico j k, K₄ * ((s (i + 1))⁻¹ ^ 4 * ((L ^ (i + 1)) ^ 2 / sx ^ 2) *
          κS i) / β (i + 1) * (64 / 49 : ℝ) ^ (k - i) * (wl * (s k / L ^ (k + 1))) ^ 2 ≤
        V * (27 / 5 * K₄ * cS * (mb * cε)) := by
      calc _ ≤ (9 / 8) * (24 / 5 * K₄ * cS * V * (mb * cε)) := by
            apply mul_le_mul (hνN hkN) (hSb.trans ?_) hS0' (by norm_num)
            gcongr
        _ = _ := by ring
    have hNF0 := pl6NF_nonneg (j := j) (r := r) hk0 hm k
    have : 0 ≤ V * (24 / 5 * cB * K₄ * cS * pl6NF j k₀ mb r k) := by positivity
    have : V * ((12 * K₄ * cQ / L ^ 2 + 24 / 5 * cB * K₄ * cS) * pl6NF j k₀ mb r k) =
        V * (12 * K₄ * cQ / L ^ 2 * pl6NF j k₀ mb r k) +
          V * (24 / 5 * cB * K₄ * cS * pl6NF j k₀ mb r k) := by ring
    rw [this]; linarith

end Groups

end

end Spin2
