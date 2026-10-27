import Spin2.Pair.PairLoop6c

/-!
# The constant loop, per scale (4): gradient, memory and the small-set recursion (pure)

* **`pl6_m4lop`**: `μ_n·λ_n(ℓ') ≤ 12ℓ'²β_{n+1}V c_M FO(n)`;
* **`pl6_g4`** (`s^g = 2δ_ke_ks_k^{-2}`): `≤ V·8E₀(256c_γ/L + 192c_M)NF(k)`;
* **`pl6_Pd_le`**, **`pl6_F_le`**: the Pauli defects `P_i ≤ 8Vc_MFO(i)` and the bilinear sizes
  `F_i ≤ s_{i+1}²V c_F r_iFO(i)`, `c_F = 4E₀'((9/2)⁴(6/5)c_γ/L + 192c_M)`;
* **`pl6_g5`** (`s^m = smE3`): `≤ V(16c_tc_M + 2560K²c_F + 2560K²c_{Wp})NF(k)`
  (kernels `(2/L)(64/49)`, `(8/(7L))(64/49) ≤ 1/4`);
* **`pl6_kseq`**: `2s_j²β_jK_i ≤ s_i²β_{i+1}((128/49)P(i) + 4ρ(64/49)Bc_W m̄Q(i))` for the
  small-set recursion `K = kseqF θ B r' m' j k₀` with `θρ ≤ 1/2`.
-/

namespace Spin2

open Finset PtCorr2

noncomputable section

section Groups2

variable {j Nh : ℕ} {L sx : ℝ} {s β r : ℕ → ℝ} (H : PL6H j Nh L sx s β r)
include H

/-- **`μ·λ` in profile form.** -/
theorem pl6_m4lop {K₄ cQ cS V k₀ mb wl ℓ' : ℝ} {κQ κS : ℕ → ℝ}
    (hK : 0 ≤ K₄) (hV : 0 ≤ V) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hcQ : 0 ≤ cQ) (hcS : 0 ≤ cS)
    (hQ0 : ∀ i, 0 ≤ κQ i) (hS0 : ∀ i, 0 ≤ κS i)
    (hQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (s i ^ 2 * β (i + 1)) * (cQ * pl6G0 j k₀ mb r i))
    (hS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (s i ^ 2 * β (i + 1)) * (cS * (mb * r i)))
    (hwl0 : 0 ≤ wl) (hwl : wl ≤ 2 * sx) (hℓ : 0 ≤ ℓ') {n : ℕ} (hn : n ≤ Nh) :
    m4RHS L K₄ sx s κQ κS j n *
      (2 * (wl * (s n ^ 2 / L ^ (n + 1))) * (ℓ' * (2 * sx * ℓ' * (L ^ (n + 1))⁻¹)) +
        s n ^ 2 * ((2 * sx * ℓ' * (L ^ (n + 1))⁻¹) * (2 * sx * ℓ' * (L ^ (n + 1))⁻¹))) ≤
      12 * ℓ' ^ 2 * (β (n + 1) * V * (K₄ * (cQ / L ^ 2 + 6 / 5 * cS) * pl6FO j k₀ mb r n)) := by
  have hμ0 : 0 ≤ m4RHS L K₄ sx s κQ κS j n := by
    unfold m4RHS
    exact sum_nonneg fun i' _ => mul_nonneg hK (add_nonneg
      (mul_nonneg (by have := H.hs0 i'; positivity) (hQ0 i'))
      (mul_nonneg (by have := H.hs0 (i' + 1); positivity) (hS0 i')))
  have h1 := pl6_lop H hwl0 hwl hℓ n
  have h2 := pl6_m4 H hK hV hk hm hcQ hcS hQ0 hS0 hQ hS hn
  calc _ ≤ m4RHS L K₄ sx s κQ κS j n * (12 * ℓ' ^ 2 * (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2))) :=
        mul_le_mul_of_nonneg_left h1 hμ0
    _ = 12 * ℓ' ^ 2 * (m4RHS L K₄ sx s κQ κS j n * (sx ^ 2 * s n ^ 2 / L ^ (2 * n + 2))) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Group 4** (`s^g`). -/
theorem pl6_g4 {γ ml e E0 cγ cM V k₀ mb : ℝ} {k : ℕ} (hk : k ≤ Nh) (hγ0 : 0 ≤ γ)
    (hml0 : 0 ≤ ml) (he0 : 0 ≤ e) (hE0 : 0 ≤ E0) (hcγ : 0 ≤ cγ) (hcM : 0 ≤ cM) (hV : 0 ≤ V)
    (hk0 : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hγ : γ ≤ s k ^ 2 * β (k + 1) * V * (cγ * pl6FO j k₀ mb r k))
    (hml : ml ≤ 12 * (2 * (2 * s k)) ^ 2 * (β (k + 1) * V * (cM * pl6FO j k₀ mb r k)))
    (he : e ≤ E0 * r k) :
    2 * (2 * ((4 : ℝ) ^ 4 * L⁻¹ * γ + ml) / β (k + 1)) * e * (s k)⁻¹ ^ 2 ≤
      V * (8 * E0 * (256 * cγ / L + 192 * cM) * pl6NF j k₀ mb r k) := by
  have hβ := H.hβp (k + 1) (by omega)
  have hs := H.hs0 k
  have hL0 := H.L0
  have hFO := pl6FO_nonneg (j := j) hk0 hm H.hr0 k
  have hmul := pl6_mul_FO (j := j) hk0 hm H.hr0 (H.hr1 k hk)
  have hδ : 2 * ((4 : ℝ) ^ 4 * L⁻¹ * γ + ml) / β (k + 1) ≤
      2 * (256 * cγ / L + 192 * cM) * s k ^ 2 * V * pl6FO j k₀ mb r k := by
    rw [div_le_iff₀ hβ]
    have h1 : (4 : ℝ) ^ 4 * L⁻¹ * γ ≤ (4 : ℝ) ^ 4 * L⁻¹ *
        (s k ^ 2 * β (k + 1) * V * (cγ * pl6FO j k₀ mb r k)) :=
      mul_le_mul_of_nonneg_left hγ (by positivity)
    have e1 : 2 * (256 * cγ / L + 192 * cM) * s k ^ 2 * V * pl6FO j k₀ mb r k * β (k + 1) =
        2 * ((4 : ℝ) ^ 4 * L⁻¹ * (s k ^ 2 * β (k + 1) * V * (cγ * pl6FO j k₀ mb r k)) +
          12 * (2 * (2 * s k)) ^ 2 * (β (k + 1) * V * (cM * pl6FO j k₀ mb r k))) := by
      rw [div_eq_mul_inv]; ring
    rw [e1]; linarith
  have hδ0 : 0 ≤ 2 * ((4 : ℝ) ^ 4 * L⁻¹ * γ + ml) / β (k + 1) := by positivity
  have hC : 0 ≤ 2 * (256 * cγ / L + 192 * cM) * s k ^ 2 * V := by positivity
  calc 2 * (2 * ((4 : ℝ) ^ 4 * L⁻¹ * γ + ml) / β (k + 1)) * e * (s k)⁻¹ ^ 2 ≤
        2 * (2 * (256 * cγ / L + 192 * cM) * s k ^ 2 * V * pl6FO j k₀ mb r k) * (E0 * r k) *
          (s k)⁻¹ ^ 2 := by gcongr
    _ = 4 * E0 * (256 * cγ / L + 192 * cM) * V * (r k * pl6FO j k₀ mb r k) := by
        field_simp; ring
    _ ≤ 4 * E0 * (256 * cγ / L + 192 * cM) * V * (2 * pl6NF j k₀ mb r k) := by
        have : 0 ≤ 4 * E0 * (256 * cγ / L + 192 * cM) * V := by positivity
        gcongr
    _ = _ := by ring

/-- **The Pauli defects** `P_i = (2μ_i/β_{i+1})(|w|s_i/L^{i+1})² ≤ 8Vc_MFO(i)`. -/
theorem pl6_Pd_le {K₄ cQ cS V k₀ mb wl : ℝ} {κQ κS : ℕ → ℝ}
    (hK : 0 ≤ K₄) (hV : 0 ≤ V) (hk : 0 ≤ k₀) (hm : 0 ≤ mb) (hcQ : 0 ≤ cQ) (hcS : 0 ≤ cS)
    (hQ0 : ∀ i, 0 ≤ κQ i) (hS0 : ∀ i, 0 ≤ κS i)
    (hQ : ∀ i, j ≤ i → i ≤ Nh → κQ i ≤ V * (s i ^ 2 * β (i + 1)) * (cQ * pl6G0 j k₀ mb r i))
    (hS : ∀ i, j ≤ i → i ≤ Nh → κS i ≤ V * (s i ^ 2 * β (i + 1)) * (cS * (mb * r i)))
    (hwl0 : 0 ≤ wl) (hwl : wl ≤ 2 * sx) {i : ℕ} (hi : i ≤ Nh) :
    2 * m4RHS L K₄ sx s κQ κS j i / β (i + 1) * (wl * (s i / L ^ (i + 1))) ^ 2 ≤
      8 * V * (K₄ * (cQ / L ^ 2 + 6 / 5 * cS) * pl6FO j k₀ mb r i) := by
  have hβ := H.hβp (i + 1) (by omega)
  have hL0 := H.L0
  have hμ0 : 0 ≤ m4RHS L K₄ sx s κQ κS j i := by
    unfold m4RHS
    exact sum_nonneg fun i' _ => mul_nonneg hK (add_nonneg
      (mul_nonneg (by have := H.hs0 i'; positivity) (hQ0 i'))
      (mul_nonneg (by have := H.hs0 (i' + 1); positivity) (hS0 i')))
  have h2 := pl6_m4 H hK hV hk hm hcQ hcS hQ0 hS0 hQ hS hi
  have hD : (wl * (s i / L ^ (i + 1))) ^ 2 ≤ 4 * (sx ^ 2 * s i ^ 2 / L ^ (2 * i + 2)) := by
    rw [show 2 * i + 2 = (i + 1) * 2 by ring, pow_mul, mul_pow, div_pow]
    have : wl ^ 2 ≤ 4 * sx ^ 2 := by nlinarith [H.hsx]
    have : 0 ≤ s i ^ 2 / (L ^ (i + 1)) ^ 2 := by positivity
    calc wl ^ 2 * (s i ^ 2 / (L ^ (i + 1)) ^ 2) ≤ 4 * sx ^ 2 * (s i ^ 2 / (L ^ (i + 1)) ^ 2) := by
          gcongr
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hβ]
  calc 2 * m4RHS L K₄ sx s κQ κS j i * (wl * (s i / L ^ (i + 1))) ^ 2 ≤
      2 * m4RHS L K₄ sx s κQ κS j i * (4 * (sx ^ 2 * s i ^ 2 / L ^ (2 * i + 2))) := by gcongr
    _ = 8 * (m4RHS L K₄ sx s κQ κS j i * (sx ^ 2 * s i ^ 2 / L ^ (2 * i + 2))) := by ring
    _ ≤ 8 * (β (i + 1) * V * (K₄ * (cQ / L ^ 2 + 6 / 5 * cS) * pl6FO j k₀ mb r i)) := by gcongr
    _ = _ := by ring

/-- **The bilinear sizes** `F_i = 2δ'_ie'_i/β_{i+1} ≤ s_{i+1}²Vc_Fr_iFO(i)`. -/
theorem pl6_F_le {γ ml e E0 cγ cM V k₀ mb : ℝ} {i : ℕ} (hi : i ≤ Nh) (hγ0 : 0 ≤ γ)
    (hml0 : 0 ≤ ml) (he0 : 0 ≤ e) (hE0 : 0 ≤ E0) (hcγ : 0 ≤ cγ) (hcM : 0 ≤ cM) (hV : 0 ≤ V)
    (hk0 : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hγ : γ ≤ s i ^ 2 * β (i + 1) * V * (cγ * pl6FO j k₀ mb r i))
    (hml : ml ≤ 12 * (2 * (2 * s (i + 1))) ^ 2 * (β (i + 1) * V * (cM * pl6FO j k₀ mb r i)))
    (he : e ≤ E0 * r i) :
    2 * (2 * ((9 / 2 : ℝ) ^ 4 * L⁻¹ * γ + ml) * e) / β (i + 1) ≤
      s (i + 1) ^ 2 * V * (4 * E0 * ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cγ / L + 192 * cM) *
        (r i * pl6FO j k₀ mb r i)) := by
  have hβ := H.hβp (i + 1) (by omega)
  have hL0 := H.L0
  have hFO := pl6FO_nonneg (j := j) hk0 hm H.hr0 i
  have hs2 := H.hs2 i
  have hδ : 2 * ((9 / 2 : ℝ) ^ 4 * L⁻¹ * γ + ml) ≤
      2 * ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cγ / L + 192 * cM) * (s (i + 1) ^ 2 * β (i + 1)) * V *
        pl6FO j k₀ mb r i := by
    have h1 : (9 / 2 : ℝ) ^ 4 * L⁻¹ * γ ≤ (9 / 2 : ℝ) ^ 4 * L⁻¹ *
        (6 / 5 * s (i + 1) ^ 2 * β (i + 1) * V * (cγ * pl6FO j k₀ mb r i)) := by
      refine mul_le_mul_of_nonneg_left (hγ.trans ?_) (by positivity)
      have : 0 ≤ β (i + 1) * V * (cγ * pl6FO j k₀ mb r i) := by positivity
      nlinarith
    have e1 : 2 * ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cγ / L + 192 * cM) * (s (i + 1) ^ 2 * β (i + 1)) *
        V * pl6FO j k₀ mb r i =
        2 * ((9 / 2 : ℝ) ^ 4 * L⁻¹ * (6 / 5 * s (i + 1) ^ 2 * β (i + 1) * V *
          (cγ * pl6FO j k₀ mb r i)) +
          12 * (2 * (2 * s (i + 1))) ^ 2 * (β (i + 1) * V * (cM * pl6FO j k₀ mb r i))) := by
      rw [div_eq_mul_inv]; ring
    rw [e1]; linarith
  rw [div_le_iff₀ hβ]
  have hδ0 : 0 ≤ 2 * ((9 / 2 : ℝ) ^ 4 * L⁻¹ * γ + ml) := by positivity
  calc 2 * (2 * ((9 / 2 : ℝ) ^ 4 * L⁻¹ * γ + ml) * e) ≤
      2 * ((2 * ((9 / 2 : ℝ) ^ 4 * (6 / 5) * cγ / L + 192 * cM) * (s (i + 1) ^ 2 * β (i + 1)) *
        V * pl6FO j k₀ mb r i) * (E0 * r i)) := by gcongr
    _ = _ := by ring

/-- The memory kernels `(2/L)(64/49)`, `(8/(7L))(64/49) ≤ 1/4`. -/
theorem PL6H.a3_le : 2 / L * (64 / 49) ≤ 1 / 4 := by
  have hL := H.hL
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith

theorem PL6H.a4_le : 8 / (7 * L) * (64 / 49) ≤ 1 / 4 := by
  have hL := H.hL
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]; linarith

/-- **Group 5** (`s^m`, the memory size `smE3`, written out). -/
theorem pl6_g5 {ct cM cF cWp lK V k₀ mb : ℝ} {Pd F Wp : ℕ → ℝ} {τ : ℕ → ℕ → ℝ} {k : ℕ}
    (hk : k ≤ Nh) (hct : 0 ≤ ct) (hcM : 0 ≤ cM) (hcF : 0 ≤ cF) (hcWp : 0 ≤ cWp) (hV : 0 ≤ V)
    (hk0 : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hPd0 : ∀ i, 0 ≤ Pd i) (hτ0 : ∀ i, 0 ≤ τ i k) (hF0 : ∀ i, 0 ≤ F i) (hW0 : ∀ i, 0 ≤ Wp i)
    (hPd : ∀ i, j ≤ i → i < k → Pd i ≤ 8 * V * (cM * pl6FO j k₀ mb r i))
    (hτ : ∀ i, j ≤ i → i < k → τ i k ≤ ct * (2 / L) ^ (k - i) * r i)
    (hF : ∀ i, j ≤ i → i < k → F i ≤ s (i + 1) ^ 2 * V * (cF * (r i * pl6FO j k₀ mb r i)))
    (hW : ∀ i, j ≤ i → i < k → Wp i ≤ s (i + 1) ^ 2 * V * (cWp * (mb * r i ^ 2))) :
    ∑ i ∈ Ico j k, (Pd i * τ i k + 1280 * lK ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) / s (i + 1) ^ 2 *
        (F i + 2 * Wp i)) * (64 / 49 : ℝ) ^ (k - i) ≤
      V * ((16 * ct * cM + 2560 * lK ^ 2 * cF + 2560 * lK ^ 2 * cWp) * pl6NF j k₀ mb r k) := by
  have hL0 := H.L0
  set a3 := 2 / L * (64 / 49) with ha3
  set a4 := 8 / (7 * L) * (64 / 49) with ha4
  have ha30 : 0 ≤ a3 := by positivity
  have ha40 : 0 ≤ a4 := by positivity
  have ha3' := H.a3_le
  have ha4' := H.a4_le
  have hterm : ∀ i ∈ Ico j k, (Pd i * τ i k + 1280 * lK ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) /
      s (i + 1) ^ 2 * (F i + 2 * Wp i)) * (64 / 49 : ℝ) ^ (k - i) ≤
      8 * ct * cM * V * (a3 ^ (k - i) * (r i * pl6FO j k₀ mb r i)) +
        1280 * lK ^ 2 * cF * V * (a4 ^ (k - i) * (r i * pl6FO j k₀ mb r i)) +
        2 * (1280 * lK ^ 2 * cWp * V) * (a4 ^ (k - i) * (mb * r i ^ 2)) := by
    intro i hi
    obtain ⟨hji, hik⟩ := mem_Ico.1 hi
    have hs := H.hs0 (i + 1)
    have hFO := pl6FO_nonneg (j := j) hk0 hm H.hr0 i
    have hr := H.hr0 i
    have e3 : a3 ^ (k - i) = (2 / L) ^ (k - i) * (64 / 49 : ℝ) ^ (k - i) := by rw [ha3, mul_pow]
    have e4 : a4 ^ (k - i) = (8 / (7 * L)) ^ (k - i) * (64 / 49 : ℝ) ^ (k - i) := by
      rw [ha4, mul_pow]
    have h1 : Pd i * τ i k ≤ (8 * V * (cM * pl6FO j k₀ mb r i)) * (ct * (2 / L) ^ (k - i) * r i) :=
      mul_le_mul (hPd i hji hik) (hτ i hji hik) (hτ0 i) (by positivity)
    have h2 : 1280 * lK ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) / s (i + 1) ^ 2 * (F i + 2 * Wp i) ≤
        1280 * lK ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) / s (i + 1) ^ 2 *
          (s (i + 1) ^ 2 * V * (cF * (r i * pl6FO j k₀ mb r i)) +
            2 * (s (i + 1) ^ 2 * V * (cWp * (mb * r i ^ 2)))) := by
      have := hF i hji hik; have := hW i hji hik
      gcongr
    have hp : 0 ≤ (64 / 49 : ℝ) ^ (k - i) := by positivity
    calc (Pd i * τ i k + 1280 * lK ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) / s (i + 1) ^ 2 *
          (F i + 2 * Wp i)) * (64 / 49 : ℝ) ^ (k - i) ≤
        ((8 * V * (cM * pl6FO j k₀ mb r i)) * (ct * (2 / L) ^ (k - i) * r i) +
          1280 * lK ^ 2 * (8 / (7 * L) : ℝ) ^ (k - i) / s (i + 1) ^ 2 *
          (s (i + 1) ^ 2 * V * (cF * (r i * pl6FO j k₀ mb r i)) +
            2 * (s (i + 1) ^ 2 * V * (cWp * (mb * r i ^ 2))))) * (64 / 49 : ℝ) ^ (k - i) := by
          gcongr
      _ = _ := by rw [e3, e4]; field_simp; ring
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have hr1 : ∀ i < k, r i ≤ 1 := fun i hi => H.hr1 i (by omega)
  have c1 := pl6_conv_rFO (j := j) ha30 ha3' hk0 hm H.hr0 hr1
  have c2 := pl6_conv_rFO (j := j) ha40 ha4' hk0 hm H.hr0 hr1
  have c3 := pl6_loc_NF (j := j) (k₀ := k₀) (r := r) ha40 (by linarith) hk0 hm k
  have h0 : 0 ≤ 8 * ct * cM * V := by positivity
  have h0' : 0 ≤ 1280 * lK ^ 2 * cF * V := by positivity
  have h0'' : 0 ≤ 2 * (1280 * lK ^ 2 * cWp * V) := by positivity
  calc 8 * ct * cM * V * ∑ i ∈ Ico j k, a3 ^ (k - i) * (r i * pl6FO j k₀ mb r i) +
        1280 * lK ^ 2 * cF * V * ∑ i ∈ Ico j k, a4 ^ (k - i) * (r i * pl6FO j k₀ mb r i) +
        2 * (1280 * lK ^ 2 * cWp * V) * ∑ i ∈ Ico j k, a4 ^ (k - i) * (mb * r i ^ 2) ≤
      8 * ct * cM * V * (2 * pl6NF j k₀ mb r k) + 1280 * lK ^ 2 * cF * V *
        (2 * pl6NF j k₀ mb r k) + 2 * (1280 * lK ^ 2 * cWp * V) * pl6NF j k₀ mb r k := by
        gcongr
    _ = _ := by ring

/-- **The small-set recursion in profile form** (`θρ ≤ 1/2`). -/
theorem pl6_kseq {θ B cW k₀ mb : ℝ} {r' m' : ℕ → ℝ} (hθ0 : 0 ≤ θ) (hθ : θ * pl6ρ ≤ 1 / 2)
    (hB : 0 ≤ B) (hcW : 0 ≤ cW) (hk : 0 ≤ k₀) (hm : 0 ≤ mb)
    (hr' : ∀ i ≤ Nh, r' i = r i)
    (hm' : ∀ i, j ≤ i → i ≤ Nh → 2 * s j ^ 2 * β j * m' i ≤ cW * (2 * s i ^ 2 * β i) * mb)
    {i : ℕ} (hji : j ≤ i) (hi : i ≤ Nh) :
    2 * s j ^ 2 * β j * kseqF θ B r' m' j k₀ i ≤
      s i ^ 2 * β (i + 1) * (128 / 49 * pl6P j k₀ i +
        4 * pl6ρ * (64 / 49) * B * cW * (mb * pl6Q j r i)) := by
  induction i, hji using Nat.le_induction with
  | base =>
    rw [kseqF_start]
    have h := H.hβr j (by omega)
    unfold pl6P pl6Q
    simp only [Nat.sub_self, pow_zero, one_mul, Ico_self, sum_empty, mul_zero, add_zero]
    have h2 : s j ^ 2 * k₀ * β j ≤ s j ^ 2 * k₀ * (64 / 49 * β (j + 1)) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    linarith
  | succ i hji ih =>
    have ih' := ih (by omega)
    rw [kseqF_succ θ B r' m' k₀ hji, pl6P_succ j k₀ hji, pl6Q_succ j r hji, hr' i (by omega)]
    have hR := H.sβ_dn (i := i) (k := i + 1) (by omega) hi
    rw [show i + 1 - i = 1 by omega, pow_one] at hR
    have hβi := H.hβr i (by omega)
    have hm'i := hm' i hji (by omega)
    have hP := pl6P_nonneg (j := j) hk i
    have hQ := pl6Q_nonneg (j := j) (r := r) i
    set X := 128 / 49 * pl6P j k₀ i + 4 * pl6ρ * (64 / 49) * B * cW * (mb * pl6Q j r i) with hX
    have hX0 : 0 ≤ X := by have := pl6ρ_ge; positivity
    set T := s (i + 1) ^ 2 * β (i + 1 + 1) with hT
    have hT0 : 0 ≤ T := mul_nonneg (sq_nonneg _) (H.hβ0 _)
    have hρ := pl6ρ_ge
    -- the decay of the old part
    have h1 : 2 * s j ^ 2 * β j * (θ * kseqF θ B r' m' j k₀ i) ≤ 1 / 2 * T * X := by
      have : 2 * s j ^ 2 * β j * (θ * kseqF θ B r' m' j k₀ i) =
          θ * (2 * s j ^ 2 * β j * kseqF θ B r' m' j k₀ i) := by ring
      rw [this]
      calc θ * (2 * s j ^ 2 * β j * kseqF θ B r' m' j k₀ i) ≤ θ * (s i ^ 2 * β (i + 1) * X) :=
            mul_le_mul_of_nonneg_left ih' hθ0
        _ ≤ θ * (pl6ρ * T * X) := by gcongr
        _ = (θ * pl6ρ) * T * X := by ring
        _ ≤ 1 / 2 * T * X := by gcongr
    -- the new source
    have h2 : 2 * s j ^ 2 * β j * (B * r i ^ 2 * m' i) ≤
        2 * (64 / 49) * pl6ρ * B * cW * mb * r i ^ 2 * T := by
      have hsβ : s i ^ 2 * β i ≤ 64 / 49 * pl6ρ * T := by
        have : s i ^ 2 * β i ≤ s i ^ 2 * (64 / 49 * β (i + 1)) :=
          mul_le_mul_of_nonneg_left hβi (sq_nonneg _)
        nlinarith
      have : 2 * s j ^ 2 * β j * (B * r i ^ 2 * m' i) = B * r i ^ 2 * (2 * s j ^ 2 * β j * m' i) :=
        by ring
      rw [this]
      have hBr : 0 ≤ B * r i ^ 2 := by positivity
      calc B * r i ^ 2 * (2 * s j ^ 2 * β j * m' i) ≤ B * r i ^ 2 * (cW * (2 * s i ^ 2 * β i) * mb) :=
            mul_le_mul_of_nonneg_left hm'i hBr
        _ = 2 * B * cW * mb * r i ^ 2 * (s i ^ 2 * β i) := by ring
        _ ≤ 2 * B * cW * mb * r i ^ 2 * (64 / 49 * pl6ρ * T) := by
            have : 0 ≤ 2 * B * cW * mb * r i ^ 2 := by positivity
            gcongr
        _ = _ := by ring
    have e : 2 * s j ^ 2 * β j * (θ * kseqF θ B r' m' j k₀ i + B * r i ^ 2 * m' i) =
        2 * s j ^ 2 * β j * (θ * kseqF θ B r' m' j k₀ i) +
          2 * s j ^ 2 * β j * (B * r i ^ 2 * m' i) := by ring
    rw [e]
    have e2 : T * (128 / 49 * (pl6P j k₀ i / 2) + 4 * pl6ρ * (64 / 49) * B * cW *
        (mb * ((pl6Q j r i + r i ^ 2) / 2))) =
        1 / 2 * T * X + 2 * (64 / 49) * pl6ρ * B * cW * mb * r i ^ 2 * T := by rw [hX]; ring
    rw [e2]; linarith

end Groups2

end

end Spin2
