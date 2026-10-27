import Spin2.H0.H0MassFlow
import Spin2.H0.H0SlackReq

/-!
# Route (a1): the slack inequality of the window ends (real analysis)

* **`h0Slack_mono`**: `h0Slack` is monotone in `ǧ` and in `m²|Λ|`;
* **`h0Slack_le_lin`**: `h0Slack(G, G) ≤ (cNuLast + 1 + h0Xc·G)G` for `0 ≤ G ≤ 1`;
* **`cNuLast_lt_win`**: `5(cNuLast + 2) < 3L⁴c_μ` at the master `c_m = (48L² + 8)ℓ²/49 + 1`, for
  `L ≥ 49` and `c_με ≤ 1/16` (the size check `L^{-4}cNuLast ≈ 1.09ℓ² < (3/4)c_μ ≈ 1.47ℓ²`, here with
  the window factor `5/4`);
* **`h0Slack_win`**: for `θ = (3/4)c_μ`, `c₁ = θǧ^c`, `m²|Λ| ≤ ǧ^c ≤ ε`, `θ(1 + 2p_Wc_μ) < c_μ` and
  `h0EReq`-type bounds, `h0Slack(g, m²|Λ|) < L⁴c₁` for all `0 ≤ g ≤ ǧ^c + p_W(c₁ + c₁)`.
-/

namespace Spin2

open Step Step2 PtCorr2

noncomputable section

open Flow2

theorem h0Ez_mono {Lr Cf g G : ℝ} (hCf : 0 ≤ Cf) (hg : 0 ≤ g) (hgG : g ≤ G) :
    h0Ez Lr Cf g ≤ h0Ez Lr Cf G := by
  unfold h0Ez
  have h2 : g ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hg hgG 2
  have hL : 0 ≤ Lr ^ 2 * Cf := by positivity
  have h3 : Lr ^ 2 * Cf * g ^ 2 ≤ Lr ^ 2 * Cf * G ^ 2 := mul_le_mul_of_nonneg_left h2 hL
  have h4 := Real.exp_le_exp.2 h3
  exact mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity)

theorem h0Slack_mono {Lr Cf ℓ cNL KT B ρ g G mV M : ℝ} (hCf : 0 ≤ Cf) (hcNL : 0 ≤ cNL)
    (hKT : 0 ≤ KT) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hg : 0 ≤ g) (hgG : g ≤ G) (hmV : 0 ≤ mV)
    (hmM : mV ≤ M) : h0Slack Lr Cf ℓ cNL KT B ρ g mV ≤ h0Slack Lr Cf ℓ cNL KT B ρ G M := by
  have hG : 0 ≤ G := hg.trans hgG
  have hM : 0 ≤ M := hmV.trans hmM
  have hE := h0Ez_mono (Lr := Lr) hCf hg hgG
  have hE0 : 0 ≤ h0Ez Lr Cf g := by unfold h0Ez; positivity
  have h3 : g ^ 3 ≤ G ^ 3 := pow_le_pow_left₀ hg hgG 3
  have hk : h0k0 Lr Cf g ≤ h0k0 Lr Cf G := by
    unfold h0k0; linarith [mul_le_mul_of_nonneg_left h3 hCf]
  have hk0 : 0 ≤ h0k0 Lr Cf g := by unfold h0k0; positivity
  have hea : h0ea Lr Cf ℓ g ≤ h0ea Lr Cf ℓ G := by
    unfold h0ea
    have a1 : Cf * g * h0Ez Lr Cf g ≤ Cf * G * h0Ez Lr Cf G :=
      mul_le_mul (mul_le_mul_of_nonneg_left hgG hCf) hE hE0 (by positivity)
    have a2 : ℓ⁻¹ ^ 2 * (h0Ez Lr Cf g + Cf * g ^ 3) ≤ ℓ⁻¹ ^ 2 * (h0Ez Lr Cf G + Cf * G ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith [mul_le_mul_of_nonneg_left h3 hCf]) (by positivity)
    linarith
  have hea0 : 0 ≤ h0ea Lr Cf ℓ g := by unfold h0ea; positivity
  have ha : h0ahi Lr Cf ℓ g ≤ h0ahi Lr Cf ℓ G := by
    unfold h0ahi; linarith [mul_le_mul_of_nonneg_left hgG hCf]
  have ha0 : 0 ≤ h0ahi Lr Cf ℓ g := by unfold h0ahi; positivity
  have hn : h0nhi Lr Cf ℓ KT g mV ≤ h0nhi Lr Cf ℓ KT G M := by
    unfold h0nhi
    have b1 : mV * (1 + h0k0 Lr Cf g) ≤ M * (1 + h0k0 Lr Cf G) :=
      mul_le_mul hmM (by linarith) (by linarith) hM
    have b2 : h0ahi Lr Cf ℓ g * (1 + KT * mV) ≤ h0ahi Lr Cf ℓ G * (1 + KT * M) :=
      mul_le_mul ha (by linarith [mul_le_mul_of_nonneg_left hmM hKT]) (by positivity)
        (ha0.trans ha)
    linarith
  have hn0 : 0 ≤ h0nhi Lr Cf ℓ KT g mV := by unfold h0nhi; positivity
  have hc0 : 0 ≤ 24 * ρ ^ 2 * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 := by positivity
  have hc1 : 0 ≤ 64 / 7 * ρ * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 := by positivity
  have hQ : h0Q Lr Cf ℓ KT B ρ g mV ≤ h0Q Lr Cf ℓ KT B ρ G M := by
    unfold h0Q
    have q1 : h0k0 Lr Cf g + h0ahi Lr Cf ℓ g * KT ≤ h0k0 Lr Cf G + h0ahi Lr Cf ℓ G * KT := by
      linarith [mul_le_mul_of_nonneg_right ha hKT]
    have q0 : 0 ≤ h0k0 Lr Cf G + h0ahi Lr Cf ℓ G * KT := by
      have := hk0.trans hk; have := ha0.trans ha; positivity
    have c1 := mul_le_mul q1 hn hn0 q0
    have c2 : h0nhi Lr Cf ℓ KT g mV ^ 2 ≤ h0nhi Lr Cf ℓ KT G M ^ 2 := pow_le_pow_left₀ hn0 hn 2
    have c3 := mul_le_mul_of_nonneg_left c2 hc0
    have c4 : h0ahi Lr Cf ℓ g * h0nhi Lr Cf ℓ KT g mV ≤ h0ahi Lr Cf ℓ G * h0nhi Lr Cf ℓ KT G M :=
      mul_le_mul ha hn hn0 (ha0.trans ha)
    have c5 := mul_le_mul_of_nonneg_left c4 hc1
    rw [← mul_assoc, ← mul_assoc] at c5
    linarith
  unfold h0Slack
  have d1 := mul_le_mul_of_nonneg_left hgG hcNL
  have d2 : h0ahi Lr Cf ℓ g * (KT * mV) ≤ h0ahi Lr Cf ℓ G * (KT * M) :=
    mul_le_mul ha (mul_le_mul_of_nonneg_left hmM hKT) (by positivity) (ha0.trans ha)
  have d3 : mV * (1 + h0k0 Lr Cf g) ≤ M * (1 + h0k0 Lr Cf G) :=
    mul_le_mul hmM (by linarith) (by linarith) hM
  linarith

theorem h0Slack_le_lin {Lr Cf ℓ cNL KT B ρ G : ℝ} (hCf : 0 ≤ Cf) (hKT : 0 ≤ KT) (hB : 0 ≤ B)
    (hρ : 0 ≤ ρ) (hG : 0 ≤ G) (hG1 : G ≤ 1) :
    h0Slack Lr Cf ℓ cNL KT B ρ G G ≤ (cNL + 1 + h0Xc Lr Cf ℓ KT B ρ * G) * G := by
  have hG2 : G ^ 2 ≤ G := by nlinarith
  have hG21 : G ^ 2 ≤ 1 := hG2.trans hG1
  have hG3 : G ^ 3 ≤ G ^ 2 := by nlinarith
  have hG20 : 0 ≤ G ^ 2 := by positivity
  set e0 := h0e0 Lr Cf with he0
  set k := h0kc Lr Cf with hkd
  set xa := h0xa Lr Cf ℓ with hxad
  set y := h0yc Lr Cf ℓ with hyd
  set n1 := h0n1 Lr Cf ℓ KT with hn1d
  set c0 := 24 * ρ ^ 2 * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 with hc0d
  set c1 := 64 / 7 * ρ * B * Real.exp (64 / 7 * ρ * B) / Lr ^ 2 with hc1d
  have he00 : 0 ≤ e0 := by rw [he0]; unfold h0e0; positivity
  have hk0 : 0 ≤ k := by rw [hkd]; unfold h0kc; rw [← he0]; positivity
  have hxa0 : 0 ≤ xa := by rw [hxad]; unfold h0xa; rw [← he0, ← hkd]; positivity
  have hy0 : 0 ≤ y := by rw [hyd]; unfold h0yc; rw [← hxad]; positivity
  have hn10 : 0 ≤ n1 := by rw [hn1d]; unfold h0n1; rw [← hkd, ← hyd]; positivity
  have hc00 : 0 ≤ c0 := by positivity
  have hc10 : 0 ≤ c1 := by positivity
  have hEz0 : 0 ≤ h0Ez Lr Cf G := by unfold h0Ez; positivity
  -- `E ≤ e₀G²`
  have hE : h0Ez Lr Cf G ≤ e0 * G ^ 2 := by
    unfold h0Ez; rw [he0]; unfold h0e0
    have hL : 0 ≤ Lr ^ 2 * Cf := by positivity
    have h1 : Real.exp (Lr ^ 2 * Cf * G ^ 2) ≤ Real.exp (Lr ^ 2 * Cf) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hL hG20)
    linarith
  have hκ : h0k0 Lr Cf G ≤ k * G ^ 2 := by
    unfold h0k0; rw [hkd]; unfold h0kc; rw [← he0]
    have := mul_le_mul_of_nonneg_left hG3 hCf
    linarith [show (e0 + Cf) * G ^ 2 = e0 * G ^ 2 + Cf * G ^ 2 by ring]
  have hκ0 : 0 ≤ h0k0 Lr Cf G := by unfold h0k0; positivity
  have hea : h0ea Lr Cf ℓ G ≤ xa * G ^ 2 := by
    unfold h0ea; rw [hxad]; unfold h0xa; rw [← he0, ← hkd]
    have a1 : Cf * G * h0Ez Lr Cf G ≤ Cf * e0 * G ^ 2 := by
      have := mul_le_mul_of_nonneg_left hE (mul_nonneg hCf hG)
      have h3 : Cf * G * (e0 * G ^ 2) = Cf * e0 * G ^ 3 := by ring
      have h4 := mul_le_mul_of_nonneg_left hG3 (mul_nonneg hCf he00)
      linarith
    have a2 : h0Ez Lr Cf G + Cf * G ^ 3 ≤ k * G ^ 2 := by
      have := hκ; unfold h0k0 at this; exact this
    have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : (0 : ℝ) ≤ ℓ⁻¹ ^ 2)
    linarith [show (Cf * e0 + ℓ⁻¹ ^ 2 * k) * G ^ 2 = Cf * e0 * G ^ 2 + ℓ⁻¹ ^ 2 * (k * G ^ 2) by ring]
  have hea0 : 0 ≤ h0ea Lr Cf ℓ G := by unfold h0ea; positivity
  have hah : h0ahi Lr Cf ℓ G ≤ y * G := by
    unfold h0ahi; rw [hyd]; unfold h0yc; rw [← hxad]
    have := mul_le_mul_of_nonneg_left hG2 hxa0
    linarith [show (Cf + xa) * G = Cf * G + xa * G by ring]
  have hah0 : 0 ≤ h0ahi Lr Cf ℓ G := by unfold h0ahi; positivity
  have hnh : h0nhi Lr Cf ℓ KT G G ≤ n1 * G := by
    unfold h0nhi; rw [hn1d]; unfold h0n1; rw [← hkd, ← hyd]
    have b1 : G * (1 + h0k0 Lr Cf G) ≤ G * (1 + k) := by
      have : k * G ^ 2 ≤ k := by
        have := mul_le_mul_of_nonneg_left hG21 hk0; linarith
      exact mul_le_mul_of_nonneg_left (by linarith) hG
    have b2 : h0ahi Lr Cf ℓ G * (1 + KT * G) ≤ y * G * (1 + KT) :=
      mul_le_mul hah (by have := mul_le_mul_of_nonneg_left hG1 hKT; linarith) (by positivity)
        (by positivity)
    linarith [show (1 + k + y * (1 + KT)) * G = G * (1 + k) + y * G * (1 + KT) by ring]
  have hnh0 : 0 ≤ h0nhi Lr Cf ℓ KT G G := by unfold h0nhi; positivity
  have hQ : h0Q Lr Cf ℓ KT B ρ G G ≤
      ((k + y * KT) * n1 + c0 * n1 ^ 2 + c1 * y * n1) * G ^ 2 := by
    unfold h0Q
    rw [← hc0d, ← hc1d]
    have q1 : h0k0 Lr Cf G + h0ahi Lr Cf ℓ G * KT ≤ (k + y * KT) * G := by
      have := mul_le_mul_of_nonneg_right hah hKT
      have : k * G ^ 2 ≤ k * G := mul_le_mul_of_nonneg_left hG2 hk0
      linarith [show (k + y * KT) * G = k * G + y * G * KT by ring]
    have r1 := mul_le_mul q1 hnh hnh0 (by positivity)
    have r2 : h0nhi Lr Cf ℓ KT G G ^ 2 ≤ (n1 * G) ^ 2 := pow_le_pow_left₀ hnh0 hnh 2
    have r3 := mul_le_mul_of_nonneg_left r2 hc00
    have r4 := mul_le_mul hah hnh hnh0 (by positivity)
    have r5 := mul_le_mul_of_nonneg_left r4 hc10
    have e1 : (k + y * KT) * G * (n1 * G) = (k + y * KT) * n1 * G ^ 2 := by ring
    have e2 : c0 * (n1 * G) ^ 2 = c0 * n1 ^ 2 * G ^ 2 := by ring
    have e3 : c1 * (y * G * (n1 * G)) = c1 * y * n1 * G ^ 2 := by ring
    have e4 : c1 * (h0ahi Lr Cf ℓ G * h0nhi Lr Cf ℓ KT G G) =
      c1 * h0ahi Lr Cf ℓ G * h0nhi Lr Cf ℓ KT G G := by ring
    have e5 : ((k + y * KT) * n1 + c0 * n1 ^ 2 + c1 * y * n1) * G ^ 2 =
      (k + y * KT) * n1 * G ^ 2 + c0 * n1 ^ 2 * G ^ 2 + c1 * y * n1 * G ^ 2 := by ring
    linarith
  have hX : h0Xc Lr Cf ℓ KT B ρ = xa + y * KT + k + (k + y * KT) * n1 + c0 * n1 ^ 2 +
      c1 * y * n1 := by
    rw [hxad, hyd, hkd, hn1d, hc0d, hc1d]; rfl
  rw [hX]
  unfold h0Slack
  have d1 : h0ahi Lr Cf ℓ G * (KT * G) ≤ y * KT * G ^ 2 := by
    have := mul_le_mul_of_nonneg_right hah (mul_nonneg hKT hG)
    linarith [show y * G * (KT * G) = y * KT * G ^ 2 by ring]
  have d2 : G * (1 + h0k0 Lr Cf G) ≤ G + k * G ^ 2 := by
    have := mul_le_mul_of_nonneg_left hκ hG
    have : G * (k * G ^ 2) ≤ k * G ^ 2 := by
      have := mul_le_mul_of_nonneg_right hG1 (mul_nonneg hk0 hG20); linarith
    linarith [show G * (1 + h0k0 Lr Cf G) = G + G * h0k0 Lr Cf G by ring]
  have e6 : (cNL + 1 + (xa + y * KT + k + (k + y * KT) * n1 + c0 * n1 ^ 2 + c1 * y * n1) * G) * G =
      cNL * G + G + xa * G ^ 2 + y * KT * G ^ 2 + k * G ^ 2 +
        ((k + y * KT) * n1 + c0 * n1 ^ 2 + c1 * y * n1) * G ^ 2 := by ring
  linarith

/-- **The size check at the master `c_m`**: `5(cNuLast + 2) < 3L⁴c_μ`. -/
theorem cNuLast_lt_win {L N : ℕ} [NeZero L] (R : RGPar 2 L N) {cm ε : ℝ} (hL : 49 ≤ L)
    (hcm : cm = 3 * (L : ℝ) ^ 2 * (16 * R.ℓ ^ 2 / 49) + 8 * R.ℓ ^ 2 / 49 + 1)
    (hu : cmu ((L : ℝ) ^ 2) cm * ε ≤ 1 / 16) :
    5 * (cNuLast R ((L : ℝ) ^ 2) cm ε + 2) < 3 * (L : ℝ) ^ 4 * cmu ((L : ℝ) ^ 2) cm := by
  set Λ : ℝ := (L : ℝ) ^ 2 with hΛ
  set q : ℝ := R.ℓ ^ 2 with hq
  set u : ℝ := cmu Λ cm * ε with hud
  have hL' : (49 : ℝ) ≤ L := by exact_mod_cast hL
  have hΛ0 : 2401 ≤ Λ := by rw [hΛ]; nlinarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hcm0 : 0 < cm := by rw [hcm]; positivity
  have hcmu0 : 0 < cmu Λ cm := by
    unfold cmu; have : 0 < Λ - 1 := by linarith
    positivity
  have hcmuE : cmu Λ cm * (Λ - 1) = 2 * cm := by
    unfold cmu; have : Λ - 1 ≠ 0 := by linarith
    field_simp
  have hL4 : (L : ℝ) ^ 4 = Λ ^ 2 := by rw [hΛ]; ring
  have hN : 5 * (cNuLast R Λ cm ε + 2) = 3200 / 1029 * (Λ ^ 2 * q * u) + 800 / 147 * (Λ ^ 2 * q) +
      (40 / 49 + 1280 / 343) * (Λ * q) + 15 / 7 * q + 10 := by
    unfold cNuLast cNuLs cZ; rw [hud, hq, hΛ]; ring
  have hR : 3 * (L : ℝ) ^ 4 * cmu Λ cm = 6 * Λ * cm + 3 * Λ * cmu Λ cm := by
    rw [hL4]; linear_combination (3 * Λ) * hcmuE
  have hcmΛ : 6 * Λ * cm = 288 / 49 * (Λ ^ 2 * q) + 48 / 49 * (Λ * q) + 6 * Λ := by
    rw [hcm]; ring
  have hP0 : 0 ≤ Λ ^ 2 * q := by positivity
  have h1 : Λ ^ 2 * q * u ≤ Λ ^ 2 * q * (1 / 16) := mul_le_mul_of_nonneg_left hu hP0
  have h2 : 2401 * (Λ * q) ≤ Λ ^ 2 * q := by
    have := mul_le_mul_of_nonneg_right hΛ0 (mul_nonneg (by linarith : (0 : ℝ) ≤ Λ) hq0)
    linarith [show Λ * (Λ * q) = Λ ^ 2 * q by ring]
  have h3 : q ≤ Λ * q := by nlinarith
  have h4 : 0 < 3 * Λ * cmu Λ cm := by positivity
  rw [hN, hR, hcmΛ]
  linarith

theorem h0Xc_nonneg {Lr Cf ℓ KT B ρ : ℝ} (hCf : 0 ≤ Cf) (hKT : 0 ≤ KT) (hB : 0 ≤ B)
    (hρ : 0 ≤ ρ) : 0 ≤ h0Xc Lr Cf ℓ KT B ρ := by
  unfold h0Xc h0n1 h0yc h0xa h0kc h0e0; positivity

/-- **The slack inequality at `θ = (3/4)c_μ`, `c₁ = θǧ^c`** (real form). -/
theorem h0Slack_win {Lr Cf ℓ cNL KT B ρ cμ gc ε mV pW : ℝ} (hCf : 0 ≤ Cf) (hcNL : 0 ≤ cNL)
    (hKT : 0 ≤ KT) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (hcμ : 0 < cμ) (hgc : 0 < gc) (hgε : gc ≤ ε)
    (hmV : 0 ≤ mV) (hmg : mV ≤ gc) (hW : 3 / 4 * cμ * (1 + 2 * pW * cμ) < cμ)
    (hε : ε ≤ 4 / 5) (hX : 5 / 4 * h0Xc Lr Cf ℓ KT B ρ * ε ≤ 1)
    (hK : 5 * (cNL + 2) < 3 * Lr ^ 4 * cμ) :
    ∀ g : ℝ, 0 ≤ g → g ≤ gc + pW * (3 / 4 * cμ * gc - -(3 / 4 * cμ * gc)) →
      h0Slack Lr Cf ℓ cNL KT B ρ g mV < Lr ^ 4 * (3 / 4 * cμ * gc) := by
  intro g hg0 hg
  have hp : 3 / 2 * pW * cμ < 1 / 4 := by
    have h1 : 3 / 2 * pW * cμ * cμ < 1 / 4 * cμ := by nlinarith
    by_contra hc; rw [not_lt] at hc
    have := mul_le_mul_of_nonneg_right hc hcμ.le
    linarith
  have hgG : g ≤ 5 / 4 * gc := by
    have e : pW * (3 / 4 * cμ * gc - -(3 / 4 * cμ * gc)) = 3 / 2 * pW * cμ * gc := by ring
    have := mul_le_mul_of_nonneg_right hp.le hgc.le
    linarith
  have hX0 := h0Xc_nonneg (Lr := Lr) (ℓ := ℓ) hCf hKT hB hρ
  have hG1 : 5 / 4 * gc ≤ 1 := by linarith
  have hS1 := h0Slack_mono (Lr := Lr) (ℓ := ℓ) (cNL := cNL) (B := B) hCf hcNL hKT hB hρ hg0 hgG hmV
    (show mV ≤ 5 / 4 * gc by linarith)
  have hS2 := h0Slack_le_lin (Lr := Lr) (ℓ := ℓ) (cNL := cNL) (KT := KT) (B := B) (ρ := ρ) hCf hKT hB
    hρ (by linarith : (0 : ℝ) ≤ 5 / 4 * gc) hG1
  have hXG : h0Xc Lr Cf ℓ KT B ρ * (5 / 4 * gc) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hgε hX0
    linarith
  have hS3 : (cNL + 1 + h0Xc Lr Cf ℓ KT B ρ * (5 / 4 * gc)) * (5 / 4 * gc) ≤
      (cNL + 2) * (5 / 4 * gc) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hS4 : (cNL + 2) * (5 / 4 * gc) < Lr ^ 4 * (3 / 4 * cμ * gc) := by
    have := mul_lt_mul_of_pos_right hK hgc
    linarith [show (cNL + 2) * (5 / 4 * gc) = 5 * (cNL + 2) * gc / 4 by ring,
      show Lr ^ 4 * (3 / 4 * cμ * gc) = 3 * Lr ^ 4 * cμ * gc / 4 by ring]
  linarith

end

end Spin2
