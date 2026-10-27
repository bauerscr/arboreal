import Step2.Flow.FlowF1b

/-!
# (F1) for the RG map

`F1_rg`: along regular histories, `|G_j - g_j - β g_j²| ≤ δ β g_j² + c_g g_j³`, given the values
of the one-loop coefficients (`2 Z C'(e₁, 0) - Z²(q_{jj} + ∑_k b_{jk}) = β + O(1) + O(g)`) and the
decay of the past coefficients.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- **The inputs of one step at the causal field scale**: `‖V♭‖ ≤ c_M ℓ²(2|μ| + 2η) + 8ℓ⁴g` and
`‖K♭‖_{A/2} ≤ 8 ‖K‖_A`. -/
theorem step_inputs {R : RGPar 2 L N} {j : ℕ} (hV : ValidAt R j) {st : RawSt 2 L N}
    (H : RawInv R j st) {g μ η : ℝ} (hg0 : 0 ≤ g) (hz : ‖st.z / st.Z‖ ≤ η)
    (hy : ‖st.y / st.Z‖ ≤ η) (hη : 2 * η ≤ R.ρ) (hηs : 8 * cM * R.ℓ ^ 2 * η ≤ 1 / 2)
    (hm : |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) {K : Act 2 L N} {A k : ℝ} (hA : 2 ≤ A) (hk0 : 0 ≤ k)
    (hKk : Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k) :
    Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤
        ENNReal.ofReal (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) ∧
      Knorm j (fscale st.Z * R.ℓ) (A / 2) (Kflat j (stDelta R j st) K) ≤ ENNReal.ofReal (8 * k) := by
  have hV' := hV
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  have hjN : j < N := by omega
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hs := fscale_pos hZ
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hgr := norm_stGr_le R j st g μ
  rw [abs_of_nonneg hg0] at hgr
  have hrZ : ‖stZ' R st / st.Z‖ ≤ 9 / 8 := by
    have e : stZ' R st / st.Z = 1 + stZeta R st := by
      unfold stZ'; rw [mul_div_cancel_left₀ _ hZ]
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  refine ⟨?_, ?_⟩
  · have e : stVf R j st g μ = VfamL j ![0, 0, (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) -
        stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2] := stVf_eq hZ hzy hyc
    rw [e]
    refine (Fnorm_VfamL_norm2 j hjN.le hℓ hZ _ 0 0 _ _ μ R.msq).trans
      (ENNReal.ofReal_le_ofReal ?_)
    simp only [zero_div, norm_zero, add_zero]
    rw [norm_stA_div hZ]
    have : ‖stZeta R st‖ * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
      rw [mul_assoc]
      calc ‖stZeta R st‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
        _ = 2 * η := mul_one _
    have h1 : ‖stZ' R st / st.Z‖ * |μ| ≤ 2 * |μ| := by
      have := mul_le_mul_of_nonneg_right hrZ (abs_nonneg μ); linarith [abs_nonneg μ]
    have h2 : ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ ≤ 2 * g := by
      have hr2 : ‖stZ' R st / st.Z‖ ^ 2 ≤ 81 / 64 := by
        have := norm_nonneg (stZ' R st / st.Z); nlinarith
      calc ‖stZ' R st / st.Z‖ ^ 2 * ‖stGr R j st g μ‖ ≤ 81 / 64 * (8 / 7 * g) := by
            gcongr
        _ ≤ 2 * g := by linarith
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (add_le_add h1 this) (mul_nonneg hM (sq_nonneg R.ℓ))
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * R.ℓ ^ 4)
    nlinarith
  · set δΔ := 8 * cM * R.ℓ ^ 2 * η with hδΔ
    have hδΔ0 : 0 ≤ δΔ := by
      have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
    have hΔ : Fnorm j (fscale st.Z * R.ℓ) (stDelta R j st) ≤ ENNReal.ofReal δΔ := by
      refine (Fnorm_stDelta_le hjN.le hℓ hZ (2 * η) hζη
        (by rw [stYc_eq hZ hyc]; linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      have : 2 * η * |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 2 * η := by
        rw [mul_assoc]
        calc 2 * η * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
          _ = 2 * η := mul_one _
      have hM : 0 ≤ cM := Nat.cast_nonneg _
      rw [hδΔ]
      nlinarith [mul_nonneg hM (sq_nonneg R.ℓ)]
    have hKf := Knorm_stKflat_le (R := R) j hsℓ (by linarith : (0 : ℝ) ≤ A) hδΔ0 st hΔ K
    have hexp : Real.exp (4 * δΔ) ≤ 8 := by
      have : 4 * δΔ ≤ 2 := by linarith
      calc Real.exp (4 * δΔ) ≤ Real.exp 2 := Real.exp_le_exp.2 this
        _ ≤ 8 := by
            have := Real.exp_one_lt_d9
            have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
            nlinarith [Real.exp_pos 1]
    have hmono : A / 2 ≤ A * Real.exp (-δΔ) := by
      have : (1 : ℝ) / 2 ≤ Real.exp (-δΔ) := by
        have h1 := Real.add_one_le_exp (-δΔ)
        linarith
      nlinarith
    refine (Knorm_mono_A (by linarith) hmono _).trans (hKf.trans ?_)
    rw [ENNReal.ofReal_mul (by norm_num)]
    calc ENNReal.ofReal (Real.exp (4 * δΔ)) * Knorm j (fscale st.Z * R.ℓ) A K
        ≤ ENNReal.ofReal 8 * ENNReal.ofReal k := by
          gcongr
      _ = _ := rfl

/-! ### Arithmetic helpers for the normalised bounds -/

theorem hb_inv1 {Cq R ℓ2 aZ a : ℝ} (hCq : 0 ≤ Cq) (hR : 0 ≤ R) (hℓ : 0 < ℓ2) (ha : 0 < a)
    (haZ : 0 < aZ) (hr : aZ ≤ 8 / 7 * a) : Cq * (ℓ2 / aZ)⁻¹ * R / a ≤ 8 / 7 * (Cq * R / ℓ2) := by
  rw [inv_div, div_le_iff₀ ha]
  have e : Cq * (aZ / ℓ2) * R = Cq * R / ℓ2 * aZ := by ring
  rw [e]
  have h0 : 0 ≤ Cq * R / ℓ2 := by positivity
  calc Cq * R / ℓ2 * aZ ≤ Cq * R / ℓ2 * (8 / 7 * a) := mul_le_mul_of_nonneg_left hr h0
    _ = _ := by ring

theorem hb_inv2 {Cq R ℓ2 aZ a : ℝ} (hCq : 0 ≤ Cq) (hR : 0 ≤ R) (hℓ : 0 < ℓ2) (ha : 0 < a)
    (haZ : 0 < aZ) (hr : aZ ≤ 8 / 7 * a) :
    Cq * ((ℓ2 / aZ) ^ 2)⁻¹ * R / a ^ 2 ≤ 64 / 49 * (Cq * R / ℓ2 ^ 2) := by
  rw [div_pow, inv_div, div_le_iff₀ (by positivity)]
  have e : Cq * (aZ ^ 2 / ℓ2 ^ 2) * R = Cq * R / ℓ2 ^ 2 * aZ ^ 2 := by ring
  rw [e]
  have h0 : 0 ≤ Cq * R / ℓ2 ^ 2 := by positivity
  have h2 : aZ ^ 2 ≤ 64 / 49 * a ^ 2 := by nlinarith
  calc Cq * R / ℓ2 ^ 2 * aZ ^ 2 ≤ Cq * R / ℓ2 ^ 2 * (64 / 49 * a ^ 2) := mul_le_mul_of_nonneg_left h2 h0
    _ = _ := by ring

theorem hb_inv0 {Cq R ℓ2 a : ℝ} (hℓ : 0 < ℓ2) (ha : 0 < a) : Cq * (ℓ2 / a)⁻¹ * R / a = Cq * R / ℓ2 := by
  field_simp

theorem hb_inv0' {Cq R ℓ2 a : ℝ} (hℓ : 0 < ℓ2) (ha : 0 < a) :
    Cq * ((ℓ2 / a) ^ 2)⁻¹ * R / a ^ 2 = Cq * R / ℓ2 ^ 2 := by
  field_simp

/-! ### The constants of the one-step expansion -/

/-- `|n| ≤ c_n g`. -/
def f1cn (ℓ cmu : ℝ) : ℝ := 4 * cmu * ℓ ^ 2
/-- `|κ'_ν/Z| L^{2(j+1)} ≤ c_K g`. -/
def f1cK (L : ℕ) (ℓ cZ cmu Cq cRQ cRL : ℝ) : ℝ :=
  (L : ℝ) ^ 2 * (cmu + 3 * cZ) + ℓ ^ 2 / 7 + (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) / ℓ ^ 2
/-- `|n'| ≤ c_{n'} g`. -/
def f1cn' (L : ℕ) (ℓ cZ cmu Cq cRQ cRL : ℝ) : ℝ := 4 * f1cK L ℓ cZ cmu Cq cRQ cRL * ℓ ^ 2
/-- `|ζ_{j+1} + c g| ≤ c_w g²`. -/
def f1cw (ℓ cmu Cq cRQ cRL : ℝ) : ℝ := (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 + ℓ ^ 2 * f1cn ℓ cmu / 7
/-- The `g²`-remainder, from the sharp bounds `|a m² w⁽¹⁾| ≤ e_A g` and `|Z² δ w⁽¹⁾| ≤ e_B`. -/
def f1e (eA eB : ℝ) : ℝ := 32 / 7 * eA + 1024 / 49 * eB
/-- `|C⁽¹⁾ ν'| ≤ c_{Cν} g`. -/
def f1cCnu (L : ℕ) (ℓ cZ cmu : ℝ) : ℝ := 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * (cmu + 3 * cZ) + ℓ ^ 2 / 7)
/-- The cubic remainder of `P`. -/
def f1cP (L : ℕ) (ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES : ℝ) : ℝ :=
  32 / 7 * (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) +
    32 / 7 * f1cCnu L ℓ cZ cmu * f1cn' L ℓ cZ cmu Cq cRQ cRL +
    9 / 8 * (cES + 3 * f1cn ℓ cmu * KB) + 2 * KB * f1cn' L ℓ cZ cmu Cq cRQ cRL +
    9 / 8 * ((64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4)
/-- The cubic constant of (F1). -/
def f1c3 (L : ℕ) (ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES eA eB : ℝ) : ℝ :=
  let c₁ := ℓ ^ 2 / 8 + 2 * KB
  let cw := f1cw ℓ cmu Cq cRQ cRL
  let e := f1e eA eB
  let cP := f1cP L ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES
  cP + 2 * cw + 5 * (c₁ + cw) ^ 2 + 3 * (c₁ + e + cP) * (c₁ + cw)

set_option maxHeartbeats 4000000 in
/-- **The core of the one-step (F1) estimate**, in plain numbers. -/
theorem F1_core {L : ℕ} {g ℓ Lj aZ cZ cmu Cq RQ RL CqD RD cRQ cRL cRD cES KB ρ msqR : ℝ}
    {z c₀ δ gr nuS A w1 C1 κQz κQy κQnu κQg κLz κLy κLnu κDg S q SB ES : ℂ}
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hℓ : 0 < ℓ) (hL4 : (4 : ℝ) ≤ (L : ℝ) ^ 2) (hLj1 : 1 ≤ Lj)
    (hap : 0 < ‖z‖) (haZp : 0 < aZ) (hr : aZ ≤ 8 / 7 * ‖z‖)
    (hcZ : 0 ≤ cZ) (hcmu : 0 ≤ cmu) (hCq : 0 ≤ Cq) (hCqD : 0 ≤ CqD) (hcRQ : 0 ≤ cRQ)
    (hcRL : 0 ≤ cRL) (hcRD : 0 ≤ cRD) (hKB : 0 ≤ KB) (hcES : 0 ≤ cES) (hρ0 : 0 ≤ ρ)
    (hρ8 : ρ ≤ 1 / 8)
    (hG : (g : ℂ) = gr * (1 + nCor nuS w1))
    (hnuS : ‖nuS / z‖ * ((L : ℝ) ^ 2 * Lj) ≤ (L : ℝ) ^ 2 * (cmu * g))
    (hA : ‖A / z‖ ≤ 16 / 7 * (cZ * g)) (hmsq : |msqR| * Lj ≤ 1) {eA eB : ℝ} (heA : 0 ≤ eA) (heB : 0 ≤ eB)
    (hT1 : ‖A * (msqR : ℂ) * w1‖ ≤ eA * g) (hT2 : ‖z ^ 2 * δ * w1‖ ≤ eB)
    (hzw1 : ‖z * w1‖ ≤ ℓ ^ 2 * Lj) (hzC1 : ‖z * C1‖ ≤ 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * Lj))
    (hzc0 : ‖z * c₀‖ ≤ ℓ ^ 2 / 16) (hzδ : ‖z * δ‖ * ((L : ℝ) ^ 2 * Lj) ≤ ℓ ^ 2 / 32)
    (q1 : ‖κQz‖ ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ) (q2 : ‖κQy‖ ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ)
    (q3 : ‖κQnu‖ ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / Lj) (q4 : ‖κQg‖ ≤ Cq * ((ℓ ^ 2 / aZ) ^ 2)⁻¹ * RQ)
    (l1 : ‖κLz‖ ≤ Cq * (ℓ ^ 2 / ‖z‖)⁻¹ * RL) (l2 : ‖κLy‖ ≤ Cq * (ℓ ^ 2 / ‖z‖)⁻¹ * RL)
    (l3 : ‖κLnu‖ ≤ Cq * (ℓ ^ 2 / ‖z‖)⁻¹ * RL / ((L : ℝ) ^ 2 * Lj))
    (hDg : ‖κDg‖ ≤ CqD * ((ℓ ^ 2 / ‖z‖) ^ 2)⁻¹ * RD)
    (hRQ0 : 0 ≤ RQ) (hRL0 : 0 ≤ RL) (hRD0 : 0 ≤ RD)
    (hRQ : RQ ≤ cRQ * g ^ 3) (hRL : RL ≤ cRL * g ^ 2) (hRD : RD ≤ cRD * g ^ 3)
    (hS : S = z ^ 2 * ((g : ℂ) ^ 2 * SB + ES)) (hES : ‖ES‖ ≤ cES * g ^ 3)
    (hq : ‖z ^ 2 * q‖ ≤ KB) (hSB : ‖SB‖ ≤ KB)
    (hn8 : f1cn ℓ cmu * g ≤ 1 / 8) (hn'8 : f1cn' L ℓ cZ cmu Cq cRQ cRL * g ≤ 1 / 8)
    (hζ8 : (ℓ ^ 2 / 7 + f1cw ℓ cmu Cq cRQ cRL) * g ≤ ρ) :
    let K0 := -(gr * z ^ 2) * c₀ - (κQz - κQg * c₀) - κLz
    let K1 := -(gr * z ^ 2) * δ - (κQy - κQg * δ) - κLy
    let K2 := nuS - A * (msqR : ℂ) + 4 * (gr * z ^ 2) * δ - (κQnu + 4 * κQg * δ) - κLnu
    let K3 := gr * z ^ 2 - κQg - (S + (gr * z ^ 2) ^ 2 * q +
      4 * C1 * (gr * z ^ 2) * (nuS - A * msqR + 4 * (gr * z ^ 2) * δ)) - κDg
    |(K3 / (z * (1 + clampDisk ρ ((K0 + K1) / z))) ^ 2 * (1 + nCor K2 (w1 + C1))).re - g -
        (2 * (z * (c₀ + δ)) - (z ^ 2 * q + SB)).re * g ^ 2| ≤
      f1e eA eB * g ^ 2 + f1c3 L ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES eA eB * g ^ 3 := by
  intro K0 K1 K2 K3
  have hLj : 0 < Lj := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hap
  set a := ‖z‖ with ha
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hg3 : g ^ 3 ≤ g ^ 2 := by nlinarith [sq_nonneg g]
  have hLLj : 0 < (L : ℝ) ^ 2 * Lj := by positivity
  -- `n`
  have hnw : ‖4 * nuS * w1‖ ≤ f1cn ℓ cmu * g := by
    have e : 4 * nuS * w1 = 4 * (nuS / z) * (z * w1) := by field_simp
    rw [e, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    have h1 : ‖nuS / z‖ ≤ cmu * g / Lj := by
      rw [le_div_iff₀ hLj]
      have := hnuS
      rw [show ‖nuS / z‖ * ((L : ℝ) ^ 2 * Lj) = (L : ℝ) ^ 2 * (‖nuS / z‖ * Lj) by ring] at this
      exact le_of_mul_le_mul_left this (by linarith)
    calc 4 * ‖nuS / z‖ * ‖z * w1‖ ≤ 4 * (cmu * g / Lj) * (ℓ ^ 2 * Lj) := by gcongr
      _ = f1cn ℓ cmu * g := by unfold f1cn; field_simp
  set n := nCor nuS w1 with hndef
  have hn : n = 4 * nuS * w1 := by rw [hndef, nCor, clampDisk_of_le (hnw.trans hn8)]
  have hnb : ‖n‖ ≤ f1cn ℓ cmu * g := by rw [hn]; exact hnw
  have h1n : 7 / 8 ≤ ‖1 + n‖ := norm_one_add_nCor _ _
  have h1n0 : 1 + n ≠ 0 := one_add_nCor_ne _ _
  have hgr : gr = (g : ℂ) / (1 + n) := by rw [hG]; field_simp
  have hgrb : ‖gr‖ ≤ 8 / 7 * g := by
    rw [hgr, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0,
      div_le_iff₀ (by linarith)]
    nlinarith
  -- `κ'_ν/z`
  set P := (L : ℝ) ^ 2 * Lj with hPdef
  have hQ1 := hb_inv1 hCq hRQ0 hℓ2 hap haZp hr
  have hQ2 := hb_inv2 hCq hRQ0 hℓ2 hap haZp hr
  have hL0 := hb_inv0 (Cq := Cq) (R := RL) hℓ2 hap
  have hD0 := hb_inv0' (Cq := CqD) (R := RD) hℓ2 hap
  have hRQg : RQ ≤ cRQ * g := hRQ.trans (by nlinarith [sq_nonneg g])
  have hRLg : RL ≤ cRL * g := hRL.trans (by nlinarith)
  have b1 : ‖A * (msqR : ℂ) / z‖ * P ≤ (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) := by
    rw [mul_div_right_comm, norm_mul, Complex.norm_real, Real.norm_eq_abs, hPdef]
    have h0 : 0 ≤ 16 / 7 * (cZ * g) := by positivity
    calc ‖A / z‖ * |msqR| * ((L : ℝ) ^ 2 * Lj) = (L : ℝ) ^ 2 * (‖A / z‖ * (|msqR| * Lj)) := by ring
      _ ≤ (L : ℝ) ^ 2 * (16 / 7 * (cZ * g) * 1) := by gcongr
      _ = _ := by ring
  have b2 : ‖4 * (gr * z ^ 2) * δ / z‖ * P ≤ ℓ ^ 2 / 7 * g := by
    have e : 4 * (gr * z ^ 2) * δ / z = 4 * gr * (z * δ) := by field_simp
    rw [e, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    calc 4 * ‖gr‖ * ‖z * δ‖ * P = 4 * ‖gr‖ * (‖z * δ‖ * P) := by ring
      _ ≤ 4 * (8 / 7 * g) * (ℓ ^ 2 / 32) := by gcongr
      _ = _ := by ring
  have b3 : ‖κQnu / z‖ * P ≤ (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) := by
    rw [norm_div, ← ha, hPdef]
    have h1 : ‖κQnu‖ / a ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / Lj / a := div_le_div_of_nonneg_right q3 hap.le
    calc ‖κQnu‖ / a * ((L : ℝ) ^ 2 * Lj) ≤ Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / Lj / a * ((L : ℝ) ^ 2 * Lj) :=
          mul_le_mul_of_nonneg_right h1 hLLj.le
      _ = (L : ℝ) ^ 2 * (Cq * (ℓ ^ 2 / aZ)⁻¹ * RQ / a) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ1 (by positivity)
  have b4 : ‖4 * κQg * δ / z‖ * P ≤ 8 / 49 * (Cq * RQ / ℓ ^ 2) := by
    have e : 4 * κQg * δ / z = 4 * κQg * (z * δ) / z ^ 2 := by field_simp
    rw [e, norm_div, norm_mul, norm_mul, norm_pow, ← ha]; simp only [Complex.norm_ofNat]
    have h1 : ‖κQg‖ / a ^ 2 ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) :=
      (div_le_div_of_nonneg_right q4 (by positivity)).trans hQ2
    calc 4 * ‖κQg‖ * ‖z * δ‖ / a ^ 2 * P = 4 * (‖κQg‖ / a ^ 2) * (‖z * δ‖ * P) := by ring
      _ ≤ 4 * (64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2)) * (ℓ ^ 2 / 32) := by gcongr
      _ = _ := by field_simp; ring
  have b5 : ‖κLnu / z‖ * P ≤ Cq * RL / ℓ ^ 2 := by
    rw [norm_div, ← ha, ← hL0]
    have h1 : ‖κLnu‖ / a ≤ Cq * (ℓ ^ 2 / a)⁻¹ * RL / P / a := div_le_div_of_nonneg_right l3 hap.le
    calc ‖κLnu‖ / a * P ≤ Cq * (ℓ ^ 2 / a)⁻¹ * RL / P / a * P := mul_le_mul_of_nonneg_right h1 hLLj.le
      _ = _ := by field_simp
  have hK2b : ‖K2 / z‖ * P ≤ f1cK L ℓ cZ cmu Cq cRQ cRL * g := by
    have e : K2 / z = nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z -
        (κQnu / z + 4 * κQg * δ / z) - κLnu / z := by simp only [K2]; ring
    rw [e]
    have hsum : ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z -
        (κQnu / z + 4 * κQg * δ / z) - κLnu / z‖ ≤
        ‖nuS / z‖ + ‖A * (msqR : ℂ) / z‖ + ‖4 * (gr * z ^ 2) * δ / z‖ +
          (‖κQnu / z‖ + ‖4 * κQg * δ / z‖) + ‖κLnu / z‖ :=
      (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) (norm_add_le _ _))) le_rfl)
    have hP := mul_le_mul_of_nonneg_right hsum hLLj.le
    have h1 : Cq * RQ / ℓ ^ 2 ≤ Cq * cRQ / ℓ ^ 2 * g := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr
    have h2 : Cq * RL / ℓ ^ 2 ≤ Cq * cRL / ℓ ^ 2 * g := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr
    have hcq : 0 ≤ Cq * RQ / ℓ ^ 2 := by positivity
    unfold f1cK
    have e3 : ((L : ℝ) ^ 2 * (cmu + 3 * cZ) + ℓ ^ 2 / 7 +
        (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) / ℓ ^ 2) * g =
        (L : ℝ) ^ 2 * (cmu * g) + (L : ℝ) ^ 2 * (3 * (cZ * g)) + ℓ ^ 2 / 7 * g +
          2 * (L : ℝ) ^ 2 * (Cq * cRQ / ℓ ^ 2 * g) + Cq * cRL / ℓ ^ 2 * g := by ring
    rw [e3]
    have hcz : 0 ≤ cZ * g := by positivity
    have hL2 : 0 ≤ (L : ℝ) ^ 2 := by positivity
    have k1 : (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) ≤ (L : ℝ) ^ 2 * (3 * (cZ * g)) :=
      mul_le_mul_of_nonneg_left (by linarith) hL2
    have k2 : (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) ≤
        2 * (L : ℝ) ^ 2 * (Cq * cRQ / ℓ ^ 2 * g) := by
      have : (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) ≤
          2 * (L : ℝ) ^ 2 * (Cq * RQ / ℓ ^ 2) := by nlinarith
      exact this.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    linarith [hP, hnuS, b1, b2, b3, b4, b5, k1, k2, h2]
  -- `n'`
  have hzW : ‖z * (w1 + C1)‖ ≤ ℓ ^ 2 * P := by
    rw [mul_add]; refine (norm_add_le _ _).trans ?_
    have h1 : ℓ ^ 2 * Lj ≤ ℓ ^ 2 * P / 4 := by
      rw [hPdef]; have := mul_le_mul_of_nonneg_left hL4 (by positivity : (0 : ℝ) ≤ ℓ ^ 2 * Lj)
      linarith
    have h2 : 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * Lj) = 9 / 16 * (ℓ ^ 2 * P) := by rw [hPdef]; ring
    have h3 : 0 ≤ ℓ ^ 2 * P := by positivity
    linarith [hzw1, hzC1]
  have hn'w : ‖4 * K2 * (w1 + C1)‖ ≤ f1cn' L ℓ cZ cmu Cq cRQ cRL * g := by
    have e : 4 * K2 * (w1 + C1) = 4 * (K2 / z) * (z * (w1 + C1)) := by field_simp
    rw [e, norm_mul, norm_mul]; simp only [Complex.norm_ofNat]
    unfold f1cn'
    calc 4 * ‖K2 / z‖ * ‖z * (w1 + C1)‖ ≤ 4 * ‖K2 / z‖ * (ℓ ^ 2 * P) := by gcongr
      _ = 4 * (‖K2 / z‖ * P) * ℓ ^ 2 := by ring
      _ ≤ 4 * (f1cK L ℓ cZ cmu Cq cRQ cRL * g) * ℓ ^ 2 := by gcongr
      _ = _ := by ring
  set n' := nCor K2 (w1 + C1) with hn'def
  have hn' : n' = 4 * K2 * (w1 + C1) := by rw [hn'def, nCor, clampDisk_of_le (hn'w.trans hn'8)]
  have hn'b : ‖n'‖ ≤ f1cn' L ℓ cZ cmu Cq cRQ cRL * g := by rw [hn']; exact hn'w
  have h1n' : ‖1 + n'‖ ≤ 9 / 8 := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith [hn'b.trans hn'8]
  -- the field strength `ζ_{j+1}`
  have hP1 : 1 ≤ P := by
    rw [hPdef]; nlinarith [hL4, hLj1]
  have hzδ1 : ‖z * δ‖ ≤ ℓ ^ 2 / 32 := by
    have h0 := norm_nonneg (z * δ)
    have : ‖z * δ‖ * 1 ≤ ‖z * δ‖ * P := mul_le_mul_of_nonneg_left hP1 h0
    linarith
  set c := z * (c₀ + δ) with hcdef
  have hcb : ‖c‖ ≤ ℓ ^ 2 / 8 := by
    rw [hcdef, mul_add]; refine (norm_add_le _ _).trans ?_; linarith
  set rw0 := (-(κQz + κQy) + κQg * (c₀ + δ) - (κLz + κLy)) / z with hrw0
  have hrw0b : ‖rw0‖ ≤ (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 * g ^ 2 := by
    have e : rw0 = -(κQz / z) - κQy / z + κQg * c / z ^ 2 - κLz / z - κLy / z := by
      rw [hrw0, hcdef]; field_simp; ring
    rw [e]
    have a1 : ‖κQz / z‖ ≤ 8 / 7 * (Cq * RQ / ℓ ^ 2) := by
      rw [norm_div, ← ha]; exact (div_le_div_of_nonneg_right q1 hap.le).trans hQ1
    have a2 : ‖κQy / z‖ ≤ 8 / 7 * (Cq * RQ / ℓ ^ 2) := by
      rw [norm_div, ← ha]; exact (div_le_div_of_nonneg_right q2 hap.le).trans hQ1
    have a3 : ‖κQg * c / z ^ 2‖ ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) * (ℓ ^ 2 / 8) := by
      rw [norm_div, norm_mul, norm_pow, ← ha, mul_div_right_comm]
      have h1 : ‖κQg‖ / a ^ 2 ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) :=
        (div_le_div_of_nonneg_right q4 (by positivity)).trans hQ2
      exact mul_le_mul h1 hcb (norm_nonneg _) (by positivity)
    have a4 : ‖κLz / z‖ ≤ Cq * RL / ℓ ^ 2 := by
      rw [norm_div, ← ha, ← hL0]; exact div_le_div_of_nonneg_right l1 hap.le
    have a5 : ‖κLy / z‖ ≤ Cq * RL / ℓ ^ 2 := by
      rw [norm_div, ← ha, ← hL0]; exact div_le_div_of_nonneg_right l2 hap.le
    have hsum : ‖-(κQz / z) - κQy / z + κQg * c / z ^ 2 - κLz / z - κLy / z‖ ≤
        ‖κQz / z‖ + ‖κQy / z‖ + ‖κQg * c / z ^ 2‖ + ‖κLz / z‖ + ‖κLy / z‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add
          (norm_neg _).le le_rfl)) le_rfl)) le_rfl)) le_rfl)
    have e3 : 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) * (ℓ ^ 2 / 8) = 8 / 49 * (Cq * RQ / ℓ ^ 2) := by
      field_simp; ring
    have h1 : Cq * RQ / ℓ ^ 2 ≤ Cq * cRQ / ℓ ^ 2 * g ^ 2 := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr; exact hRQ.trans (mul_le_mul_of_nonneg_left hg3 hcRQ)
    have h2 : Cq * RL / ℓ ^ 2 ≤ Cq * cRL / ℓ ^ 2 * g ^ 2 := by
      rw [div_mul_eq_mul_div, mul_assoc]; gcongr
    have e4 : (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 * g ^ 2 =
        3 * (Cq * cRQ / ℓ ^ 2 * g ^ 2) + 2 * (Cq * cRL / ℓ ^ 2 * g ^ 2) := by ring
    rw [e4]
    have hq0 : 0 ≤ Cq * RQ / ℓ ^ 2 := by positivity
    linarith [hsum, a1, a2, a3, a4, a5, e3, h1, h2]
  have hK01 : (K0 + K1) / z = -(gr * c) + rw0 := by
    simp only [K0, K1]; rw [hrw0, hcdef]; field_simp; ring
  have hgrn : (g : ℂ) - gr = gr * n := by rw [hG]; ring
  set rw := rw0 + c * (gr * n) with hrwdef
  have hw_eq : (K0 + K1) / z = -(c * g) + rw := by
    rw [hK01, hrwdef, ← hgrn]; ring
  have hcw : ‖rw‖ ≤ f1cw ℓ cmu Cq cRQ cRL * g ^ 2 := by
    rw [hrwdef]; refine (norm_add_le _ _).trans ?_
    have h1 : ‖c * (gr * n)‖ ≤ ℓ ^ 2 / 8 * (8 / 7 * g) * (f1cn ℓ cmu * g) := by
      rw [norm_mul c, norm_mul gr n, ← mul_assoc]
      exact mul_le_mul (mul_le_mul hcb hgrb (norm_nonneg _) (by positivity)) hnb (norm_nonneg _)
        (by positivity)
    unfold f1cw
    have e : ℓ ^ 2 / 8 * (8 / 7 * g) * (f1cn ℓ cmu * g) = ℓ ^ 2 * f1cn ℓ cmu / 7 * g ^ 2 := by ring
    rw [e] at h1
    have e2 : ((3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 + ℓ ^ 2 * f1cn ℓ cmu / 7) * g ^ 2 =
        (3 * Cq * cRQ + 2 * Cq * cRL) / ℓ ^ 2 * g ^ 2 + ℓ ^ 2 * f1cn ℓ cmu / 7 * g ^ 2 := by ring
    rw [e2]; linarith
  have hwin : ‖(K0 + K1) / z‖ ≤ ρ := by
    rw [hw_eq]; refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]
    have h1 : ‖c‖ * g ≤ ℓ ^ 2 / 7 * g := mul_le_mul_of_nonneg_right (by linarith) hg0
    have hcw0 : 0 ≤ f1cw ℓ cmu Cq cRQ cRL := by unfold f1cw f1cn; positivity
    have h2 : f1cw ℓ cmu Cq cRQ cRL * g ^ 2 ≤ f1cw ℓ cmu Cq cRQ cRL * g :=
      mul_le_mul_of_nonneg_left hg2 hcw0
    have e : (ℓ ^ 2 / 7 + f1cw ℓ cmu Cq cRQ cRL) * g = ℓ ^ 2 / 7 * g + f1cw ℓ cmu Cq cRQ cRL * g := by
      ring
    linarith
  have hw : clampDisk ρ ((K0 + K1) / z) = (K0 + K1) / z := clampDisk_of_le hwin
  rw [hw]
  -- the expansion of `P`
  have hid := P_identity (z := z) (gr := gr) (n := n) (n' := n') (K2 := K2) (K3 := K3) (nu := nuS)
    (a := A) (msq := (msqR : ℂ)) (w1 := w1) (C1 := C1) (δ := δ) (κQg := κQg) (κQnu := κQnu)
    (κLnu := κLnu) (κDg := κDg) (S := S) (q := q) (SB := SB) (ES := ES) (G := (g : ℂ)) hz0 hG hn
    hn' rfl rfl hS
  -- the remainder bounds
  have hgg : ‖gr ^ 2 - (g : ℂ) ^ 2‖ ≤ 3 * f1cn ℓ cmu * g ^ 3 := by
    have e : gr ^ 2 - (g : ℂ) ^ 2 = -((g : ℂ) ^ 2 * (n * (2 + n)) / (1 + n) ^ 2) := by
      rw [hgr]; field_simp; ring
    rw [e, norm_neg, norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hg0]
    have h2 : ‖2 + n‖ ≤ 17 / 8 := by
      refine (norm_add_le _ _).trans ?_; simp only [Complex.norm_ofNat]; linarith [hnb.trans hn8]
    have h3 : (49 / 64 : ℝ) ≤ ‖1 + n‖ ^ 2 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 8) h1n 2
      linarith only [this, show ((7 : ℝ) / 8) ^ 2 = 49 / 64 by norm_num]
    rw [div_le_iff₀ (by linarith only [h3])]
    have hcn0 : 0 ≤ f1cn ℓ cmu * g := (norm_nonneg _).trans hnb
    have h4 : ‖n‖ * ‖2 + n‖ ≤ f1cn ℓ cmu * g * (17 / 8) := mul_le_mul hnb h2 (norm_nonneg _) hcn0
    have hA' : g ^ 2 * (‖n‖ * ‖2 + n‖) ≤ g ^ 2 * (f1cn ℓ cmu * g * (17 / 8)) :=
      mul_le_mul_of_nonneg_left h4 (sq_nonneg g)
    have hB : 3 * f1cn ℓ cmu * g ^ 3 * (49 / 64) ≤ 3 * f1cn ℓ cmu * g ^ 3 * ‖1 + n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by unfold f1cn; positivity)
    have h5 : 0 ≤ f1cn ℓ cmu * g ^ 3 := by unfold f1cn; positivity
    linarith only [hA', hB, h5]
  have hT3 : ‖(κQnu + 4 * κQg * δ + κLnu) * (w1 + C1)‖ ≤
      (2 * (L : ℝ) ^ 2 * Cq * cRQ + Cq * cRL) * g ^ 2 := by
    have e : (κQnu + 4 * κQg * δ + κLnu) * (w1 + C1) =
        (κQnu / z + 4 * κQg * δ / z + κLnu / z) * (z * (w1 + C1)) := by field_simp
    rw [e, norm_mul]
    have hs : ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * P ≤
        (L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) + Cq * RL / ℓ ^ 2 := by
      have h0 : ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ ≤
          ‖κQnu / z‖ + ‖4 * κQg * δ / z‖ + ‖κLnu / z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      have := mul_le_mul_of_nonneg_right h0 hLLj.le
      linarith only [this, b3, b4, b5]
    have h0 : 0 ≤ ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ := norm_nonneg _
    calc ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * ‖z * (w1 + C1)‖ ≤
        ‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * (ℓ ^ 2 * P) := by gcongr
      _ = (‖κQnu / z + 4 * κQg * δ / z + κLnu / z‖ * P) * ℓ ^ 2 := by ring
      _ ≤ ((L : ℝ) ^ 2 * (8 / 7 * (Cq * RQ / ℓ ^ 2)) + 8 / 49 * (Cq * RQ / ℓ ^ 2) +
          Cq * RL / ℓ ^ 2) * ℓ ^ 2 := by gcongr
      _ = ((L : ℝ) ^ 2 * (8 / 7) + 8 / 49) * (Cq * RQ) + Cq * RL := by field_simp
      _ ≤ 2 * (L : ℝ) ^ 2 * (Cq * (cRQ * g ^ 2)) + Cq * (cRL * g ^ 2) := by
          have hRQ2 : RQ ≤ cRQ * g ^ 2 := hRQ.trans (mul_le_mul_of_nonneg_left hg3 hcRQ)
          have h1 : Cq * RQ ≤ Cq * (cRQ * g ^ 2) := mul_le_mul_of_nonneg_left hRQ2 hCq
          have h2 : Cq * RL ≤ Cq * (cRL * g ^ 2) := mul_le_mul_of_nonneg_left hRL hCq
          have h3 : ((L : ℝ) ^ 2 * (8 / 7) + 8 / 49) * (Cq * RQ) ≤ 2 * (L : ℝ) ^ 2 * (Cq * RQ) := by
            have h0 : 0 ≤ Cq * RQ := by positivity
            have := mul_le_mul_of_nonneg_right hL4 h0
            linarith only [this, h0]
          have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) ^ 2)
          linarith only [h2, h3, h4]
      _ = _ := by ring
  have hT4 : ‖C1 * (nuS - A * msqR + 4 * (gr * z ^ 2) * δ)‖ ≤ f1cCnu L ℓ cZ cmu * g := by
    have e : C1 * (nuS - A * msqR + 4 * (gr * z ^ 2) * δ) =
        (z * C1) * (nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z) := by field_simp
    rw [e, norm_mul]
    have hs : ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ * P ≤
        (L : ℝ) ^ 2 * (cmu * g) + (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) + ℓ ^ 2 / 7 * g := by
      have h0 : ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ ≤
          ‖nuS / z‖ + ‖A * (msqR : ℂ) / z‖ + ‖4 * (gr * z ^ 2) * δ / z‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      have := mul_le_mul_of_nonneg_right h0 hLLj.le
      linarith only [this, hnuS, b1, b2]
    have h0 : 0 ≤ ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ := norm_nonneg _
    unfold f1cCnu
    calc ‖z * C1‖ * ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ ≤
        9 / 16 * ℓ ^ 2 * P * ‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ := by
          rw [hPdef]; gcongr
      _ = 9 / 16 * ℓ ^ 2 * (‖nuS / z - A * (msqR : ℂ) / z + 4 * (gr * z ^ 2) * δ / z‖ * P) := by ring
      _ ≤ 9 / 16 * ℓ ^ 2 * ((L : ℝ) ^ 2 * (cmu * g) + (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) +
          ℓ ^ 2 / 7 * g) := by gcongr
      _ ≤ _ := by
          have hcz : 0 ≤ cZ * g := by positivity
          have : (L : ℝ) ^ 2 * (16 / 7 * (cZ * g)) ≤ (L : ℝ) ^ 2 * (3 * (cZ * g)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          have h9 : (0 : ℝ) ≤ 9 / 16 * ℓ ^ 2 := by positivity
          linarith only [mul_le_mul_of_nonneg_left this h9]
  have hQD : ‖(κQg + κDg) / z ^ 2‖ ≤ (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3 := by
    rw [add_div]; refine (norm_add_le _ _).trans ?_
    rw [norm_div, norm_div, norm_pow, ← ha]
    have h1 : ‖κQg‖ / a ^ 2 ≤ 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) :=
      (div_le_div_of_nonneg_right q4 (by positivity)).trans hQ2
    have h2 : ‖κDg‖ / a ^ 2 ≤ CqD * RD / (ℓ ^ 2) ^ 2 := by
      rw [← hD0]; exact div_le_div_of_nonneg_right hDg (by positivity)
    have e : (64 / 49 * Cq * cRQ + CqD * cRD) / ℓ ^ 4 * g ^ 3 =
        64 / 49 * (Cq * (cRQ * g ^ 3) / (ℓ ^ 2) ^ 2) + CqD * (cRD * g ^ 3) / (ℓ ^ 2) ^ 2 := by
      field_simp
    rw [e]
    have h3 : 64 / 49 * (Cq * RQ / (ℓ ^ 2) ^ 2) ≤ 64 / 49 * (Cq * (cRQ * g ^ 3) / (ℓ ^ 2) ^ 2) := by
      gcongr
    have h4 : CqD * RD / (ℓ ^ 2) ^ 2 ≤ CqD * (cRD * g ^ 3) / (ℓ ^ 2) ^ 2 := by gcongr
    linarith only [h1, h2, h3, h4]
  have hrP := rP_bound (L2 := (L : ℝ) ^ 2) hg0
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg0]) hgrb hT1 hT2 hT3 hT4 hn'b h1n'
    hES hgg hq hSB hQD
  -- the algebra of (F1)
  set Pv := K3 / z ^ 2 * (1 + n') with hPv
  set p₂ := -(z ^ 2 * q + SB) with hp₂
  have hPe : Pv = (g : ℂ) + p₂ * (g : ℂ) ^ 2 + (Pv - g - p₂ * (g : ℂ) ^ 2) := by ring
  have hrP' : ‖Pv - g - p₂ * (g : ℂ) ^ 2‖ ≤ f1e eA eB * g ^ 2 +
      f1cP L ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES * g ^ 3 := by
    have e : Pv - g - p₂ * (g : ℂ) ^ 2 = K3 / z ^ 2 * (1 + n') - g + (z ^ 2 * q + SB) * (g : ℂ) ^ 2 := by
      rw [hPv, hp₂]; ring
    rw [e, hid]
    refine hrP.trans (le_of_eq ?_)
    unfold f1e f1cP; ring
  have hp₂b : ‖p₂‖ ≤ ℓ ^ 2 / 8 + 2 * KB := by
    rw [hp₂, norm_neg]; refine (norm_add_le _ _).trans ?_
    have : 0 ≤ ℓ ^ 2 / 8 := by positivity
    linarith only [hq, hSB, this]
  have hw8 : ‖(K0 + K1) / z‖ ≤ 1 / 8 := hwin.trans hρ8
  have hfin := F1_alg hg0 hg1 (by unfold f1e; positivity)
    (by unfold f1cP f1cCnu f1cn' f1cK f1cn; positivity) (by positivity)
    (by unfold f1cw f1cn; positivity) hPe hrP' hw_eq hcw hw8
    (hcb.trans (by linarith)) hp₂b
  have e1 : K3 / (z * (1 + (K0 + K1) / z)) ^ 2 * (1 + n') = Pv / (1 + (K0 + K1) / z) ^ 2 := by
    have h1 : 1 + (K0 + K1) / z ≠ 0 := by
      intro h; have := norm_nonneg ((K0 + K1) / z)
      have h2 : (K0 + K1) / z = -1 := by linear_combination h
      rw [h2, norm_neg, norm_one] at hw8; norm_num at hw8
    rw [hPv]; field_simp
  rw [e1]
  have e2 : (2 * c - (z ^ 2 * q + SB)).re = (p₂ + 2 * c).re := by rw [hp₂]; ring_nf
  rw [e2]
  refine hfin.trans (le_of_eq ?_)
  unfold f1c3; ring

set_option maxHeartbeats 8000000 in
/-- **(F1) for one step**: with the exact quartic coupling of `Loc S`, the output
`ǧ' = Re(κ'_g(1+n')/Z_{j+2}²)` satisfies
`|ǧ' - g - Re(2c - Z²q - SB) g²| ≤ e g² + c₃ g³`, where `c = Z_{j+1} C_j(e₁, 0)`. -/
theorem step_F1 : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 2 ≤ A →
    ∀ cZ cmu : ℝ, 0 ≤ cZ → 0 ≤ cmu → 0 ≤ g → g ≤ 1 →
      ‖st.z / st.Z‖ ≤ cZ * g → ‖st.y / st.Z‖ ≤ cZ * g → 2 * (cZ * g) ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * (cZ * g) ≤ 1 / 2 → |μ| ≤ cmu * g → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 →
      ∀ eA eB : ℝ, 0 ≤ eA → 0 ≤ eB →
      ‖stA R st * (R.msq : ℂ) * st.w1‖ ≤ eA * g →
      ‖stZ' R st ^ 2 * stCov R j st (dirVec (Sum.inl 0)) 0 * st.w1 -
          stZ' R st ^ 2 * stCov R j st 0 0 * st.w1‖ ≤ eB →
      ‖stZ' R st * st.w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 →
    ∀ w dd k : ℝ, 0 ≤ w → 0 ≤ dd → 0 ≤ k → w ≤ 1 → dd ≤ 1 → 8 * k ≤ 1 →
      Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal w →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ * g)) + 8 * R.ℓ ^ 4 * g ≤ 1 →
    ∀ cRQ cRL cRD : ℝ, 0 ≤ cRQ → 0 ≤ cRL → 0 ≤ cRD →
      cS * (Cl * (8 * k)) ≤ cRQ * g ^ 3 →
      Cl * ((L : ℝ) ^ 2 * BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ * g)) + 8 * R.ℓ ^ 4 * g)
        w) ≤ cRL * g ^ 2 →
      ClD * ((L : ℝ) ^ 2 * BH.sig 2 L 0 dd) ≤ cRD * g ^ 3 →
    ∀ (S q SB ES : ℂ) (KB cES : ℝ), 0 ≤ KB → 0 ≤ cES →
      (∃ c₀ δ : ℂ, (∀ x, stCov R j st x x = c₀) ∧ (∀ x e, stCov R j st (x + dirVec e) x = c₀ + δ) ∧
        cvec4 (blockSet (L := L) (N := N) j 0) R.i₀
          (LS j (stCov R j st) (stVf R j st g μ) st.Wl 0 : Alg 2 L N) 3 =
          S + (stKap R j st g μ).g ^ 2 * q + 4 * (∑ x, stCov R j st x 0) * (stKap R j st g μ).g *
            ((stKap R j st g μ).nu + 2 * (2 : ℕ) * (stKap R j st g μ).g * δ)) →
      S = stZ' R st ^ 2 * ((g : ℂ) ^ 2 * SB + ES) → ‖ES‖ ≤ cES * g ^ 3 →
      ‖stZ' R st ^ 2 * q‖ ≤ KB → ‖SB‖ ≤ KB →
      f1cn R.ℓ cmu * g ≤ 1 / 8 → f1cn' L R.ℓ cZ cmu Cq cRQ cRL * g ≤ 1 / 8 →
      (R.ℓ ^ 2 / 7 + f1cw R.ℓ cmu Cq cRQ cRL) * g ≤ R.ρ →
      |(rawStep R j st g μ D K).g.re - g -
          (2 * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0) - (stZ' R st ^ 2 * q + SB)).re *
            g ^ 2| ≤
        f1e eA eB * g ^ 2 + f1c3 L R.ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES eA eB * g ^ 3 := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := rawStep_coup
  obtain ⟨CqD, hCqD, ClD, hClD, hDb⟩ := LS_D_bound
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK A hA cZ cmu hcZ hcmu hg0 hg1 hz hy hη hηs hμ hm eA eB heA heB hTA hTB
    hw1
    w dd k hw0 hdd0 hk0 hw1' hdd1 hk1 hWw hDd hKk hv1 cRQ cRL cRD hcRQ hcRL hcRD hRQ hRL hRD
    S q SB ES KB cES hKB hcES hLS hS hES hq hSB hn8 hn'8 hζ8
  have hV' := hV
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hjN : j < N := by omega
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
  -- inactive input clamps
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hA' := stA_eq hZ hzy
  have hY' := stYc_eq hZ hyc
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * (cZ * g) := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8' : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  have h1ζ : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
  have hzn : ‖stZ' R st‖ = ‖st.Z‖ * ‖1 + stZeta R st‖ := norm_stZ'
  have hz0 : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hap : 0 < ‖stZ' R st‖ := norm_pos_iff.2 hz0
  have hrat : ‖st.Z‖ ≤ 8 / 7 * ‖stZ' R st‖ := by rw [hzn]; nlinarith
  -- inputs and the representation
  obtain ⟨hVv, hKflat⟩ := step_inputs hV H hg0 hz hy hη hηs hm (K := K) hA hk0 hKk
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ * g)) + 8 * R.ℓ ^ 4 * g := by
    have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
  obtain ⟨c₀, δ, κQ, κL, hc₀, hδ, hrep, q1, q2, q3, q4, l1, l2, l3, l4, hLcv⟩ :=
    hcoup L hL8 hLp N R j hV st H g μ D K hD hK (A / 2) (by linarith) _ w (8 * k) hv0 hw0
      (by positivity) hv1 hw1' hk1 hVv hWw hKflat
  have hDg := hDb L hL8 hLp N R j hV st H D hD dd hdd0 hdd1 hDd
  clear hcoup hDb
  obtain ⟨c₀', δ', hc₀', hδ', hLSg⟩ := hLS
  have hcc : c₀' = c₀ := by rw [← hc₀' 0, hc₀ 0]
  have hdd : δ' = δ := by
    have h1 := hδ 0 (Sum.inl 0); have h2 := hδ' 0 (Sum.inl 0)
    rw [h1, hcc] at h2; exact (add_left_cancel h2).symm
  rw [hdd] at hLSg
  -- covariance entries
  obtain ⟨hC0, -, -, hCsym0⟩ := H.cov hV
  have hC : GoodCov2 j (fscale (stZ' R st) * R.ℓ / 4) (stCov R j st) := hC0
  have hδ2 : ∀ x e, stCov R j st x (x + dirVec e) = c₀ + δ := fun x e => by
    rw [show stCov R j st x (x + dirVec e) = stCov R j st (x + dirVec e) x from hCsym0 _ _]
    exact hδ x e
  obtain ⟨hc0b, hδb⟩ := cov_c0_delta_le hC hc₀ hδ hδ2
  have hℓC2 : (fscale (stZ' R st) * R.ℓ / 4) ^ 2 = R.ℓ ^ 2 / (16 * ‖stZ' R st‖) := by
    rw [div_pow, mul_pow, fscale_sq]; field_simp; ring
  rw [hℓC2] at hc0b hδb
  have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hPj : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by ring
  have hzc0 : ‖stZ' R st * c₀‖ ≤ R.ℓ ^ 2 / 16 := by
    rw [norm_mul]
    calc ‖stZ' R st‖ * ‖c₀‖ ≤ ‖stZ' R st‖ * (R.ℓ ^ 2 / (16 * ‖stZ' R st‖)) :=
          mul_le_mul_of_nonneg_left hc0b hap.le
      _ = _ := by field_simp
  have hzδ : ‖stZ' R st * δ‖ * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) ≤ R.ℓ ^ 2 / 32 := by
    rw [norm_mul, ← hPj]
    have := mul_le_mul_of_nonneg_left hδb hap.le
    calc ‖stZ' R st‖ * ‖δ‖ * ((L : ℝ) ^ (j + 1)) ^ 2 ≤
        ‖stZ' R st‖ * (R.ℓ ^ 2 / (16 * ‖stZ' R st‖) / (2 * ((L : ℝ) ^ (j + 1)) ^ 2)) *
          ((L : ℝ) ^ (j + 1)) ^ 2 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by field_simp; ring
  have hzC1 : ‖stZ' R st * ∑ x, stCov R j st x 0‖ ≤
      9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) := by
    have h := zero_mode_le (by omega) hC
    rw [hℓC2] at h
    rw [norm_mul, ← hPj]
    calc ‖stZ' R st‖ * ‖∑ x, stCov R j st x 0‖ ≤
        ‖stZ' R st‖ * (9 * ((L : ℝ) ^ (j + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * ‖stZ' R st‖))) :=
          mul_le_mul_of_nonneg_left h hap.le
      _ = _ := by field_simp
  -- normalised coupling bounds
  have hs2 : (fscale st.Z * R.ℓ) ^ 2 = R.ℓ ^ 2 / ‖st.Z‖ := by rw [mul_pow, fscale_sq]; ring
  have hs4 : (fscale st.Z * R.ℓ) ^ 4 = (R.ℓ ^ 2 / ‖st.Z‖) ^ 2 := by rw [← hs2]; ring
  have hs'2 : (fscale (stZ' R st) * R.ℓ) ^ 2 = R.ℓ ^ 2 / ‖stZ' R st‖ := by
    rw [mul_pow, fscale_sq]; ring
  have hs'4 : (fscale (stZ' R st) * R.ℓ) ^ 4 = (R.ℓ ^ 2 / ‖stZ' R st‖) ^ 2 := by rw [← hs'2]; ring
  rw [hs2] at q1 q2 q3
  rw [hs4] at q4
  rw [hs'2, hPj] at l3
  rw [hs'2] at l1 l2
  rw [hs'4] at hDg
  -- the coupling components
  have e0 := congrArg Coup.z hrep
  have e1 := congrArg Coup.y hrep
  have e2 := congrArg Coup.nu hrep
  have e3 := congrArg Coup.g hrep
  have hkz : (stKap R j st g μ).z = 0 := by
    show st.z + stYc R st - stA R st = 0; rw [hA', hY']; ring
  have hky : (stKap R j st g μ).y = 0 := by
    show st.y - stYc R st = 0; rw [hY']; ring
  have hLsplit : κL.g = cvec4 (blockSet (L := L) (N := N) j 0) R.i₀
      (LS j (stCov R j st) (stVf R j st g μ) st.Wl 0 : Alg 2 L N) 3 +
      cvec4 (blockSet (L := L) (N := N) j 0) R.i₀ (LS j (stCov R j st) 0 D 0 : Alg 2 L N) 3 := by
    have h := hLcv 0 (zero_mem_blockIdx j) R.i₀
    rw [LS_addW, Subalgebra.coe_add, map_add] at h
    have := congrFun h 3
    rw [Pi.add_apply] at this
    exact this.symm
  -- the output
  have hkg : (stKap R j st g μ).g = stGr R j st g μ * stZ' R st ^ 2 := rfl
  have hknu : (stKap R j st g μ).nu = stNu R j st μ - stA R st * R.msq := rfl
  have h0 : stCv R j st g μ D K 0 = -(stGr R j st g μ * stZ' R st ^ 2) * c₀ -
      (κQ.z - κQ.g * c₀) - κL.z := by
    have h := e0
    simp only [Coup.sub_z, Coup.shift] at h
    rw [show stCv R j st g μ D K 0 = (Coup.ofVec (stCv R j st g μ D K)).z from rfl, h, hkz, hkg]
    ring
  have h1 : stCv R j st g μ D K 1 = -(stGr R j st g μ * stZ' R st ^ 2) * δ -
      (κQ.y - κQ.g * δ) - κL.y := by
    have h := e1
    simp only [Coup.sub_y, Coup.shift] at h
    rw [show stCv R j st g μ D K 1 = (Coup.ofVec (stCv R j st g μ D K)).y from rfl, h, hky, hkg]
    ring
  have h2 : stCv R j st g μ D K 2 = stNu R j st μ - stA R st * (R.msq : ℂ) +
      4 * (stGr R j st g μ * stZ' R st ^ 2) * δ - (κQ.nu + 4 * κQ.g * δ) - κL.nu := by
    have h := e2
    simp only [Coup.sub_nu, Coup.shift] at h
    rw [show stCv R j st g μ D K 2 = (Coup.ofVec (stCv R j st g μ D K)).nu from rfl, h, hknu, hkg]
    push_cast; ring
  have h3 : stCv R j st g μ D K 3 = stGr R j st g μ * stZ' R st ^ 2 - κQ.g -
      (S + (stGr R j st g μ * stZ' R st ^ 2) ^ 2 * q +
        4 * (∑ x, stCov R j st x 0) * (stGr R j st g μ * stZ' R st ^ 2) *
          (stNu R j st μ - stA R st * (R.msq : ℂ) + 4 * (stGr R j st g μ * stZ' R st ^ 2) * δ)) -
      cvec4 (blockSet (L := L) (N := N) j 0) R.i₀ (LS j (stCov R j st) 0 D 0 : Alg 2 L N) 3 := by
    have h := e3
    simp only [Coup.sub_g, Coup.shift] at h
    rw [show stCv R j st g μ D K 3 = (Coup.ofVec (stCv R j st g μ D K)).g from rfl, h, hLsplit,
      hLSg, hkg, hknu]
    push_cast; ring
  have hZ2 : stZ2 R j st g μ D K = stZ' R st * (1 + clampDisk R.ρ
      ((stCv R j st g μ D K 0 + stCv R j st g μ D K 1) / stZ' R st)) := rfl
  have hW1 : stW1 R j st = st.w1 + ∑ x, stCov R j st x 0 := rfl
  have hcδ : stCov R j st (dirVec (Sum.inl 0)) 0 = c₀ + δ := by
    have := hδ 0 (Sum.inl 0); rwa [zero_add] at this
  rw [rawStep_g, hZ2, hW1, h0, h1, h2, h3, hcδ]
  -- the core estimate
  have hgrG : (g : ℂ) = stGr R j st g μ * (1 + nCor (stNu R j st μ) st.w1) := by
    unfold stGr; field_simp [one_add_nCor_ne]
  have hnuS : ‖stNu R j st μ / stZ' R st‖ * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) ≤
      (L : ℝ) ^ 2 * (cmu * g) := by
    have e : stNu R j st μ / stZ' R st = (μ : ℂ) / (L : ℂ) ^ (2 * j) := by
      rw [show stNu R j st μ = (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) from rfl]; field_simp
    have nP2 : ‖(L : ℂ) ^ (2 * j)‖ = ((L : ℝ) ^ j) ^ 2 := by
      rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
    rw [e, norm_div, Complex.norm_real, Real.norm_eq_abs, nP2]
    have : |μ| / ((L : ℝ) ^ j) ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) = (L : ℝ) ^ 2 * |μ| := by
      field_simp
    rw [this]; exact mul_le_mul_of_nonneg_left hμ (by positivity)
  have hAz : ‖stA R st / stZ' R st‖ ≤ 16 / 7 * (cZ * g) := by
    have e : stA R st / stZ' R st = stZeta R st / (1 + stZeta R st) := by
      show st.Z * stZeta R st / (st.Z * (1 + stZeta R st)) = _
      rw [mul_div_mul_left _ _ hZ]
    rw [e, norm_div, div_le_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left h1ζ (by positivity : (0 : ℝ) ≤ 16 / 7 * (cZ * g))
    linarith
  have hL4 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
    nlinarith
  have hLj1 : (1 : ℝ) ≤ ((L : ℝ) ^ j) ^ 2 :=
    one_le_pow₀ (one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)))
  have hRQ0 : 0 ≤ cS * (Cl * (8 * k)) := by positivity
  have hRL0 : 0 ≤ Cl * ((L : ℝ) ^ 2 * BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ * g)) +
      8 * R.ℓ ^ 4 * g) w) := by
    have := BH.sig_nonneg (L := L) (d := 2) (by norm_num)
      (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ * g)) + 8 * R.ℓ ^ 4 * g) w hw0
    positivity
  have hRD0 : 0 ≤ ClD * ((L : ℝ) ^ 2 * BH.sig 2 L 0 dd) := by
    have := BH.sig_nonneg (L := L) (d := 2) (by norm_num) 0 dd hdd0
    positivity
  have hTB' : ‖stZ' R st ^ 2 * δ * st.w1‖ ≤ eB := by
    have e : stZ' R st ^ 2 * δ * st.w1 = stZ' R st ^ 2 * stCov R j st (dirVec (Sum.inl 0)) 0 * st.w1 -
        stZ' R st ^ 2 * stCov R j st 0 0 * st.w1 := by rw [hcδ, hc₀ 0]; ring
    rw [e]; exact hTB
  exact F1_core (L := L) hg0 hg1 hℓ hL4 hLj1 hap hZn hrat hcZ hcmu hCq hCqD hcRQ hcRL hcRD hKB
    hcES hρ0 hρ8 hgrG hnuS hAz hm heA heB hTA hTB' hw1 hzC1 hzc0 hzδ q1 q2 q3 q4 l1 l2 l3 hDg hRQ0 hRL0 hRD0
    hRQ hRL hRD hS hES hq hSB hn8 hn'8 hζ8

end

end Step2
