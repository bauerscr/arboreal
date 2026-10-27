import Step2.Last.LastStep
import Step2.Flow.FlowHist

/-!
# The step at `j = N - 2`: the output quartic coupling

`StepBounds` (and `Last.StepBounds`) have no bound on the output marginal coupling
`ǧ' = κ_g / Z_{j+2}² (1 + n')`; the band (F1) needs `ValidAt` (`j + 2 < N`). For the gluing of the
last two steps a crude bound suffices: from `Last.rawStep_coup`,
`κ_g = ǧ_r Z_{j+1}² - κ_Q.g - κ_L.g` with `ǧ_r = ǧ/(1 + n)`, hence

  `ǧ' = ǧ w + e`,  `w = (1 + n')/((1 + n)(1 + ζ_{j+1})²)`,  `|w - 1| ≤ 5/6`,  `|e| ≤ 2 E`,

with `E = (2 C_q R_Q + C_q R_L)/ℓ⁴` (`gErr`). So `|ǧ'| ≤ 2ǧ + 2E` and `Re ǧ' ≥ ǧ/6 - 2E`
(`GStepBound`, `g_step_bounds`), under `ValidAtL`, with the inputs of `StepBounds`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

/-- The remainder of the output quartic coupling. -/
def gErr (L : ℕ) (Cq Cl cS ℓ k v w : ℝ) : ℝ :=
  (2 * Cq * (cS * (Cl * (8 * k))) + Cq * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w))) / ℓ ^ 2 / ℓ ^ 2

/-- The algebra of the output quartic coupling. -/
theorem gout_alg {g X : ℝ} (hg : 0 ≤ g) (hX : 0 ≤ X) {a b c Z e₀ : ℂ} (hZ : Z ≠ 0)
    (ha : ‖a - 1‖ ≤ 1 / 8) (hb : ‖b - 1‖ ≤ 1 / 8) (hc : ‖c - 1‖ ≤ 1 / 8)
    (he : ‖e₀‖ ≤ X * ‖Z‖ ^ 2) :
    ‖((g : ℂ) / a * Z ^ 2 - e₀) / (Z * b) ^ 2 * c‖ ≤ 2 * g + 2 * X ∧
      g / 6 - 2 * X ≤ (((g : ℂ) / a * Z ^ 2 - e₀) / (Z * b) ^ 2 * c).re := by
  have hna : 7 / 8 ≤ ‖a‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - a)
    rw [norm_one, sub_sub_cancel, ← norm_neg, neg_sub] at this; linarith
  have hnb : 7 / 8 ≤ ‖b‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - b)
    rw [norm_one, sub_sub_cancel, ← norm_neg, neg_sub] at this; linarith
  have hna' : ‖a‖ ≤ 9 / 8 := by
    have := norm_add_le (a - 1) 1; rw [sub_add_cancel, norm_one] at this; linarith
  have hnc' : ‖c‖ ≤ 9 / 8 := by
    have := norm_add_le (c - 1) 1; rw [sub_add_cancel, norm_one] at this; linarith
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at hna; linarith
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hnb; linarith
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = c / (a * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨e, he'⟩ : ∃ e : ℂ, e = -(e₀ / Z ^ 2) * (c / b ^ 2) := ⟨_, rfl⟩
  have hid : ((g : ℂ) / a * Z ^ 2 - e₀) / (Z * b) ^ 2 * c = (g : ℂ) * w + e := by
    rw [hw, he']; field_simp; ring
  rw [hid]
  -- `|w - 1| ≤ 5/6`
  have hb2 : ‖b ^ 2 - 1‖ ≤ 17 / 64 := by
    have e1 : b ^ 2 - 1 = (b - 1) * ((b - 1) + 2) := by ring
    rw [e1, norm_mul]
    have : ‖(b - 1) + 2‖ ≤ 17 / 8 := by
      refine (norm_add_le _ _).trans ?_
      rw [show ‖(2 : ℂ)‖ = 2 by simp]; linarith
    calc ‖b - 1‖ * ‖(b - 1) + 2‖ ≤ 1 / 8 * (17 / 8) :=
          mul_le_mul hb this (norm_nonneg _) (by norm_num)
      _ = 17 / 64 := by norm_num
  have hnum : ‖c - a * b ^ 2‖ ≤ 281 / 512 := by
    have e1 : c - a * b ^ 2 = (c - 1) - (a - 1) - a * (b ^ 2 - 1) := by ring
    rw [e1]
    have t1 : ‖a * (b ^ 2 - 1)‖ ≤ 9 / 8 * (17 / 64) := by
      rw [norm_mul]; exact mul_le_mul hna' hb2 (norm_nonneg _) (by norm_num)
    have := norm_sub_le ((c - 1) - (a - 1)) (a * (b ^ 2 - 1))
    have := norm_sub_le (c - 1) (a - 1)
    linarith
  have hden : 343 / 512 ≤ ‖a * b ^ 2‖ := by
    rw [norm_mul, norm_pow]
    have h1 : 49 / 64 ≤ ‖b‖ ^ 2 := by nlinarith
    calc (343 / 512 : ℝ) = 7 / 8 * (49 / 64) := by norm_num
      _ ≤ ‖a‖ * ‖b‖ ^ 2 := mul_le_mul hna h1 (by norm_num) (by linarith)
  have hab0 : a * b ^ 2 ≠ 0 := mul_ne_zero ha0 (pow_ne_zero 2 hb0)
  have hw1 : ‖w - 1‖ ≤ 5 / 6 := by
    have e1 : w - 1 = (c - a * b ^ 2) / (a * b ^ 2) := by rw [hw]; field_simp
    rw [e1, norm_div, div_le_iff₀ (by linarith)]
    linarith
  have hwn : ‖w‖ ≤ 2 := by
    have := norm_add_le (w - 1) 1; rw [sub_add_cancel, norm_one] at this; linarith
  have hre : 1 / 6 ≤ w.re := by
    have h1 := Complex.abs_re_le_norm (w - 1)
    rw [Complex.sub_re, Complex.one_re] at h1
    have := (abs_le.1 (h1.trans hw1)).1
    linarith
  -- `|e| ≤ 2X`
  have hen : ‖e‖ ≤ 2 * X := by
    rw [he', norm_mul, norm_neg, norm_div, norm_div, norm_pow, norm_pow]
    have h1 : ‖e₀‖ / ‖Z‖ ^ 2 ≤ X := by rw [div_le_iff₀ (by positivity)]; exact he
    have h2 : ‖c‖ / ‖b‖ ^ 2 ≤ 72 / 49 := by
      rw [div_le_iff₀ (by positivity)]
      have : 49 / 64 ≤ ‖b‖ ^ 2 := by nlinarith
      nlinarith
    calc ‖e₀‖ / ‖Z‖ ^ 2 * (‖c‖ / ‖b‖ ^ 2) ≤ X * (72 / 49) :=
          mul_le_mul h1 h2 (by positivity) hX
      _ ≤ 2 * X := by nlinarith
  constructor
  · refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
    have := mul_le_mul_of_nonneg_left hwn hg
    linarith
  · rw [Complex.add_re, Complex.re_ofReal_mul]
    have h1 := mul_le_mul_of_nonneg_left hre hg
    have h2 : -‖e‖ ≤ e.re := by
      have := Complex.abs_re_le_norm e; exact (abs_le.1 this).1
    linarith

/-- **The output quartic coupling of one step** (crude), with the inputs of `StepBounds`, under
`ValidAtL`. -/
def GStepBound (L : ℕ) [NeZero L] (A Cq Cl cS : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAtL R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
      ∀ η : ℝ, ‖st.z / st.Z‖ ≤ η → ‖st.y / st.Z‖ ≤ η → 2 * η ≤ R.ρ →
        8 * cM * R.ℓ ^ 2 * η ≤ 1 / 2 →
      ∀ wl dd k r : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 → r ≤ 1 →
      8 * k ≤ 1 →
      ‖(rawStep R j st g μ D K).g‖ ≤ 2 * g + 2 * gErr L Cq Cl cS R.ℓ k
          (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd) ∧
        g / 6 - 2 * gErr L Cq Cl cS R.ℓ k
          (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd) ≤
          (rawStep R j st g μ D K).g.re

set_option maxHeartbeats 4000000 in
theorem g_step_bounds : ∃ Cq Cl cS : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L → ∀ A : ℝ, 2 ≤ A →
      GStepBound L A Cq Cl cS := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := Last.rawStep_coup
  refine ⟨Cq, Cl, cS, hCq, hCl, hcS, fun L _ hL8 hLp A hA => ?_⟩
  intro N R j hVL st H g μ D K hD hK hm hg0 η hz hy hη hηs wl dd k r hwl0 hdd0 hk0 hWl hDd hKk
    hvr hwr hr1 hk8
  have hV' := hVL
  obtain ⟨-, hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  have hjN : j < N := by omega
  -- clamps
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  have hs := fscale_pos hZ
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hgr := norm_stGr_le R j st g μ
  rw [abs_of_nonneg hg0] at hgr
  have hrZ : ‖stZ' R st / st.Z‖ ≤ 9 / 8 := by
    have e : stZ' R st / st.Z = 1 + stZeta R st := by
      unfold stZ'; rw [mul_div_cancel_left₀ _ hZ]
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have hVv : Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤
      ENNReal.ofReal (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) := by
    have e : stVf R j st g μ = VfamL j ![0, 0, (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) -
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
    have hℓ4 : 0 ≤ R.ℓ ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left (add_le_add h1 this) (mul_nonneg hM (sq_nonneg R.ℓ))
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * R.ℓ ^ 4)
    nlinarith
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hv0 : 0 ≤ cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g := by
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    positivity
  have hv1 : cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g ≤ 1 := hvr.trans hr1
  have hr0 : 0 ≤ r := hv0.trans hvr
  have hw1 : wl + dd ≤ 1 := hwr.trans (by nlinarith)
  -- `Δ` and `K♭`
  obtain ⟨δΔ, hδΔ⟩ : ∃ δΔ : ℝ, δΔ = 8 * cM * R.ℓ ^ 2 * η := ⟨_, rfl⟩
  have hδΔ0 : 0 ≤ δΔ := by
    rw [hδΔ]; have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
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
  have hδ4 : 4 * δΔ ≤ 2 := by rw [hδΔ]; linarith
  have hexp : Real.exp (4 * δΔ) ≤ 8 := by
    calc Real.exp (4 * δΔ) ≤ Real.exp 2 := Real.exp_le_exp.2 hδ4
      _ ≤ 8 := by
          have := Real.exp_one_lt_d9
          have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith [Real.exp_pos 1]
  have hKflat : Knorm j (fscale st.Z * R.ℓ) (A / 2) (Kflat j (stDelta R j st) K) ≤
      ENNReal.ofReal (8 * k) := by
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
  -- the couplings
  obtain ⟨c₀, δ, κQ, κL, -, -, hrep, -, -, -, q4, -, -, -, l4, -⟩ :=
    hcoup L hL8 hLp N R j hVL st H g μ D K hD hK (A / 2) (by linarith)
      (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd) (8 * k)
      hv0 (by positivity) (by positivity) hv1 hw1 hk8 hVv hw hKflat
  have h3 : stCv R j st g μ D K 3 = stGr R j st g μ * stZ' R st ^ 2 - (κQ.g + κL.g) := by
    have h := congrArg Coup.g hrep
    simp only [Coup.sub_g, Coup.shift] at h
    rw [show stCv R j st g μ D K 3 = (Coup.ofVec (stCv R j st g μ D K)).g from rfl, h]
    show stGr R j st g μ * stZ' R st ^ 2 - κQ.g - κL.g = _
    ring
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hZ'n : 0 < ‖stZ' R st‖ := norm_pos_iff.2 hZ'
  have hrat : ‖st.Z‖ ≤ 8 / 7 * ‖stZ' R st‖ := by
    have h1ζ : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
    rw [norm_stZ']; nlinarith [norm_nonneg st.Z]
  -- the remainder
  have hRQ0 : 0 ≤ cS * (Cl * (8 * k)) := by
    have : (0 : ℝ) ≤ cS := by linarith
    positivity
  have hRL0 : 0 ≤ Cl * ((L : ℝ) ^ 2 *
      BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd)) := by
    have := BH.sig_nonneg (L := L) (d := 2) (by norm_num)
      (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd) (by positivity)
    positivity
  obtain ⟨RQ, hRQ⟩ : ∃ RQ, RQ = cS * (Cl * (8 * k)) := ⟨_, rfl⟩
  obtain ⟨RL, hRL⟩ : ∃ RL, RL = Cl * ((L : ℝ) ^ 2 *
      BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd)) := ⟨_, rfl⟩
  rw [← hRQ] at q4 hRQ0
  rw [← hRL] at l4 hRL0
  have hs4 : ((fscale st.Z * R.ℓ) ^ 4)⁻¹ = ‖st.Z‖ ^ 2 / R.ℓ ^ 4 := by
    rw [show (fscale st.Z * R.ℓ) ^ 4 = (fscale st.Z ^ 2) ^ 2 * R.ℓ ^ 4 by ring, fscale_sq]
    field_simp
  have hs'4 : ((fscale (stZ' R st) * R.ℓ) ^ 4)⁻¹ = ‖stZ' R st‖ ^ 2 / R.ℓ ^ 4 := by
    rw [show (fscale (stZ' R st) * R.ℓ) ^ 4 = (fscale (stZ' R st) ^ 2) ^ 2 * R.ℓ ^ 4 by ring,
      fscale_sq]
    field_simp
  rw [hs4] at q4
  rw [hs'4] at l4
  have hℓ4 : 0 < R.ℓ ^ 4 := by positivity
  have hX0 : 0 ≤ (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 4 := by positivity
  have he₀ : ‖κQ.g + κL.g‖ ≤ (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    have hZ2 : ‖st.Z‖ ^ 2 ≤ 2 * ‖stZ' R st‖ ^ 2 := by nlinarith [norm_nonneg st.Z]
    have a1 : Cq * (‖st.Z‖ ^ 2 / R.ℓ ^ 4) * RQ ≤ 2 * Cq * RQ / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 := by
      rw [show Cq * (‖st.Z‖ ^ 2 / R.ℓ ^ 4) * RQ = Cq * RQ * ‖st.Z‖ ^ 2 / R.ℓ ^ 4 by ring,
        show 2 * Cq * RQ / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 = Cq * RQ * (2 * ‖stZ' R st‖ ^ 2) / R.ℓ ^ 4 by
          ring]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hZ2 (mul_nonneg hCq hRQ0))
        hℓ4.le
    have a2 : Cq * (‖stZ' R st‖ ^ 2 / R.ℓ ^ 4) * RL = Cq * RL / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 := by
      ring
    have e : (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 =
        2 * Cq * RQ / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 + Cq * RL / R.ℓ ^ 4 * ‖stZ' R st‖ ^ 2 := by ring
    rw [e]
    linarith only [q4, l4, a1, a2]
  have hgE : gErr L Cq Cl cS R.ℓ k (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd) =
      (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 4 := by
    rw [gErr, hRQ, hRL, div_div]; ring
  rw [hgE]
  have hout : (rawStep R j st g μ D K).g = ((g : ℂ) / (1 + nCor (stNu R j st μ) st.w1) *
      stZ' R st ^ 2 - (κQ.g + κL.g)) / (stZ' R st * (1 + stZeta2 R j st g μ D K)) ^ 2 *
      (1 + nCor (stCv R j st g μ D K 2) (stW1 R j st)) := by
    rw [rawStep_g, h3]; rfl
  rw [hout]
  have hn1 : ∀ ν w1 : ℂ, ‖(1 + nCor ν w1) - 1‖ ≤ 1 / 8 := fun ν w1 => by
    rw [add_sub_cancel_left]; exact norm_nCor_le ν w1
  have hz2 : ‖(1 + stZeta2 R j st g μ D K) - 1‖ ≤ 1 / 8 := by
    rw [add_sub_cancel_left]
    exact (absorb_le R hρ0 _ _).trans hρ8
  exact gout_alg hg0 hX0 hZ' (hn1 _ _) hz2 (hn1 _ _) he₀

end

end Step2
