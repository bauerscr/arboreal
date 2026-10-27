import Step2.Flow.FlowHor2Aux
import Step2.Last.FlowGlueHist
import Step2.Last.LastStep
import Step2.Last.ZeroMode

-- Merged from `Step2/LastValid.lean` (phase 3).
section

/-!
# The step at `j = N - 2`: the concrete covariances

`validAtL_concrete`: for the concrete dressed decomposition (`d = 2`) and `L > 2^6 + 4`,
`ValidAtL R j` holds for all `j + 1 < N` (in particular at `j = N - 2`), from
`validCov_concrete` (`Step2.Last.ZeroMode`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L : ℕ} [NeZero L]

/-- **`ValidAtL` for the concrete dressed decomposition**, for all `j + 1 < N` (from
`validCov_concrete`). -/
theorem validAtL_concrete (P : PtFamily) (hL : 2 ^ (2 + 4) + 4 < L) :
    ∃ ℓ₀ : ℝ, 0 < ℓ₀ ∧ ∃ ζbar : ℝ, 0 < ζbar ∧ ζbar ≤ 1 / 8 ∧
    ∀ (N : ℕ) (R : RGPar 2 L N), R.P = P → 1 ≤ N → 0 < R.msq →
      R.msq ≤ (L : ℝ) ^ (-(2 * ((N : ℝ) - 1))) → ℓ₀ ≤ R.ℓ → 0 ≤ R.ρ → R.ρ ≤ ζbar →
      ∀ j, j + 1 < N → ValidAtL R j := by
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by norm_num at hL ⊢; omega
  obtain ⟨ℓ₀, hℓ₀, ζbar, hζ, hζ8, h⟩ := validCov_concrete P hL8
  refine ⟨ℓ₀, hℓ₀, ζbar, hζ, hζ8, fun N R hP hN hm0 hm hℓ hρ0 hρ j hj => ?_⟩
  exact ⟨hL, hj, by norm_num, hL8, hρ0, hρ.trans hζ8, by linarith,
    h N R hP hN hm0 hm hℓ hρ0 hρ j hj⟩

end

end Step2

end

/-!
# The last two steps: the quartic coupling stays close to `ǧ_{N-2}` (a weak band)

`GStepBound` (`Step2/Last/FlowGlueG.lean`) bounds the output quartic coupling of the step `j = N - 2`
crudely (`|ǧ'| ≤ 2ǧ + 2E`, `Re ǧ' ≥ ǧ/6 - 2E`). Here the same algebra is kept exact in the three
clamped factors: with `ǧ' = ((ǧ/a) Z'² - e₀)/(Z' b)² c`, `a = 1 + n`, `b = 1 + ζ'`, `c = 1 + n'`,

  `|ǧ' - ǧ| ≤ 4 ǧ (|n| + |ζ'| + |n'|) + 2E`     (`gout_alg2`, `GStepBand`, `g_step_band`).

Along the flow `n, n' = O(ǧ)` (from `|Z_{j+1} w^{(1)}_j| ≤ ℓ² L^{2j}`, `Zw1_le'`, `Zw1_step`),
`ζ' = O(ǧ)` and `E = O(ǧ²)`, which gives `ǧ_{N-1} = ǧ_{N-2}(1 + O(ǧ_{N-2}))` (`FlowLastBand2`).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

/-- **The algebra of the output quartic coupling, close to the input.** -/
theorem gout_alg2 {g X : ℝ} (hg : 0 ≤ g) (hX : 0 ≤ X) {a b c Z e₀ : ℂ} (hZ : Z ≠ 0)
    (ha : ‖a - 1‖ ≤ 1 / 8) (hb : ‖b - 1‖ ≤ 1 / 8) (hc : ‖c - 1‖ ≤ 1 / 8)
    (he : ‖e₀‖ ≤ X * ‖Z‖ ^ 2) :
    ‖((g : ℂ) / a * Z ^ 2 - e₀) / (Z * b) ^ 2 * c - g‖ ≤
      4 * g * (‖a - 1‖ + ‖b - 1‖ + ‖c - 1‖) + 2 * X := by
  have hna : 7 / 8 ≤ ‖a‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - a)
    rw [norm_one, sub_sub_cancel, ← norm_neg, neg_sub] at this; linarith
  have hnb : 7 / 8 ≤ ‖b‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - b)
    rw [norm_one, sub_sub_cancel, ← norm_neg, neg_sub] at this; linarith
  have hna' : ‖a‖ ≤ 9 / 8 := by
    have := norm_add_le (a - 1) 1; rw [sub_add_cancel, norm_one] at this; linarith
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at hna; linarith
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hnb; linarith
  have hZn : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = c / (a * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨e, he'⟩ : ∃ e : ℂ, e = -(e₀ / Z ^ 2) * (c / b ^ 2) := ⟨_, rfl⟩
  have hid : ((g : ℂ) / a * Z ^ 2 - e₀) / (Z * b) ^ 2 * c - g = (g : ℂ) * (w - 1) + e := by
    rw [hw, he']; field_simp; ring
  rw [hid]
  have hb2 : ‖b ^ 2 - 1‖ ≤ 17 / 8 * ‖b - 1‖ := by
    have e1 : b ^ 2 - 1 = (b - 1) * ((b - 1) + 2) := by ring
    rw [e1, norm_mul]
    have : ‖(b - 1) + 2‖ ≤ 17 / 8 := by
      refine (norm_add_le _ _).trans ?_
      rw [show ‖(2 : ℂ)‖ = 2 by simp]; linarith
    have := mul_le_mul_of_nonneg_left this (norm_nonneg (b - 1))
    linarith
  have hnum : ‖c - a * b ^ 2‖ ≤ ‖c - 1‖ + ‖a - 1‖ + 9 / 8 * (17 / 8 * ‖b - 1‖) := by
    have e1 : c - a * b ^ 2 = (c - 1) - (a - 1) - a * (b ^ 2 - 1) := by ring
    rw [e1]
    have t1 : ‖a * (b ^ 2 - 1)‖ ≤ 9 / 8 * (17 / 8 * ‖b - 1‖) := by
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
  have hw1 : ‖w - 1‖ ≤ 4 * (‖a - 1‖ + ‖b - 1‖ + ‖c - 1‖) := by
    have e1 : w - 1 = (c - a * b ^ 2) / (a * b ^ 2) := by rw [hw]; field_simp
    rw [e1, norm_div, div_le_iff₀ (by linarith)]
    have h0 : 0 ≤ ‖a - 1‖ + ‖b - 1‖ + ‖c - 1‖ := by positivity
    have := mul_le_mul_of_nonneg_left hden (by positivity : (0 : ℝ) ≤ 4 * (‖a - 1‖ + ‖b - 1‖ + ‖c - 1‖))
    have := norm_nonneg (a - 1); have := norm_nonneg (b - 1); have := norm_nonneg (c - 1)
    nlinarith
  have hen : ‖e‖ ≤ 2 * X := by
    rw [he', norm_mul, norm_neg, norm_div, norm_div, norm_pow, norm_pow]
    have h1 : ‖e₀‖ / ‖Z‖ ^ 2 ≤ X := by rw [div_le_iff₀ (by positivity)]; exact he
    have hnc' : ‖c‖ ≤ 9 / 8 := by
      have := norm_add_le (c - 1) 1; rw [sub_add_cancel, norm_one] at this; linarith
    have h2 : ‖c‖ / ‖b‖ ^ 2 ≤ 72 / 49 := by
      rw [div_le_iff₀ (by positivity)]
      have : 49 / 64 ≤ ‖b‖ ^ 2 := by nlinarith
      nlinarith
    calc ‖e₀‖ / ‖Z‖ ^ 2 * (‖c‖ / ‖b‖ ^ 2) ≤ X * (72 / 49) :=
          mul_le_mul h1 h2 (by positivity) hX
      _ ≤ 2 * X := by nlinarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]
  have := mul_le_mul_of_nonneg_left hw1 hg
  linarith

/-- **The output quartic coupling of one step, close to the input**, under `ValidAtL`, with the
inputs of `StepBounds`: `|ǧ' - ǧ| ≤ 4ǧ(|n| + |ζ'| + |n'|) + 2E`, where `n = nCor(ν♭, w^{(1)})`,
`ζ' = ζ_{j+1}`, `n' = nCor(κ'_ν, w'^{(1)})` are the three clamped factors of the step. -/
def GStepBand (L : ℕ) [NeZero L] (A Cq Cl cS : ℝ) : Prop :=
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
      ‖(rawStep R j st g μ D K).g - g‖ ≤
        4 * g * (‖nCor (stNu R j st μ) st.w1‖ + ‖stZeta2 R j st g μ D K‖ +
          ‖nCor (stCv R j st g μ D K 2) (stW1 R j st)‖) +
        2 * gErr L Cq Cl cS R.ℓ k (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd)

set_option maxHeartbeats 4000000 in
/-- **The output quartic coupling of one step, close to the input** (`GStepBand`). -/
theorem g_step_band : ∃ Cq Cl cS : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L → ∀ A : ℝ, 2 ≤ A →
      GStepBand L A Cq Cl cS := by
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
  have h := gout_alg2 hg0 hX0 hZ' (hn1 (stNu R j st μ) st.w1) hz2
    (hn1 (stCv R j st g μ D K 2) (stW1 R j st)) he₀
  simp only [add_sub_cancel_left] at h
  exact h


end

end Step2
