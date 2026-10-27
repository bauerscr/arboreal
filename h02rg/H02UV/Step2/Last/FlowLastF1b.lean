import Step2.Last.FlowLastF1a

/-!
# (F1) at the step `j = N - 2`: one RG step under `ValidAtL`

Copies of `step_inputs` (`FlowF1c`), `LS_D_bound` (`FlowF1`) and `step_F1s` (`FlowF1S2`) with
`ValidAtL R j` (resp. `ValidCore R j`) in place of `ValidAt R j`; the coupling bounds come from
`Last.rawStep_coup` and `Last.coupP_bound` (the only change in the proofs).
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-- `step_inputs` under `ValidCore`. **The inputs of one step at the causal field scale**: `‖V♭‖ ≤ c_M ℓ²(2|μ| + 2η) + 8ℓ⁴g` and
`‖K♭‖_{A/2} ≤ 8 ‖K‖_A`. -/
theorem step_inputsL {R : RGPar 2 L N} {j : ℕ} (hV : ValidCore R j) {st : RawSt 2 L N}
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

/-- `LS_D_bound` under `ValidAtL` (from `Last.coupP_bound`). **The `D`-part of `Loc S`**: `|κ_{D}| ≤ C_q (s'ℓ)^{-4} C_l L² Q₁ ‖D‖`. -/
theorem LS_D_boundL : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAtL R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ D : Fam 2 L N, D ∈ BSub (L := L) (N := N) j → ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal w →
      ‖cvec4 (blockSet (L := L) (N := N) j 0) R.i₀ (LS j (stCov R j st) 0 D 0 : Alg 2 L N) 3‖ ≤
        Cq * ((fscale (stZ' R st) * R.ℓ) ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L 0 w)) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := Last.coupP_bound
  refine ⟨Cq, hCq, Cl, hCl, ?_⟩
  intro L _ hL8 hLp N R j hV st H D hD w hw0 hw1 hDw
  have hV' := hV.2
  have hLg := hV.1
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ0 st).trans hρ8
  obtain ⟨hC, -, hCs, hCsym⟩ := H.covL hV.2
  have hsc := scale_ok hZ hζ hℓ
  have hs := fscale_pos hZ
  have hs' : 0 < fscale (stZ' R st) := fscale_pos (mul_ne_zero hZ (one_add_ne_zero (by linarith)))
  have hK0 : (0 : Act 2 L N) ∈ ASub (L := L) (N := N) j := zero_mem _
  obtain ⟨c₀, δ, κQ, κL, -, -, -, -, -, -, -, -, -, -, l4, hLcv⟩ :=
    h L hL8 hLp N j hj2 hLg (fscale st.Z * R.ℓ) (fscale (stZ' R st) * R.ℓ)
      (fscale (stZ' R st) * R.ℓ / 4) (by positivity) (by positivity) (by positivity)
      (by have e : fscale (stZ' R st) = fscale (st.Z * (1 + stZeta R st)) := rfl
          have := mul_pos hs hℓ
          rw [e]; linarith) (stCov R j st) hC hCs hCsym (Coup.ofVec 0) D 0 hD hK0 1 le_rfl
      0 w 0 le_rfl hw0 le_rfl zero_le_one hw1 zero_le_one
      (by rw [VfamL_zero_vec]; unfold Fnorm; simp [Step.Tj_zero]) hDw
      (by rw [Knorm_zero]; exact zero_le)
  have e := hLcv 0 (zero_mem_blockIdx j) R.i₀
  rw [VfamL_zero_vec] at e
  rw [e]
  exact l4

set_option maxHeartbeats 8000000 in
/-- `step_F1s` under `ValidAtL` (the step `j = N - 2`). **(F1) for one step, sharp form**: with `c = Z_{j+1} C_j(e₁, 0)` and the tadpole
`T = 16 Z_{j+1}² (C_j(e₁, 0) - C_j(0, 0)) w⁽¹⁾`,
`|ǧ' - g - Re(2c - Z²q - S_B + T) g²| ≤ (32/7) e_A g² + c₃ g³`. -/
theorem step_F1sL : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAtL R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 2 ≤ A →
    ∀ cZ cmu : ℝ, 0 ≤ cZ → 0 ≤ cmu → 0 ≤ g → g ≤ 1 →
      ‖st.z / st.Z‖ ≤ cZ * g → ‖st.y / st.Z‖ ≤ cZ * g → 2 * (cZ * g) ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * (cZ * g) ≤ 1 / 2 → |μ| ≤ cmu * g → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 →
      ∀ eA em : ℝ, 0 ≤ eA → 32 / 7 * eA ≤ em →
      ‖stA R st * (R.msq : ℂ) * st.w1‖ ≤ eA * g →
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
          (2 * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0) - (stZ' R st ^ 2 * q + SB) +
            16 * (stZ' R st ^ 2 * (stCov R j st (dirVec (Sum.inl 0)) 0 - stCov R j st 0 0) *
              st.w1)).re * g ^ 2| ≤
        32 / 7 * eA * g ^ 2 + f1c3s L R.ℓ cZ cmu Cq cRQ cRL CqD cRD KB cES em * g ^ 3 := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := Last.rawStep_coup
  obtain ⟨CqD, hCqD, ClD, hClD, hDb⟩ := LS_D_boundL
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK A hA cZ cmu hcZ hcmu hg0 hg1 hz hy hη hηs hμ hm eA em heA heAm hTA
    hw1
    w dd k hw0 hdd0 hk0 hw1' hdd1 hk1 hWw hDd hKk hv1 cRQ cRL cRD hcRQ hcRL hcRD hRQ hRL hRD
    S q SB ES KB cES hKB hcES hLS hS hES hq hSB hn8 hn'8 hζ8
  have hV' := hV.2
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
  obtain ⟨hVv, hKflat⟩ := step_inputsL hV.2 H hg0 hz hy hη hηs hm (K := K) hA hk0 hKk
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
  obtain ⟨hC0, -, -, hCsym0⟩ := H.covL hV.2
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
  rw [hc₀ 0, show c₀ + δ - c₀ = δ by ring]
  exact F1_core2 (L := L) hg0 hg1 hℓ hL4 hLj1 hap hZn hrat hcZ hcmu hCq hCqD hcRQ hcRL hcRD hKB
    hcES hρ0 hρ8 hgrG hnuS hAz hm heA heAm hTA hw1 hzC1 hzc0 hzδ q1 q2 q3 q4 l1 l2 l3 hDg hRQ0 hRL0 hRD0
    hRQ hRL hRD hS hES hq hSB hn8 hn'8 hζ8

set_option maxHeartbeats 4000000 in
/-- `F1_rg_sharp` at the single step `j = N_h` under `ValidAtL R N_h` (`N_h = N - 2`), with the
inputs (`HS`, `HD`, `HV`) at `N_h` only. **(F1) for the RG map, sharp form.** Given the sharp one-loop coefficient including the
tadpole (`|Re(f1Coef + T) - β| ≤ E₀(j) + E₁ g`), the decay of the past coefficients (`HD`) and the
mass term `|a m² w⁽¹⁾| ≤ e_A(j) g`, along regular histories
`|G_j - g_j - β g_j²| ≤ ((32/7) e_A(j) + E₀(j)) g_j² + c_g g_j³`. -/
theorem F1_rg_sharpL : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (C₀ η εs CK C₂ CD Cq' Cl' cS' : ℝ),
      StepBounds L R.A C₀ η εs CK C₂ CD Cq' Cl' cS' → 2 ≤ R.A →
    ∀ (Nh : ℕ), (∀ j < Nh, ValidAt R j) → ValidAtL R Nh →
      (∀ j ≤ Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1) →
    ∀ (Λ β δ κ cg cm cT ε : ℝ), ApHyp R Λ κ cg cm cT ε εs C₀ C₂ Cq' Cl' cS' → 0 < β → δ ≤ 1 / 2 →
      cg * ε ≤ β / 2 → cR R Λ cm C₂ * ε ≤ 1 → 8 * cx κ cT * ε ≤ 1 →
    ∀ (KB E1 em eA E0 c3 : ℝ), 0 ≤ KB → 0 ≤ eA → 32 / 7 * eA ≤ em →
      (∀ t, Hist.InDh Λ β δ κ cg cm cT ε Nh t →
        ‖stA R (rawHist R Nh t) * (R.msq : ℂ) * (rawHist R Nh t).w1‖ ≤ eA * (t Nh).1) →
      (∀ t, Hist.InDh Λ β δ κ cg cm cT ε Nh t → ‖hqTil R Nh t‖ ≤ KB ∧
        ∑ k ∈ range Nh, ((Nh : ℝ) - k + 1) * 2 ^ (Nh - k) * ‖hbTil R Nh t k‖ ≤ KB) →
      (∀ t, Hist.InDh Λ β δ κ cg cm cT ε Nh t →
        |(f1Coef R Nh t + htad R Nh t).re - β| ≤ E0 + E1 * (t Nh).1) →
      f1cn R.ℓ (cmu Λ cm) * ε ≤ 1 / 8 →
      f1cn' L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT)) (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))
        * ε ≤ 1 / 8 →
      (R.ℓ ^ 2 / 7 + f1cw R.ℓ (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
        (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))) * ε ≤ R.ρ →
      f1c3s L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT)) (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))
          CqD (f1cRD L ClD (cx κ cT)) KB
          ((24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB) em + E1 ≤ c3 →
      ∀ t, Hist.InDh Λ β δ κ cg cm cT ε Nh t →
        |(histOut R Nh t).g.re - (t Nh).1 - β * (t Nh).1 ^ 2| ≤
          (32 / 7 * eA + E0) * (t Nh).1 ^ 2 + c3 * (t Nh).1 ^ 3 := by
  obtain ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, hstep⟩ := step_F1sL
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R _ _ C₀ η εs CK C₂ CD Cq' Cl' cS' hSB hA2 Nh hV hVL hm1 Λ β δ κ cg cm cT ε
    H hβ hδ1 hcgβ hcR1 hk1 KB E1 em eA E0 c3 hKB heA heAm HS HD HV hs1 hs2 hs3 hcg t ht
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ : 0 ≤ R.ρ := hVL.2.2.2.2.1
  have hρ8 : R.ρ ≤ 1 / 8 := hVL.2.2.2.2.2.1
  have hTA := HS t ht
  -- the a priori bounds
  have hAP : ∀ i ≤ Nh, APB R (cZ R) (cW R Λ cm C₂) (t i).1 (rawHist R i t) i := fun i hi =>
    apriori R hSB hV (fun j hj => hm1 j hj.le) hβ.le (by linarith) H i hi t
      ⟨fun i' hi' => ht.1 i' (by omega), fun i' hi' => ht.2 i' (by omega)⟩
  obtain ⟨hz, hy, hWl⟩ := hAP Nh le_rfl
  obtain ⟨hg, hgε, hμ, hx⟩ := ht.1 Nh le_rfl
  set g := (t Nh).1 with hgdef
  set μ := (t Nh).2.1
  set x := (t Nh).2.2
  have HI := rawInv_hist R hρ Nh hV t
  set st := rawHist R Nh t with hst
  have hZ : st.Z ≠ 0 := HI.Z_ne_zero (by linarith)
  have hcz : 0 ≤ cZ R := by unfold cZ; positivity
  have hcv : 0 ≤ cV R Λ cm := by unfold cV; have := H.hcmu; positivity
  have hcw : 0 ≤ cW R Λ cm C₂ := by unfold cW; have := H.hC₂; positivity
  have hcx := H.hcx
  have hcmu := H.hcmu
  have hg1 : g ≤ 1 := hgε.trans H.hε1
  have hx1 : ‖x.1‖ ≤ cx κ cT * g ^ 3 := (norm_fst_le x).trans hx
  have hx2 : ‖x.2‖ ≤ cx κ cT * g ^ 3 := (norm_snd_le x).trans hx
  have hcxg : cx κ cT * g ≤ 1 := (mul_le_mul_of_nonneg_left hgε hcx).trans H.h3
  have hg2 : g ^ 2 ≤ g := by nlinarith
  have hg3 : g ^ 3 ≤ g ^ 2 := by nlinarith [sq_nonneg g]
  -- the smallness conditions at `g ≤ ε`
  have hη : 2 * (cZ R * g) ≤ R.ρ := by
    have := H.h1; nlinarith [mul_le_mul_of_nonneg_left hgε hcz]
  have hηs : 8 * cM * R.ℓ ^ 2 * (cZ R * g) ≤ 1 / 2 := by
    have := H.h2
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hgε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num :
      (0:ℝ) ≤ 8) hM) (sq_nonneg R.ℓ)) hcz)]
  -- the input norms
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * (cZ R * g)) + 8 * R.ℓ ^ 4 * g with hvdef
  have hv : v ≤ cV R Λ cm * g := by
    rw [hvdef]; unfold cV
    have hM : 0 ≤ cM := Nat.cast_nonneg _
    have : 2 * |μ| + 2 * (cZ R * g) ≤ (2 * cmu Λ cm + 2 * cZ R) * g := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hM (sq_nonneg R.ℓ))]
  have hcR : cV R Λ cm + cW R Λ cm C₂ + 2 ≤ cR R Λ cm C₂ := le_of_eq rfl
  have hv1 : v ≤ 1 := by
    have : cV R Λ cm * g ≤ cR R Λ cm C₂ * ε := by
      have := mul_le_mul_of_nonneg_left hgε (by linarith : (0 : ℝ) ≤ cR R Λ cm C₂)
      nlinarith
    linarith
  set w := cW R Λ cm C₂ * g ^ 2 + ‖x.1‖ with hwdef
  have hwb : w ≤ (cW R Λ cm C₂ + 1) * g ^ 2 := by
    rw [hwdef]
    have : ‖x.1‖ ≤ g ^ 2 := hx1.trans (by
      have := mul_le_mul_of_nonneg_right hcxg (sq_nonneg g)
      calc cx κ cT * g ^ 3 = cx κ cT * g * g ^ 2 := by ring
        _ ≤ 1 * g ^ 2 := this
        _ = g ^ 2 := one_mul _)
    nlinarith
  have hw1 : w ≤ 1 := by
    refine hwb.trans ?_
    have : (cW R Λ cm C₂ + 1) * g ^ 2 ≤ cR R Λ cm C₂ * g := by
      have h1 : cW R Λ cm C₂ + 1 ≤ cR R Λ cm C₂ := by linarith
      calc (cW R Λ cm C₂ + 1) * g ^ 2 ≤ cR R Λ cm C₂ * g ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg g)
        _ ≤ cR R Λ cm C₂ * g := mul_le_mul_of_nonneg_left hg2 (by linarith)
    have : cR R Λ cm C₂ * g ≤ 1 :=
      (mul_le_mul_of_nonneg_left hgε (by linarith : (0 : ℝ) ≤ cR R Λ cm C₂)).trans hcR1
    linarith
  have hdd1 : ‖x.1‖ ≤ 1 := hx1.trans (by nlinarith)
  have hk1' : 8 * ‖x.2‖ ≤ 1 := by
    have : cx κ cT * g ^ 3 ≤ cx κ cT * ε := by
      have : g ^ 3 ≤ ε := by nlinarith [sq_nonneg g, pow_le_one₀ hg.le hg1 (n := 2)]
      exact mul_le_mul_of_nonneg_left this hcx
    linarith
  have hWw : Fnorm Nh (fscale st.Z * R.ℓ) (st.Wl + rawD R st.u x) ≤ ENNReal.ofReal w :=
    Fnorm_add_le _ _ (by positivity) (norm_nonneg _) hWl (le_of_eq (Fnorm_rawD R HI.hu hZ x))
  -- `Z w⁽¹⁾`
  have hw1Z := Zw1_hist R hρ Nh hV t
  -- the past part
  have hζ : ∀ i ≤ Nh, ‖stZeta R (rawHist R i t)‖ ≤ 2 * cZ R * (t i).1 := fun i hi => by
    obtain ⟨hzi, hyi, -⟩ := hAP i hi
    unfold stZeta absorbZeta
    refine (norm_clampDisk_le_self hρ _).trans ?_
    rw [add_div]; refine (norm_add_le _ _).trans ?_; linarith
  have hnk : ∀ k < Nh, ‖nCor (stNu R k (rawHist R k t) (t k).2.1) (rawHist R k t).w1‖ ≤
      f1cn R.ℓ (cmu Λ cm) * (t k).1 := fun k hk => by
    unfold nCor
    refine (norm_clampDisk_le_self (by norm_num) _).trans ?_
    have hw1k := norm_Zw1_le R hρ k (fun i hi => hV i (by omega)) t
    have hμk := (ht.1 k (by omega)).2.2.1
    have e : 4 * stNu R k (rawHist R k t) (t k).2.1 * (rawHist R k t).w1 =
        4 * ((t k).2.1 : ℂ) * (stZ' R (rawHist R k t) * (rawHist R k t).w1) / (L : ℂ) ^ (2 * k) := by
      simp only [stNu]; ring
    have nP2 : ‖(L : ℂ) ^ (2 * k)‖ = ((L : ℝ) ^ k) ^ 2 := by
      rw [norm_pow, Complex.norm_natCast, ← pow_mul, mul_comm]
    have hLk : (0 : ℝ) < ((L : ℝ) ^ k) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    rw [e, norm_div, norm_mul, norm_mul, nP2, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.norm_ofNat]
    rw [div_le_iff₀ hLk]
    unfold f1cn
    have := mul_le_mul hμk hw1k (norm_nonneg _)
      (mul_nonneg hcmu (ht.1 k (by omega)).1.le)
    nlinarith
  obtain ⟨hSe, hESb⟩ := hist_S_decompU R hV hρ hρ8 t ht hβ.le hδ1 H.hcg hcgβ (by linarith [H.h6])
    H.hε1 (by positivity) (by unfold f1cn; positivity) hζ hnk
  obtain ⟨hqb, hBb⟩ := HD t ht
  have hSBb : ‖∑ k ∈ range Nh, hbTil R Nh t k‖ ≤ KB := by
    refine (norm_sum_le _ _).trans (le_trans ?_ hBb)
    refine sum_le_sum fun k hk => ?_
    have hkj := mem_range.1 hk
    have h1 : (1 : ℝ) ≤ ((Nh : ℝ) - k + 1) * 2 ^ (Nh - k) := by
      have : (1 : ℝ) ≤ (Nh : ℝ) - k + 1 := by
        have : (k : ℝ) ≤ Nh := by exact_mod_cast hkj.le
        linarith
      nlinarith [one_le_pow₀ (M₀ := ℝ) (by norm_num : (1 : ℝ) ≤ 2) (n := Nh - k)]
    nlinarith [norm_nonneg (hbTil R Nh t k)]
  have hESb' : ‖_‖ ≤ (24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB * g ^ 3 :=
    hESb.trans (by
      have h0 : 0 ≤ 24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1) := by
        unfold f1cn; positivity
      have := mul_le_mul_of_nonneg_left hBb h0
      exact mul_le_mul_of_nonneg_right this (by positivity))
  -- the constants
  have hcR0 : 0 ≤ cR R Λ cm C₂ := by unfold cR; positivity
  have hQ1 : 1 ≤ Q1 2 := one_le_Q1 (by norm_num)
  have hN0 : 0 ≤ cNear 2 L := Nat.cast_nonneg _
  have hRQ : cS * (Cl * (8 * ‖x.2‖)) ≤ f1cRQ Cl cS (cx κ cT) * g ^ 3 := by
    unfold f1cRQ
    have h0 : 0 ≤ cS * Cl := mul_nonneg (by linarith) hCl
    have := mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ 8 * cS * Cl)
    nlinarith
  have hRL : Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w) ≤
      f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂) * g ^ 2 := by
    unfold f1cRL BH.sig
    have hv0 : 0 ≤ v := by have : (0 : ℝ) ≤ cM := Nat.cast_nonneg _; positivity
    have h1 : v ^ 2 ≤ cV R Λ cm ^ 2 * g ^ 2 := by
      have := pow_le_pow_left₀ hv0 hv 2; rw [mul_pow] at this; exact this
    have h2 : cNear 2 L * Q1 2 ^ 2 * v ^ 2 + Q1 2 * w ≤
        (cNear 2 L * Q1 2 ^ 2 * cV R Λ cm ^ 2 + Q1 2 * (cW R Λ cm C₂ + 1)) * g ^ 2 := by
      have a1 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ cNear 2 L * Q1 2 ^ 2)
      have a2 := mul_le_mul_of_nonneg_left hwb (by linarith : (0 : ℝ) ≤ Q1 2)
      linarith only [a1, a2]
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ Cl * (L : ℝ) ^ 2)
    linarith only [h3]
  have hRD : ClD * ((L : ℝ) ^ 2 * BH.sig 2 L 0 ‖x.1‖) ≤ f1cRD L ClD (cx κ cT) * g ^ 3 := by
    unfold f1cRD BH.sig
    have := mul_le_mul_of_nonneg_left hx1 (by positivity : (0 : ℝ) ≤ ClD * (L : ℝ) ^ 2 * Q1 2)
    have e : ClD * ((L : ℝ) ^ 2 * (cNear 2 L * Q1 2 ^ 2 * 0 ^ 2 + Q1 2 * ‖x.1‖)) =
        ClD * (L : ℝ) ^ 2 * Q1 2 * ‖x.1‖ := by ring
    rw [e]; linarith only [this]
  have hcRQ : 0 ≤ f1cRQ Cl cS (cx κ cT) := by unfold f1cRQ; have : 0 ≤ cS := by linarith
                                              positivity
  have hcRL : 0 ≤ f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂) := by unfold f1cRL; positivity
  have hcRD : 0 ≤ f1cRD L ClD (cx κ cT) := by unfold f1cRD; positivity
  have hcES : 0 ≤ (24 * (2 * cZ R) + 3 * f1cn R.ℓ (cmu Λ cm) + 2 * (2 * β + 1)) * KB := by
    unfold f1cn; have := hβ.le; positivity
  -- smallness at `g ≤ ε`
  have hn8 : f1cn R.ℓ (cmu Λ cm) * g ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hgε (by unfold f1cn; positivity)).trans hs1
  have hcK : 0 ≤ f1cK L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
      (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂)) := by unfold f1cK; positivity
  have hn'8 : f1cn' L R.ℓ (cZ R) (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
      (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂)) * g ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_left hgε (by unfold f1cn'; positivity)).trans hs2
  have hζ8 : (R.ℓ ^ 2 / 7 + f1cw R.ℓ (cmu Λ cm) Cq (f1cRQ Cl cS (cx κ cT))
      (f1cRL L Cl (cV R Λ cm) (cW R Λ cm C₂))) * g ≤ R.ρ :=
    (mul_le_mul_of_nonneg_left hgε (by unfold f1cw f1cn; positivity)).trans hs3
  -- the step estimate
  have hS := hstep L hL8 hLp N R Nh hVL st HI g μ (rawD R st.u x) (rawK R st.u x) (rawD_mem R _ _)
    (rawK_mem R _ _) R.A hA2 (cZ R) (cmu Λ cm) hcz hcmu hg.le hg1 hz hy hη hηs hμ (hm1 Nh le_rfl) eA em heA heAm hTA
    hw1Z w ‖x.1‖ ‖x.2‖ (by positivity) (norm_nonneg _) (norm_nonneg _) hw1 hdd1 hk1' hWw
    (le_of_eq (Fnorm_rawD R HI.hu hZ x)) (le_of_eq (Knorm_rawK R HI.hu hZ x)) hv1
    _ _ _ hcRQ hcRL hcRD hRQ hRL hRD _ ((histFS R Nh t).betaQ Nh Nh 0 R.i₀ (eC 3) (eC 3) 3)
    (∑ k ∈ range Nh, hbTil R Nh t k) _ KB _ hKB hcES (hist_LS_gU R hV hVL t) hSe hESb' hqb hSBb hn8 hn'8 hζ8
  have hre : (2 * (stZ' R st * stCov R Nh st (dirVec (Sum.inl 0)) 0) -
      (stZ' R st ^ 2 * (histFS R Nh t).betaQ Nh Nh 0 R.i₀ (eC 3) (eC 3) 3 +
        ∑ k ∈ range Nh, hbTil R Nh t k) +
      16 * (stZ' R st ^ 2 * (stCov R Nh st (dirVec (Sum.inl 0)) 0 - stCov R Nh st 0 0) *
        st.w1)).re = (f1Coef R Nh t + htad R Nh t).re := rfl
  rw [hre] at hS
  have hHV := HV t ht
  show |(histOut R Nh t).g.re - g - β * g ^ 2| ≤ (32 / 7 * eA + E0) * g ^ 2 + c3 * g ^ 3
  exact F1_final hS hHV hcg (by positivity)

/-- **The sharp band at the step `N_h`** (`N_h = N - 2` in the applications): with the error
`e` of the `ǧ²` term, `e ≤ β/2` (the band `δ = 1/2`) and, for `N_h ≥ 1`,
`e ≤ K_e (L^{-2N_h} + m² L^{2(N_h+1)})` (at `N_h = N - 2` the mass term `m² L^{2(N-1)} ≤ 1` does not
vanish), `|Re ǧ_{N_h+1} - ǧ_{N_h} - β ǧ_{N_h}²| ≤ e ǧ_{N_h}² + C ǧ_{N_h}³`. -/
def BandSharp (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)] (Nh : ℕ) (β Ke C : ℝ)
    (t : Hist.Seq (Xs R)) : Prop :=
  ∃ e : ℝ, 0 ≤ e ∧ e ≤ 1 / 2 * β ∧
    (1 ≤ Nh → e ≤ Ke * ((((L : ℝ) ^ Nh) ^ 2)⁻¹ + R.msq * ((L : ℝ) ^ (Nh + 1)) ^ 2)) ∧
    |(histOut R Nh t).g.re - (t Nh).1 - β * (t Nh).1 ^ 2| ≤ e * (t Nh).1 ^ 2 + C * (t Nh).1 ^ 3

/-- The mass term of the last step: `|m²| L^{2n} ≤ L^{-2}` from `|m²| L^{2(n+1)} ≤ 1`. -/
theorem msq_last2 {L : ℝ} (hL : 0 < L) {m : ℝ} {n : ℕ} (h : |m| * (L ^ (n + 1)) ^ 2 ≤ 1) :
    |m| * (L ^ n) ^ 2 ≤ (L ^ 2)⁻¹ := by
  rw [← one_div, le_div_iff₀ (by positivity)]
  have e : |m| * (L ^ n) ^ 2 * L ^ 2 = |m| * (L ^ (n + 1)) ^ 2 := by ring
  rw [e]; exact h

/-- The `L`-independent bound on the mass constant of the last step. -/
theorem emL_le {C₄ M₀ L : ℝ} (hC₄ : 0 ≤ C₄) (hM₀ : 0 ≤ M₀) (hL : 1 ≤ L) :
    32 / 7 * (8 / 7 * (6 / 5 * (8 / 7 * (C₄ * L ^ 2 + 1) + 2)) * (M₀ + 1) * (L ^ 2)⁻¹) ≤
      32 / 7 * (8 / 7 * (6 / 5 * (8 / 7 * C₄ + 4)) * (M₀ + 1)) := by
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL0 : 0 < L ^ 2 := by positivity
  have hi : (L ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL2
  have hi0 : 0 ≤ (L ^ 2)⁻¹ := by positivity
  have key : (6 / 5 * (8 / 7 * (C₄ * L ^ 2 + 1) + 2)) * (L ^ 2)⁻¹ =
      6 / 5 * (8 / 7 * C₄ + 22 / 7 * (L ^ 2)⁻¹) := by
    field_simp; ring
  have h1 : 6 / 5 * (8 / 7 * C₄ + 22 / 7 * (L ^ 2)⁻¹) ≤ 6 / 5 * (8 / 7 * C₄ + 4) := by
    linarith only [hi]
  have e : 32 / 7 * (8 / 7 * (6 / 5 * (8 / 7 * (C₄ * L ^ 2 + 1) + 2)) * (M₀ + 1) * (L ^ 2)⁻¹) =
      32 / 7 * 8 / 7 * (M₀ + 1) * ((6 / 5 * (8 / 7 * (C₄ * L ^ 2 + 1) + 2)) * (L ^ 2)⁻¹) := by ring
  rw [e, key]
  have hM : 0 ≤ 32 / 7 * 8 / 7 * (M₀ + 1) := by positivity
  have := mul_le_mul_of_nonneg_left h1 hM
  linarith only [this]

end

end Step2
