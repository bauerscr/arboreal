import Step2.Flow.FlowF1S1

/-!
# Sharp (F1) for one RG step

`step_F1s`: the analogue of `step_F1` with the tadpole `16 Z² (C_j(e₁,0) - C_j(0,0)) w⁽¹⁾` in the
`g²` coefficient; the `g²` remainder is only the mass term `(32/7) e_A`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 8000000 in
/-- **(F1) for one step, sharp form**: with `c = Z_{j+1} C_j(e₁, 0)` and the tadpole
`T = 16 Z_{j+1}² (C_j(e₁, 0) - C_j(0, 0)) w⁽¹⁾`,
`|ǧ' - g - Re(2c - Z²q - S_B + T) g²| ≤ (32/7) e_A g² + c₃ g³`. -/
theorem step_F1s : ∃ Cq Cl cS CqD ClD : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧ 0 ≤ CqD ∧ 0 ≤ ClD ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
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
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := rawStep_coup
  obtain ⟨CqD, hCqD, ClD, hClD, hDb⟩ := LS_D_bound
  refine ⟨Cq, Cl, cS, CqD, ClD, hCq, hCl, hcS, hCqD, hClD, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK A hA cZ cmu hcZ hcmu hg0 hg1 hz hy hη hηs hμ hm eA em heA heAm hTA
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
  rw [hc₀ 0, show c₀ + δ - c₀ = δ by ring]
  exact F1_core2 (L := L) hg0 hg1 hℓ hL4 hLj1 hap hZn hrat hcZ hcmu hCq hCqD hcRQ hcRL hcRD hKB
    hcES hρ0 hρ8 hgrG hnuS hAz hm heA heAm hTA hw1 hzC1 hzc0 hzδ q1 q2 q3 q4 l1 l2 l3 hDg hRQ0 hRL0 hRD0
    hRQ hRL hRD hS hES hq hSB hn8 hn'8 hζ8

end

end Step2
