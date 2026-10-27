import Step2.Last.LastNStep

/-!
# The last step `j = N - 1`: the normalised bounds (`rg_last_bounds`)

The analogue of `rg_step_bounds` (`Step2.Flow.FlowRG`) and `Last.rg_step_bounds` for the last step,
with the same input hypotheses (raw state with `RawInv`, inactive clamps, `‖V♭‖ ≤ v ≤ r`,
`‖W^lin‖ + ‖D‖ ≤ r²`, `‖K‖ ≤ k`), under `ValidLast R j` (`j + 1 = N`, covariance `C'^{≠0}_N`).
The outputs are the final-scale object `rawStepN` (`LastOut`):

* the normalised final couplings `z_N/Z_N`, `y_N/Z_N`, `L^{2N} ν_N/Z_N - L² μ`, `g_N/Z_N²`;
* `V_N(B) = V_{κ_N}(B)`, `|u_N(B)| ≤ Q₁ v`, `‖V_N(B)‖ ≤ 2Q₁ v`, `|u_N(Λ)| ≤ L² Q₁ v`;
* `‖𝒲_N(B)‖ ≤ L² Q₁² v² + Q₁ (‖W^lin‖ + ‖D‖)`;
* `‖K_N(Λ)‖ ≤ C_K (r³ + 8k)`,

all at scale `N` with the output field scale `s_N ℓ`. There is no contraction and no Lipschitz
bound (the trajectory ends here); `rawStepN_ZVK` is the exact identity for the integrated
partition function.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

namespace LastN

set_option maxHeartbeats 4000000 in
/-- **The normalised bounds of the last step** `j = N - 1`. -/
theorem rg_last_bounds : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ (εs CK : ℝ), 0 < εs ∧ 0 ≤ CK ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidLast R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
      ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
        8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
      ∀ wl dd k r : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      Knorm j (fscale st.Z * R.ℓ) A K ≤ ENNReal.ofReal k →
      let v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g
      v ≤ r → wl + dd ≤ r ^ 2 → r ≤ εs → 8 * k ≤ εs →
      let out := rawStepN R j st g μ D K
      let s' := fscale out.Z
      ‖out.κ.z / out.Z‖ ≤ R.ℓ ^ 2 / 14 * g ∧ ‖out.κ.y / out.Z‖ ≤ R.ℓ ^ 2 / 14 * g ∧
      ‖(L : ℂ) ^ (2 * (j + 1)) * out.κ.nu / out.Z - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
        16 / 7 * (L : ℝ) ^ 2 * ηz + R.ℓ ^ 2 / 7 * g ∧
      ‖out.κ.g / out.Z ^ 2‖ ≤ 8 / 7 * g ∧
      ‖out.u‖ ≤ (L : ℝ) ^ 2 * (Q1 2 * v) ∧
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        (out.V b : Alg 2 L N) = Vcoup out.κ (blockSet j b) ∧
        ‖upN out.C (stVf R j st g μ) b‖ ≤ Q1 2 * v ∧
        Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ) (out.V b : Alg 2 L N) ≤
          ENNReal.ofReal (2 * (Q1 2 * v)) ∧
        Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ) (out.W b : Alg 2 L N) ≤
          ENNReal.ofReal ((L : ℝ) ^ 2 * Q1 2 ^ 2 * v ^ 2 + Q1 2 * (wl + dd))) ∧
      Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ) (out.K : Alg 2 L N) ≤
        ENNReal.ofReal (CK * (r ^ 3 + 8 * k)) := by
  obtain ⟨Lk, hLk⟩ := lastK_ts 2 (by norm_num)
  refine ⟨max Lk (max 49 ⌈pauliL0 2⌉₊), fun L _ hL => ?_⟩
  have hLk' : Lk ≤ L := le_trans (le_max_left _ _) hL
  have hL49 : 49 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by omega
  have hLc : ⌈pauliL0 2⌉₊ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hLc)
  obtain ⟨A₀K, hA₀K, hK'⟩ := hLk L hLk'
  refine ⟨2 * A₀K, by linarith, fun A hA => ?_⟩
  have hA2 : A₀K ≤ A / 2 := by linarith
  have hA1 : 1 ≤ A := by linarith
  obtain ⟨ε₀, C₁, hε₀, hC₁, hK''⟩ := hK' (A / 2) hA2
  refine ⟨min ε₀ 1, C₁, lt_min hε₀ one_pos, hC₁, ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 η hz hy hη hηs wl dd k r hwl0 hdd0 hk0 hWl hDd hKk
    v hvr hwr hrε hkε out s'
  have hV' := hV
  obtain ⟨hjN, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  have hj : j < N := by omega
  -- clamps
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  -- scales
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < s' := fscale_pos hZ'
  have hsc := scale_ok hZ hζ8 hℓ
  have hsc' : s' * R.ℓ + s' * R.ℓ / 4 ≤ 3 / 2 * (fscale st.Z * R.ℓ) := hsc
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hsum : s' * R.ℓ + s' * R.ℓ / 4 ≤ 2 * (fscale st.Z * R.ℓ) := by linarith
  obtain ⟨hC0, -, hCs, hCsym⟩ := covN hV H
  have hC : GoodCov2 j (s' * R.ℓ / 4) (stCovN R j st) := hC0
  -- the inputs
  have hVmem := VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hj
    (stKap R j st g μ).toVec
  have hVf_mem : stVf R j st g μ ∈ BSub (L := L) (N := N) j := by
    rw [stVf_eq_kap]; exact hVmem
  have hgr := norm_stGr_le R j st g μ
  rw [abs_of_nonneg hg0] at hgr
  have hrZ : ‖stZ' R st / st.Z‖ ≤ 9 / 8 := by
    have e : stZ' R st / st.Z = 1 + stZeta R st := by
      unfold stZ'; rw [mul_div_cancel_left₀ _ hZ]
    rw [e]; refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
  have hVv : Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤ ENNReal.ofReal v := by
    have e : stVf R j st g μ = VfamL j ![0, 0, (μ : ℂ) * stZ' R st / (L : ℂ) ^ (2 * j) -
        stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2] := stVf_eq hZ hzy hyc
    rw [e]
    refine (Fnorm_VfamL_norm2 j hj.le hℓ hZ _ 0 0 _ _ μ R.msq).trans
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
    simp only [v]
    nlinarith
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hv0 : 0 ≤ v := by positivity
  have hr0 : 0 ≤ r := hv0.trans hvr
  -- `Δ` and `K♭`
  set δΔ := 8 * cM * R.ℓ ^ 2 * η with hδΔ
  have hδΔ0 : 0 ≤ δΔ := by
    have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
  have hΔ : Fnorm j (fscale st.Z * R.ℓ) (stDelta R j st) ≤ ENNReal.ofReal δΔ := by
    refine (Fnorm_stDelta_le hj.le hℓ hZ (2 * η) hζη
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
  have hKfmem := Kflat_mem hj (VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hj _)
    (eps_stDelta R j st) hK
  -- the couplings
  obtain ⟨c1, c2, c3, c4⟩ := coupN_bounds R hjN st g μ D K hZ hρ0 hg0 hm η hz hy hη hρ8 hC0
    hCs hCsym
  have hsℓ' : 0 < s' * R.ℓ := mul_pos hs' hℓ
  have hsℓC : 0 < s' * R.ℓ / 4 := by positivity
  refine ⟨c1, c2, c3, c4, ?_, fun b hb => ⟨rawStepN_V R j st g μ D K hCs hCsym b,
    upN_le_v (by norm_num) hLp hjN hsℓ' hsℓC hsum hC hVf_mem.1 hv0 hVv hb,
    VpN_le_v (by norm_num) hLp hjN hsℓ' hsℓC hsum hC hVf_mem.1 hv0 hVv hb,
    Sb_le_vw (by norm_num) hLp hjN hsℓ' hsℓC hsum hC hVf_mem.1 (add_mem H.hWl hD).1 hv0
      (by positivity) hVv hw hb⟩, ?_⟩
  · -- `u_N(Λ)`
    show ‖uXN j (stCovN R j st) (stVf R j st g μ) univ‖ ≤ _
    rw [uXN]
    refine (norm_sum_le _ _).trans ?_
    refine (sum_le_card_nsmul _ _ (Q1 2 * v) fun b hb =>
      upN_le_v (by norm_num) hLp hjN hsℓ' hsℓC hsum hC hVf_mem.1 hv0 hVv
        (mem_blockIdx_of_mem_blocks hb)).trans ?_
    rw [nsmul_eq_mul]
    have hn : ((blockIdx (d := 2) (L := L) (N := N) j).card : ℝ) ≤ (L : ℝ) ^ 2 := by
      exact_mod_cast card_blockIdx_last (d := 2) (L := L) hjN
    have hQ : 0 ≤ Q1 2 * v := mul_nonneg (by linarith [one_le_Q1 (d := 2) (by norm_num)]) hv0
    exact mul_le_mul_of_nonneg_right hn hQ
  · -- `K_N(Λ)`
    have hKU := hK'' N j hjN _ _ _ hsℓ hsℓ' hsℓC hsum _ hC _ _ _
      hVf_mem.1 (add_mem H.hWl hD).1 (fun b => eps_VfamL j _ b) hKfmem.1 r hr0
      (hrε.trans (min_le_left _ _)) (hVv.trans (ENNReal.ofReal_le_ofReal hvr))
      (hw.trans (ENNReal.ofReal_le_ofReal hwr))
      (hKflat.trans (ENNReal.ofReal_le_ofReal (hkε.trans (min_le_left _ _))))
    refine hKU.trans ?_
    calc ENNReal.ofReal C₁ * (ENNReal.ofReal (r ^ 3) +
          Knorm j (fscale st.Z * R.ℓ) (A / 2) (Kflat j (stDelta R j st) K))
        ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal (r ^ 3) + ENNReal.ofReal (8 * k)) := by
          gcongr
      _ = ENNReal.ofReal (C₁ * (r ^ 3 + 8 * k)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul hC₁]

end LastN

end

end Step2
