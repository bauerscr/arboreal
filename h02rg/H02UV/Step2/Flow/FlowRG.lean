import Step2.Flow.FlowStep

/-!
# The normalised one-step bounds of the renormalisation group map (`d = 2`)

`rg_step_bounds`: at scale `j`, with field-scale factor `s = |Z|^{-1/2}` in the input and
`s' = |Z'|^{-1/2}` in the output, for a raw state with inactive clamps (`|z/Z|, |y/Z| ≤ η`) and
`v = c_M ℓ² (|μ| + 2η) + 4ℓ⁴ g` (the size of `V♭`):
* the gradient couplings and the relevant coupling of `V_{j+1}` (`step_coup_norm`);
* `‖W^lin_{j+1}‖ ≤ C₂ v² + θ_W ‖W^lin_j‖`;
* `‖D_{j+1}‖ ≤ θ_D ‖D_j‖ + C_D (v² + w)²`;
* `‖K_{j+1}‖_{j+1,A} ≤ κ_K ‖K_j‖_{j,A} + C_K (r³ + r k + k²)` for a radius `r ≥ v, √w`;
all at the causal field scales, with `θ_W, θ_D = O(1/L)` and `κ_K = O(1/L + A^{-η})`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

theorem Knorm_le_of_wnorm {k : ℕ} {ℓ A : ℝ} {M : ENNReal} {K : Act 2 L N}
    (h : ∀ U, IsConn k U → wnorm k ℓ A U (K U) ≤ M) : Knorm k ℓ A K ≤ M := by
  rw [Knorm_eq_iSup]
  exact iSup₂_le fun U hU => h U (by simpa [connSets] using hU)

theorem wnorm_Kconn {k : ℕ} {ℓ A : ℝ} {K : Act 2 L N} {U : Finset (Lam 2 L N)} (hU : IsConn k U) :
    wnorm k ℓ A U (Kconn k K U) = wnorm k ℓ A U (K U) := by
  simp [Kconn, if_pos hU]

theorem ennreal_bound_aux {x : ENNReal} {y a b c d : ℝ} (hy : 0 ≤ y) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hx : x ≤ ENNReal.ofReal y) :
    ENNReal.ofReal a * x + ENNReal.ofReal b * (ENNReal.ofReal c + ENNReal.ofReal d * x + x ^ 2) ≤
      ENNReal.ofReal (a * y + b * (c + d * y + y ^ 2)) := by
  calc ENNReal.ofReal a * x + ENNReal.ofReal b * (ENNReal.ofReal c + ENNReal.ofReal d * x + x ^ 2)
      ≤ ENNReal.ofReal a * ENNReal.ofReal y + ENNReal.ofReal b * (ENNReal.ofReal c +
          ENNReal.ofReal d * ENNReal.ofReal y + ENNReal.ofReal y ^ 2) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_pow hy,
          ← ENNReal.ofReal_add hc (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_add (by positivity)
            (by positivity)]

/-- The normalised one-step bounds, with the constants of `rg_step_bounds`. -/
def StepBounds (L : ℕ) [NeZero L] (A C₀ η εs CK C₂ CD Cq Cl cS : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
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
      let out := rawStep R j st g μ D K
      let s' := fscale (stZ' R st)
      let RQ := cS * (Cl * (8 * k))
      let RL := Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v (wl + dd))
      ‖out.st.z / stZ' R st‖ ≤ 8 * R.ℓ ^ 2 / 49 * g + (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 ∧
      ‖out.st.y / stZ' R st‖ ≤ 8 * R.ℓ ^ 2 / 49 * g + (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 ∧
      ‖out.nu - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
        16 / 7 * (L : ℝ) ^ 2 * (8 * R.ℓ ^ 2 / 49 * g + (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2) * |μ| +
        3 * (L : ℝ) ^ 2 * ηz + 8 * R.ℓ ^ 2 / 49 * g +
        2 * ((L : ℝ) ^ 2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 ∧
      Fnorm (j + 1) (s' * R.ℓ) out.st.Wl ≤ ENNReal.ofReal (C₂ * v ^ 2 + C₀ / L * wl) ∧
      Fnorm (j + 1) (s' * R.ℓ) out.D ≤ ENNReal.ofReal (C₀ / L * dd + CD * (v ^ 2 + (wl + dd)) ^ 2) ∧
      Knorm (j + 1) (s' * R.ℓ) A out.K ≤
        ENNReal.ofReal (8 * C₀ * ((L : ℝ)⁻¹ + (A / 2) ^ (-η)) * k +
          CK * (r ^ 3 + r * (8 * k) + (8 * k) ^ 2))

set_option maxHeartbeats 4000000 in
/-- **The normalised one-step bounds.** -/
theorem rg_step_bounds : ∃ (C₀ η : ℝ) (L₀ : ℕ), 0 ≤ C₀ ∧ 0 < η ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ A : ℝ, A₀ ≤ A →
    ∃ (εs CK C₂ CD Cq Cl cS : ℝ), 0 < εs ∧ 0 ≤ CK ∧ 0 ≤ C₂ ∧ 0 ≤ CD ∧ 0 ≤ Cq ∧ 0 ≤ Cl ∧
      1 ≤ cS ∧
    StepBounds L A C₀ η εs CK C₂ CD Cq Cl cS := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := step_coup_norm
  obtain ⟨L₁, hsrc⟩ := Src_bound_ts 2 le_rfl
  obtain ⟨C₀T, hC₀T, L₂, htrl⟩ := TrL_contract'_ts 2 le_rfl
  obtain ⟨C₀D, hC₀D, L₃, hdn⟩ := Dnext_bound_ts 2 le_rfl
  obtain ⟨C₀K, ηK, L₄, hC₀K, hηK, hK⟩ := stepK_tsW 2 le_rfl
  refine ⟨max C₀T (max C₀D C₀K), ηK, max (max L₁ L₂) (max (max L₃ L₄) (max 49 ⌈pauliL0 2⌉₊)),
    by positivity, hηK, ?_⟩
  intro L _ hL
  have hL1 : L₁ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL3 : L₃ ≤ L := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hL
  have hL4 : L₄ ≤ L := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hL
  have hL49 : 49 ≤ L := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hL
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L := by omega
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_trans
    (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hL)
  obtain ⟨C₂, hC₂, hsrc'⟩ := hsrc L hL1
  obtain ⟨C₃, hC₃, hdn'⟩ := hdn L hL3
  obtain ⟨A₀K, hA₀K, hK'⟩ := hK L hL4 2 (by norm_num)
  refine ⟨2 * A₀K, by linarith, fun A hA => ?_⟩
  have hA2 : A₀K ≤ A / 2 := by linarith
  have hA1 : 1 ≤ A := by linarith
  obtain ⟨εK, C₁K, hεK, hC₁K, hK''⟩ := hK' (A / 2) hA2
  refine ⟨min εK 1, C₁K, C₂, C₃, Cq, Cl, cS, lt_min hεK one_pos, hC₁K, hC₂, hC₃, hCq, hCl, hcS, ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 η hz hy hη hηs wl dd k r hwl0 hdd0 hk0 hWl hDd hKk
    v hvr hwr hrε hkε out s' RQ RL
  have hV' := hV
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
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
  -- scales
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < s' := fscale_pos hZ'
  have hsc := scale_ok hZ hζ8 hℓ
  have hsc' : s' * R.ℓ + s' * R.ℓ / 4 ≤ 3 / 2 * (fscale st.Z * R.ℓ) := hsc
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hsum : s' * R.ℓ + s' * R.ℓ / 4 ≤ 2 * (fscale st.Z * R.ℓ) := by linarith
  have hCℓ : s' * R.ℓ / 4 ≤ fscale st.Z * R.ℓ := by linarith [mul_pos hs' hℓ]
  obtain ⟨hC0, hCt0, -, -⟩ := H.cov hV
  have hC : GoodCov2 j (s' * R.ℓ / 4) (stCov R j st) := hC0
  have hCt : TInv (stCov R j st) := hCt0
  -- the inputs
  have hVmem := VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN
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
    simp only [v]
    nlinarith
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hv0 : 0 ≤ v := by positivity
  have hr1 : r ≤ 1 := hrε.trans (min_le_right _ _)
  have hv1 : v ≤ 1 := hvr.trans hr1
  have hr0 : 0 ≤ r := hv0.trans hvr
  have hw1 : wl + dd ≤ 1 := hwr.trans (by nlinarith)
  -- `Δ` and `K♭`
  set δΔ := 8 * cM * R.ℓ ^ 2 * η with hδΔ
  have hδΔ0 : 0 ≤ δΔ := by have := (Nat.cast_nonneg (α := ℝ) (Fintype.card (Mono 2))); positivity
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
  have hKfmem := Kflat_mem hjN (VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN _)
    (eps_stDelta R j st) hK
  have hk8 : 8 * k ≤ 1 := hkε.trans (min_le_right _ _)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLL : (L : ℝ) ^ 2 / (L : ℝ) ^ 3 = (L : ℝ)⁻¹ := by field_simp
  -- the couplings
  have hc := hcoup L hL8 hLp N R j hV st H g μ D K hD hK (A / 2) (by linarith) v (wl + dd) (8 * k)
    hv0 (by positivity) (by positivity) hv1 hw1 hk8 hVv hw hKflat η hz hy hη hm
  obtain ⟨c1, c2, c3⟩ := hc
  have hEz : R.ℓ ^ 2 / 16 * ‖stGr R j st g μ‖ ≤ 8 * R.ℓ ^ 2 / 49 * g := by
    have : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
    calc R.ℓ ^ 2 / 16 * ‖stGr R j st g μ‖ ≤ R.ℓ ^ 2 / 16 * (8 / 7 * g) := by gcongr
      _ ≤ _ := by nlinarith
  have hEz7 : R.ℓ ^ 2 / 7 * ‖stGr R j st g μ‖ ≤ 8 * R.ℓ ^ 2 / 49 * g := by
    have : 0 ≤ R.ℓ ^ 2 := sq_nonneg _
    calc R.ℓ ^ 2 / 7 * ‖stGr R j st g μ‖ ≤ R.ℓ ^ 2 / 7 * (8 / 7 * g) := by gcongr
      _ = _ := by ring
  refine ⟨c1.trans (by linarith), c2.trans (by linarith), c3.trans ?_, ?_, ?_, ?_⟩
  · have hE := add_le_add_right hEz ((2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2)
    have hL2 : (0 : ℝ) ≤ 16 / 7 * (L : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hL2) (abs_nonneg μ)
    linarith
  · -- `W^lin`
    show Fnorm (j + 1) (s' * R.ℓ) (WlinNext j (stCov R j st) (stVf R j st g μ) st.Wl) ≤ _
    rw [WlinNext]
    refine Fnorm_add_le _ _ (by positivity) (by positivity)
      (hsrc' N j (by omega) _ _ _ hsℓ (mul_pos hs' hℓ) (by positivity) hsum hCℓ _ hC hCt _
        hVf_mem.1 (fun b => eps_VfamL j _ b) v hv0 hv1 hVv) ?_
    refine (htrl L hL2 N j (by omega) _ _ _ hsℓ (mul_pos hs' hℓ) (by positivity) hsum hCℓ _ hC hCt
      _ H.hWl.1 H.hWl.2.1 1 (by simp) wl hwl0 hWl).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hLL]
    have : C₀T ≤ max C₀T (max C₀D C₀K) := le_max_left _ _
    have := mul_le_mul_of_nonneg_right this (inv_nonneg.2 hL0.le)
    have := mul_le_mul_of_nonneg_right this hwl0
    rw [div_eq_mul_inv]; linarith
  · -- `D`
    show Fnorm (j + 1) (s' * R.ℓ) (Dnext j (stCov R j st) (stVf R j st g μ) st.Wl D) ≤ _
    refine (hdn' N j (by omega) _ _ _ hsℓ (mul_pos hs' hℓ) (by positivity) hsum hCℓ _ hC hCt _ _ _
      hVf_mem.1 H.hWl.1 hD.1 hD.2.1 (fun b => eps_VfamL j _ b) v (wl + dd) dd hv0 (by positivity)
      hdd0 hv1 hw1 hVv hw hDd).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hLL]
    have : C₀D ≤ max C₀T (max C₀D C₀K) := (le_max_left _ _).trans (le_max_right _ _)
    have := mul_le_mul_of_nonneg_right this (inv_nonneg.2 hL0.le)
    have := mul_le_mul_of_nonneg_right this hdd0
    rw [div_eq_mul_inv]; linarith
  · -- `K`
    show Knorm (j + 1) (s' * R.ℓ) A (Kconn (j + 1) (Kplus j (stCov R j st) (stVf R j st g μ)
      (st.Wl + D) (Kflat j (stDelta R j st) K))) ≤ _
    refine Knorm_le_of_wnorm fun U hU => ?_
    rw [wnorm_Kconn hU]
    have hKU := hK'' N j (by omega) _ _ _ hsℓ (mul_pos hs' hℓ) (by positivity) hsum _ hC _ _ _
      hVf_mem.1 (add_mem H.hWl hD).1 (fun b => eps_VfamL j _ b) hKfmem.1 r hr0
      (hrε.trans (min_le_left _ _)) (hVv.trans (ENNReal.ofReal_le_ofReal hvr))
      (hw.trans (ENNReal.ofReal_le_ofReal hwr))
      (hKflat.trans (ENNReal.ofReal_le_ofReal (hkε.trans (min_le_left _ _)))) U hU
    rw [show (2 : ℝ) * (A / 2) = A by ring] at hKU
    refine hKU.trans ((ennreal_bound_aux (by positivity) (by positivity) hC₁K
      (by positivity) hr0 hKflat).trans (ENNReal.ofReal_le_ofReal ?_))
    rw [hLL]
    have hC0 : C₀K ≤ max C₀T (max C₀D C₀K) := (le_max_right _ _).trans (le_max_right _ _)
    have hpos : 0 ≤ (L : ℝ)⁻¹ + (A / 2) ^ (-ηK) := by positivity
    have h1 := mul_le_mul_of_nonneg_right hC0 hpos
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 8 * k)
    have e1 : max C₀T (max C₀D C₀K) * ((L : ℝ)⁻¹ + (A / 2) ^ (-ηK)) * (8 * k) =
        8 * max C₀T (max C₀D C₀K) * ((L : ℝ)⁻¹ + (A / 2) ^ (-ηK)) * k := by ring
    linarith

end

end Step2
