import Step2.Coup.CoupFlow

/-!
# The coupling outputs of one raw step (`h02uv-outline.tex`, Section `sec:reduction`)

`rawStep_coup`: the couplings `(z, y, ν, g)_{j+1}` of `V_{j+1}` are
`κ♭' - κ_Q' - κ_L` (`κ♭` the couplings of `V♭`, `'` the first-order shift with `c₀ = C(x,x)`,
`δ = C(x+e,x) - C(x,x)`), with `κ_Q` bounded by `‖K♭‖` and `κ_L` by `v² + w`, at the input scale
`s ℓ`, output scale `s' ℓ` and Gram scale `s' ℓ/4`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

theorem Coup.toVec_ofVec (v : Fin 4 → ℂ) : (Coup.ofVec v).toVec = v := by
  funext i; fin_cases i <;> rfl

theorem cvec4_Vcoup_block (hL8 : 2 ^ (2 + 3) + 8 * 2 < L) {k : ℕ} (hk : k < N) (i₀ : Fin 2)
    (κ : Coup) :
    cvec4 (blockSet (L := L) (N := N) k (0 : Fin 2 → ℕ)) i₀ (Vcoup κ (blockSet k 0)) =
      κ.toVec := by
  have hX := isSmall_blockSet_of_mem (zero_mem_blockIdx (d := 2) (L := L) (N := N) k)
  exact cvec4_unif (patch_of_small hL8 hk hX) hX.2.1.1 i₀ 0 κ

section Read

variable (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N)

/-- The coupling vector read off by the step. -/
def stCv : Fin 4 → ℂ := cvec4 (blockSet (L := L) (N := N) (j + 1) 0) R.i₀
  (Vnext2 j (stCov R j st) (stVf R j st g μ) (st.Wl + D) (Kflat j (stDelta R j st) K) 0)

/-- The coupling `ζ_{j+1} = clamp_ρ((z' + y')/Z_{j+1})` absorbed in the next step. -/
def stZeta2 : ℂ := absorbZeta R (stZ' R st) (stCv R j st g μ D K 0 + stCv R j st g μ D K 1)

/-- `Z_{j+2} = Z_{j+1}(1 + ζ_{j+1})`, the normalisation of the output couplings. -/
def stZ2 : ℂ := stZ' R st * (1 + stZeta2 R j st g μ D K)

/-- The accumulated zero mode after the step. -/
def stW1 : ℂ := st.w1 + ∑ x, stCov R j st x 0

theorem rawStep_nu : (rawStep R j st g μ D K).nu =
    stCv R j st g μ D K 2 * (L : ℂ) ^ (2 * (j + 1)) / stZ2 R j st g μ D K := rfl
theorem rawStep_g : (rawStep R j st g μ D K).g = stCv R j st g μ D K 3 /
    stZ2 R j st g μ D K ^ 2 * (1 + nCor (stCv R j st g μ D K 2) (stW1 R j st)) := rfl

end Read

/-- The coefficient vector of `V♭`. -/
def stKap (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) : Coup :=
  Coup.ofVec ![st.z + stYc R st - stA R st, st.y - stYc R st,
    stNu R j st μ - stA R st * R.msq, stGr R j st g μ * stZ' R st ^ 2]

theorem stVf_eq_kap (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ) :
    stVf R j st g μ = VfamL j (stKap R j st g μ).toVec := by
  rw [stKap, Coup.toVec_ofVec]; rfl

/-- **The couplings of `V_{j+1}` after one raw step**: `κ' = κ♭' - κ_Q' - κ_L`. -/
theorem rawStep_coup : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 1 ≤ A → ∀ v w k : ℝ, 0 ≤ v → 0 ≤ w → 0 ≤ k →
      v ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤ ENNReal.ofReal v →
      Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal w →
      Knorm j (fscale st.Z * R.ℓ) A (Kflat j (stDelta R j st) K) ≤ ENNReal.ofReal k →
    ∃ (c₀ δ : ℂ) (κQ κL : Coup), (∀ x, stCov R j st x x = c₀) ∧
      (∀ x e, stCov R j st (x + dirVec e) x = c₀ + δ) ∧
      Coup.ofVec (stCv R j st g μ D K) =
        (stKap R j st g μ).shift 2 c₀ δ - κQ.shift 2 c₀ δ - κL ∧
      ‖κQ.z‖ ≤ Cq * ((fscale st.Z * R.ℓ) ^ 2)⁻¹ * (cS * (Cl * k)) ∧
      ‖κQ.y‖ ≤ Cq * ((fscale st.Z * R.ℓ) ^ 2)⁻¹ * (cS * (Cl * k)) ∧
      ‖κQ.nu‖ ≤ Cq * ((fscale st.Z * R.ℓ) ^ 2)⁻¹ * (cS * (Cl * k)) / ((L : ℝ) ^ j) ^ 2 ∧
      ‖κQ.g‖ ≤ Cq * ((fscale st.Z * R.ℓ) ^ 4)⁻¹ * (cS * (Cl * k)) ∧
      ‖κL.z‖ ≤ Cq * ((fscale (stZ' R st) * R.ℓ) ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ∧
      ‖κL.y‖ ≤ Cq * ((fscale (stZ' R st) * R.ℓ) ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ∧
      ‖κL.nu‖ ≤ Cq * ((fscale (stZ' R st) * R.ℓ) ^ 2)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) /
        ((L : ℝ) ^ (j + 1)) ^ 2 ∧
      ‖κL.g‖ ≤ Cq * ((fscale (stZ' R st) * R.ℓ) ^ 4)⁻¹ *
        (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)) ∧
      ∀ b ∈ blockIdx (L := L) (N := N) j, ∀ i₀ : Fin 2,
        cvec4 (blockSet (L := L) (N := N) j b) i₀
          (LS j (stCov R j st) (stVf R j st g μ) (st.Wl + D) b : Alg 2 L N) = κL.toVec := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupP_bound
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK A hA v w k hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk
  have hV' := hV
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ0 st).trans hρ8
  obtain ⟨hC, hCt, hCs, hCsym⟩ := H.cov hV
  have hsc := scale_ok hZ hζ hℓ
  have hs := fscale_pos hZ
  have hs' : 0 < fscale (stZ' R st) := fscale_pos (mul_ne_zero hZ (one_add_ne_zero (by linarith)))
  have hjN : j < N := by omega
  have hVf := stVf_eq_kap R j st g μ
  have hKf := Kflat_mem hjN (VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN _)
    (eps_stDelta R j st) hK
  obtain ⟨c₀, δ, κQ, κL, hc₀, hδ, hrep, q1, q2, q3, q4, l1, l2, l3, l4, hLcv⟩ :=
    h L hL8 hLp N j hj2 (fscale st.Z * R.ℓ) (fscale (stZ' R st) * R.ℓ)
      (fscale (stZ' R st) * R.ℓ / 4) (by positivity) (by positivity) (by positivity)
      (by have e : fscale (stZ' R st) = fscale (st.Z * (1 + stZeta R st)) := rfl
          have := mul_pos hs hℓ
          rw [e]; linarith) (stCov R j st) hC hCs hCsym (stKap R j st g μ) (st.Wl + D)
      (Kflat j (stDelta R j st) K) (add_mem H.hWl hD) hKf A hA v w k hv0 hw0 hk0 hv1 hw1 hk1
      (by rw [← hVf]; exact hVv) hWw hKk
  refine ⟨c₀, δ, κQ, κL, hc₀, hδ, ?_, q1, q2, q3, q4, l1, l2, l3, l4,
    fun b hb i₀ => by rw [hVf]; exact hLcv b hb i₀⟩
  have h0 := zero_mem_blockIdx (d := 2) (L := L) (N := N) (j + 1)
  have hcv := cvec4_Vcoup_block hL8 (by omega : j + 1 < N) R.i₀
    ((stKap R j st g μ).shift 2 c₀ δ - κQ.shift 2 c₀ δ - κL)
  rw [← hrep 0 h0] at hcv
  have e2 : stCv R j st g μ D K = cvec4 (blockSet (L := L) (N := N) (j + 1) 0) R.i₀
      (Vnext2 j (stCov R j st) (VfamL j (stKap R j st g μ).toVec) (st.Wl + D)
        (Kflat j (stDelta R j st) K) 0) := by
    rw [stCv, hVf]
  rw [e2, hcv, Coup.ofVec_toVec]

/-! ### Normalised bounds -/

/-- The entries of a covariance with `GoodCov2` at `ℓ_C`: `|C(x,x)| ≤ ℓ_C²` and the first difference
`|δ| ≤ ℓ_C²/(2 L^{2(j+1)})`. -/
theorem cov_c0_delta_le {j : ℕ} {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    (hC : GoodCov2 j ℓC C) {c₀ δ : ℂ} (hc₀ : ∀ x, C x x = c₀)
    (hδ : ∀ x e, C (x + dirVec e) x = c₀ + δ) (hδ' : ∀ x e, C x (x + dirVec e) = c₀ + δ) :
    ‖c₀‖ ≤ ℓC ^ 2 ∧ ‖δ‖ ≤ ℓC ^ 2 / (2 * ((L : ℝ) ^ (j + 1)) ^ 2) := by
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  refine ⟨?_, ?_⟩
  · rw [← hc₀ 0]; exact norm_cov_le hG hB 0 0
  · have h := norm_cov_diff_le hG (by simp [pPhi]) hB (Sum.inl 0) 0
    rw [add_comm (dirVec (Sum.inl 0)) 0, hc₀, hδ, hδ', hc₀] at h
    have e : c₀ - (c₀ + δ) - (c₀ + δ) + c₀ = -(2 * δ) := by ring
    rw [e, norm_neg, norm_mul] at h
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h
    have hh : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by positivity
    rw [le_div_iff₀ (by positivity)]
    have : ℓC ^ 2 * (((L : ℝ) ^ (j + 1)) ^ 2)⁻¹ * ((L : ℝ) ^ (j + 1)) ^ 2 = ℓC ^ 2 := by
      field_simp
    nlinarith

theorem fscale_sq {Z : ℂ} : fscale Z ^ 2 = ‖Z‖⁻¹ := by
  unfold fscale; rw [Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _))]

theorem norm_stZ' {R : RGPar 2 L N} {st : RawSt 2 L N} :
    ‖stZ' R st‖ = ‖st.Z‖ * ‖1 + stZeta R st‖ := by unfold stZ'; rw [norm_mul]

theorem norm_clampDisk_le_self {r : ℝ} (hr : 0 ≤ r) (u : ℂ) : ‖clampDisk r u‖ ≤ ‖u‖ := by
  unfold clampDisk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one
    (div_nonneg hr (norm_nonneg _)))]
  exact mul_le_of_le_one_right (norm_nonneg _) (min_le_left _ _)

set_option maxHeartbeats 4000000 in
/-- **The normalised couplings after one step**: with inactive clamps
(`|z/Z|, |y/Z| ≤ η`, `2η ≤ ρ`), `R_Q = c_S C_l k`, `R_L = C_l L² σ(v, w)`, the raw quartic coupling
`g_r = ǧ/(1 + n)` and `E_z = (ℓ²/16)|g_r| + (2 C_q R_Q + C_q R_L)/ℓ²`,
* `|z'/Z_{j+1}|, |y'/Z_{j+1}| ≤ E_z`;
* `|ν' - L² μ| ≤ (16/7) L² E_z |μ| + 3 L² η + (ℓ²/7)|g_r| + 2(L² C_q R_Q + C_q R_L)/ℓ²`
  (if `|m²| L^{2j} ≤ 1`), with `ν' = κ_ν L^{2(j+1)}/Z_{j+2}`. -/
theorem step_coup_norm : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → ∀ A : ℝ, 1 ≤ A → ∀ v w k : ℝ, 0 ≤ v → 0 ≤ w → 0 ≤ k →
      v ≤ 1 → w ≤ 1 → k ≤ 1 →
      Fnorm j (fscale st.Z * R.ℓ) (stVf R j st g μ) ≤ ENNReal.ofReal v →
      Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal w →
      Knorm j (fscale st.Z * R.ℓ) A (Kflat j (stDelta R j st) K) ≤ ENNReal.ofReal k →
      ∀ η : ℝ, ‖st.z / st.Z‖ ≤ η → ‖st.y / st.Z‖ ≤ η → 2 * η ≤ R.ρ →
      |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 →
      let RQ := cS * (Cl * k)
      let RL := Cl * ((L : ℝ) ^ 2 * BH.sig 2 L v w)
      let Ez := R.ℓ ^ 2 / 16 * ‖stGr R j st g μ‖ + (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2
      ‖stCv R j st g μ D K 0 / stZ' R st‖ ≤ Ez ∧
      ‖stCv R j st g μ D K 1 / stZ' R st‖ ≤ Ez ∧
      ‖(rawStep R j st g μ D K).nu - (L : ℂ) ^ 2 * (μ : ℂ)‖ ≤
          16 / 7 * (L : ℝ) ^ 2 * Ez * |μ| + 3 * (L : ℝ) ^ 2 * η +
            R.ℓ ^ 2 / 7 * ‖stGr R j st g μ‖ + 2 * ((L : ℝ) ^ 2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := rawStep_coup
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK A hA v w k hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk
    η hz hy hη hm RQ RL Ez
  obtain ⟨c₀, δ, κQ, κL, hc₀, hδ, hrep, q1, q2, q3, q4, l1, l2, l3, l4, -⟩ :=
    h L hL8 hLp N R j hV st H g μ D K hD hK A hA v w k hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk
  have hV' := hV
  obtain ⟨-, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hZn : 0 < ‖st.Z‖ := norm_pos_iff.2 hZ
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hz
  -- inactive clamps
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hyc : ‖st.y / st.Z‖ ≤ R.ρ := by linarith
  have hA' := stA_eq hZ hzy
  have hY' := stYc_eq hZ hyc
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * η := by rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  have h1ζ : 7 / 8 ≤ ‖1 + stZeta R st‖ := by linarith [norm_one_add_ge (ζ := stZeta R st)]
  have hZ'n : ‖stZ' R st‖ = ‖st.Z‖ * ‖1 + stZeta R st‖ := norm_stZ'
  have hZ'p : 0 < ‖stZ' R st‖ := by rw [hZ'n]; positivity
  have hrat : ‖st.Z‖ / ‖stZ' R st‖ ≤ 8 / 7 := by
    rw [hZ'n, div_le_iff₀ (by positivity)]; nlinarith
  -- the covariance entries
  obtain ⟨hC0, -, -, hCsym0⟩ := H.cov hV
  have hC : GoodCov2 j (fscale (stZ' R st) * R.ℓ / 4) (stCov R j st) := hC0
  have hδ2 : ∀ x e, stCov R j st x (x + dirVec e) = c₀ + δ := fun x e => by
    rw [show stCov R j st x (x + dirVec e) = stCov R j st (x + dirVec e) x from hCsym0 _ _]
    exact hδ x e
  obtain ⟨hc0b, hδb⟩ := cov_c0_delta_le hC hc₀ hδ hδ2
  have hℓC2 : (fscale (stZ' R st) * R.ℓ / 4) ^ 2 = R.ℓ ^ 2 / (16 * ‖stZ' R st‖) := by
    rw [div_pow, mul_pow, fscale_sq]; field_simp; ring
  rw [hℓC2] at hc0b hδb
  -- the components
  set gr := stGr R j st g μ with hgr
  set Z' := stZ' R st with hZ'def
  set κ := stCv R j st g μ D K with hκdef
  have ez : κ 0 = (st.z + stYc R st - stA R st - gr * Z' ^ 2 * c₀) -
      (κQ.z - κQ.g * c₀) - κL.z := congrArg Coup.z hrep
  have ey : κ 1 = (st.y - stYc R st - gr * Z' ^ 2 * δ) - (κQ.y - κQ.g * δ) - κL.y :=
    congrArg Coup.y hrep
  rw [hA', hY'] at ez
  rw [hY'] at ey
  have ez' : κ 0 = -(gr * Z' ^ 2 * c₀) - κQ.z + κQ.g * c₀ - κL.z := by rw [ez]; ring
  have ey' : κ 1 = -(gr * Z' ^ 2 * δ) - κQ.y + κQ.g * δ - κL.y := by rw [ey]; ring
  -- real abbreviations
  set a := ‖st.Z‖ with ha
  set a' := ‖Z'‖ with ha'
  have ha'p : 0 < a' := hZ'p
  have hr : a / a' ≤ 8 / 7 := hrat
  have hr0 : 0 ≤ a / a' := by positivity
  have hr2 : (a / a') ^ 2 ≤ 64 / 49 := by nlinarith
  have hℓ2 : 0 < R.ℓ ^ 2 := by positivity
  have hs2 : (fscale st.Z * R.ℓ) ^ 2 = R.ℓ ^ 2 / a := by rw [mul_pow, fscale_sq, ← ha]; ring
  have hs4 : (fscale st.Z * R.ℓ) ^ 4 = (R.ℓ ^ 2 / a) ^ 2 := by rw [← hs2]; ring
  have hs'2 : (fscale Z' * R.ℓ) ^ 2 = R.ℓ ^ 2 / a' := by rw [mul_pow, fscale_sq, ← ha']; ring
  rw [hs2] at q1 q2 q3
  rw [hs4] at q4
  rw [hs'2] at l1 l2 l3
  have hRQ : 0 ≤ RQ := by positivity
  have hRL : 0 ≤ RL := by
    have := BH.sig_nonneg (L := L) (d := 2) (by norm_num) v w hw0; positivity
  have hgr0 : 0 ≤ ‖gr‖ := norm_nonneg _
  have hp : 0 ≤ Cq * RQ / R.ℓ ^ 2 := by positivity
  have hCL : 0 ≤ Cq * RL / R.ℓ ^ 2 := by positivity
  -- generic bound for the gradient components
  have grad : ∀ (u : ℂ) (κz κg κl : ℂ) (e : ℂ), u = -(gr * Z' ^ 2 * e) - κz + κg * e - κl →
      ‖κz‖ ≤ Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ → ‖κg‖ ≤ Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ →
      ‖e‖ ≤ R.ℓ ^ 2 / (16 * a') → ‖κl‖ ≤ Cq * (R.ℓ ^ 2 / a')⁻¹ * RL →
      ‖u / Z'‖ ≤ Ez := by
    intro u κz κg κl e hu hz hg he hl
    have he0 : 0 ≤ ‖e‖ := norm_nonneg _
    rw [hu, norm_div]
    have t1 : ‖gr * Z' ^ 2 * e‖ ≤ ‖gr‖ * a' ^ 2 * (R.ℓ ^ 2 / (16 * a')) := by
      rw [norm_mul, norm_mul, norm_pow]; gcongr
    have t2 : ‖κg * e‖ ≤ Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) := by
      rw [norm_mul]; gcongr
    have hnum : ‖-(gr * Z' ^ 2 * e) - κz + κg * e - κl‖ ≤
        ‖gr‖ * a' ^ 2 * (R.ℓ ^ 2 / (16 * a')) + Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ +
          Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) +
          Cq * (R.ℓ ^ 2 / a')⁻¹ * RL := by
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add (by rw [norm_neg]; exact t1) hz)) t2)) hl
    have ha0 : 0 < a := hZn
    have eq1 : (‖gr‖ * a' ^ 2 * (R.ℓ ^ 2 / (16 * a')) + Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ +
        Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) +
        Cq * (R.ℓ ^ 2 / a')⁻¹ * RL) / a' =
        R.ℓ ^ 2 / 16 * ‖gr‖ + Cq * RQ / R.ℓ ^ 2 * (a / a') +
        Cq * RQ / (16 * R.ℓ ^ 2) * (a / a') ^ 2 + Cq * RL / R.ℓ ^ 2 := by
      field_simp
    have e2 : Cq * RQ / R.ℓ ^ 2 * (a / a') ≤ Cq * RQ / R.ℓ ^ 2 * (8 / 7) := by gcongr
    have e3 : Cq * RQ / (16 * R.ℓ ^ 2) * (a / a') ^ 2 ≤
        Cq * RQ / (16 * R.ℓ ^ 2) * (64 / 49) := by gcongr
    have e4 : (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 =
        2 * (Cq * RQ / R.ℓ ^ 2) + Cq * RL / R.ℓ ^ 2 := by ring
    have e3' : Cq * RQ / (16 * R.ℓ ^ 2) * (64 / 49) = (Cq * RQ / R.ℓ ^ 2) * (4 / 49) := by ring
    calc ‖-(gr * Z' ^ 2 * e) - κz + κg * e - κl‖ / a'
        ≤ (‖gr‖ * a' ^ 2 * (R.ℓ ^ 2 / (16 * a')) + Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ +
          Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) +
          Cq * (R.ℓ ^ 2 / a')⁻¹ * RL) / a' := div_le_div_of_nonneg_right hnum ha'p.le
      _ = _ := eq1
      _ ≤ Ez := by simp only [Ez]; linarith
  have hδb' : ‖δ‖ ≤ R.ℓ ^ 2 / (16 * a') := by
    refine hδb.trans (div_le_self (by positivity) ?_)
    have h1 : (1 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2 :=
      one_le_pow₀ (one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)))
    linarith
  have hz0 := grad (κ 0) κQ.z κQ.g κL.z c₀ ez' q1 q4 hc0b l1
  have hy0 := grad (κ 1) κQ.y κQ.g κL.y δ ey' q2 q4 hδb' l2
  refine ⟨hz0, hy0, ?_⟩
  -- the relevant coupling
  set ζ := stZeta R st with hζdef
  set ζ2 := stZeta2 R j st g μ D K with hζ2def
  have hZ'e : Z' = st.Z * (1 + ζ) := rfl
  have h1ζ0 : (1 + ζ) ≠ 0 := one_add_ne_zero (by linarith)
  have hZ'0 : Z' ≠ 0 := by rw [hZ'e]; exact mul_ne_zero hZ h1ζ0
  have hζ2ρ : ‖ζ2‖ ≤ 1 / 8 := (absorb_le R hρ0 _ _).trans hρ8
  have hEz0 : 0 ≤ Ez := (norm_nonneg _).trans hz0
  have hζ2E : ‖ζ2‖ ≤ 2 * Ez := by
    refine (norm_clampDisk_le_self hρ0 _).trans ?_
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have h1ζ2 : 7 / 8 ≤ ‖1 + ζ2‖ := by linarith [norm_one_add_ge (ζ := ζ2)]
  have h1ζ20 : (1 + ζ2) ≠ 0 := one_add_ne_zero (by linarith)
  have hZ2e : stZ2 R j st g μ D K = Z' * (1 + ζ2) := rfl
  set Z2 := stZ2 R j st g μ D K with hZ2def
  have hZ2n : ‖Z2‖ = a' * ‖1 + ζ2‖ := by rw [hZ2e, norm_mul]
  have hZ2p : 7 / 8 * a' ≤ ‖Z2‖ := by rw [hZ2n]; nlinarith
  have hZ2pos : 0 < ‖Z2‖ := by linarith
  have hdiv : ∀ (X : ℂ) (B : ℝ), ‖X‖ ≤ B * (7 / 8 * a') → ‖X / Z2‖ ≤ B := by
    intro X B hX
    rw [norm_div]
    calc ‖X‖ / ‖Z2‖ ≤ ‖X‖ / (7 / 8 * a') :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hZ2p
      _ ≤ B := by rw [div_le_iff₀ (by positivity)]; exact hX
  set ν' := (rawStep R j st g μ D K).nu
  have en : κ 2 = (stNu R j st μ - stA R st * R.msq + 2 * (2 : ℕ) * (gr * Z' ^ 2) * δ) -
      (κQ.nu + 2 * (2 : ℕ) * κQ.g * δ) - κL.nu := congrArg Coup.nu hrep
  rw [hA'] at en
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  have hPj : (L : ℂ) ^ (2 * (j + 1)) = (L : ℂ) ^ 2 * (L : ℂ) ^ (2 * j) := by ring
  have hPj0 : (L : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ hL0
  have hzy' : st.z + st.y = ζ * st.Z := by rw [hζ, div_mul_cancel₀ _ hZ]
  set P := (L : ℂ) ^ (2 * (j + 1)) with hP
  -- the decomposition
  have key : ν' - (L : ℂ) ^ 2 * μ =
      -((L : ℂ) ^ 2 * μ * (ζ2 / (1 + ζ2))) -
        (L : ℂ) ^ 2 * (ζ * st.Z * R.msq * (L : ℂ) ^ (2 * j)) / Z2 +
        4 * gr * Z' ^ 2 * δ * P / Z2 - κQ.nu * P / Z2 - 4 * κQ.g * δ * P / Z2 -
        κL.nu * P / Z2 := by
    have hν : ν' = κ 2 * P / Z2 := rfl
    have hNu : stNu R j st μ = (μ : ℂ) * (st.Z * (1 + ζ)) / (L : ℂ) ^ (2 * j) := rfl
    rw [hν, en, hzy', hZ2e, hPj, hNu, hZ'e]
    push_cast
    field_simp
    ring
  rw [key]
  -- the norms
  have hLr : ‖(L : ℂ)‖ = (L : ℝ) := Complex.norm_natCast L
  have nP : ‖P‖ = ((L : ℝ) ^ (j + 1)) ^ 2 := by
    rw [hP, norm_pow, hLr, ← pow_mul, mul_comm]
  have nP2 : ‖(L : ℂ) ^ (2 * j)‖ = ((L : ℝ) ^ j) ^ 2 := by rw [norm_pow, hLr, ← pow_mul, mul_comm]
  have hh1 : (0 : ℝ) < ((L : ℝ) ^ (j + 1)) ^ 2 := by positivity
  have hhj : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by ring
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ 2 :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hδP : ‖δ‖ * ((L : ℝ) ^ (j + 1)) ^ 2 ≤ R.ℓ ^ 2 / (16 * a') / 2 := by
    have := hδb; rw [le_div_iff₀ (by positivity)] at this; linarith
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  have T1 : ‖(L : ℂ) ^ 2 * μ * (ζ2 / (1 + ζ2))‖ ≤ 16 / 7 * (L : ℝ) ^ 2 * Ez * |μ| := by
    rw [norm_mul, norm_mul, norm_pow, hLr, Complex.norm_real, Real.norm_eq_abs, norm_div]
    have : ‖ζ2‖ / ‖1 + ζ2‖ ≤ 16 / 7 * Ez := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc (L : ℝ) ^ 2 * |μ| * (‖ζ2‖ / ‖1 + ζ2‖) ≤ (L : ℝ) ^ 2 * |μ| * (16 / 7 * Ez) := by gcongr
      _ = _ := by ring
  have T2 : ‖(L : ℂ) ^ 2 * (ζ * st.Z * R.msq * (L : ℂ) ^ (2 * j)) / Z2‖ ≤ 3 * (L : ℝ) ^ 2 * η := by
    refine hdiv _ _ ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, hLr, Complex.norm_real,
      Real.norm_eq_abs, nP2]
    have hm' : ‖ζ‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η := by
      calc ‖ζ‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2) ≤ 2 * η * 1 := by gcongr
        _ = _ := mul_one _
    have haa : a ≤ 8 / 7 * a' := by rw [div_le_iff₀ ha'p] at hr; linarith
    calc (L : ℝ) ^ 2 * (‖ζ‖ * a * |R.msq| * ((L : ℝ) ^ j) ^ 2)
        = (L : ℝ) ^ 2 * a * (‖ζ‖ * (|R.msq| * ((L : ℝ) ^ j) ^ 2)) := by ring
      _ ≤ (L : ℝ) ^ 2 * (8 / 7 * a') * (2 * η) := by gcongr
      _ ≤ 3 * (L : ℝ) ^ 2 * η * (7 / 8 * a') := by
          have : 0 ≤ (L : ℝ) ^ 2 * (a' * η) := by positivity
          nlinarith
  have T3 : ‖4 * gr * Z' ^ 2 * δ * P / Z2‖ ≤ R.ℓ ^ 2 / 7 * ‖gr‖ := by
    refine hdiv _ _ ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, nP, h4]
    calc 4 * ‖gr‖ * a' ^ 2 * ‖δ‖ * ((L : ℝ) ^ (j + 1)) ^ 2
        = 4 * ‖gr‖ * a' ^ 2 * (‖δ‖ * ((L : ℝ) ^ (j + 1)) ^ 2) := by ring
      _ ≤ 4 * ‖gr‖ * a' ^ 2 * (R.ℓ ^ 2 / (16 * a') / 2) := by gcongr
      _ = R.ℓ ^ 2 / 7 * ‖gr‖ * (7 / 8 * a') := by field_simp; ring
  have T4 : ‖κQ.nu * P / Z2‖ ≤ 64 / 49 * (L : ℝ) ^ 2 * (Cq * RQ / R.ℓ ^ 2) := by
    refine hdiv _ _ ?_
    rw [norm_mul, nP, hhj]
    have hq : ‖κQ.nu‖ * ((L : ℝ) ^ j) ^ 2 ≤ Cq * RQ / R.ℓ ^ 2 * a := by
      have := q3; rw [le_div_iff₀ (by positivity)] at this
      refine this.trans (le_of_eq ?_); simp only [RQ]; field_simp
    have haa : a ≤ 8 / 7 * a' := by rw [div_le_iff₀ ha'p] at hr; linarith
    calc ‖κQ.nu‖ * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) = (L : ℝ) ^ 2 * (‖κQ.nu‖ * ((L : ℝ) ^ j) ^ 2) := by ring
      _ ≤ (L : ℝ) ^ 2 * (Cq * RQ / R.ℓ ^ 2 * a) := by gcongr
      _ ≤ (L : ℝ) ^ 2 * (Cq * RQ / R.ℓ ^ 2 * (8 / 7 * a')) := by gcongr
      _ = _ := by ring
  have T5 : ‖4 * κQ.g * δ * P / Z2‖ ≤ 1 / 4 * (Cq * RQ / R.ℓ ^ 2) := by
    refine hdiv _ _ ?_
    rw [norm_mul, norm_mul, norm_mul, nP, h4]
    calc 4 * ‖κQ.g‖ * ‖δ‖ * ((L : ℝ) ^ (j + 1)) ^ 2 = 4 * ‖κQ.g‖ * (‖δ‖ * ((L : ℝ) ^ (j + 1)) ^ 2) := by ring
      _ ≤ 4 * (Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ) * (R.ℓ ^ 2 / (16 * a') / 2) := by gcongr
      _ = Cq * RQ / R.ℓ ^ 2 / 7 * (a / a') ^ 2 * (7 / 8 * a') := by field_simp; ring
      _ ≤ Cq * RQ / R.ℓ ^ 2 / 7 * (64 / 49) * (7 / 8 * a') := by gcongr
      _ ≤ 1 / 4 * (Cq * RQ / R.ℓ ^ 2) * (7 / 8 * a') := by
          have : 0 ≤ Cq * RQ / R.ℓ ^ 2 * a' := by positivity
          nlinarith
  have T6 : ‖κL.nu * P / Z2‖ ≤ 8 / 7 * (Cq * RL / R.ℓ ^ 2) := by
    refine hdiv _ _ ?_
    rw [norm_mul, nP]
    have := l3; rw [le_div_iff₀ hh1] at this
    refine this.trans (le_of_eq ?_); simp only [RL]; field_simp
  have e6 : 2 * ((L : ℝ) ^ 2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 =
      2 * (L : ℝ) ^ 2 * (Cq * RQ / R.ℓ ^ 2) + 2 * (Cq * RL / R.ℓ ^ 2) := by ring
  rw [e6]
  have hX : Cq * RQ / R.ℓ ^ 2 ≤ (L : ℝ) ^ 2 * (Cq * RQ / R.ℓ ^ 2) := le_mul_of_one_le_left hp hL1
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add ((norm_neg _).le.trans T1) T2)) T3)) T4)) T5)) T6).trans ?_
  have : 0 ≤ (L : ℝ) ^ 2 * (Cq * RQ / R.ℓ ^ 2) := by positivity
  nlinarith

end

end Step2
