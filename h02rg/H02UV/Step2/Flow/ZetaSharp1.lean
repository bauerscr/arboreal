import Step2.Lip.FlowZetaApriori

/-!
# The sharp gradient coupling: the difference form (`h02uv-outline.tex`, `e:zflow`)

`step_zeta_sharp2`: in one raw step, the absorbed gradient coupling of the output is
`-ǧ_r Z_{j+1} C_j(e, 0)` up to the remainders of `rawStep_coup`:

  `‖(z' + y')/Z_{j+1} + ǧ_r Z_{j+1} C_j(e, 0)‖ ≤ 2 (2 C_q R_Q + C_q R_L)/ℓ²`

(a copy of `step_zeta_sharp`, which only bounded the norm). `ZetaStepBound2`,
`zeta_step_bounds2`: the same with the inputs of `StepBounds` (copies of `ZetaStepBound`,
`zeta_step_bounds`); `ZetaStepBound2.toZSB`: the difference form implies the old norm form.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
theorem step_zeta_sharp2 : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
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
      ‖(stCv R j st g μ D K 0 + stCv R j st g μ D K 1) / stZ' R st +
          stGr R j st g μ * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0)‖ ≤
        2 * ((2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := rawStep_coup
  refine ⟨Cq, hCq, Cl, hCl, cS, hcS, ?_⟩
  intro L _ hL8 hLp N R j hV st H g μ D K hD hK A hA v w k hv0 hw0 hk0 hv1 hw1 hk1 hVv hWw hKk
    η hz hy hη hm RQ RL
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
  -- the remainder of a gradient component
  have rest : ∀ (u : ℂ) (κz κg κl : ℂ) (e : ℂ), u = -κz + κg * e - κl →
      ‖κz‖ ≤ Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ → ‖κg‖ ≤ Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ →
      ‖e‖ ≤ R.ℓ ^ 2 / (16 * a') → ‖κl‖ ≤ Cq * (R.ℓ ^ 2 / a')⁻¹ * RL →
      ‖u / Z'‖ ≤ (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 := by
    intro u κz κg κl e hu hz hg he hl
    have he0 : 0 ≤ ‖e‖ := norm_nonneg _
    rw [hu, norm_div]
    have t2 : ‖κg * e‖ ≤ Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) := by
      rw [norm_mul]; gcongr
    have hnum : ‖-κz + κg * e - κl‖ ≤
        Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ +
          Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) +
          Cq * (R.ℓ ^ 2 / a')⁻¹ * RL := by
      refine (norm_sub_le _ _).trans ?_
      refine add_le_add ((norm_add_le _ _).trans (add_le_add (by rw [norm_neg]; exact hz) t2)) hl
    have ha0 : 0 < a := hZn
    have eq1 : (Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ +
        Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) +
        Cq * (R.ℓ ^ 2 / a')⁻¹ * RL) / a' =
        Cq * RQ / R.ℓ ^ 2 * (a / a') +
        Cq * RQ / (16 * R.ℓ ^ 2) * (a / a') ^ 2 + Cq * RL / R.ℓ ^ 2 := by
      field_simp
    have e2 : Cq * RQ / R.ℓ ^ 2 * (a / a') ≤ Cq * RQ / R.ℓ ^ 2 * (8 / 7) := by gcongr
    have e3 : Cq * RQ / (16 * R.ℓ ^ 2) * (a / a') ^ 2 ≤
        Cq * RQ / (16 * R.ℓ ^ 2) * (64 / 49) := by gcongr
    have e4 : (2 * Cq * RQ + Cq * RL) / R.ℓ ^ 2 =
        2 * (Cq * RQ / R.ℓ ^ 2) + Cq * RL / R.ℓ ^ 2 := by ring
    have e3' : Cq * RQ / (16 * R.ℓ ^ 2) * (64 / 49) = (Cq * RQ / R.ℓ ^ 2) * (4 / 49) := by ring
    calc ‖-κz + κg * e - κl‖ / a'
        ≤ (Cq * (R.ℓ ^ 2 / a)⁻¹ * RQ +
          Cq * ((R.ℓ ^ 2 / a) ^ 2)⁻¹ * RQ * (R.ℓ ^ 2 / (16 * a')) +
          Cq * (R.ℓ ^ 2 / a')⁻¹ * RL) / a' := div_le_div_of_nonneg_right hnum ha'p.le
      _ = _ := eq1
      _ ≤ _ := by linarith
  have hδb' : ‖δ‖ ≤ R.ℓ ^ 2 / (16 * a') := by
    refine hδb.trans (div_le_self (by positivity) ?_)
    have h1 : (1 : ℝ) ≤ ((L : ℝ) ^ (j + 1)) ^ 2 :=
      one_le_pow₀ (one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)))
    linarith
  have hz0 := rest (-κQ.z + κQ.g * c₀ - κL.z) κQ.z κQ.g κL.z c₀ rfl q1 q4 hc0b l1
  have hy0 := rest (-κQ.y + κQ.g * δ - κL.y) κQ.y κQ.g κL.y δ rfl q2 q4 hδb' l2
  have hC1 : stCov R j st (dirVec (Sum.inl 0)) 0 = c₀ + δ := by
    have := hδ 0 (Sum.inl 0); rwa [zero_add] at this
  have hsum : κ 0 + κ 1 = -(gr * Z' ^ 2 * (c₀ + δ)) + (-κQ.z + κQ.g * c₀ - κL.z) +
      (-κQ.y + κQ.g * δ - κL.y) := by rw [ez', ey']; ring
  have hZ'0 : Z' ≠ 0 := norm_pos_iff.1 ha'p
  have e5 : (κ 0 + κ 1) / Z' + gr * (Z' * stCov R j st (dirVec (Sum.inl 0)) 0) =
      (-κQ.z + κQ.g * c₀ - κL.z) / Z' + (-κQ.y + κQ.g * δ - κL.y) / Z' := by
    rw [hsum, hC1]; field_simp; ring
  rw [e5]
  refine (norm_add_le _ _).trans ?_
  linarith only [hz0, hy0]


/-- **The sharp one-step bound on the absorbed gradient coupling, difference form**, with the inputs of
`StepBounds`. -/
def ZetaStepBound2 (L : ℕ) [NeZero L] (A Cq Cl cS : ℝ) : Prop :=
  ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
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
      ‖(stCv R j st g μ D K 0 + stCv R j st g μ D K 1) / stZ' R st +
          stGr R j st g μ * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0)‖ ≤
          2 * ((2 * Cq * (cS * (Cl * (8 * k))) + Cq * (Cl * ((L : ℝ) ^ 2 *
            BH.sig 2 L (cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g) (wl + dd)))) /
              R.ℓ ^ 2)

set_option maxHeartbeats 4000000 in
theorem zeta_step_bounds2 : ∃ Cq Cl cS : ℝ, 0 ≤ Cq ∧ 0 ≤ Cl ∧ 1 ≤ cS ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L → ∀ A : ℝ, 2 ≤ A →
      ZetaStepBound2 L A Cq Cl cS := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, hcoup⟩ := step_zeta_sharp2
  refine ⟨Cq, Cl, cS, hCq, hCl, hcS, fun L _ hL8 hLp A hA => ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 η hz hy hη hηs wl dd k r hwl0 hdd0 hk0 hWl hDd hKk
    hvr hwr hr1 hk8
  set v := cM * R.ℓ ^ 2 * (2 * |μ| + 2 * η) + 8 * R.ℓ ^ 4 * g with hvdef
  set s' := fscale (stZ' R st) with hs'd
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
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLL : (L : ℝ) ^ 2 / (L : ℝ) ^ 3 = (L : ℝ)⁻¹ := by field_simp
  -- the couplings
  have hc := hcoup L hL8 hLp N R j hV st H g μ D K hD hK (A / 2) (by linarith) v (wl + dd) (8 * k)
    hv0 (by positivity) (by positivity) hv1 hw1 hk8 hVv hw hKflat η hz hy hη hm
  exact hc


/-- The difference form implies the norm form `ZetaStepBound`. -/
theorem ZetaStepBound2.toZSB {L : ℕ} [NeZero L] {A Cq Cl cS : ℝ}
    (h : ZetaStepBound2 L A Cq Cl cS) : ZetaStepBound L A Cq Cl cS := by
  intro N R j hV st H g μ D K hD hK hm hg0 η hz hy hη hηs wl dd k r hwl0 hdd0 hk0 hWl hDd hKk
    hvr hwr hr1 hk8
  have h1 := h N R j hV st H g μ D K hD hK hm hg0 η hz hy hη hηs wl dd k r hwl0 hdd0 hk0 hWl hDd
    hKk hvr hwr hr1 hk8
  set w := (stCv R j st g μ D K 0 + stCv R j st g μ D K 1) / stZ' R st
  set a := stGr R j st g μ * (stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0)
  have e : w = (w + a) - a := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have : ‖a‖ = ‖stGr R j st g μ‖ * ‖stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0‖ :=
    norm_mul _ _
  linarith only [h1, this]

end

end Step2
