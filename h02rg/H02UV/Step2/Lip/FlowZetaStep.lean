import Step2.Flow.FlowStep

/-!
# The sharp size of the dressed gradient coupling

`step_zeta_sharp`: in one raw step, the absorbed gradient coupling of the output,
`(z' + y')/Z_{j+1}`, is `-ǧ_r Z_{j+1} C_j(e, 0)` up to the remainders `κ_Q`, `κ_L` of
`rawStep_coup`:

  `‖(z' + y')/Z_{j+1}‖ ≤ |ǧ_r| ‖Z_{j+1} C_j(e, 0)‖ + 2 (2 C_q R_Q + C_q R_L)/ℓ²`.

`step_coup_norm` bounds `‖Z_{j+1} C_j(x, x)‖` by the field scale `ℓ²/16`; here the covariance entry
is kept, so that the explicit bound `Zcov_hist` (`O(L²)`, independent of `ℓ`) can be used.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 4000000 in
theorem step_zeta_sharp : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧ ∃ cS : ℝ, 1 ≤ cS ∧
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
      ‖(stCv R j st g μ D K 0 + stCv R j st g μ D K 1) / stZ' R st‖ ≤
        ‖stGr R j st g μ‖ * ‖stZ' R st * stCov R j st (dirVec (Sum.inl 0)) 0‖ +
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
  have hlead : ‖-(gr * Z' ^ 2 * (c₀ + δ)) / Z'‖ = ‖gr‖ * ‖Z' * stCov R j st (dirVec (Sum.inl 0)) 0‖ := by
    rw [hC1, show -(gr * Z' ^ 2 * (c₀ + δ)) / Z' = -(gr * (Z' * (c₀ + δ))) by field_simp]
    rw [norm_neg, norm_mul]
  rw [hsum, add_div, add_div]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_add_le _ _) hy0).trans ?_
  rw [hlead]
  linarith only [hz0]

end

end Step2
