import PtCorr2.Obs.WObsStep
import Obs2.Flow.VObs2

/-!
# The `V^{obs}` step of the observable flow at the raw level (Case (1), `σ_a`)

**`beta_raw_step`**: one step of `obsStep` for the `ℓ¹` coupling `β^{abs}_j = ∑_B |m₁(V_j(B)_a)|`
(`Obs2.beta_step`), in the normalisation of `kobs_raw_step` (weights `Obs2.wA = (1,0,0)`, causal field
scales `s`, `s'`, bulk radius `r`): if `V_j(B)_a ∈ ℂψ̄_a`, `‖𝒲^{obs}_j(B)‖ ≤ m_W` and
`‖K^{obs}_j(X)‖ ≤ k` on small sets, then

  `β^{abs}_{j+1} ≤ β^{abs}_j + c C_m s^{-1} 8k + C_m s'^{-1}(2c_{near}Q₁² r s β^{abs}_j + c' Q₁ m_W)`.

The activity of the step is the flattened `K♭` (`oTo_fullK_le`, factor `8`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

theorem fullV_a {c : Obs.Case} (R : RGPar 2 L N) (j : ℕ) (st : RawSt 2 L N) (g μ : ℝ)
    (o : ObsSt c L N) (b : Fin 2 → ℕ) :
    (fullV R j st g μ o b : SA c (Lam 2 L N)).a = (o.V b : SA c (Lam 2 L N)).a := by
  show 0 + (o.V b : SA c (Lam 2 L N)).a = _; rw [zero_add]

set_option maxHeartbeats 1000000 in
/-- **The `ℓ¹` coupling step at the raw level** (Case (1)). -/
theorem beta_raw_step : ∃ (Cm : ℝ) (cs cn : ℕ) (L₀ : ℕ), 0 ≤ Cm ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (P : ObsPts 2 L N) (o : ObsSt .one L N), o.IsObs → ObsLocInv P j o → ObsSymInv j o →
      (∀ b, (o.V b : SA .one (Lam 2 L N)).a ∈ (ℂ ∙ psibar P.a)) →
    ∀ wl dd r mV mW k : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ 1 → 0 ≤ mV → 0 ≤ mW → 0 ≤ k →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo Obs2.wA j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      (∀ X, IsSmall j X → oTo Obs2.wA j (fscale st.Z * R.ℓ) (o.K X) ≤ ENNReal.ofReal k) →
      ∑ c' ∈ blockIdx (L := L) (N := N) (j + 1),
          ‖mass1L (-1) ((obsStep R P j st g μ D K o).V c' : SA .one (Lam 2 L N)).a‖ ≤
        ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1L (-1) (o.V b : SA .one (Lam 2 L N)).a‖ +
          cs * Cm * (fscale st.Z * R.ℓ)⁻¹ * (8 * k) +
          Cm * (fscale (stZ' R st) * R.ℓ)⁻¹ * (2 * Step2.cNear 2 L * Step2.Q1 2 ^ 2 * r *
            (fscale st.Z * R.ℓ) *
            ∑ b ∈ blockIdx (L := L) (N := N) j, ‖mass1L (-1) (o.V b : SA .one (Lam 2 L N)).a‖ +
            cn * Step2.Q1 2 * mW) := by
  classical
  obtain ⟨Cm, cs, cn, hCm, hB⟩ := beta_step 2 one_le_two
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound 2 one_le_two
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_obs_bound 2
  obtain ⟨cN, hcN⟩ := card_small_containing 2
  refine ⟨Cm, cs, cn, max (2 ^ (2 + 3) + 8 * 2 + 1) ⌈pauliL0 2⌉₊, hCm, fun L _ hL => ?_⟩
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hL)
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hL)
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs P o ho hlo hsym hform
    wl dd r mV mW k hwl0 hdd0 hr0 hr1 hmV hmW hk0 hWl hDd hvr hwr hVo hWo hKo
  have hV' := hV
  obtain ⟨hj1, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hjN : j < N := by omega
  have hzy : ‖(st.z + st.y) / st.Z‖ ≤ R.ρ := by
    rw [add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ : stZeta R st = (st.z + st.y) / st.Z := by
    unfold stZeta absorbZeta; rw [clampDisk_of_le hzy]
  have hζη : ‖stZeta R st‖ ≤ 2 * ηz := by
    rw [hζ, add_div]; exact (norm_add_le _ _).trans (by linarith)
  have hζ8 : ‖stZeta R st‖ ≤ 1 / 8 := by linarith
  set s' := fscale (stZ' R st)
  have hs := fscale_pos hZ
  have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
  have hs' : 0 < s' := fscale_pos hZ'
  have hsc := scale_ok hZ hζ8 hℓ
  have hsc' : s' * R.ℓ + s' * R.ℓ / 4 ≤ 3 / 2 * (fscale st.Z * R.ℓ) := hsc
  have hsℓ : 0 < fscale st.Z * R.ℓ := mul_pos hs hℓ
  have hsum : s' * R.ℓ + s' * R.ℓ / 4 ≤ 2 * (fscale st.Z * R.ℓ) := by linarith
  obtain ⟨hC0, -, -, -⟩ := H.covL hV
  have hC : GoodCov2 j (s' * R.ℓ / 4) (stCov R j st) := hC0
  obtain ⟨hVv, hΔ⟩ := rg_inputs R j hV st H g μ hm hg0 ηz hz hy hηρ
  have hcount : ∀ b ∈ blockIdx (d := 2) (L := L) (N := N) j,
      (((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS := fun b hb => by
    have h1 : ((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ cN := by convert hcN L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have HL := olocS_full R P g μ hV H hD hK hlo
  have hw0 : Obs2.wA.ab = 0 := Obs2.wA_ab
  -- the activity on small sets
  have hM : (0 : ℝ) ≤ cM := Nat.cast_nonneg _
  have hδ0 : 0 ≤ 8 * cM * R.ℓ ^ 2 * ηz := by
    have := (norm_nonneg _).trans hz; positivity
  have hKk : ∀ X, IsSmall j X →
      oTo Obs2.wA j (fscale st.Z * R.ℓ) (fullK R j st K o X) ≤ ENNReal.ofReal (8 * k) := by
    intro X hX
    have h := oTo_fullK_le R j st K o Obs2.wA hw0 hsℓ (A := 1) one_pos hδ0 (by linarith) hΔ X
    have e : nb j X - 2 ^ 2 = 0 := Nat.sub_eq_zero_of_le hX.2.2
    rw [e, pow_zero, pow_zero, ENNReal.ofReal_one, one_mul, one_mul] at h
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num)]
    exact mul_le_mul_right (hKo X hX) _
  have HO : BHO P j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
      (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) Obs2.wA r mV mW (8 * k) Clo cS :=
    { hd := one_le_two, hLp := hLp, hL8 := hL8, hjN := hj1, hℓ := hsℓ, hℓ' := mul_pos hs' hℓ,
      hℓC := by positivity, hsum := hsum, hC := hC, hw := Obs2.wA_sub, hw0 := hw0
      hVl := fun b => cmpIn_of_osub (HL.hV b), hWl := fun b => cmpIn_of_osub (HL.hW b)
      hKl := fun X hX => cmpIn_of_osub (HL.hK X ⟨hX.1, hX.2.1⟩), hr := hr0, hmV := hmV,
      hmW := hmW, hk := by positivity
      hVr := fun b hb => by
        show Tj 2 (L : ℝ) j (fscale st.Z * R.ℓ)
          ((bulkF (fullV R j st g μ o) b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ _
        rw [bulkF_fullV R j st g μ ho]
        exact (Tj_le_Fnorm _ hb).trans (hVv.trans (ENNReal.ofReal_le_ofReal hvr))
      hVm := fun b hb => (oTo_emb_add_le Obs2.wA j _ _ _).trans (hVo b hb)
      hWm := fun b hb => (oTo_emb_add_le Obs2.wA j _ _ _).trans (hWo b hb)
      hKk := hKk, hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hF =>
        hlocO L hL8 N .one P Obs2.wA hw0 k' hk ℓ₀ hℓ₀ X Y hX hYX F hF
      hlocl := bho_hlocl one_le_two P j, hcS := hcS1, hcount := hcount }
  have key := hB L N P j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
    (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) r mV mW (8 * k) Clo cS HO
    (fun b => by rw [fullV_a]; exact hform b)
    (fun b ha => osub_a_zero (HL.hW b) ha)
    (fun X hX ha => osub_a_zero (HL.hK X ⟨hX.1, hX.2.1⟩) ha)
  have e1 : ∀ c', ((obsStep R P j st g μ D K o).V c' : SA .one (Lam 2 L N)).a =
      (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (fullK R j st K o) c' :
        SA .one (Lam 2 L N)).a := fun c' => by
    show (πobs (Vnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o)
      (fullK R j st K o) c') : SA .one (Lam 2 L N)).a = _
    rw [coe_πobs, piobs_apply]
  have e2 : ∀ b, (fullV R j st g μ o b : SA .one (Lam 2 L N)).a = (o.V b : SA .one (Lam 2 L N)).a :=
    fun b => fullV_a R j st g μ o b
  simp only [e1]
  simp only [e2] at key
  exact key

end

end PtCorr2
