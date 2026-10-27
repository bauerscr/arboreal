import PtCorr2.Obs.WObsStep
import PtCorr2.Pair.ObsHistAnch
import Obs2.Est.WObsAB
import Obs2.Est.BlockOAB5

/-!
# The `𝒲^{obs}` step on the `σ_aσ_b` sector at the raw level (`ab` copy of `PtCorr2.Obs.WObsStep`)

**`wobs_raw_stepAB`**: `PtCorr2.wobs_raw_step` for an anchored observable state
(`ObsAnchInv P j o`) and weights with `w.Sub`, conditional on the `ab` contraction after the
expectation `Obs2.EthSubLocAB 2`: if `‖V^{obs}_j(B)‖ ≤ m_V`, `‖𝒲^{obs}_j(B)‖ ≤ m_W`, then

  `‖𝒲^{obs}_{j+1}(B_+)‖_{T_{j+1}(s')} ≤ (K L^{-1} + C₁ r) m_W + C₁ r m_V`

for `r ≤ ε₁(L)`, `K` independent of `L`. From `Obs2.Wnext2O_obs_leAB` (`BHOAB` with `K = 0`).
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The `𝒲^{obs}` step at the raw level.** -/
theorem wobs_raw_stepAB (hE : EthSubLocAB 2) : ∃ (Kw : ℝ) (L₀ : ℕ), 0 ≤ Kw ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → ∃ C₁ ε₁ : ℝ, 0 ≤ C₁ ∧ 0 < ε₁ ∧
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ ε₁ → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ) ((obsStep R P j st g μ D K o).W c') ≤
          ENNReal.ofReal ((Kw / L + C₁ * r) * mW + C₁ * r * mV) := by
  classical
  obtain ⟨Kc, hKc, L₁, hW⟩ := Wnext2O_obs_leAB 2 hE
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound 2 one_le_two
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_ab_bound 2 one_le_two
  obtain ⟨cN, hcN⟩ := card_small_containing 2
  refine ⟨Kc, max L₁ (max (2 ^ (2 + 3) + 8 * 2 + 1) ⌈pauliL0 2⌉₊), hKc, fun L _ hL => ?_⟩
  have hL1 : L₁ ≤ L := (le_max_left _ _).trans hL
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans ((le_max_right _ _).trans hL))
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  set n : ℝ := (L : ℝ) ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  set cW : ℝ := cWblk 2 L Cl with hcW
  have hcW0 : 0 ≤ cW := by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (2 + 3) + 7) ^ 2)
    have := one_le_Q1 (d := 2) one_le_two
    simp only [hcW, cWblk, cSblk, cNear]; positivity
  set Q : ℝ := Q1 2 with hQ
  have hQ1 : 1 ≤ Q := one_le_Q1 one_le_two
  set cn : ℝ := cNear 2 L with hcn
  have hcn0 : 0 ≤ cn := Nat.cast_nonneg _
  set A1 : ℝ := n * (1 + Clo * n) * (2 * n * cW) with hA1
  have hA10 : 0 ≤ A1 := by positivity
  refine ⟨(1 + Clo) * (n * (cn * (2 * Q ^ 2))) + A1 * (2 * cn * Q ^ 2 + Q),
    min 1 (1 / (n * cW + 1)), by positivity, lt_min one_pos (by positivity), ?_⟩
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hwS o ho hlo hsym hanc
    wl dd r mV mW hwl0 hdd0 hr0 hrε hmV hmW hWl hDd hvr hwr hVo hWo c' hc'
  have hr1 : r ≤ 1 := hrε.trans (min_le_left _ _)
  have hrn : n * cW * r ≤ 1 := by
    have h1 : r ≤ 1 / (n * cW + 1) := hrε.trans (min_le_right _ _)
    have h2 : 0 < n * cW + 1 := by positivity
    rw [le_div_iff₀ h2] at h1
    nlinarith
  have hV' := hV
  obtain ⟨hj1, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ ηz := (norm_nonneg _).trans hz
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
  have hCℓ : s' * R.ℓ / 4 ≤ fscale st.Z * R.ℓ := by
    have : 0 < s' * R.ℓ := mul_pos hs' hℓ
    linarith
  obtain ⟨hC0, -, -, -⟩ := H.covL hV
  have hC : GoodCov2 j (s' * R.ℓ / 4) (stCov R j st) := hC0
  obtain ⟨hVv, -⟩ := rg_inputs R j hV st H g μ hm hg0 ηz hz hy hηρ
  have hVf_mem : stVf R j st g μ ∈ BSub (L := L) (N := N) j := by
    rw [stVf_eq_kap]
    exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN (stKap R j st g μ).toVec
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hcount : ∀ b ∈ blockIdx (d := 2) (L := L) (N := N) j,
      (((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS := fun b hb => by
    have h1 : ((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ cN := by convert hcN L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  -- the bulk block hypotheses (with `K = 0`)
  have hK0 : InK2 j (0 : Act 2 L N) :=
    { loc := fun _ _ => zero_mem _, sym := fun _ _ => (isSym_iff_mem_SymS _).2 (zero_mem _) }
  have HB : Step2.BH j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
      (stVf R j st g μ) (st.Wl + D) 0 1 r Cl cS :=
    { hd := one_le_two, hLp := hLp, hL8 := hL8, hjN := hj1, hℓ := hsℓ, hℓ' := mul_pos hs' hℓ,
      hℓC := by positivity, hsum := hsum, hC := hC, hV := hVf_mem.1, hW := (add_mem H.hWl hD).1,
      hV0 := fun b => eps_VfamL j _ b, hK := hK0, hA := le_rfl, hr := hr0, hr1 := hr1
      hVr := fun b hb => (Tj_le_Fnorm _ hb).trans (hVv.trans (ENNReal.ofReal_le_ofReal hvr))
      hWr := fun b hb => (Tj_le_Fnorm _ hb).trans (hw.trans (ENNReal.ofReal_le_ofReal
        (hwr.trans hr2)))
      hKr := by rw [Knorm_zero]; exact zero_le
      hCl := hCl0
      hloc := fun k hk ℓ₀ hℓ₀ X Y hX hYX F hF => hloc L hL8 N k hk X Y hX hYX F hF ℓ₀ hℓ₀
      hcS := hcS1, hcount := hcount }
  -- the observable block hypotheses (with `K = 0`)
  have HL := olocS_full R P g μ hV H hD hK hlo
  have HS := osymS_full R g μ hV H hD hK hsym
  have hwsub : w.Sub := hwS
  have HA := oanchS_full R P g μ (st := st) (D := D) (K := K) hanc
  have HAb := HA.toAb
  have HO : BHOAB P j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
      (fullV R j st g μ o) (fullW st D o) (0 : OAct c 2 L N) w r mV mW 0 Clo cS :=
    { hd := one_le_two, hLp := hLp, hL8 := hL8, hjN := hj1, hℓ := hsℓ, hℓ' := mul_pos hs' hℓ,
      hℓC := by positivity, hsum := hsum, hC := hC, hw := hwsub, hVab := HAb.hV, hWab := HAb.hW, hKab := fun _ _ => zero_mem _
      hVl := fun b => cmpInA_of_osub (HL.hV b), hWl := fun b => cmpInA_of_osub (HL.hW b)
      hKl := fun _ _ => CmpInA.zero, hr := hr0, hmV := hmV, hmW := hmW, hk := le_rfl
      hVr := fun b hb => by
        show Tj 2 (L : ℝ) j (fscale st.Z * R.ℓ)
          ((bulkF (fullV R j st g μ o) b : EvR (Lam 2 L N)) : Alg 2 L N) ≤ _
        rw [bulkF_fullV R j st g μ ho]
        exact (Tj_le_Fnorm _ hb).trans (hVv.trans (ENNReal.ofReal_le_ofReal hvr))
      hVm := fun b hb => (oTo_emb_add_le w j _ _ _).trans (hVo b hb)
      hWm := fun b hb => (oTo_emb_add_le w j _ _ _).trans (hWo b hb)
      hKk := fun X _ => by
        show oTo w j (fscale st.Z * R.ℓ) (0 : OE c (Lam 2 L N)) ≤ _
        rw [oTo_zero']; exact zero_le
      hCl := hClo0
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hFab hF =>
        hlocO L hL8 N c P w k' hk ℓ₀ hℓ₀ X Y hX hYX F hFab hF.ab
      hlocl := bho_hloclAB one_le_two P j, hcS := hcS1, hcount := hcount }
  have hWe : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ)
        (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b : SA c (Lam 2 L N)).e ≤
        ENNReal.ofReal (cW * r) := fun b hb => by
    show Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ)
      ((bulk (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) : EvR (Lam 2 L N)) :
        Alg 2 L N) ≤ _
    rw [bulk_WpO, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho]
    exact HB.Wp_le hb
  have key := hW L hL1 N c P j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
    (fullV R j st g μ o) (fullW st D o) 0 w r mV mW 0 Clo cS (cW * r) HO hCℓ
    (mul_nonneg hcW0 hr0) (fun b => mem_symSub.1 (HS.hW b))
    HA.hW (fun b ha => ((HL.hW b).2.2.2.2.1 ha).2) (fun b hb => ((HL.hW b).2.2.2.2.2 hb).2)
    hWe c' hc'
  have e : (obsStep R P j st g μ D K o).W c' =
      πobs (Wnext2O P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c') := rfl
  rw [e, oTo_πobs]
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the real inequality
  have hp : (1 + cW * r) ^ (L ^ 2) - 1 ≤ 2 * (n * (cW * r)) := by
    have h := PtCorr2.one_add_pow_sub_one_le (mul_nonneg hcW0 hr0) (L ^ 2) (by
      push_cast; rw [← hn]; linarith)
    push_cast at h; rw [← hn] at h; exact h
  have hsO : sO 2 L r mV mW = 2 * cn * Q ^ 2 * (r * mV) + Q * mW := by
    unfold sO; rw [← hcn, ← hQ]
  have hoW : oWc 2 L r mV mW Clo = (1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) := by
    unfold oWc; rw [hsO, ← hn]; ring
  rw [hoW]
  have hQ0 : 0 ≤ Q := by linarith
  have hQ2 : 0 ≤ Q ^ 2 := pow_nonneg hQ0 2
  have hsO0 : 0 ≤ 2 * cn * Q ^ 2 * (r * mV) + Q * mW :=
    add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hcn0) hQ2) (mul_nonneg hr0 hmV))
      (mul_nonneg hQ0 hmW)
  have h3 : n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) *
      ((1 + cW * r) ^ (L ^ 2) - 1) ≤
      A1 * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) * r := by
    have h4 : 0 ≤ n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) :=
      mul_nonneg hn0 (mul_nonneg (by have := mul_nonneg hClo0 hn0; linarith) hsO0)
    calc n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) *
          ((1 + cW * r) ^ (L ^ 2) - 1)
        ≤ n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) * (2 * (n * (cW * r))) :=
          mul_le_mul_of_nonneg_left hp h4
      _ = A1 * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) * r := by rw [hA1]; ring
  have h5 : A1 * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) * r ≤
      A1 * (2 * cn * Q ^ 2) * (r * mV) + A1 * Q * (r * mW) := by
    have h6 : A1 * (2 * cn * Q ^ 2) * (r * mV) * r ≤ A1 * (2 * cn * Q ^ 2) * (r * mV) :=
      mul_le_of_le_one_right (mul_nonneg (mul_nonneg hA10
        (mul_nonneg (mul_nonneg (by norm_num) hcn0) hQ2)) (mul_nonneg hr0 hmV)) hr1
    have e7 : A1 * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) * r =
        A1 * (2 * cn * Q ^ 2) * (r * mV) * r + A1 * Q * (r * mW) := by ring
    linarith
  have e8 : ((1 + Clo) * (n * (cn * (2 * Q ^ 2))) + A1 * (2 * cn * Q ^ 2 + Q)) * r * mV +
      (Kc / L + ((1 + Clo) * (n * (cn * (2 * Q ^ 2))) + A1 * (2 * cn * Q ^ 2 + Q)) * r) * mW =
      Kc / L * mW + (1 + Clo) * (n * (cn * (2 * Q ^ 2 * (r * mV)))) +
        (A1 * (2 * cn * Q ^ 2) * (r * mV) + A1 * Q * (r * mW)) +
        ((1 + Clo) * (n * (cn * (2 * Q ^ 2))) * (r * mW) + A1 * Q * (r * mV)) +
        A1 * 2 * cn * Q ^ 2 * (r * mW) := by ring
  have h9 : 0 ≤ (1 + Clo) * (n * (cn * (2 * Q ^ 2))) * (r * mW) + A1 * Q * (r * mV) :=
    add_nonneg (mul_nonneg (mul_nonneg (by linarith) (mul_nonneg hn0 (mul_nonneg hcn0
      (mul_nonneg (by norm_num) hQ2)))) (mul_nonneg hr0 hmW))
      (mul_nonneg (mul_nonneg hA10 hQ0) (mul_nonneg hr0 hmV))
  have h10 : 0 ≤ A1 * 2 * cn * Q ^ 2 * (r * mW) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA10 (by norm_num)) hcn0) hQ2)
      (mul_nonneg hr0 hmW)
  linarith

end

end PtCorr2
