import PtCorr2.Obs.WObsStep
import PtCorr2.Obs.ObsHist
import Obs2.Flow.ProdObs

/-!
# The product part of `𝒲^{obs}_{j+1}` along the history

**`prod_raw_step`**: in the normalisation of `wobs_raw_step`, the product part
`Prod_{j+1}(B_+) = 𝒲_{j+1}(B_+) − ∑_{B ⊆ B_+} 𝒲'(B)` satisfies
`‖Prod^{obs}(B_+)‖_{T_{j+1}(s')} ≤ C_P(L) r (r m_V + m_W)` (quadratic in the block quantities:
`L^2 o ((1 + c_W r)^{L^2} − 1) ≤ 2L^4 c_W r o`) for `r ≤ ε_P(L)`, with explicit `C_P`, `ε_P`
(functions of `L`), and `Prod ∈ 𝒩^{obs}(𝒩_{j+1}(B_+))`. `prod_hist_step`: the same along the
history.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- The conclusion of `prod_raw_step` for given constants. -/
def PObsBounds (L : ℕ) [NeZero L] (Cp ε₁ : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.ab = 0 →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ ε₁ → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
          (prodO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c') ≤
          ENNReal.ofReal (Cp * r * (r * mV + mW)) ∧
        prodO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) c' ∈
          osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c'))

set_option maxHeartbeats 1000000 in
/-- **The product part of `𝒲^{obs}_{j+1}` at the raw level**: `‖Prod^{obs}‖ ≤ C_P r (r m_V + m_W)`,
and `Prod ∈ 𝒩^{obs}(𝒩_{j+1}(B_+))`. -/
theorem prod_raw_step : ∃ (Cpf εpf : ℕ → ℝ) (L₀ : ℕ), (∀ L, 0 ≤ Cpf L) ∧
    ∀ (L : ℕ) [NeZero L], L₀ ≤ L → 0 < εpf L ∧
    PObsBounds L (Cpf L) (εpf L) := by
  classical
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound 2 one_le_two
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_obs_bound 2
  obtain ⟨cN, hcN⟩ := card_small_containing 2
  have hcW0' : ∀ L : ℕ, (0 : ℝ) ≤ cWblk 2 L Cl := fun L => by
    have := Nat.cast_nonneg (α := ℝ) ((L + 2 ^ (2 + 3) + 7) ^ 2)
    have := one_le_Q1 (d := 2) one_le_two
    simp only [cWblk, cSblk, cNear]; positivity
  refine ⟨fun L => (L : ℝ) ^ 2 * (1 + Clo * (L : ℝ) ^ 2) * (2 * (L : ℝ) ^ 2 * cWblk 2 L Cl) *
      (2 * cNear 2 L * Q1 2 ^ 2 + Q1 2),
    fun L => min 1 (1 / ((L : ℝ) ^ 2 * cWblk 2 L Cl + 1)),
    max (2 ^ (2 + 3) + 8 * 2 + 1) ⌈pauliL0 2⌉₊, fun L => ?_, fun L _ hL => ?_⟩
  · have := hcW0' L
    have := one_le_Q1 (d := 2) one_le_two
    have : (0 : ℝ) ≤ cNear 2 L := Nat.cast_nonneg _
    positivity
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _ |>.trans hL)
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hL)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  set n : ℝ := (L : ℝ) ^ 2 with hn
  have hn0 : 0 ≤ n := by positivity
  set cW : ℝ := cWblk 2 L Cl with hcW
  have hcW0 : 0 ≤ cW := hcW0' L
  set Q : ℝ := Q1 2 with hQ
  have hQ1 : 1 ≤ Q := one_le_Q1 one_le_two
  set cn : ℝ := cNear 2 L with hcn
  have hcn0 : 0 ≤ cn := Nat.cast_nonneg _
  set A1 : ℝ := n * (1 + Clo * n) * (2 * n * cW) with hA1
  have hA10 : 0 ≤ A1 := by positivity
  refine ⟨lt_min one_pos (by positivity), ?_⟩
  unfold PObsBounds
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hw0 o ho hlo hsym
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
  have hwsub : w.Sub := by simp [Wt.Sub, hw0]
  have HO : BHO P j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
      (fullV R j st g μ o) (fullW st D o) (0 : OAct c 2 L N) w r mV mW 0 Clo cS :=
    { hd := one_le_two, hLp := hLp, hL8 := hL8, hjN := hj1, hℓ := hsℓ, hℓ' := mul_pos hs' hℓ,
      hℓC := by positivity, hsum := hsum, hC := hC, hw := hwsub, hw0 := hw0
      hVl := fun b => cmpIn_of_osub (HL.hV b), hWl := fun b => cmpIn_of_osub (HL.hW b)
      hKl := fun _ _ => CmpIn.zero, hr := hr0, hmV := hmV, hmW := hmW, hk := le_rfl
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
      hloc := fun k' hk ℓ₀ hℓ₀ X Y hX hYX F hF =>
        hlocO L hL8 N c P w hw0 k' hk ℓ₀ hℓ₀ X Y hX hYX F hF
      hlocl := bho_hlocl one_le_two P j, hcS := hcS1, hcount := hcount }
  have hWe : ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ)
        (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b : SA c (Lam 2 L N)).e ≤
        ENNReal.ofReal (cW * r) := fun b hb => by
    show Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ)
      ((bulk (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) : EvR (Lam 2 L N)) :
        Alg 2 L N) ≤ _
    rw [bulk_WpO, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho]
    exact HB.Wp_le hb
  refine ⟨(prodO_obs_le HO (mul_nonneg hcW0 hr0) hWe).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
  · have hp : (1 + cW * r) ^ (L ^ 2) - 1 ≤ 2 * (n * (cW * r)) := by
      have h := one_add_pow_sub_one_le (mul_nonneg hcW0 hr0) (L ^ 2) (by
        push_cast; rw [← hn]; linarith)
      push_cast at h; rw [← hn] at h; exact h
    have hsO : sO 2 L r mV mW = 2 * cn * Q ^ 2 * (r * mV) + Q * mW := by
      unfold sO; rw [← hcn, ← hQ]
    have hoW : oWc 2 L r mV mW Clo = (1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) := by
      unfold oWc; rw [hsO, ← hn]; ring
    rw [hoW, ← hn]
    have hQ0 : 0 ≤ Q := by linarith
    have hcQ : 0 ≤ 2 * cn * Q ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hcn0) (sq_nonneg Q)
    have hrV : 0 ≤ r * mV := mul_nonneg hr0 hmV
    have hsO0 : 0 ≤ 2 * cn * Q ^ 2 * (r * mV) + Q * mW :=
      add_nonneg (mul_nonneg hcQ hrV) (mul_nonneg hQ0 hmW)
    have hCn : 0 ≤ 1 + Clo * n := by have := mul_nonneg hClo0 hn0; linarith
    have h4 : 0 ≤ n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) :=
      mul_nonneg hn0 (mul_nonneg hCn hsO0)
    have h5 : 2 * cn * Q ^ 2 * (r * mV) + Q * mW ≤ (2 * cn * Q ^ 2 + Q) * (r * mV + mW) := by
      have : 0 ≤ 2 * cn * Q ^ 2 * mW + Q * (r * mV) :=
        add_nonneg (mul_nonneg hcQ hmW) (mul_nonneg hQ0 hrV)
      have e : (2 * cn * Q ^ 2 + Q) * (r * mV + mW) =
          2 * cn * Q ^ 2 * (r * mV) + Q * mW + (2 * cn * Q ^ 2 * mW + Q * (r * mV)) := by ring
      rw [e]; linarith
    calc n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) * ((1 + cW * r) ^ (L ^ 2) - 1)
        ≤ n * ((1 + Clo * n) * (2 * cn * Q ^ 2 * (r * mV) + Q * mW)) * (2 * (n * (cW * r))) :=
          mul_le_mul_of_nonneg_left hp h4
      _ = A1 * (2 * cn * Q ^ 2 * (r * mV) + Q * mW) * r := by rw [hA1]; ring
      _ ≤ A1 * ((2 * cn * Q ^ 2 + Q) * (r * mV + mW)) * r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hA10) hr0
      _ = _ := by rw [hA1]; ring
  · have hCR : CovRange j (stCov R j st) := fun x y h => hC.range hj1 x y h
    exact prodO_mem HL one_le_two (by omega) hj1 hCR


section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The product part along the history**: `‖Prod^{obs}_{j+1}(B_+)‖_{T_{j+1}(s_{j+1})} ≤
C_P r_j (r_j m_V + m_W)`, and `Prod_{j+1}(B_+) ∈ 𝒩^{obs}(𝒩_{j+1}(B_+))`. -/
theorem prod_hist_step {Cp εp : ℝ} (hPB : PObsBounds L Cp εp)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    {c : Obs.Case} (P : ObsPts 2 L N) (w : Wt) (hw0 : w.ab = 0)
    (o₀ : ObsSt c L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P 0 o₀) (hs0 : ObsSymInv 0 o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t)
    (hεp : cR R Λ cm C₂ * ε ≤ εp) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHist R P o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      oTo w (j + 1) (histS R (j + 1) t)
        (prodO P j (stCov R j (rawHist R j t))
          (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
          (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)) c') ≤
        ENNReal.ofReal (Cp * (cR R Λ cm C₂ * (t j).1) * (cR R Λ cm C₂ * (t j).1 * mV + mW)) ∧
      prodO P j (stCov R j (rawHist R j t))
          (fullV R j (rawHist R j t) (t j).1 (t j).2.1 (obsHist R P o₀ j t))
          (fullW (rawHist R j t) (rawD R (rawHist R j t).u (t j).2.2) (obsHist R P o₀ j t)) c' ∈
        osub P (nbhd (j + 1) (blockSet (L := L) (N := N) (j + 1) c')) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcw, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_hist R P o₀ hl0 t j fun i hi => hval i (by omega)
  have hsym := obsSymInv_hist R P o₀ hs0 t j fun i hi => hval i (by omega)
  have hobs := obsHist_isObs R P o₀ h0 j t
  exact hPB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs c P w hw0 (obsHist R P o₀ j t) hobs hloc hsym _ _ _ mV mW
    (by positivity) (norm_nonneg _) hr0.le (hrε.trans hεp) hmV hmW hWl hDd hvr hwr hVo hWo

end Hist

end

end PtCorr2
