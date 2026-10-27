import PtCorr2.Pair.KObsHistAB
import PtCorr2.Pair.PairSizesAB
import PtCorr2.Pair.PairReduceChain

/-!
# The second-order part `S_j(B_+)` of the `ab` step in `wM`-type weights

The block bound `Obs2.BHOAB.SX_o` (`‖S(B_+)‖_{w, T_{j+1}(ℓ')} ≤ L^d s_O(r, m_V, m_W)`) is used
inside the `BlockOAB` chain (`Loc S`, `𝒲'`) but was not available along the history. Here it is
exposed:

* **`sxo_raw_stepAB`** (raw level): for an anchored observable state and weights with `w.Sub`,
  `‖S_j(B_+)‖_{w} ≤ L²s_O(r, m_V, m_W)` (`s_O = 2c_{near}Q₁²rm_V + Q₁m_W`), and `S_j(B_+)` is
  anchored at `B_+` (its `ab` part vanishes unless `B_+ ∩ {a, b} ≠ ∅`);
* **`sxo_hist_stepAB`**: the same along the history from `j₀` (`hVR`, `hWR`, `histCovO`);
* **`sxo_hist_ab_le`**: with the weights `wM(M_a, M_b)` of scale `j`:
  `‖S_j(B_+)_{ab}‖_{T_{j+1}(s_{j+1})} ≤ M_aM_bL²s_O(r_j, m_V, m_W)` — the `κ^S_j(B)` of
  `m4_hist_weighted_sizes`, `cfAB4_hVR_block_sizes`, `gradM4Sz_hVR_block_sizes`.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

/-- **`S_j(B_+)` is anchored at `B_+`.** -/
theorem SXO_Bp_anch {c : Obs.Case} {P : ObsPts 2 L N} {j : ℕ}
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} {V W : OFam c 2 L N} {K : OAct c 2 L N}
    (H : OAnchS P j V W K) (b : Fin 2 → ℕ) :
    SXO j C V W (Step2.Bp (L := L) (N := N) j b) ∈
      (anc P (Step2.Bp (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam 2 L N))) := by
  rw [SXO]
  refine Subalgebra.sum_mem _ fun b'' hb'' => anc_mono ?_ (H.Sb_anch (C := C) b'')
  exact (subset_clo j _).trans (Step2.BH.Bp_sub hb'')

set_option maxHeartbeats 1000000 in
/-- **The `S_j(B_+)` block bound at the raw level** (anchored states, `w.Sub`). -/
theorem sxo_raw_stepAB : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ r mV mW : ℝ, 0 ≤ r → 0 ≤ mV → 0 ≤ mW →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
          (SXO j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (Step2.Bp (L := L) (N := N) j b))
          ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * sO 2 L r mV mW) ∧
        SXO j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (Step2.Bp (L := L) (N := N) j b) ∈
          (anc P (Step2.Bp (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam 2 L N))) := by
  classical
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_ab_bound 2 one_le_two
  obtain ⟨cN, hcN⟩ := card_small_containing 2
  refine ⟨max (2 ^ (2 + 3) + 8 * 2 + 1) ⌈pauliL0 2⌉₊, fun L _ hL => ?_⟩
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hL)
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hL)
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hwS o ho hlo hsym hanc
    r mV mW hr0 hmV hmW hvr hVo hWo b hb
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  have hV' := hV
  obtain ⟨hj1, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hη0 : 0 ≤ ηz := (norm_nonneg _).trans hz
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
  obtain ⟨hVv, -⟩ := rg_inputs R j hV st H g μ hm hg0 ηz hz hy hηρ
  have hcount : ∀ b ∈ blockIdx (d := 2) (L := L) (N := N) j,
      (((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card : ℝ) ≤ cS := fun b hb => by
    have h1 : ((smallSets (d := 2) (L := L) (N := N) j).filter
        (fun X => blockSet j b ⊆ X)).card ≤ cN := by convert hcN L N j b hb
    have h2 := Nat.cast_le (α := ℝ) |>.2 h1
    linarith
  have HL := olocS_full R P g μ hV H hD hK hlo
  have HA := oanchS_full R P g μ (st := st) (D := D) (K := K) hanc
  have HAb := HA.toAb
  have HO : BHOAB P j (fscale st.Z * R.ℓ) (s' * R.ℓ) (s' * R.ℓ / 4) (stCov R j st)
      (fullV R j st g μ o) (fullW st D o) (0 : OAct c 2 L N) w r mV mW 0 Clo cS :=
    { hd := one_le_two, hLp := hLp, hL8 := hL8, hjN := hj1, hℓ := hsℓ, hℓ' := mul_pos hs' hℓ,
      hℓC := by positivity, hsum := hsum, hC := hC, hw := hwS, hVab := HAb.hV, hWab := HAb.hW,
      hKab := fun _ _ => zero_mem _
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
  exact ⟨HO.SX_o b, SXO_Bp_anch HA b⟩

/-- The conclusion of `sxo_raw_stepAB` at `L` (as a named property). -/
def SXOBoundsAB (L : ℕ) [NeZero L] : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ r mV mW : ℝ, 0 ≤ r → 0 ≤ mV → 0 ≤ mW →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
          (SXO j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (Step2.Bp (L := L) (N := N) j b))
          ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * sO 2 L r mV mW) ∧
        SXO j (stCov R j st) (fullV R j st g μ o) (fullW st D o) (Step2.Bp (L := L) (N := N) j b) ∈
          (anc P (Step2.Bp (L := L) (N := N) j b) : Subalgebra ℂ (OE c (Lam 2 L N)))

theorem sxo_bounds_AB : ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L → SXOBoundsAB L :=
  sxo_raw_stepAB

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The `S_j(B_+)` block bound along the history from `j₀`.** -/
theorem sxo_hist_stepAB (hSX : SXOBoundsAB L)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) (w : Wt) (hws : w.Sub)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo w (j + 1) (histS R (j + 1) t)
          (SXO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j)
            (Step2.Bp (L := L) (N := N) j b)) ≤
        ENNReal.ofReal ((L : ℝ) ^ 2 * sO 2 L (cR R Λ cm C₂ * (t j).1) mV mW) ∧
      SXO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j)
          (Step2.Bp (L := L) (N := N) j b) ∈
        (anc P (Step2.Bp (L := L) (N := N) j b) : Subalgebra ℂ (OE .two (Lam 2 L N))) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, -, -, hvr, -, hr0, -, -, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  exact hSX N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs .two P w hws (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc
    _ mV mW hr0.le hmV hmW hvr hVo hWo

/-- **`κ^S_j(B)` from the `wM` sizes**: with the weights `wM(M_a, M_b)` of scale `j`,
`‖S_j(B_+)_{ab}‖_{T_{j+1}(s_{j+1})} ≤ M_aM_bL²s_O(r_j, m_V, m_W)`, and `S_j(B_+)_{ab} = 0` unless
`B_+` meets `{a, b}`. -/
theorem sxo_hist_ab_le (hSX : SXOBoundsAB L)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    ∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          (SXO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j)
            (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 * sO 2 L (cR R Λ cm C₂ * (t j).1) mV mW)) ∧
      (¬ (Step2.Bp (L := L) (N := N) j b ∩ P.pts).Nonempty →
        (SXO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j)
          (Step2.Bp (L := L) (N := N) j b) : SA .two (Lam 2 L N)).ab = 0) := by
  intro b hb
  obtain ⟨h1, h2⟩ := sxo_hist_stepAB R hSX hSB hV hm hβ hδ1 H P (wM Ma Mb) (wM_sub _ _) o₀ h0 hl0
    hs0 ha0 t j hjj hj ht mV mW hmV hmW hVo hWo b hb
  exact ⟨Tj_ab_le_of_oTo_wM hMa hMb (j + 1) _ (anchSub_ab h2) h1, h2.2.2⟩

end Hist

end

end PtCorr2
