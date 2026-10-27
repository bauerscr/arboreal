import PtCorr2.Pair.SXOStepAB
import PtCorr2.Obs.ProdBdHist
import Obs2.Est.ErrAB

/-!
# The `E`-step sizes (1): `𝒲'_{j+1}(B)`, `Loc S_j(B)` and the product part of `𝒲_{j+1}(B_+)`

Item (i) of `PairESizes` asks for the `T_{j+1}(s_{j+1})` sizes of the per-block pieces
`𝒲'_{j+1}(B) = WpO_j(B) = S_j(B) - Loc_{B_+,B}S(B_+)` (bulk part `.e` and `ab` part); item (vi)
for `Loc S_j(B)_{ab}` and for the product part `𝒲_{j+1}(B_+) - ∑_{B ⊆ B_+}𝒲'_{j+1}(B)`. These
are internal to the `𝒲` chain (`Obs2.BHOAB.Wp_o`, `LS_o`; bulk `Step2.BH.Wp_le`); here they are
exposed, in the pattern of `sxo_raw_stepAB`/`sxo_hist_ab_le`:

* **`wpo_raw_stepAB`** (raw level): for anchored states and weights with `w.Sub`, per block
  `‖WpO(B)_∅‖_{T_{j+1}} ≤ c_W(L)r` (bulk), `‖WpO(B)‖_w ≤ s_O + C_{lo}L²s_O`,
  `‖Loc S(B)‖_w ≤ C_{lo}L²s_O`;
* **`WpOBoundsAB L Clo Cl`**, **`wpo_bounds_AB`** (the constants exist);
* **`oTo_prodPart_le`**: the product part from the per-block sizes
  (`‖∏(1+𝒲'(B)) - 1 - ∑𝒲'(B)‖_w ≤ L²o((1+e)^{L²} - 1)`);
* **`wpo_hist_stepAB`**, **`wpo_hist_ab_le`**: along the history from `j₀`, and in the weights
  `wM(M_a, M_b)` of scale `j` (the `ab` parts `≤ M_aM_b·(…)`), including the product part.
-/

set_option linter.unusedSectionVars false

namespace PtCorr2

noncomputable section

open Finset Grassmann Obs Obs.SA Loc LocObs Step Step2 FRD Obs2 Flow2

variable {L N : ℕ} [NeZero L]

set_option maxHeartbeats 1000000 in
/-- **The per-block `𝒲'` and `Loc S` bounds at the raw level** (anchored states, `w.Sub`). -/
theorem wpo_raw_stepAB : ∃ Clo Cl : ℝ, 0 ≤ Clo ∧ 0 ≤ Cl ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ 1 → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        Tj 2 (L : ℝ) (j + 1) (fscale (stZ' R st) * R.ℓ)
            (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b : SA c (Lam 2 L N)).e ≤
          ENNReal.ofReal (cWblk 2 L Cl * r) ∧
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
            (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) ≤
          ENNReal.ofReal (sO 2 L r mV mW + Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)) ∧
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
            (LSO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) ≤
          ENNReal.ofReal (Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)) := by
  classical
  obtain ⟨Clo, hClo0, hlocO⟩ := exists_LocO2_ab_bound 2 one_le_two
  obtain ⟨Cl, hCl0, hloc⟩ := exists_Loc2sXY_bound 2 one_le_two
  obtain ⟨cN, hcN⟩ := card_small_containing 2
  refine ⟨Clo, Cl, hClo0, hCl0, max (2 ^ (2 + 3) + 8 * 2 + 1) ⌈pauliL0 2⌉₊, fun L _ hL => ?_⟩
  have hL8 : 2 ^ (2 + 3) + 8 * 2 < L :=
    lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hL)
  have hLp : pauliL0 2 ≤ L := (Nat.le_ceil _).trans
    (by exact_mod_cast (le_max_right _ _).trans hL)
  intro N R j hV st H g μ D K hD hK hm hg0 ηz hz hy hηρ hηs c P w hwS o ho hlo hsym hanc
    wl dd r mV mW hwl0 hdd0 hr0 hr1 hmV hmW hWl hDd hvr hwr hVo hWo b hb
  set cS : ℝ := cN + 1 with hcSdef
  have hcS1 : 1 ≤ cS := by rw [hcSdef]; linarith [Nat.cast_nonneg (α := ℝ) cN]
  have hV' := hV
  obtain ⟨hj1, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hjN : j < N := by omega
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
  -- the bulk block hypotheses (with `K = 0`)
  have hVf_mem : stVf R j st g μ ∈ BSub (L := L) (N := N) j := by
    rw [stVf_eq_kap]
    exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN (stKap R j st g μ).toVec
  have hw : Fnorm j (fscale st.Z * R.ℓ) (st.Wl + D) ≤ ENNReal.ofReal (wl + dd) :=
    Fnorm_add_le _ _ hwl0 hdd0 hWl hDd
  have hr2 : r ^ 2 ≤ r := by nlinarith
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
  refine ⟨?_, HO.Wp_o hb, HO.LS_o hb⟩
  show Tj 2 (L : ℝ) (j + 1) (s' * R.ℓ)
    ((bulk (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) : EvR (Lam 2 L N)) :
      Alg 2 L N) ≤ _
  rw [bulk_WpO, bulkF_fullV R j st g μ ho, bulkF_fullW st D ho]
  exact HB.Wp_le hb

/-- The conclusion of `wpo_raw_stepAB` at `L` (as a named property). -/
def WpOBoundsAB (L : ℕ) [NeZero L] (Clo Cl : ℝ) : Prop :=
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidCore R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ (g μ : ℝ) (D : Fam 2 L N) (K : Act 2 L N), D ∈ BSub (L := L) (N := N) j →
      K ∈ ASub (L := L) (N := N) j → |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1 → 0 ≤ g →
    ∀ ηz : ℝ, ‖st.z / st.Z‖ ≤ ηz → ‖st.y / st.Z‖ ≤ ηz → 2 * ηz ≤ R.ρ →
      8 * cM * R.ℓ ^ 2 * ηz ≤ 1 / 2 →
    ∀ (c : Obs.Case) (P : ObsPts 2 L N) (w : Wt), w.Sub →
    ∀ o : ObsSt c L N, o.IsObs → ObsLocInv P j o → ObsSymInv j o → ObsAnchInv P j o →
    ∀ wl dd r mV mW : ℝ, 0 ≤ wl → 0 ≤ dd → 0 ≤ r → r ≤ 1 → 0 ≤ mV → 0 ≤ mW →
      Fnorm j (fscale st.Z * R.ℓ) st.Wl ≤ ENNReal.ofReal wl →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal dd →
      cM * R.ℓ ^ 2 * (2 * |μ| + 2 * ηz) + 8 * R.ℓ ^ 4 * g ≤ r → wl + dd ≤ r ^ 2 →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.V b) ≤ ENNReal.ofReal mV) →
      (∀ b ∈ blockIdx (L := L) (N := N) j,
        oTo w j (fscale st.Z * R.ℓ) (o.W b) ≤ ENNReal.ofReal mW) →
      ∀ b ∈ blockIdx (L := L) (N := N) j,
        Tj 2 (L : ℝ) (j + 1) (fscale (stZ' R st) * R.ℓ)
            (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b : SA c (Lam 2 L N)).e ≤
          ENNReal.ofReal (cWblk 2 L Cl * r) ∧
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
            (WpO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) ≤
          ENNReal.ofReal (sO 2 L r mV mW + Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)) ∧
        oTo w (j + 1) (fscale (stZ' R st) * R.ℓ)
            (LSO P j (stCov R j st) (fullV R j st g μ o) (fullW st D o) b) ≤
          ENNReal.ofReal (Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW))

theorem wpo_bounds_AB : ∃ Clo Cl : ℝ, 0 ≤ Clo ∧ 0 ≤ Cl ∧ ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], L₀ ≤ L →
    WpOBoundsAB L Clo Cl :=
  wpo_raw_stepAB

/-- **The product part of `𝒲_{j+1}(B_+)` from the per-block sizes** (anchored inputs, any
weights): `‖∏_{B ⊆ B_+}(1+𝒲'(B)) - 1 - ∑𝒲'(B)‖_w ≤ L²o((1+e)^{L²} - 1)`. -/
theorem oTo_prodPart_le {c : Obs.Case} {P : ObsPts 2 L N} {j : ℕ}
    {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ} {V W : OFam c 2 L N} {K : OAct c 2 L N}
    (H : OAnchS P j V W K) (w : Wt) {ℓ e o : ℝ} (hℓ : 0 < ℓ) (he : 0 ≤ e) (ho : 0 ≤ o)
    (c' : Fin 2 → ℕ)
    (hWe : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      Tj 2 (L : ℝ) (j + 1) ℓ (WpO P j C V W b : SA c (Lam 2 L N)).e ≤ ENNReal.ofReal e)
    (hWo : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
      oTo w (j + 1) ℓ (WpO P j C V W b) ≤ ENNReal.ofReal o) :
    oTo w (j + 1) ℓ (Wnext2O P j C V W c' -
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b) ≤
      ENNReal.ofReal ((L : ℝ) ^ 2 * o * ((1 + e) ^ (L ^ 2) - 1)) ∧
    Wnext2O P j C V W c' -
        ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'), WpO P j C V W b ∈
      (anc P (blockSet (L := L) (N := N) (j + 1) c') : Subalgebra ℂ (OE c (Lam 2 L N))) := by
  have hh : (0 : ℝ) < (L : ℝ) ^ (j + 1) :=
    pow_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)) _
  set s := blocks j (blockSet (L := L) (N := N) (j + 1) c') with hs
  have hab : ∀ b ∈ s, WpO P j C V W b ∈ (abSub : Subalgebra ℂ (OE c (Lam 2 L N))) :=
    fun b _ => anchSub_ab (H.Wp_anch (C := C) b)
  have hP := (oTo_prod_sub_leAB (w := w) hh hℓ s (fun b => WpO P j C V W b) he ho hWe hWo hab).2
  have hn : (s.card : ℝ) ≤ (L : ℝ) ^ 2 := by
    have := nb_blockSet_succ_le (L := L) (N := N) j c'
    unfold nb at this; exact_mod_cast this
  have hn' : s.card ≤ L ^ 2 := by exact_mod_cast hn
  have hpow : (1 + e) ^ s.card ≤ (1 + e) ^ (L ^ 2) := pow_le_pow_right₀ (by linarith) hn'
  have hB : (s.card : ℝ) * o * ((1 + e) ^ s.card - 1) ≤ (L : ℝ) ^ 2 * o * ((1 + e) ^ (L ^ 2) - 1) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hn ho) (by linarith) (by
      have := one_le_pow₀ (n := s.card) (show (1 : ℝ) ≤ 1 + e by linarith); linarith)
      (by positivity)
  refine ⟨?_, sub_mem (H.Wnext_anch (C := C) c') (Subalgebra.sum_mem _ fun b hb => anc_mono
    (blockSet_subset (IsPolymer.of_succ (isPolymer_blockSet (j + 1) c')) hb)
    (H.Wp_anch (C := C) b))⟩
  have e1 : Wnext2O P j C V W c' - ∑ b ∈ s, WpO P j C V W b =
      ∏ b ∈ s, (1 + WpO P j C V W b) - 1 - ∑ b ∈ s, WpO P j C V W b := rfl
  rw [e1]
  exact hP.trans (ENNReal.ofReal_le_ofReal hB)

section Hist

variable {C₀' η' εs CK C₂ CD Cq Cl cS : ℝ} (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]
  {Nh : ℕ} {Λ β δ κ cg cm cT ε : ℝ}

/-- **The per-block `𝒲'`, `Loc S` bounds along the history from `j₀`.** -/
theorem wpo_hist_stepAB {Clo Clb : ℝ} (hWB : WpOBoundsAB L Clo Clb)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS) (hε1 : cR R Λ cm C₂ * ε ≤ 1)
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
      Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
            SA .two (Lam 2 L N)).e ≤
        ENNReal.ofReal (cWblk 2 L Clb * (cR R Λ cm C₂ * (t j).1)) ∧
      oTo w (j + 1) (histS R (j + 1) t)
          (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b) ≤
        ENNReal.ofReal (sO 2 L (cR R Λ cm C₂ * (t j).1) mV mW +
          Clo * ((L : ℝ) ^ 2 * sO 2 L (cR R Λ cm C₂ * (t j).1) mV mW)) ∧
      oTo w (j + 1) (histS R (j + 1) t)
          (LSO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b) ≤
        ENNReal.ofReal (Clo * ((L : ℝ) ^ 2 * sO 2 L (cR R Λ cm C₂ * (t j).1) mV mW)) := by
  obtain ⟨hVc, HI, hg, -, hz, hy, hη, hηs, hWl, hDd, hvr, hwr, hr0, hrε, hcW, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hval := hist_valid R hV t (n := j + 1) (by omega)
  have hloc := obsLocInv_histFrom' R P hl0 t hjj fun i _ hi => hval i (by omega)
  have hsym := obsSymInv_histFrom' R P hs0 t hjj fun i _ hi => hval i (by omega)
  have hanc := obsAnchInv_histFrom' R P ha0 t hjj
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  have hg0 : 0 ≤ (t j).1 := hg
  exact hWB N R j hVc (rawHist R j t) HI (t j).1 (t j).2.1 (rawD R (rawHist R j t).u (t j).2.2)
    (rawK R (rawHist R j t).u (t j).2.2) (rawD_mem R _ _) (rawK_mem R _ _)
    (hm j hj) hg _ hz hy hη hηs .two P w hws (obsHistFrom R P j₀ o₀ j t) hobs hloc hsym hanc
    _ _ _ mV mW (mul_nonneg hcW (sq_nonneg _)) (norm_nonneg _) hr0.le (hrε.trans hε1) hmV hmW
    hWl hDd hvr hwr hVo hWo

/-- **The `E`-step sizes of items (i) and (vi) in the weights `wM(M_a, M_b)` of scale `j`**:
`‖𝒲'_{j+1}(B)_∅‖ ≤ c_W(L)r_j`, `‖𝒲'_{j+1}(B)_{ab}‖ ≤ M_aM_b·o_j`,
`‖Loc S_j(B)_{ab}‖ ≤ M_aM_b·C_{lo}L²s_O`, and the product part
`‖(𝒲_{j+1}(B_+) - ∑𝒲'_{j+1}(B))_{ab}‖ ≤ M_aM_bL²o_j((1+c_W(L)r_j)^{L²} - 1)`, all in
`T_{j+1}(s_{j+1})`, `o_j = s_O + C_{lo}L²s_O`, `s_O = s_O(r_j, m_V, m_W)`. -/
theorem wpo_hist_ab_le {Clo Clb : ℝ} (hWB : WpOBoundsAB L Clo Clb) (hClo : 0 ≤ Clo)
    (hClb : 0 ≤ Clb)
    (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS) (hε1 : cR R Λ cm C₂ * ε ≤ 1)
    (P : ObsPts 2 L N) {Ma Mb : ℝ} (hMa : 0 < Ma) (hMb : 0 < Mb)
    {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (hl0 : ObsLocInv P j₀ o₀)
    (hs0 : ObsSymInv j₀ o₀) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) (mV mW : ℝ) (hmV : 0 ≤ mV) (hmW : 0 ≤ mW)
    (hVo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).V b) ≤ ENNReal.ofReal mV)
    (hWo : ∀ b ∈ blockIdx (L := L) (N := N) j,
      oTo (wM Ma Mb) j (histS R j t) ((obsHistFrom R P j₀ o₀ j t).W b) ≤ ENNReal.ofReal mW) :
    let r := cR R Λ cm C₂ * (t j).1
    let oj := sO 2 L r mV mW + Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)
    (∀ b ∈ blockIdx (L := L) (N := N) j,
      Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
            SA .two (Lam 2 L N)).e ≤ ENNReal.ofReal (cWblk 2 L Clb * r) ∧
      Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
            SA .two (Lam 2 L N)).ab ≤ ENNReal.ofReal (Ma * Mb * oj) ∧
      Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          (LSO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
            SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * (Clo * ((L : ℝ) ^ 2 * sO 2 L r mV mW)))) ∧
    (∀ c' ∈ blockIdx (L := L) (N := N) (j + 1),
      Tj 2 (L : ℝ) (j + 1) (histS R (j + 1) t)
          ((Wnext2O P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) c' -
            ∑ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
              WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
                OE .two (Lam 2 L N)) : SA .two (Lam 2 L N)).ab ≤
        ENNReal.ofReal (Ma * Mb * ((L : ℝ) ^ 2 * oj * ((1 + cWblk 2 L Clb * r) ^ (L ^ 2) - 1)))) := by
  intro r oj
  have HW := wpo_hist_stepAB R hWB hSB hV hm hβ hδ1 H hε1 P (wM Ma Mb) (wM_sub _ _) o₀ h0 hl0 hs0
    ha0 t j hjj hj ht mV mW hmV hmW hVo hWo
  have HA := oanchS_full (R := R) (j := j) (st := rawHist R j t) (g := (t j).1) (μ := (t j).2.1)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2) P
    (obsAnchInv_histFrom' R P ha0 t hjj)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hr0, -, hcW, -, -⟩ :=
    hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hsO : 0 ≤ sO 2 L r mV mW := by
    unfold sO
    have hQ := Step2.one_le_Q1 (d := 2) one_le_two
    have hn : (0 : ℝ) ≤ Step2.cNear 2 L := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ r := hr0.le
    exact add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hn) (by positivity))
      (mul_nonneg h1 hmV)) (mul_nonneg (by linarith) hmW)
  have hoj : 0 ≤ oj := add_nonneg hsO (mul_nonneg hClo (mul_nonneg (by positivity) hsO))
  have hcWb : 0 ≤ cWblk 2 L Clb := by
    have hQ := one_le_Q1 (d := 2) one_le_two
    have hn : (0 : ℝ) ≤ cNear 2 L := Nat.cast_nonneg _
    unfold cWblk cSblk
    generalize Q1 2 = q at *
    generalize cNear 2 L = cn at *
    have : 0 ≤ cn * q ^ 2 + q := by positivity
    positivity
  have hℓ1 : 0 < histS R (j + 1) t := by
    obtain ⟨-, -, -, hρ0, hρ8, -, -⟩ := (hV j hj).toValidCore
    exact histS_pos' R hρ0 (by linarith) t (j + 1)
  refine ⟨fun b hb => ⟨(HW b hb).1, ?_, ?_⟩, fun c' hc' => ?_⟩
  · exact Tj_ab_le_of_oTo_wM hMa hMb (j + 1) _ (anchSub_ab (HA.Wp_anch b)) (HW b hb).2.1
  · have hm' : LSO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b ∈
        (abSub : Subalgebra ℂ (OE .two (Lam 2 L N))) := by
      have e : LSO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b =
          SbO j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b -
            WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b := by
        rw [WpO]; abel
      rw [e]
      exact sub_mem (anchSub_ab (HA.Sb_anch b)) (anchSub_ab (HA.Wp_anch b))
    exact Tj_ab_le_of_oTo_wM hMa hMb (j + 1) _ hm' (HW b hb).2.2
  · have hbI : ∀ b ∈ blocks j (blockSet (L := L) (N := N) (j + 1) c'),
        b ∈ blockIdx (L := L) (N := N) j := fun b hb => mem_blockIdx_of_mem_blocks hb
    have hPP := oTo_prodPart_le HA (wM Ma Mb) hℓ1 (mul_nonneg hcWb hr0.le) hoj c'
      (fun b hb => (HW b (hbI b hb)).1) (fun b hb => (HW b (hbI b hb)).2.1)
    exact Tj_ab_le_of_oTo_wM hMa hMb (j + 1) _ (anchSub_ab hPP.2) hPP.1

/-- **Off the lattice blocks `𝒲'_{j+1}(B)` vanishes** along the history (`B ∉ 𝓑_j`): the bulk
part because the bulk families are in `BSub` (zero off the lattice, `Bp j B = ∅`), the `ab` part by
anchoring. -/
theorem wpo_hist_off (hSB : StepBounds L R.A C₀' η' εs CK C₂ CD Cq Cl cS)
    (hV : ∀ j < Nh, ValidAt R j) (hm : ∀ j < Nh, |R.msq| * ((L : ℝ) ^ j) ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (hδ1 : δ ≤ 1)
    (H : ApHyp R Λ κ cg cm cT ε εs C₀' C₂ Cq Cl cS)
    (P : ObsPts 2 L N) {j₀ : ℕ} (o₀ : ObsSt .two L N) (h0 : o₀.IsObs) (ha0 : ObsAnchInv P j₀ o₀)
    (t : Flow2.Hist.Seq (Xs R)) (j : ℕ) (hjj : j₀ ≤ j) (hj : j < Nh)
    (ht : Flow2.Hist.InDh Λ β δ κ cg cm cT ε j t) (hL8 : 2 ^ (2 + 3) + 8 * 2 < L)
    {b : Fin 2 → ℕ} (hb : b ∉ blockIdx (L := L) (N := N) j) :
    (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
        SA .two (Lam 2 L N)).e = 0 ∧
      (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b :
        SA .two (Lam 2 L N)).ab = 0 := by
  obtain ⟨hVc, HI, -, -⟩ := hist_raw R hSB hV hm hβ hδ1 H t j hj ht
  have hobs := obsHistFrom_isObs (R := R) (P := P) (j := j₀) h0 t j
  have hjN : j < N := by have := hVc.1; omega
  have HA := oanchS_full (R := R) (j := j) (st := rawHist R j t) (g := (t j).1) (μ := (t j).2.1)
    (D := rawD R (rawHist R j t).u (t j).2.2) (K := rawK R (rawHist R j t).u (t j).2.2) P
    (obsAnchInv_histFrom' R P ha0 t hjj)
  refine ⟨?_, ?_⟩
  · have hVf : stVf R j (rawHist R j t) (t j).1 (t j).2.1 ∈ BSub (L := L) (N := N) j := by
      rw [stVf_eq_kap]
      exact VfamL_mem (L := L) (N := N) (d := 2) (by norm_num) hL8 hjN
        (stKap R j (rawHist R j t) (t j).1 (t j).2.1).toVec
    have hWf : (rawHist R j t).Wl + rawD R (rawHist R j t).u (t j).2.2 ∈
        BSub (L := L) (N := N) j := add_mem HI.hWl (rawD_mem R _ _)
    have hBp : Step2.Bp (L := L) (N := N) j b = ∅ := by
      unfold Step2.Bp; rw [blockSet_eq_empty hb]
      ext y; simp [clo, blocks]
    show ((bulk (WpO P j (histCovO R t j) (hVR R P j₀ o₀ t j) (hWR R P j₀ o₀ t j) b) :
      EvR (Lam 2 L N)) : Alg 2 L N) = 0
    rw [bulk_WpO]
    unfold hVR hWR
    rw [bulkF_fullV R j _ _ _ hobs, bulkF_fullW _ _ hobs]
    simp only [Step2.Wp, Step2.Sb, Step2.LS, Step2.SX, Step2.Vpr, hBp, hVf.2.2.2.2 b hb,
      hWf.2.2.2.2 b hb, EthE_zero, FCE_zero_left, blocks, Finset.image_empty, Finset.sum_empty,
      Loc2E_zero, smul_zero, zero_add, sub_self, ZeroMemClass.coe_zero]
  · have hba : b ≠ blk j P.a := fun h => hb (h ▸ mem_image_of_mem _ (mem_univ _))
    have hbb : b ≠ blk j P.b := fun h => hb (h ▸ mem_image_of_mem _ (mem_univ _))
    exact ab_eq_zero_of_anch P (HA.Wp_anch b) hba hbb

end Hist

end

end PtCorr2
