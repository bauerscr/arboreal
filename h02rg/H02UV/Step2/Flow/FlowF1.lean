import Step2.Flow.FlowHist
import Step2.Coup.CoupG

/-!
# The exact quartic coupling of one RG step along a history (`h02uv-outline.tex`, (F1))

* `histFS`: the flow sequence of a history (`FlowSeq` with `s ≡ 1`, the step covariances and the
  couplings of `V♭`), with `W^lin` equal to the raw state (`histFS_Wlin`);
* `LS_addW`: `Loc S` is affine in `𝒲`;
* `stCv_g_exact`: the quartic coupling after one step,
  `κ'_g = g♭ - κ_{Q,g} - (∑_{k<j} g_k² b_{j,k} + g_j² q_{j,j} + 4 C⁽¹⁾ g_j ν'_j) - κ_{D,g}`.
-/

namespace Step2

open Step

noncomputable section

open Finset Grassmann Loc FRD Flow2

variable {L N : ℕ} [NeZero L]

/-! ### `Loc S` is affine in `𝒲` -/

section LSadd

variable {d : ℕ} (j : ℕ) (C : Matrix (Lam d L N) (Lam d L N) ℂ)

theorem LS_addW (V W₁ W₂ : Fam d L N) (b : Fin d → ℕ) :
    LS j C V (W₁ + W₂) b = LS j C V W₁ b + LS j C 0 W₂ b := by
  have hS : ∀ b', Sb j C V (W₁ + W₂) b' = Sb j C V W₁ b' + Sb j C 0 W₂ b' := fun b' => by
    simp only [Sb, Pi.add_apply, EthE_add, VprL, Vpr_zero, FCE_zero_left, sum_const_zero,
      smul_zero, zero_add]
    abel
  simp only [LS, SX, hS, sum_add_distrib, Loc2E_add]

end LSadd

/-! ### The zero covariance -/

theorem goodCov2_zero {d : ℕ} (j : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    GoodCov2 (d := d) (L := L) (N := N) j ℓ 0 where
  gram := ⟨ℂ, inferInstance, inferInstance, fun _ => 0, fun _ => 0, fun x y => by simp,
    fun a _ x => by
      simp only [gvec, smul_zero, sum_const_zero, norm_zero]
      exact ⟨by positivity, by positivity⟩⟩
  range := fun _ _ _ _ => rfl

/-! ### The part of `Loc S` linear in `D` -/

theorem VfamL_zero_vec {d : ℕ} (k : ℕ) :
    VfamL (d := d) (L := L) (N := N) k (Coup.ofVec 0).toVec = 0 := by
  rw [Coup.toVec_ofVec, map_zero]

/-- **The `D`-part of `Loc S`**: `|κ_{D}| ≤ C_q (s'ℓ)^{-4} C_l L² Q₁ ‖D‖`. -/
theorem LS_D_bound : ∃ Cq : ℝ, 0 ≤ Cq ∧ ∃ Cl : ℝ, 0 ≤ Cl ∧
    ∀ (L : ℕ) [NeZero L], 2 ^ (2 + 3) + 8 * 2 < L → pauliL0 2 ≤ L →
    ∀ (N : ℕ) (R : RGPar 2 L N) (j : ℕ), ValidAt R j → ∀ st : RawSt 2 L N, RawInv R j st →
    ∀ D : Fam 2 L N, D ∈ BSub (L := L) (N := N) j → ∀ w : ℝ, 0 ≤ w → w ≤ 1 →
      Fnorm j (fscale st.Z * R.ℓ) D ≤ ENNReal.ofReal w →
      ‖cvec4 (blockSet (L := L) (N := N) j 0) R.i₀ (LS j (stCov R j st) 0 D 0 : Alg 2 L N) 3‖ ≤
        Cq * ((fscale (stZ' R st) * R.ℓ) ^ 4)⁻¹ * (Cl * ((L : ℝ) ^ 2 * BH.sig 2 L 0 w)) := by
  obtain ⟨Cq, hCq, Cl, hCl, cS, hcS, h⟩ := coupP_bound
  refine ⟨Cq, hCq, Cl, hCl, ?_⟩
  intro L _ hL8 hLp N R j hV st H D hD w hw0 hw1 hDw
  have hV' := hV
  obtain ⟨hj2, -, -, hρ0, hρ8, hℓ, -⟩ := hV'
  have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
  have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ0 st).trans hρ8
  obtain ⟨hC, -, hCs, hCsym⟩ := H.cov hV
  have hsc := scale_ok hZ hζ hℓ
  have hs := fscale_pos hZ
  have hs' : 0 < fscale (stZ' R st) := fscale_pos (mul_ne_zero hZ (one_add_ne_zero (by linarith)))
  have hK0 : (0 : Act 2 L N) ∈ ASub (L := L) (N := N) j := zero_mem _
  obtain ⟨c₀, δ, κQ, κL, -, -, -, -, -, -, -, -, -, -, l4, hLcv⟩ :=
    h L hL8 hLp N j hj2 (fscale st.Z * R.ℓ) (fscale (stZ' R st) * R.ℓ)
      (fscale (stZ' R st) * R.ℓ / 4) (by positivity) (by positivity) (by positivity)
      (by have e : fscale (stZ' R st) = fscale (st.Z * (1 + stZeta R st)) := rfl
          have := mul_pos hs hℓ
          rw [e]; linarith) (stCov R j st) hC hCs hCsym (Coup.ofVec 0) D 0 hD hK0 1 le_rfl
      0 w 0 le_rfl hw0 le_rfl zero_le_one hw1 zero_le_one
      (by rw [VfamL_zero_vec]; unfold Fnorm; simp [Step.Tj_zero]) hDw
      (by rw [Knorm_zero]; exact zero_le)
  have e := hLcv 0 (zero_mem_blockIdx j) R.i₀
  rw [VfamL_zero_vec] at e
  rw [e]
  exact l4

/-! ### The zero mode -/

/-- **The zero mode of a covariance** with `GoodCov2` at `ℓ_C`: `|∑_x C(x, 0)| ≤ 9 L^{2(j+1)} ℓ_C²`. -/
theorem zero_mode_le {j : ℕ} (hjN : j + 1 < N) {ℓC : ℝ} {C : Matrix (Lam 2 L N) (Lam 2 L N) ℂ}
    (hC : GoodCov2 j ℓC C) : ‖∑ x, C x 0‖ ≤ 9 * ((L : ℝ) ^ (j + 1)) ^ 2 * ℓC ^ 2 := by
  classical
  obtain ⟨H, _, _, Fv, Gv, hG, hB⟩ := hC.gram
  set k := L ^ (j + 1)
  set S := univ.filter fun y : Lam 2 L N => supNorm (y - 0) ≤ k
  have hz : ∀ x ∈ univ, x ∉ S → C x 0 = 0 := by
    intro x _ hx
    simp only [S, mem_filter, mem_univ, true_and, not_le] at hx
    refine hC.range hjN x 0 ?_
    have : ((k : ℕ) : ℝ) < (supNorm (x - 0) : ℝ) := by exact_mod_cast hx
    push_cast [k] at this
    have hL0 : (0 : ℝ) ≤ (L : ℝ) ^ (j + 1) := by positivity
    linarith
  rw [← sum_subset (subset_univ S) hz]
  have hcard : (S.card : ℝ) ≤ 9 * ((L : ℝ) ^ (j + 1)) ^ 2 := by
    have h := card_ball_le (d := 2) (L := L) (N := N) 0 k
    have h' : (S.card : ℝ) ≤ ((2 * k + 1) ^ 2 : ℕ) := by exact_mod_cast h
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have : 1 ≤ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
      exact_mod_cast this
    have e : ((k : ℕ) : ℝ) = (L : ℝ) ^ (j + 1) := by push_cast [k]; rfl
    push_cast at h'
    rw [e] at h' hk1
    nlinarith
  calc ‖∑ x ∈ S, C x 0‖ ≤ ∑ x ∈ S, ‖C x 0‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ S, ℓC ^ 2 := sum_le_sum fun x _ => norm_cov_le hG hB x 0
    _ = S.card * ℓC ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 9 * ((L : ℝ) ^ (j + 1)) ^ 2 * ℓC ^ 2 := by
        have : 0 ≤ ℓC ^ 2 := sq_nonneg _
        nlinarith

/-! ### The flow sequence of a history -/

section Seq

variable (R : RGPar 2 L N) [Fact (0 < R.ℓ)] [Fact (0 < R.A)]

/-- **The flow sequence of a history**, truncated after step `j`: covariances `C_i` of the steps,
`s ≡ 1`, and the couplings of `V♭_i`. -/
def histFS (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) : FlowSeq 2 L N where
  C i := if i ≤ j then stCov R i (rawHist R i t) else 0
  s _ := 1
  κ i := stKap R i (rawHist R i t) (t i).1 (t i).2.1

theorem histFS_C {j : ℕ} (t : Flow2.Hist.Seq (Xs R)) {i : ℕ} (hi : i ≤ j) :
    (histFS R j t).C i = stCov R i (rawHist R i t) := by
  simp only [histFS, if_pos hi]

theorem histFS_Vin (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) (i : ℕ) :
    (histFS R j t).Vin i = stVf R i (rawHist R i t) (t i).1 (t i).2.1 := by
  rw [FlowSeq.Vin, stVf_eq_kap]; rfl

/-- **`W^lin` of the flow sequence is the raw state.** -/
theorem histFS_Wlin (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ i ≤ j + 1, (histFS R j t).Wlin i = (rawHist R i t).Wl
  | 0, _ => rfl
  | i + 1, hi => by
    rw [FlowSeq.Wlin_succ, histFS_Wlin j t i (by omega), histFS_Vin, histFS_C R t (by omega)]
    rfl

/-- A common Gram scale for the covariances of the steps `≤ j`. -/
def ellM (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) : ℝ :=
  ∑ i ∈ range (j + 1), fscale (stZ' R (rawHist R i t)) * R.ℓ / 4

theorem histFS_good {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) (t : Flow2.Hist.Seq (Xs R)) :
    ∀ i, GoodCov2 i (ellM R j t) ((histFS R j t).C i) := by
  have hℓ : 0 < R.ℓ := Fact.out
  have hρ := (hV 0 (Nat.zero_le _)).2.2.2.1
  have hnn : ∀ i ∈ range (j + 1), 0 ≤ fscale (stZ' R (rawHist R i t)) * R.ℓ / 4 := fun i _ => by
    unfold fscale; positivity
  intro i
  by_cases hi : i ≤ j
  · rw [histFS_C R t hi]
    have H := rawInv_hist R hρ i (fun i' hi' => hV i' (by omega)) t
    exact (H.cov (hV i hi)).1.mono (single_le_sum hnn (mem_range.2 (by omega)))
  · simp only [histFS, if_neg hi]
    exact goodCov2_zero i (sum_nonneg hnn)

/-- **The `g`-component of `Loc S(V♭, W^lin)` along a history** (`FlowSeq.kappaS_g`): with
`g_k`, `ν_k` the couplings of `V♭_k` and `C⁽¹⁾ = ∑_x C_j(x, 0)`,
`∑_{k<j} g_k² b_{j,k} + g_j² q_{j,j} + 4 C⁽¹⁾ g_j (ν_j + 4 g_j δ)`. -/
theorem hist_LS_g {j : ℕ} (hV : ∀ i ≤ j, ValidAt R i) (t : Flow2.Hist.Seq (Xs R)) :
    ∃ c₀ δ : ℂ, (∀ x, stCov R j (rawHist R j t) x x = c₀) ∧
      (∀ x e, stCov R j (rawHist R j t) (x + dirVec e) x = c₀ + δ) ∧
      cvec4 (blockSet (L := L) (N := N) j 0) R.i₀
        (LS j (stCov R j (rawHist R j t)) (stVf R j (rawHist R j t) (t j).1 (t j).2.1)
          (rawHist R j t).Wl 0 : Alg 2 L N) 3 =
        ∑ k ∈ range j, ((histFS R j t).κ k).g ^ 2 *
            (histFS R j t).beta j k 0 R.i₀ (eC 3) (eC 3) 3 +
          ((histFS R j t).κ j).g ^ 2 * (histFS R j t).betaQ j j 0 R.i₀ (eC 3) (eC 3) 3 +
          4 * (∑ x, stCov R j (rawHist R j t) x 0) * ((histFS R j t).κ j).g *
            (((histFS R j t).κ j).nu + 2 * (2 : ℕ) * ((histFS R j t).κ j).g * δ) := by
  have hρ := (hV 0 (Nat.zero_le _)).2.2.2.1
  have hVj := hV j le_rfl
  obtain ⟨hj2, hd, hL, -⟩ := hVj
  have H := rawInv_hist R hρ j (fun i' hi' => hV i' (by omega)) t
  obtain ⟨-, -, hCs, hsym⟩ := H.cov (hV j le_rfl)
  set D := histFS R j t
  have hCj : D.C j = stCov R j (rawHist R j t) := histFS_C R t le_rfl
  have hCs' : CSym (D.C j) := by rw [hCj]; exact hCs
  have hsym' : ∀ x y, D.C j x y = D.C j y x := by rw [hCj]; exact hsym
  obtain ⟨c₀, δ, hc₀, hδ, hδ'⟩ := covProps (by norm_num) hCs' hsym'
  have h0 := zero_mem_blockIdx (d := 2) (L := L) (N := N) j
  have hk := D.kappaS_g (by norm_num) hL (by omega) (histFS_good R hV t) h0 R.i₀
    (covH_of_good hL (by omega) (histFS_good R hV t j) hCs' hsym')
    (region_of_size (by norm_num) hL (by omega) h0) hc₀ hδ hδ'
  refine ⟨c₀, δ, fun x => by rw [← hCj]; exact hc₀ x, fun x e => by rw [← hCj]; exact hδ x e, ?_⟩
  have hW : (fun b' => sigE (D.s j) (D.Wlin j b')) = (rawHist R j t).Wl := by
    funext b'
    rw [histFS_Wlin R j t j (by omega)]
    exact sigE_one' _
  rw [hW, histFS_Vin, hCj] at hk
  rw [hk, ← hCj]

/-- The accumulated zero mode after step `j`. -/
theorem rawHist_w1_succ (j : ℕ) (t : Flow2.Hist.Seq (Xs R)) :
    (rawHist R (j + 1) t).w1 = (rawHist R j t).w1 + ∑ x, stCov R j (rawHist R j t) x 0 := rfl

/-- **The accumulated zero mode is `O(L^{2j})` in normalised units**:
`|Z_{j+1} w^{(1)}_j| ≤ ℓ² L^{2j}`. -/
theorem norm_Zw1_le (hρ : 0 ≤ R.ρ) :
    ∀ j, (∀ i < j + 1, ValidAt R i) → ∀ t : Flow2.Hist.Seq (Xs R),
      ‖stZ' R (rawHist R j t) * (rawHist R j t).w1‖ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2
  | 0, _, t => by
    have : (rawHist R 0 t).w1 = 0 := rfl
    rw [this, mul_zero, norm_zero]; positivity
  | j + 1, hV, t => by
    have ih := norm_Zw1_le hρ j (fun i hi => hV i (by omega)) t
    have hVj := hV j (by omega)
    obtain ⟨hj2, -, hL8, -, hρ8, hℓ, -⟩ := hVj
    have H := rawInv_hist R hρ j (fun i hi => hV i (by omega)) t
    set st := rawHist R j t
    have hZ : st.Z ≠ 0 := H.Z_ne_zero (by linarith)
    have hζ : ‖stZeta R st‖ ≤ 1 / 8 := (norm_stZeta_le hρ st).trans hρ8
    have hZ' : stZ' R st ≠ 0 := mul_ne_zero hZ (one_add_ne_zero (by linarith))
    have hZ'n : 0 < ‖stZ' R st‖ := norm_pos_iff.2 hZ'
    -- the new zero mode
    obtain ⟨hC, -⟩ := H.cov (hV j (by omega))
    have hz := zero_mode_le (by omega) hC
    have hℓC : (fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) * R.ℓ / 4) ^ 2 =
        R.ℓ ^ 2 / (16 * ‖stZ' R st‖) := by
      rw [div_pow, mul_pow, show fscale (st.Z * (1 + absorbZeta R st.Z (st.z + st.y))) ^ 2 =
        ‖stZ' R st‖⁻¹ from by unfold fscale; rw [Real.sq_sqrt (inv_nonneg.2 (norm_nonneg _))]; rfl]
      field_simp; ring
    rw [hℓC] at hz
    have hzZ : ‖stZ' R st * ∑ x, stCov R j st x 0‖ ≤ 9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ (j + 1)) ^ 2 := by
      rw [norm_mul]
      calc ‖stZ' R st‖ * ‖∑ x, stCov R j st x 0‖
          ≤ ‖stZ' R st‖ * (9 * ((L : ℝ) ^ (j + 1)) ^ 2 * (R.ℓ ^ 2 / (16 * ‖stZ' R st‖))) :=
            mul_le_mul_of_nonneg_left hz (norm_nonneg _)
        _ = _ := by field_simp
    -- the next normalisation
    set st' := rawHist R (j + 1) t
    have hst'Z : st'.Z = stZ' R st := rfl
    have hVj1 := hV (j + 1) (Nat.lt_succ_self _)
    have hρ8' := hVj1.2.2.2.2.1
    have hζ' : ‖stZeta R st'‖ ≤ 1 / 8 := (norm_stZeta_le hρ st').trans hρ8'
    have e : stZ' R st' * st'.w1 = (1 + stZeta R st') *
        (stZ' R st * st.w1 + stZ' R st * ∑ x, stCov R j st x 0) := by
      show st'.Z * (1 + stZeta R st') * (st.w1 + ∑ x, stCov R j st x 0) = _
      rw [hst'Z]; ring
    rw [e, norm_mul]
    have h1 : ‖1 + stZeta R st'‖ ≤ 9 / 8 := by
      refine (norm_add_le _ _).trans ?_; rw [norm_one]; linarith
    have h2 := (norm_add_le _ _).trans (add_le_add ih hzZ)
    have hL2 : (4 : ℝ) ≤ (L : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ L := by exact_mod_cast (show 2 ≤ L by omega)
      nlinarith
    have hP : ((L : ℝ) ^ (j + 1)) ^ 2 = (L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2 := by ring
    rw [hP] at h2 ⊢
    have hl : 0 ≤ R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 := by positivity
    calc ‖1 + stZeta R st'‖ * ‖stZ' R st * st.w1 + stZ' R st * ∑ x, stCov R j st x 0‖
        ≤ 9 / 8 * (R.ℓ ^ 2 * ((L : ℝ) ^ j) ^ 2 +
            9 / 16 * R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ ≤ R.ℓ ^ 2 * ((L : ℝ) ^ 2 * ((L : ℝ) ^ j) ^ 2) := by nlinarith

end Seq

end

end Step2
